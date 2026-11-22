#!/usr/bin/env pypy3
"""ode2.py: Prototype single-tool front end for higher-level Ode (trial, two targets).

Implements the concrete constructs from paper/ODE.md sections 4 and 5:
  target x86_64 | aarch64
  data NAME = W0, W1, ...
  inline fn NAME(p: kind, ...) [distinct(a, b) ...] [changes p, ...] { ... }
  fn NAME as "SYMBOL" {
      reg ALIAS = REG
      frame { FIELD: COUNT * KIND | BYTES  ... }    // kinds: byte/u8(1), u32(4), u64(8), cv(32), block(64)
      for VAR in START..END { ... }
      place { LINES... }                             // attached to the following instruction; byte offset computed
      DST := SRC                                     // explicit store (register, immediate, memory, frame slot, &field)
      RAW INSTRUCTION                                // any raw target instruction remains valid
  }

Nothing is chosen silently: no register allocation, no spills, no inserted moves, no instruction rewriting.
Every check (frame slot bounds, register kind, distinctness, inline `changes`) reports `<file>:<line>: ...`.
"""
import os, re, struct, sys

KINDS_BYTES = {"byte": 1, "u8": 1, "u32": 4, "word": 4, "u64": 8, "qword": 8, "cv": 32, "block": 64}
X86_GPR64 = set("rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split())
X86_GPR32 = set("eax ecx edx ebx esp ebp esi edi r8d r9d r10d r11d r12d r13d r14d r15d".split())
X86_ZMM = {f"zmm{i}" for i in range(32)}
X86_XMM = {f"xmm{i}" for i in range(16)}
ARM_GPR64 = {f"x{i}" for i in range(31)} | {"sp", "xzr"}
ARM_GPR32 = {f"w{i}" for i in range(31)} | {"wzr"}
ARM_VREG = {f"v{i}" for i in range(32)}

class OdeError(Exception):
    def __init__(self, src, line, msg):
        super().__init__(f"{src}:{line}: {msg}")
        self.src, self.line, self.msg = src, line, msg

def strip_comment(line):
    return line.split("//", 1)[0].strip()

def eval_int(expr, env, src, line):
    e = expr.strip()
    for k, v in env.items():
        e = re.sub(r"\b" + re.escape(k) + r"\b", str(v), e)
    if not re.fullmatch(r"[0-9a-fA-FxX\s+\-*()]+", e):
        raise OdeError(src, line, f"expected integer expression, got `{expr}`")
    try:
        return int(eval(e, {"__builtins__": {}}, {}))
    except Exception as ex:
        raise OdeError(src, line, f"cannot evaluate `{expr}`: {ex}")

def check_reg_kind(target, reg, kind, src, line):
    if target == "x86_64":
        ok = {"gpr": X86_GPR64, "gpr32": X86_GPR32, "zmm": X86_ZMM, "xmm": X86_XMM}.get(kind)
    else:
        ok = {"gpr": ARM_GPR64, "gpr32": ARM_GPR32, "vreg": ARM_VREG}.get(kind)
    if ok is None:
        raise OdeError(src, line, f"unknown register kind `{kind}` for target {target}")
    if reg not in ok:
        raise OdeError(src, line, f"register `{reg}` is not of kind `{kind}` on {target}")

def base_reg(target, tok):
    """Canonical register name written by an operand token (e.g. `v0.16b` -> `v0`, `eax` -> `rax`)."""
    t = tok.strip().lower()
    if target == "aarch64":
        m = re.fullmatch(r"(v\d+)(?:\.[0-9]+[bhsd])?", t)
        if m: return m.group(1)
        m = re.fullmatch(r"([xw]\d+|sp|xzr|wzr)", t)
        if m: return m.group(1)
        return None
    # x86_64
    if t in X86_ZMM or t in X86_XMM or t in X86_GPR64: return t
    m32 = {"eax": "rax", "ecx": "rcx", "edx": "rdx", "ebx": "rbx", "esp": "rsp", "ebp": "rbp", "esi": "rsi", "edi": "rdi"}
    if t in m32: return m32[t]
    if t in X86_GPR32 and t.endswith("d"): return t[:-1]
    return None

def written_reg_of_insn(target, insn):
    """First operand register written by an instruction (Intel syntax on x86-64, standard on AArch64)."""
    parts = insn.strip().split(None, 1)
    if not parts: return None
    op = parts[0].lower()
    if op in ("cmp", "test", "jmp", "je", "jne", "jae", "jb", "cbz", "cbnz", "b", "b.eq", "b.ne", "b.vs",
              "ret", "nop", "call", "bl", "vzeroupper", "endbr64", "st1", "str"):
        return None
    if len(parts) < 2: return None
    first = parts[1].split(",", 1)[0].strip()
    if first.startswith("[") or "ptr" in first.lower():
        return None
    return base_reg(target, first)

def parse_block(lines, start, src):
    depth, j = 1, start
    while depth:
        if j >= len(lines):
            raise OdeError(src, start, "a `{` block with no `}`")
        s = strip_comment(lines[j])
        if s.endswith("{"): depth += 1
        elif s == "}": depth -= 1
        j += 1
    return [(k + 1, lines[k]) for k in range(start, j - 1)], j

def parse_file(text, src="<source>"):
    lines = text.splitlines()
    target = None
    data, inlines, fns = [], {}, []
    i = 0
    while i < len(lines):
        lineno = i + 1
        s = strip_comment(lines[i]); i += 1
        if not s: continue
        m = re.fullmatch(r"target\s+(x86_64|aarch64)", s)
        if m:
            if target is not None:
                raise OdeError(src, lineno, "duplicate `target` declaration")
            target = m.group(1); continue
        m = re.fullmatch(r"data\s+(\w+)\s*=\s*(.+)", s)
        if m:
            ws = [int(w.strip().replace("_", ""), 0) for w in m.group(2).split(",")]
            data.append((m.group(1), ws)); continue
        m = re.fullmatch(r"inline\s+fn\s+(\w+)\(([^)]*)\)(.*)\{", s)
        if m:
            if target is None:
                raise OdeError(src, lineno, "`target` must appear before `inline fn`")
            name = m.group(1)
            params = []
            if m.group(2).strip():
                for p in m.group(2).split(","):
                    pm = re.fullmatch(r"(\w+)\s*:\s*(\w+)", p.strip())
                    if not pm: raise OdeError(src, lineno, f"bad parameter `{p.strip()}`")
                    params.append((pm.group(1), pm.group(2)))
            pnames = [p for p, _ in params]
            clauses = m.group(3).strip()
            distincts = []
            for dm in re.finditer(r"distinct\(\s*(\w+)\s*,\s*(\w+)\s*\)", clauses):
                a, b = dm.group(1), dm.group(2)
                if a not in pnames or b not in pnames:
                    raise OdeError(src, lineno, f"distinct({a}, {b}) names an unknown parameter")
                distincts.append((a, b))
            changes = None
            cm = re.search(r"changes\s+([A-Za-z0-9_,\s]+)$", re.sub(r"distinct\([^)]*\)", "", clauses).strip())
            if cm:
                changes = [c.strip() for c in cm.group(1).split(",") if c.strip()]
                for c in changes:
                    if c not in pnames:
                        raise OdeError(src, lineno, f"changes names unknown parameter `{c}`")
            body, i = parse_block(lines, i, src)
            inlines[name] = {
                "line": lineno, "params": params, "distincts": distincts,
                "changes": changes, "body": body,
            }
            continue
        m = re.fullmatch(r'fn\s+(\w+)\s+as\s+"(\w+)"\s*\{', s)
        if m:
            if target is None:
                raise OdeError(src, lineno, "`target` must appear before `fn`")
            body, i = parse_block(lines, i, src)
            fns.append((m.group(1), m.group(2), lineno, body))
            continue
        raise OdeError(src, lineno, f"not a `target`, `data`, `fn` or `inline fn` line: `{s}`")
    if target is None:
        raise OdeError(src, 1, "missing `target x86_64` or `target aarch64`")
    return target, data, inlines, fns

def parse_frame(body, src):
    """Parse frame { name: count * kind | name: bytes } -> (total_size, fields_dict)."""
    off = 0
    fields = {}
    for lineno, raw in body:
        s = strip_comment(raw)
        if not s: continue
        m = re.fullmatch(r"(\w+)\s*:\s*(\d+)\s*\*\s*(\w+)", s)
        if m:
            fname, cnt, kind = m.group(1), int(m.group(2)), m.group(3)
            if kind not in KINDS_BYTES:
                raise OdeError(src, lineno, f"unknown frame element kind `{kind}`")
            if fname in fields:
                raise OdeError(src, lineno, f"duplicate frame field `{fname}`")
            elem = KINDS_BYTES[kind]
            size = cnt * elem
            fields[fname] = {"offset": off, "count": cnt, "elem": elem, "size": size, "kind": kind}
            off += size
            continue
        m = re.fullmatch(r"(\w+)\s*:\s*(\d+)", s)
        if m:
            fname, size = m.group(1), int(m.group(2))
            if fname in fields:
                raise OdeError(src, lineno, f"duplicate frame field `{fname}`")
            fields[fname] = {"offset": off, "count": size, "elem": 1, "size": size, "kind": "byte"}
            off += size
            continue
        raise OdeError(src, lineno, f"bad frame entry: `{s}`")
    return off, fields

def compile_fn(target, name, symbol, fn_line, body, inlines, src):
    regs = {}       # alias -> concrete reg
    frame_size = 0
    frame_fields = {}
    out = []        # list of (lineno, lowered_instruction_or_label)
    places = []     # list of (instr_index, place_lines)

    def subst_regs_and_vars(s, vars_env):
        # Replace frame.size first
        s = re.sub(r"\bframe\.size\b", str(frame_size), s)
        # Replace loop vars (avoiding inside registers/identifiers)
        for k, v in vars_env.items():
            s = re.sub(r"\b" + re.escape(k) + r"\b", str(v), s)
        # Replace register aliases (word boundary; supports `d.16b` too since `.` is non-word)
        for alias, real in regs.items():
            s = re.sub(r"\b" + re.escape(alias) + r"\b", real, s)
        return s

    def resolve_frame_slot(expr, vars_env, lineno):
        """Parse `field[idx]` or `field.qword[idx]` -> (size_word, byte_offset)."""
        m = re.fullmatch(r"(\w+)(?:\.(byte|u8|u32|word|u64|qword))?\[([^\]]+)\]", expr.strip())
        if not m: return None
        fname, view, idx_expr = m.group(1), m.group(2), m.group(3)
        if fname not in frame_fields:
            raise OdeError(src, lineno, f"unknown frame field `{fname}`")
        f = frame_fields[fname]
        idx = eval_int(idx_expr, vars_env, src, lineno)
        if view is None:
            elem, cnt = f["elem"], f["count"]
        else:
            elem = KINDS_BYTES[view]
            if f["size"] % elem != 0:
                raise OdeError(src, lineno, f"frame field `{fname}` ({f['size']} bytes) is not a multiple of {elem}")
            cnt = f["size"] // elem
        if idx < 0 or idx >= cnt:
            vtag = f".{view}" if view else ""
            raise OdeError(src, lineno, f"frame slot `{fname}{vtag}[{idx}]` out of bounds (declared 0..{cnt})")
        return elem, f["offset"] + idx * elem

    def resolve_mem_expr(expr, vars_env, lineno):
        """Parse `qword [base + expr]` or `dword [base + expr]` or `byte [base + expr]`."""
        m = re.fullmatch(r"(qword|dword|byte)\s*\[\s*(\w+)\s*(?:([+-])\s*(.+))?\s*\]", expr.strip())
        if not m: return None
        sz_word, base_tok, sign, off_expr = m.group(1), m.group(2), m.group(3), m.group(4)
        base = regs.get(base_tok, base_tok)
        off = 0
        if off_expr is not None:
            off = eval_int(off_expr, vars_env, src, lineno)
            if sign == "-": off = -off
        return sz_word, base, off

    def lower_store(lhs, rhs, vars_env, lineno):
        lhs, rhs = lhs.strip(), rhs.strip()
        if target != "x86_64":
            raise OdeError(src, lineno, "`:=` store sugar currently implemented for x86_64; use raw AArch64 instructions")
        # Case 1: dst := &field  (lea dst, [rsp + offset])
        m_addr = re.fullmatch(r"&(\w+)", rhs)
        if m_addr:
            fname = m_addr.group(1)
            if fname not in frame_fields:
                raise OdeError(src, lineno, f"unknown frame field `{fname}` in `&{fname}`")
            dst = regs.get(lhs, lhs)
            return f"lea {dst}, [rsp + {frame_fields[fname]['offset']}]"
        # Case 2: frame_slot := reg
        if "[" in lhs and not re.match(r"^(qword|dword|byte)\s*\[", lhs):
            elem, off = resolve_frame_slot(lhs, vars_env, lineno)
            if elem != 8:
                raise OdeError(src, lineno, f"frame store expects 8-byte slot, got {elem}-byte slot `{lhs}`")
            src_r = regs.get(rhs, rhs)
            return f"mov qword ptr [rsp + {off}], {src_r}"
        # Case 3: qword [base + off] := reg
        mem_l = resolve_mem_expr(lhs, vars_env, lineno)
        if mem_l is not None:
            sz_word, base, off = mem_l
            src_r = regs.get(rhs, rhs)
            return f"mov {sz_word} ptr [{base} + {off}], {src_r}"
        # Case 4: reg := frame_slot
        if "[" in rhs and not re.match(r"^(qword|dword|byte)\s*\[", rhs):
            elem, off = resolve_frame_slot(rhs, vars_env, lineno)
            if elem != 8:
                raise OdeError(src, lineno, f"frame load expects 8-byte slot, got {elem}-byte slot `{rhs}`")
            dst = regs.get(lhs, lhs)
            return f"mov {dst}, qword ptr [rsp + {off}]"
        # Case 5: reg := qword/dword/byte [base + off]
        mem_r = resolve_mem_expr(rhs, vars_env, lineno)
        if mem_r is not None:
            sz_word, base, off = mem_r
            dst = regs.get(lhs, lhs)
            return f"mov {dst}, {sz_word} ptr [{base} + {off}]"
        # Case 6: reg := reg | immediate
        dst = regs.get(lhs, lhs)
        val = subst_regs_and_vars(rhs, vars_env)
        return f"mov {dst}, {val}"

    def expand_inline(iname, arg_tokens, call_line):
        inf = inlines[iname]
        params = inf["params"]
        if len(arg_tokens) != len(params):
            raise OdeError(src, call_line, f"inline fn `{iname}` expects {len(params)} arguments, got {len(arg_tokens)}")
        binding = {}
        for (pname, pkind), tok in zip(params, arg_tokens):
            real = regs.get(tok, tok)
            check_reg_kind(target, real, pkind, src, call_line)
            binding[pname] = real
        # Distinctness checks
        for a, b in inf["distincts"]:
            if binding[a] == binding[b]:
                raise OdeError(src, call_line, f"inline fn `{iname}`: distinct({a}, {b}) violated (both bound to {binding[a]})")
        allowed_writes = None
        if inf["changes"] is not None:
            allowed_writes = {binding[c] for c in inf["changes"]}
        for bline, braw in inf["body"]:
            bs = strip_comment(braw)
            if not bs: continue
            inst = bs
            for pname, real in binding.items():
                inst = re.sub(r"\b" + re.escape(pname) + r"\b", real, inst)
            if allowed_writes is not None:
                w = written_reg_of_insn(target, inst)
                if w is not None and w not in allowed_writes:
                    raise OdeError(src, bline, f"inline fn `{iname}`: instruction `{inst}` writes `{w}`, not listed in changes ({', '.join(inf['changes'])})")
            out.append((call_line, inst))

    def process_lines(block_lines, vars_env):
        k = 0
        while k < len(block_lines):
            lineno, raw = block_lines[k]; k += 1
            s = strip_comment(raw)
            if not s: continue
            m = re.fullmatch(r"reg\s+(\w+)\s*=\s*(\w+)", s)
            if m:
                regs[m.group(1)] = m.group(2); continue
            if s == "frame {":
                sub, k2 = parse_block([r for _, r in block_lines], k, src)
                # Adjust sub line numbers back to original file line numbers
                sub_orig = [(block_lines[idx - 1][0], block_lines[idx - 1][1]) for idx in range(k + 1, k2)]
                nonlocal frame_size, frame_fields
                frame_size, frame_fields = parse_frame(sub_orig, src)
                k = k2; continue
            if s == "place {":
                _, k2 = parse_block([r for _, r in block_lines], k, src)
                plines = [strip_comment(block_lines[idx - 1][1]) for idx in range(k + 1, k2)]
                plines = [l for l in plines if l]
                places.append((len(out), plines))
                k = k2; continue
            m = re.fullmatch(r"for\s+(\w+)\s+in\s+([^.]+)\.\.([^{]+)\{", s)
            if m:
                vname = m.group(1)
                lo = eval_int(m.group(2), vars_env, src, lineno)
                hi = eval_int(m.group(3), vars_env, src, lineno)
                _, k2 = parse_block([r for _, r in block_lines], k, src)
                sub_orig = [(block_lines[idx - 1][0], block_lines[idx - 1][1]) for idx in range(k + 1, k2)]
                for val in range(lo, hi):
                    process_lines(sub_orig, {**vars_env, vname: val})
                k = k2; continue
            # Inline fn call: NAME(a, b, ...)
            m = re.fullmatch(r"(\w+)\(([^)]*)\)", s)
            if m and m.group(1) in inlines:
                args = [a.strip() for a in m.group(2).split(",")] if m.group(2).strip() else []
                expand_inline(m.group(1), args, lineno); continue
            # Store sugar: LHS := RHS
            if ":=" in s:
                lhs, rhs = s.split(":=", 1)
                out.append((lineno, lower_store(lhs, rhs, vars_env, lineno))); continue
            # Label or raw instruction
            inst = subst_regs_and_vars(s, vars_env)
            if target == "x86_64":
                m_call = re.fullmatch(r"call\s+(\w+)", inst)
                if m_call and m_call.group(1) not in X86_GPR64:
                    inst = f"call CALL({m_call.group(1)})"
                inst = re.sub(r"@(\w+)", lambda g: f".Lode_{name}_{g.group(1)}", inst)
                inst = re.sub(r"#([A-Za-z_]\w*)", lambda g: f".Lode_data_{g.group(1)}", inst)
            else:
                inst = re.sub(r"@(\w+)", lambda g: f".Lode_{name}_{g.group(1)}", inst)
            out.append((lineno, re.sub(r"\s+", " ", inst)))

    process_lines(body, {})
    return {
        "name": name, "symbol": symbol, "line": fn_line,
        "frame_size": frame_size, "frame_fields": frame_fields,
        "instructions": [inst for _, inst in out],
        "places": places,
    }

def read_elf_place_offset(elf_bytes):
    """Read the 4-byte uint32 offset from the `.ode.place` section of an x86-64 ELF object."""
    e_shoff = struct.unpack_from("<Q", elf_bytes, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", elf_bytes, 58)
    shstr_off = struct.unpack_from("<Q", elf_bytes, e_shoff + e_shstrndx * e_shentsize + 24)[0]
    for i in range(e_shnum):
        base = e_shoff + i * e_shentsize
        sh_name, _, _, _, sh_off, sh_size = struct.unpack_from("<IIQQQQ", elf_bytes, base)
        end = elf_bytes.index(b"\0", shstr_off + sh_name)
        sname = elf_bytes[shstr_off + sh_name:end].decode()
        if sname == ".ode.place":
            assert sh_size == 4
            return struct.unpack_from("<I", elf_bytes, sh_off)[0]
    raise RuntimeError("missing .ode.place section")

def emit_x86_elf(compiled, data, core_dir):
    sys.path.insert(0, core_dir)
    import asm
    ins = compiled["instructions"]
    # Emit clean ELF (no embedded .ode.place section) AND compute exact place byte offsets if any.
    clean_elf = asm.build_elf(compiled["name"], compiled["symbol"], ins, [], data)
    places_text = []
    for idx, plines in compiled["places"]:
        probe_elf = asm.build_elf(compiled["name"], compiled["symbol"], ins, [("place", idx, "p", plines)], data)
        off = read_elf_place_offset(probe_elf)
        places_text.append(f"place +0x{off:x} {{\n" + "".join(f"    {l}\n" for l in plines) + "}\n")
    return clean_elf, "".join(places_text)

def emit_aarch64_asm(compiled_list, macho=True):
    lines = [".text"]
    for c in compiled_list:
        sym = ("_" + c["symbol"]) if macho else c["symbol"]
        lines.extend([".p2align 2", f".global {sym}", f"{sym}:"])
        for inst in c["instructions"]:
            lines.append(inst if inst.endswith(":") else "    " + inst)
    return "\n".join(lines) + "\n"

def compile_source(text, src="<source>"):
    target, data, inlines, fns = parse_file(text, src)
    compiled = [compile_fn(target, name, sym, fline, body, inlines, src) for name, sym, fline, body in fns]
    return target, data, compiled

if __name__ == "__main__":
    print("ode2.py library ready")
