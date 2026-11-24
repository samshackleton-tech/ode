#!/usr/bin/env python3
"""odec: Ode source to assembly, and to an object.

    python3 odec.py SOURCE.ode NAME            prints the assembly of the function NAME
    python3 odec.py SOURCE.ode NAME OUT.o      makes the object from the instruction table, without clang
    python3 odec.py SOURCE.ode NAME --places [ENTRY]   prints the function's places, as the prover of proof-core reads them
    python3 odec.py SOURCE.ode --all FOLDER    makes FOLDER/NAME.o for every function of the source
    python3 odec.py --from FOLDER NAME OUT.o   makes the object of the function NAME of whichever source in FOLDER has it

Ode has one layer: a function is the instructions its coder chose, one a line, as an assembler takes them
(Intel syntax). Nothing is chosen here: no register, no instruction, no layout. The source:

    target x86_64                       the processor the source is written for; x86_64 where the line is missing
    data NAME = NUMBER, NUMBER, ...     32-bit words of read-only data, on a 64-byte boundary; `#NAME` is its address
    inline fn NAME(P: CLASS, Q: CLASS) distinct(P, Q) changes P {
      LINES                             an inline function: wherever a function says `NAME(r, s)`, LINES stand,
    }                                   with the register r for P and s for Q (more below; its head may go over lines)
    fn NAME as "SYMBOL" {               a function, under the name SYMBOL that a linker sees
      INSTRUCTION                       an instruction (`call SYMBOL` calls a function by its linker name)
      @LABEL:                           a place a jump names: `jmp @LABEL`
      NAME(r, s)                        a use of the inline function NAME: its instructions, here
      reg NAME = REGISTER               from here on in the function, NAME in an operand is that register (never in
                                        `call`, which takes the name a linker knows a function by)
      frame { FIELD: COUNT * KIND ... } the function's frame: its fields in their order, the first at the stack pointer
      DST := SRC                        one `mov` (or one `lea`): a store into a register or into memory (more below)
      for I in 0..8 { LINES }           LINES eight times, with `$I` replaced by 0 to 7
      place { LINES }                   what holds whenever the code comes to the instruction after it (a loop's
                                        invariant, in the lines the prover of proof-core reads); no part of the object
      place "SYMBOL" { LINES }          the same, for the proof of the function as entered at `entry "SYMBOL"`
      place B { LINES }                 for kcheck's verifier of kernels (kfn.py): what holds here after B turns of a loop
      entry "SYMBOL"                    the function is entered here too, under that name
      .p2align N                        (first line) the boundary the function starts on; 16 bytes without it
    }
    // a comment

A place is written where it holds. The prover is given it with the count of bytes from the function's first
byte (or from the entry's) to that instruction: `--places` prints that, and the count is worked out here,
so it moves with the code.

`DST := SRC` is one instruction, and which one is fixed by what stands on its two sides. A side is a general
register; a number; memory, written `byte [ADDRESS]`, `dword [ADDRESS]` or `qword [ADDRESS]`, the address being a
register, or two, and a number; a slot of the frame, `FIELD[I]`; or, on the right, `&FIELD`, the address of a
field. `R := &FIELD` is `lea R, [rsp + N]`, R being a register of 64 bits. Every other is `mov DST, SRC`: into a
register from a register, a number or memory, and into memory from a register or a number. Where both sides
have a size (a register's, or memory's `byte`, `dword`, `qword`, or a slot's kind), the two must be the same:
`:=` moves as many bytes as both sides say, and never widens or cuts. Whether the table of instructions has
that `mov` is the assembler's to say, as for a `mov` written out. Numbers in an address and in a slot may be
sums and products of constants (`[rbx + $w * 8]`), worked out here. A vector register is moved by an
instruction the coder names.

A frame's fields lie in the order written, each `COUNT * KIND` (kinds: byte, u32, u64, cv of 32 bytes, block
of 64) or a plain count of bytes. `frame.size` is the bytes of all of them. `FIELD[I]` is the slot I of a
field, at `[rsp + N]`, and `FIELD.KIND[I]` the same bytes taken as slots of another kind; a slot outside
the field is refused at its line. The slots are counted from the stack pointer as it is once the function
has taken `frame.size` from it: nothing here follows the stack pointer, and the verifier judges the code.

An inline function says, of each register it takes, which class it is of (gpr, gpr32, xmm, zmm). It may say
which of them must differ: `distinct(P, Q, ...)`, as often as needed; no two of those named in one may be
given the same register, or two parts of one register. And it says which it changes: `changes P, ...`;
without that, none. Its lines name a register only by a parameter. These are refused, each at its line: a
use that gives a register of another class; a use that gives one register for two that must differ; a line
of the inline function that names a register outright; and a line that changes a register which `changes`
does not list (what an instruction changes is read from its row of the instruction table; the flags and
bytes of memory are not registers, and `changes` does not speak of them). A use puts the inline function's
instructions there and nothing else: no call, no return, no move. A label in an inline function is each
use's own. An inline function may be used in a `for` and in another inline function; it may hold a `for`
but no `place`, `entry` or `call`.

The forms that expand (a use of an inline function, a `for`, a name for a register, `:=`, a slot of the
frame) do so in the one way written above. Each instruction is then laid down by the instruction table as
the instruction it names, or refused (../core/asm.py); a refusal names the source line and quotes the line
as it was typed. What the verifier is given is the object's bytes; nothing here is relied on."""
import importlib.util, itertools, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
G64 = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split()
G32 = "eax ecx edx ebx esp ebp esi edi r8d r9d r10d r11d r12d r13d r14d r15d".split()
G16 = "ax cx dx bx sp bp si di r8w r9w r10w r11w r12w r13w r14w r15w".split()
G8 = "al cl dl bl spl bpl sil dil r8b r9b r10b r11b r12b r13b r14b r15b".split()
REGISTERS = set(G64)
TARGETS = ("x86_64", "arm64")
# The classes a parameter of an inline function may be of; and, for every name of a register, the whole
# register it is or is a part of (`eax` and `al` are parts of `rax`; `xmm3` is a part of `zmm3`).
CLASSES = {"gpr": set(G64), "gpr32": set(G32), "xmm": {f"xmm{i}" for i in range(32)}, "zmm": {f"zmm{i}" for i in range(32)}}
WHOLE = {n: G64[i] for names in (G64, G32, G16, G8, ("ah", "ch", "dh", "bh")) for i, n in enumerate(names)}
WHOLE.update({f"{p}mm{i}": f"zmm{i}" for p in "xyz" for i in range(32)})
WHOLE.update({f"k{i}": f"k{i}" for i in range(8)})
GENERAL = {r: size for names, size in ((G64, 8), (G32, 4), (G16, 2), (G8, 1)) for r in names}        # the general registers, and the bytes of each

ARM_G64 = [f"x{i}" for i in range(31)]
ARM_G32 = [f"w{i}" for i in range(31)]
ARM_VEC = [f"v{i}" for i in range(32)]
ARM_CLASSES = {"gpr": set(ARM_G64), "gpr32": set(ARM_G32), "vec": set(ARM_VEC)}
ARM_WHOLE = {f"x{i}": f"x{i}" for i in range(31)}
ARM_WHOLE.update({f"w{i}": f"x{i}" for i in range(31)})
ARM_WHOLE.update({"sp": "sp", "wsp": "sp", "xzr": "xzr", "wzr": "xzr"})
ARM_WHOLE.update({f"v{i}": f"v{i}" for i in range(32)})
ARM_GENERAL = {r: 8 for r in ARM_G64}
ARM_GENERAL.update({r: 4 for r in ARM_G32})

RESERVED_COMMON = {"frame", "budget", "if", "else", "loop", "while", "break", "continue"}
RESERVED_X86 = {"byte", "word", "dword", "qword", "xmmword", "ymmword", "zmmword", "ptr", "rip"}
RESERVED = RESERVED_COMMON | RESERVED_X86                             # kept for callers importing RESERVED


def _reserved_for(target):
    return RESERVED_COMMON if target == "arm64" else RESERVED


def _reserved_err(what, name, target):
    if target != "arm64" and name in RESERVED_X86:
        return (f"{what} cannot be named `{name}` on x86-64 "
                f"(reserved for memory operands like `byte ptr [...]`; use `p` or `buf` instead)")
    return f"{what} cannot be named `{name}`"
BRANCH_X86 = {"eq": "je", "ne": "jne", "ult": "jb", "uge": "jae"}
BRANCH_ARM = {"eq": "b.eq", "ne": "b.ne", "ult": "b.lo", "uge": "b.hs"}
INVERT_COND = {"eq": "ne", "ne": "eq", "ult": "uge", "uge": "ult"}
COND_ALIAS = {"lo": "ult", "cc": "ult", "hs": "uge", "cs": "uge"}
SIZES = {1: "byte", 4: "dword", 8: "qword"}                        # what one `mov` moves, as memory is written in an operand
KINDS = {"byte": 1, "u32": 4, "u64": 8, "cv": 32, "block": 64}     # what a field of a frame holds, and the bytes of one
BUDGET_KEYS = {
    "max_bytes", "max_icache_lines", "max_frame_bytes",
    "max_line_splits", "max_page_crossings", "max_stlf_partial", "max_alias_4k",
}


def budget_of(src, start_n, body):
    """Advisory performance/layout budgets declared inside a function (`budget { max_bytes 64 ... }`).
    Emits zero bytes in the object; checked by ode_tool.py."""
    out = {}
    for ln, raw in body:
        s = raw.split("//")[0].strip()
        if not s: continue
        m = re.fullmatch(r"(\w+)\s*(?:[:=]\s*|\s+)(.+)", s)
        if not m: stop(src, ln, f"a budget line is `KEY NUMBER`, not `{s}`")
        key, val_s = m.group(1), m.group(2).strip()
        if key not in BUDGET_KEYS:
            stop(src, ln, f"`{key}` is no budget key ({', '.join(sorted(BUDGET_KEYS))})")
        v = number(val_s)
        if v is None or v < 0: stop(src, ln, f"budget `{key}` takes a nonnegative whole number, not `{val_s}`")
        if key in out: stop(src, ln, f"budget `{key}` is listed twice")
        out[key] = v
    return out


def target_spec(target):
    if target == "arm64":
        return ARM_CLASSES, ARM_WHOLE, ARM_GENERAL, set(ARM_G64) | {"sp"}, "sp"
    return CLASSES, WHOLE, GENERAL, set(G64), "rsp"


def read_source(src):
    with open(src) as f:
        return f.read()


def stop(src, n, msg):
    raise SystemExit(f"{src}: line {n}: {msg}")


def number(text):
    """The value of a constant, whole numbers with + - * and brackets; None where the text is not one."""
    tokens, at = re.findall(r"0[xX][0-9a-fA-F_]+|\d[\d_]*|[-+*()]|\S+", text), [0]
    def peek(): return tokens[at[0]] if at[0] < len(tokens) else None
    def take(): at[0] += 1; return tokens[at[0] - 1]
    def atom():
        t = take() if peek() is not None else ""
        if t == "(":
            v = total()
            if peek() != ")": raise ValueError(text)
            take(); return v
        if t in ("-", "+"): return -atom() if t == "-" else atom()
        if re.fullmatch(r"0[xX][0-9a-fA-F_]+|\d[\d_]*", t): return int(t.replace("_", ""), 0)
        raise ValueError(text)
    def product():
        v = atom()
        while peek() == "*": take(); v *= atom()
        return v
    def total():
        v = product()
        while peek() in ("+", "-"): v = v + product() if take() == "+" else v - product()
        return v
    try:
        v = total()
        return v if peek() is None else None
    except ValueError: return None


def frame_of(src, n, body, taken, target="x86_64"):
    """A frame as (its size, {field: (the bytes before it, how many it holds, the bytes of one)}): the fields
    lie in the order written, the first at the stack pointer. `taken`: the names the function has already."""
    _, whole, _, _, _ = target_spec(target)
    fields, size = {}, 0
    for k, line in body:
        f = line.split("//")[0].strip()
        if not f: continue
        m = re.fullmatch(r"(\w+)\s*:\s*(.+)", f)
        if not m: stop(src, k, f"a field of a frame is `NAME: COUNT * KIND` or `NAME: BYTES`, not `{f}`")
        name, what = m.groups()
        if name in whole or name in _reserved_for(target): stop(src, k, _reserved_err("a field", name, target))
        if name in fields or name in taken: stop(src, k, f"`{name}` is a name already")
        m = re.fullmatch(r"(.+)\*\s*([A-Za-z_]\w*)", what)
        count, kind = (number(m.group(1)), m.group(2)) if m else (number(what), "byte")
        if kind not in KINDS: stop(src, k, f"`{kind}` is no kind of a field ({', '.join(KINDS)})")
        if count is None or count < 1: stop(src, k, f"a field holds a count of things, one or more: not `{what.strip()}`")
        fields[name] = (size, count, KINDS[kind]); size += count * KINDS[kind]
    if not fields: stop(src, n, "a frame with no field")
    return size, fields


class Inline:
    """An inline function: its name, the number of its first line, its parameters [(name, class)], the lists
    of parameters that must differ, the parameters it changes, its lines [(number, text)], its labels."""
    def __init__(self, name, line, params, distinct, changes, body):
        self.name, self.line, self.params, self.distinct, self.changes, self.body = name, line, params, distinct, changes, body
        self.labels = {m.group(1) for _, l in body for m in [re.fullmatch(r"@(\w+):", l.split("//")[0].strip())] if m}


def inline_of(src, n, name, params, clauses, body, target="x86_64"):
    """The inline function a source's lines say, or a refusal of what in it cannot be read."""
    classes, whole, _, _, _ = target_spec(target)
    ps = []
    for p in [p.strip() for p in params.split(",")] if params.strip() else []:
        m = re.fullmatch(r"(\w+)\s*:\s*(\w+)", p)
        if not m: stop(src, n, f"inline fn {name}: a parameter is `NAME: CLASS`, not `{p}`")
        if m.group(2) not in classes: stop(src, n, f"inline fn {name}: `{m.group(2)}` is no class of register ({', '.join(classes)})")
        if m.group(1) in whole: stop(src, n, f"inline fn {name}: a parameter cannot have a register's name, `{m.group(1)}`")
        if m.group(1) in [q for q, _ in ps]: stop(src, n, f"inline fn {name}: two parameters are named `{m.group(1)}`")
        ps.append((m.group(1), m.group(2)))
    names, distinct, changes, rest = [p for p, _ in ps], [], [], clauses.strip()
    def listed(text, what):
        got = [x.strip() for x in text.split(",")]
        for x in got:
            if x not in names: stop(src, n, f"inline fn {name}: `{what}` names `{x}`, which is not a parameter")
            if got.count(x) > 1: stop(src, n, f"inline fn {name}: `{what}` names `{x}` twice")
        return got
    while True:
        m = re.match(r"distinct\(\s*(\w+(?:\s*,\s*\w+)+)\s*\)\s*", rest)
        if not m: break
        distinct.append(listed(m.group(1), "distinct")); rest = rest[m.end():]
    m = re.fullmatch(r"changes\s+(\w+(?:\s*,\s*\w+)*)", rest)
    if m: changes = listed(m.group(1), "changes")
    elif rest: stop(src, n, f"inline fn {name}: after the parameters comes `distinct(P, Q)`, then `changes P, ...`, not `{rest}`")
    for k, line in body:
        s = line.split("//")[0].strip()
        if re.match(r"(place|entry)\b", s): stop(src, k, f"inline fn {name}: a place or an entry inside an inline function")
        for word in re.findall(r"(?<![@#$\w])[A-Za-z_]\w*", s):
            if word in whole: stop(src, k, f"inline fn {name}: the line names the register `{word}`; an inline function takes each register it uses as a parameter")
    return Inline(name, n, ps, distinct, changes, body)


def source(text, src="the source", target=None):
    """A source read: (its target, its data, its inline functions, its functions), as
    (name, [(name, [words])], {name: Inline}, [(name, symbol, lines, the number of the first of them)]).
    Supports both unified `.ode` files (with contracts on `fn` and multi-arch `for <arch>` blocks)
    and legacy `.ode` files (`fn name as "sym" { ... }`)."""
    import ode_unified
    if ode_unified.is_unified(text):
        parsed = ode_unified.parse_unified(text, src)
        arch, u_data, u_inlines, u_fns = ode_unified.target_source_view(parsed, target, src)
        inlines = {}
        for raw_inl, lno in u_inlines:
            ilines = raw_inl.split("\n")
            head, h = ilines[0].split("//")[0].rstrip(), 0
            while not head.endswith("{"):
                h += 1
                if h >= len(ilines):
                    stop(src, lno, "the head of an inline fn ends with `{`")
                head += " " + ilines[h].split("//")[0].strip()
            m = re.match(r"^inline\s+fn\s+(\w+)\s*\((.*?)\)(.*)\{$", head)
            if not m:
                stop(src, lno, "the head of an inline fn is `inline fn NAME(P: CLASS, ...) distinct(P, Q) changes P, ... {`")
            if m.group(1) in inlines:
                stop(src, lno, f"a second inline fn {m.group(1)}")
            body = [(lno + k, ilines[k]) for k in range(h + 1, len(ilines) - 1)]
            inlines[m.group(1)] = inline_of(src, lno, m.group(1), m.group(2), m.group(3), body, arch)
        for f in inlines.values():
            for p, _ in f.params:
                if p in inlines:
                    stop(src, f.line, f"inline fn {f.name}: the parameter `{p}` has an inline function's name")
        return arch, u_data, inlines, u_fns

    parsed_target, data, inlines, fns, lines, i = None, [], {}, [], text.split("\n"), 0
    def closing(i):                     # the `}` that stands alone at the start of a line, after line i
        j = i + 1
        while j < len(lines) and lines[j] != "}": j += 1
        if j == len(lines): stop(src, i + 1, "the `}` that ends this, alone at the start of a line, is missing")
        return j
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^target\s+(\w+)\s*$", line.split("//")[0])
        if m:
            if parsed_target is not None or inlines or fns: stop(src, i + 1, "`target` stands once, before the functions")
            if m.group(1) not in TARGETS: stop(src, i + 1, f"odec.py makes code for {', '.join(TARGETS)} only, not for {m.group(1)}")
            parsed_target = m.group(1); i += 1; continue
        m = re.match(r"^data\s+(\w+)\s*=\s*(.*)$", line)
        if m:
            data.append((m.group(1), [int(w.strip().replace("_", ""), 0) for w in m.group(2).split("//")[0].split(",")])); i += 1; continue
        if re.match(r"^inline\s+fn\b", line):
            head, h = line.split("//")[0].rstrip(), i                # the head may go on over lines, to the one that ends with `{`
            while not head.endswith("{"):
                h += 1
                if h == len(lines) or lines[h] == "}": stop(src, i + 1, "the head of an inline fn ends with `{`")
                head += " " + lines[h].split("//")[0].strip()
            m = re.match(r"^inline\s+fn\s+(\w+)\s*\((.*?)\)(.*)\{$", head)
            if not m: stop(src, i + 1, "the head of an inline fn is `inline fn NAME(P: CLASS, ...) distinct(P, Q) changes P, ... {`")
            j = closing(h)
            if m.group(1) in inlines: stop(src, i + 1, f"a second inline fn {m.group(1)}")
            inlines[m.group(1)] = inline_of(src, i + 1, m.group(1), m.group(2), m.group(3), [(k + 1, lines[k]) for k in range(h + 1, j)], parsed_target or TARGETS[0])
            i = j + 1; continue
        m = re.match(r'^fn\s+(\w+)\s+as\s+"(\w+)"\s*\{\s*$', line)
        if m:
            j = closing(i)
            fns.append((m.group(1), m.group(2), lines[i + 1:j], i + 2)); i = j + 1; continue
        if line.split("//")[0].strip(): sys.exit(f"{src}: line {i + 1} is neither data, a function nor a comment: {line.strip()}")
        i += 1
    for f in inlines.values():
        for p, _ in f.params:
            if p in inlines: stop(src, f.line, f"inline fn {f.name}: the parameter `{p}` has an inline function's name")
    return parsed_target or TARGETS[0], data, inlines, fns


def functions(text, src="the source"):
    """(the data, the functions) of a source: [(name, [words])], [(name, symbol, lines)]."""
    _, data, _, fns = source(text, src)
    return data, [(name, symbol, lines) for name, symbol, lines, _ in fns]


WRITTEN = {}
_ASM_MODS = {}


def _asm_mod(target):
    if target not in _ASM_MODS:
        folder = "arm64" if target == "arm64" else "core"
        path = os.path.join(HERE, "..", folder, "asm.py")
        spec = importlib.util.spec_from_file_location(f"_ode_asm_{target}", path)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _ASM_MODS[target] = mod
    return _ASM_MODS[target]


def written(line, target="x86_64"):
    """The registers an instruction changes, each by the name of the whole register, as its row of the
    instruction table says. (The flags and bytes of memory are not among them.)"""
    key = (target, line)
    if key not in WRITTEN:
        if target == "arm64":
            WRITTEN[key] = _asm_mod("arm64").written(line)
            return WRITTEN[key]
        core = os.path.join(HERE, "..", "core")
        if core not in sys.path: sys.path.insert(0, core)
        import decode, table
        item, regs = _asm_mod("x86_64").instruction(line), set()
        if item[0] != "jump":
            got = decode.decode(item[1], 0, 0, lambda kind, start, end: itertools.repeat("0"))
            if got is None: raise ValueError("the instruction table does not read back the bytes it writes for this")
            row, bind = table.find(decode.HEADS, table.parse_row(got[1]))
            for st in row.effect:
                if st[0] == "call": raise ValueError("a call inside an inline function: not here yet")
                if st[0] != "set" or st[1][0] != "name" or st[1][1] in ("zf", "cf"): continue
                place = st[1][1]
                if place in table.REGISTERS: regs.add(WHOLE[bind[place]])
                elif place in table.VECTORS: regs.add(f"zmm{bind[place]}")
                elif place in table.WIDE: regs.add(f"zmm{bind[table.WIDE[place]]}")
                elif place in table.MASKS: regs.add(f"k{bind[place]}")
                else: regs.add(WHOLE.get(place, place))             # a register the row names outright; or `above128` (vzeroupper)
        WRITTEN[key] = regs
    return WRITTEN[key]


def expand(src, fn, numbered, inlines, notes=None, typed_lines=None, target="x86_64", meta=None):
    """A function's lines [(number, text)] as instructions: the uses of inline functions and the fors
    expanded, `$x`, `@label` and `#data` replaced. What is no instruction is left out of them and, where
    `notes` is a list, put there with the number of the instruction it stands before:
    ("place", number, the count's name, its lines) for `place b { ... }` (what holds there after b turns of
    the loop: the proof of the loop is written from it); ("entry", number, NAME) for `entry "NAME"` (the
    function is entered there too, under that name). Where `typed_lines` is a list, it gets, for each
    instruction given back, (the number of its line, the line as it was typed, with a for's number put in).
    Where `meta` is a dict, it receives `regs` ({name: register}) and `frame` ((size, fields) or None)."""
    classes, whole, general, g64_addr, sp_name = target_spec(target)
    branch_map = BRANCH_ARM if target == "arm64" else BRANCH_X86
    jmp_op = "b" if target == "arm64" else "jmp"
    out, uses, ctrl_seq, names, frame, budget = [], [0], [0], {}, [None], [None]          # (names: the registers' names; frame: (size, fields); budget: {key: int})

    def branch_op(cond, n, invert=False):
        c = COND_ALIAS.get(cond, cond)
        if c not in INVERT_COND:
            stop(src, n, f"unknown condition `{cond}` (supported: eq, ne, ult/lo, uge/hs)")
        return branch_map[INVERT_COND[c] if invert else c]

    def emit(n, asm_line, typed_line, inside):
        if inside: kept(asm_line, n, inside)
        out.append(asm_line)
        if typed_lines is not None: typed_lines.append((n, typed_line))

    def rewrite_place_line(ln, line):
        """Replace declared `reg` names and `frame` fields in the register/cell positions of a `place { ... }`
        line so loop invariants can use the coder's own names without colliding with contract variables."""
        if not names and frame[0] is None:
            return line
        m = re.fullmatch(r"name\s+(\w+)\s*=\s*(\w+)", line)
        if m and m.group(2) in names:
            return f"name {m.group(1)} = {names[m.group(2)]}"
        m = re.fullmatch(r"keep\s+(.+)", line)
        if m:
            toks = [names.get(t, t) for t in m.group(1).split()]
            return "keep " + " ".join(toks)
        m = re.fullmatch(r"lane\s+(\w+):\s*(.+)", line)
        if m and m.group(1) in names:
            return f"lane {names[m.group(1)]}: {m.group(2)}"
        m = re.fullmatch(r"cell\s+(\w+)(?:\[([^\]]+)\])?:\s*(.+)", line)
        if m and frame[0] is not None and m.group(1) in frame[0][1]:
            fname, slot_s, rest = m.group(1), m.group(2), m.group(3)
            before, count, one = frame[0][1][fname]
            idx = 0 if slot_s is None else number(slot_s)
            if idx is None or not 0 <= idx < count:
                stop(src, ln, f"place cell `{fname}[{slot_s}]` is out of range (0 to {count - 1})")
            off = before + idx * one
            return f"cell [{sp_name} + {off}]: {rest}"
        return line

    def field(name, n, inside):
        if inside: stop(src, n, "a field of the frame inside an inline function")
        if frame[0] is None or name not in frame[0][1]: stop(src, n, f"`{name}` is no field of the function's frame")
        return frame[0][1][name]

    def address(text, n):
        """An address of `:=`, a register (or two on x86-64) and a number, with the number worked out."""
        terms, depth, cur, sign = [], 0, "", 1
        for ch in text + "+":
            if ch in "+-" and depth == 0:
                if cur.strip(): terms.append((sign, cur.strip())); sign = 1
                if ch == "-": sign = -sign
                cur = ""
            else: depth += ch == "("; depth -= ch == ")"; cur += ch
        regs, total = [], 0
        for sign, term in terms:
            if term in g64_addr and sign == 1: regs.append(term)
            elif number(term) is not None: total += sign * number(term)
            else: stop(src, n, f"an address of `:=` is a register (or two) and a number: not `[{text.strip()}]`")
        if target == "arm64":
            if len(regs) != 1 or total < 0:
                stop(src, n, f"on arm64 an address of `:=` is one base register and a nonnegative offset: not `[{text.strip()}]`")
            return f"{regs[0]}, {total}"
        if not 1 <= len(regs) <= 2: stop(src, n, f"an address of `:=` is a register (or two) and a number: not `[{text.strip()}]`")
        return " + ".join(regs) + (f" + {total}" if total >= 0 else f" - {-total}")

    def operand(text, n, inside):
        """A side of `:=`, as (what it is, how the assembler is given it, its bytes where it has a size)."""
        t = text.strip()
        if t in general: return "register", t, general[t]
        if t in whole: stop(src, n, f"`:=` is one move or load/store: `{t}` is moved by an instruction that the coder names")
        if number(t) is not None: return "number", str(number(t)), None
        m = re.fullmatch(r"(byte|dword|qword|u32|u64)\s*\[(.*)\]", t)
        if m:
            w = {"byte": "byte", "u32": "dword", "dword": "dword", "u64": "qword", "qword": "qword"}[m.group(1)]
            sz = {v: k for k, v in SIZES.items()}[w]
            if target == "arm64":
                if sz not in (4, 8): stop(src, n, f"on arm64 `:=` moves 4 or 8 bytes of memory (`u32`/`dword` or `u64`/`qword`), not `{m.group(1)}`")
                return "memory", f"[{address(m.group(2), n)}]", sz
            return "memory", f"{w} ptr [{address(m.group(2), n)}]", sz
        m = re.fullmatch(r"&\s*(\w+)", t)
        if m:
            off = field(m.group(1), n, inside)[0]
            return "address", (f"{sp_name}, {off}" if target == "arm64" else f"[rsp + {off}]"), 8
        m = re.fullmatch(r"(\w+)(?:\.(\w+))?\[(.*)\]", t)
        if m:
            name, view, slot = m.groups()
            before, count, one = field(name, n, inside)
            if view is not None:
                if view not in KINDS: stop(src, n, f"`{view}` is no kind of a field ({', '.join(KINDS)})")
                if count * one % KINDS[view]: stop(src, n, f"`{name}` has {count * one} bytes: not a whole count of {view}")
                count, one = count * one // KINDS[view], KINDS[view]
            i = number(slot)
            if i is None: stop(src, n, f"a slot is a number: not `{slot.strip()}`")
            if not 0 <= i < count: stop(src, n, f"`{t}`: the slots of `{name + ('.' + view if view else '')}` are 0 to {count - 1}")
            allowed = (4, 8) if target == "arm64" else tuple(SIZES)
            if one not in allowed:
                words = "4 or 8" if target == "arm64" else "1, 4 or 8"
                stop(src, n, f"`:=` moves {words} bytes, and a slot of `{name}` has {one}: take it as `{name}.u64[I]`, or name the instruction")
            off = before + i * one
            return "memory", (f"[{sp_name}, {off}]" if target == "arm64" else f"{SIZES[one]} ptr [rsp + {off}]"), one
        stop(src, n, f"`{t}` is nothing that `:=` moves: a general register, a number, `qword [ADDRESS]`, a slot of the frame or `&FIELD`")

    def store(s, n, inside, typed):
        """`DST := SRC` as the one instruction it is (`typed`: the line before a name was replaced by its register)."""
        left, right = s.split(":=", 1)
        (a, dst, into), (b, src_, of) = operand(left, n, inside), operand(right, n, inside)
        if into is not None and of is not None and into != of:
            was = [side.strip() for side in typed.split(":=", 1)]
            stop(src, n, f"`:=` moves as many bytes as both sides have: `{was[0]}` has {into} and `{was[1]}` has {of}")
        if target == "arm64":
            if (a, b) == ("register", "address"): return f"add {dst}, {src_}"
            if (a, b) in (("register", "register"), ("register", "number")): return f"mov {dst}, {src_}"
            if (a, b) == ("register", "memory"): return f"ldr {dst}, {src_}"
            if (a, b) == ("memory", "register"): return f"str {src_}, {dst}"
            stop(src, n, f"on arm64 `:=` is one `mov`, `ldr`, `str`, or `add` (no store of an immediate to memory): not `{s}`")
        if (a, b) == ("register", "address"): return f"lea {dst}, {src_}"
        if (a, b) in (("register", "register"), ("register", "number"), ("register", "memory"), ("memory", "register"), ("memory", "number")): return f"mov {dst}, {src_}"
        stop(src, n, f"`:=` is one `mov`: into a register from a register, a number or memory, or into memory from a register or a number; not `{s}`")

    def block_end(lines, start):
        depth, j = 1, start
        while depth:
            if j == len(lines): stop(src, lines[start - 1][0], "the `}` that ends this is missing")
            s = lines[j][1].split("//")[0].strip()
            if s.startswith("}"):
                depth -= 1
                if depth == 0:
                    return lines[start:j], j + 1, s, lines[j][0]
                if s.endswith("{"):
                    depth += 1
            elif s.endswith("{"):
                depth += 1
            j += 1
        return lines[start:j - 1], j, "}", lines[j - 1][0]

    def block(lines, start):
        body, nxt, close_s, close_n = block_end(lines, start)
        if close_s != "}":
            stop(src, close_n, f"expected `}}`, not `{close_s}`")
        return body, nxt

    def use(f, args, n, inside):
        if any(f is g for g, _, _ in inside): stop(src, n, f"the inline function {f.name} uses itself")
        if len(args) != len(f.params): stop(src, n, f"{f.name} takes {len(f.params)} registers, not {len(args)}")
        bind = {}
        for (p, cls), a in zip(f.params, args):
            if a not in classes[cls]: stop(src, n, f"{f.name}: `{p}` is a register of the class {cls}, and `{a}` is not one")
            bind[p] = a
        for group in f.distinct:
            for a, b in itertools.combinations(group, 2):
                if whole[bind[a]] == whole[bind[b]]:
                    same = f"both are given {bind[a]}" if bind[a] == bind[b] else f"{bind[a]} and {bind[b]} are parts of one register"
                    stop(src, n, f"{f.name}: `{a}` and `{b}` must differ, and {same}")
        uses[0] += 1
        run(f.body, {}, {l: f".Lode_{fn}_{f.name}{uses[0]}_{l}" for l in f.labels}, inside + [(f, n, bind)], [])

    def kept(s, n, inside):
        """An instruction of an inline function changes only what `changes` lists: of that function, and of
        every inline function this use of it stands in."""
        if s.endswith(":") or s.startswith("."): return
        try: regs = sorted(written(s, target))
        except (ValueError, KeyError, IndexError) as e: stop(src, n, f"{inside[-1][0].name}, used at line {inside[-1][1]}: `{s}`: {e}")
        for f, at, bind in reversed(inside):
            for r in regs:
                if r not in {whole[bind[p]] for p in f.changes}:
                    stop(src, n, f"{f.name}, used at line {at}: `{s}` changes {r}, which `changes` of {f.name} does not list")

    def run(lines, env, labels, inside, loops):
        """`env`: what each `$x` of a for stands for. `labels`: the names in the object of the labels that
        are a use's own. `inside`: the uses of inline functions these lines stand in, the outermost first,
        each as (the inline function, the number of the use's line, {parameter: register}).
        `loops`: stack of `(head_label, end_label)` for enclosing `loop { ... }` blocks."""
        i = 0
        while i < len(lines):
            n, s = lines[i][0], lines[i][1].split("//")[0].strip(); i += 1
            if not s:
                continue
            m = re.fullmatch(r"for\s+(\w+)\s+in\s+(\d+)\.\.(\d+)\s*\{", s)
            if m:
                body, i = block(lines, i)
                for k in range(int(m.group(2)), int(m.group(3))): run(body, {**env, m.group(1): str(k)}, labels, inside, loops)
                continue
            m = re.fullmatch(r"if\s+(\w+)\s*\{", s)
            if m:
                cond = m.group(1)
                inv = branch_op(cond, n, invert=True)
                then_body, i, close_s, close_n = block_end(lines, i)
                ctrl_seq[0] += 1
                cid = ctrl_seq[0]
                else_lbl = f".Lode_{fn}__if{cid}_else"
                end_lbl = f".Lode_{fn}__if{cid}_end"
                else_body = None
                else_n = close_n
                if re.fullmatch(r"\}\s*else\s*\{", close_s):
                    else_body, i = block(lines, i)
                elif close_s == "}":
                    # Also accept `else {` on the next non-blank line
                    k = i
                    while k < len(lines) and not lines[k][1].split("//")[0].strip():
                        k += 1
                    if k < len(lines) and re.fullmatch(r"else\s*\{", lines[k][1].split("//")[0].strip()):
                        else_n = lines[k][0]
                        else_body, i = block(lines, k + 1)
                else:
                    stop(src, close_n, f"after `if {cond}` expected `}}` or `}} else {{`, not `{close_s}`")
                if else_body is None:
                    emit(n, f"{inv} {end_lbl}", s, inside)
                    run(then_body, env, labels, inside, loops)
                    emit(close_n, f"{end_lbl}:", f"{end_lbl}:", inside)
                else:
                    emit(n, f"{inv} {else_lbl}", s, inside)
                    run(then_body, env, labels, inside, loops)
                    emit(else_n, f"{jmp_op} {end_lbl}", "else", inside)
                    emit(else_n, f"{else_lbl}:", f"{else_lbl}:", inside)
                    run(else_body, env, labels, inside, loops)
                    emit(close_n, f"{end_lbl}:", f"{end_lbl}:", inside)
                continue
            if re.fullmatch(r"else\s*\{", s) or re.fullmatch(r"\}\s*else\s*\{", s):
                stop(src, n, "`else` without a preceding `if`")
            if re.fullmatch(r"loop\s*\{", s):
                body, i, close_s, close_n = block_end(lines, i)
                ctrl_seq[0] += 1
                cid = ctrl_seq[0]
                head_lbl = f".Lode_{fn}__loop{cid}_head"
                end_lbl = f".Lode_{fn}__loop{cid}_end"
                emit(n, f"{head_lbl}:", f"{head_lbl}:", inside)
                run(body, env, labels, inside, loops + [(head_lbl, end_lbl)])
                if close_s == "}":
                    emit(close_n, f"{jmp_op} {head_lbl}", "}", inside)
                else:
                    mw = re.fullmatch(r"\}\s*while\s+(\w+)", close_s)
                    if not mw:
                        stop(src, close_n, f"after `loop` expected `}}` or `}} while COND`, not `{close_s}`")
                    br = branch_op(mw.group(1), close_n, invert=False)
                    emit(close_n, f"{br} {head_lbl}", close_s, inside)
                emit(close_n, f"{end_lbl}:", f"{end_lbl}:", inside)
                continue
            if s == "break":
                if not loops: stop(src, n, "`break` outside a `loop`")
                emit(n, f"{jmp_op} {loops[-1][1]}", s, inside); continue
            m = re.fullmatch(r"break\s+if\s+(\w+)", s)
            if m:
                if not loops: stop(src, n, "`break if` outside a `loop`")
                br = branch_op(m.group(1), n, invert=False)
                emit(n, f"{br} {loops[-1][1]}", s, inside); continue
            if s == "continue":
                if not loops: stop(src, n, "`continue` outside a `loop`")
                emit(n, f"{jmp_op} {loops[-1][0]}", s, inside); continue
            m = re.fullmatch(r"continue\s+if\s+(\w+)", s)
            if m:
                if not loops: stop(src, n, "`continue if` outside a `loop`")
                br = branch_op(m.group(1), n, invert=False)
                emit(n, f"{br} {loops[-1][0]}", s, inside); continue
            if re.match(r"(if|loop|break|continue)\b", s):
                stop(src, n, f"malformed control form `{s}` (use `if COND {{`, `loop {{`, `break [if COND]`, `continue [if COND]`)")
            m = re.fullmatch(r'place\s*(?:"(\w+)"\s*)?\{', s) or re.fullmatch(r"place\s+(\w+)\s*\{", s)
            if m:
                if env or inside: stop(src, n, f"fn {fn}: a place inside a for or an inline function")
                body, i = block(lines, i)
                said = [rewrite_place_line(ln, l.split("//")[0].strip()) for ln, l in body if l.split("//")[0].strip()]
                if notes is None: continue
                if '"' in s or m.group(1) is None: notes.append(("at", len(out), m.group(1), said, n))      # a place for the prover of proof-core
                else: notes.append(("place", len(out), m.group(1), said))                                # a kernel's, with its count's name
                continue
            if re.fullmatch(r"budget\s*\{", s):
                if env or inside: stop(src, n, f"fn {fn}: a budget inside a for or an inline function")
                if budget[0] is not None: stop(src, n, f"fn {fn}: a second budget")
                body, i = block(lines, i)
                budget[0] = budget_of(src, n, body); continue
            m = re.fullmatch(r'entry\s+"(\w+)"', s)
            if m:
                if env or inside: stop(src, n, f"fn {fn}: an entry inside a for or an inline function")
                if notes is not None: notes.append(("entry", len(out), m.group(1)))
                continue
            if re.fullmatch(r"def\s+\w+\s*\(.*\)\s*\{", s): stop(src, n, "`def` is not a form of Ode any more: write an `inline fn`, outside the function")
            m = re.fullmatch(r"reg\s+(\w+)\s*=\s*(\w+)", s)
            if m:
                name, register = m.groups()
                if env or inside: stop(src, n, f"fn {fn}: a name for a register inside a for or an inline function")
                if register not in whole: stop(src, n, f"`{register}` is no register")
                if name in whole or name in _reserved_for(target): stop(src, n, _reserved_err("a register", name, target))
                if name in names or name in inlines or (frame[0] is not None and name in frame[0][1]): stop(src, n, f"`{name}` is a name already")
                names[name] = register; continue
            if re.fullmatch(r"frame\s*\{", s):
                if env or inside: stop(src, n, f"fn {fn}: a frame inside a for or an inline function")
                if frame[0] is not None: stop(src, n, f"fn {fn}: a second frame")
                body, i = block(lines, i)
                frame[0] = frame_of(src, n, body, set(names) | set(inlines), target); continue
            for k, v in env.items():
                s = re.sub(r"\$" + k + r"\b", v, s)
            if inside and inside[-1][2]:
                bind = inside[-1][2]
                s = re.sub(r"(?<![@#$\w])(?:" + "|".join(map(re.escape, bind)) + r")\b", lambda g: bind[g.group(0)], s)
            typed = s
            call_op = "bl" if target == "arm64" else "call"
            tail_op = "b" if target == "arm64" else "jmp"
            m = re.fullmatch(rf"({call_op}|{tail_op})\s+(\w+)", s)
            if m and m.group(2) in names and not inside:
                stop(src, n, f"`{m.group(2)}` is the name of a register here ({names[m.group(2)]}), and `{m.group(1)}` takes the name a linker knows a function by")
            if names and not inside:                # a register's name, wherever an operand has it (never the instruction's own name)
                put = lambda text: re.sub(r"(?<![@#$\w.])(?:" + "|".join(map(re.escape, names)) + r")\b", lambda g: names[g.group(0)], text)
                m = None if ":=" in s else re.match(r"\w+\(|\S+\s+", s)
                s = put(s) if ":=" in s else s[:m.end()] + put(s[m.end():]) if m else s
            if re.search(r"\bframe\.\w+\b", s):
                if inside or frame[0] is None:
                    what = re.search(r"\bframe\.\w+\b", s).group(0)
                    stop(src, n, f"`{what}` inside an inline function" if inside else f"`{what}`, and fn {fn} has said no frame yet")
                def _frame_const(g):
                    key = g.group(1)
                    if key == "size": return str(frame[0][0])
                    if key in frame[0][1]: return str(frame[0][1][key][0])
                    stop(src, n, f"`{key}` is no field of the function's frame (fields: {', '.join(frame[0][1])})")
                s = re.sub(r"\bframe\.(\w+)\b", _frame_const, s)
            if ":=" in s: s = store(s, n, inside, typed)
            m = re.fullmatch(r"(\w+)\((.*)\)", s)
            if m and m.group(1) in inlines:
                use(inlines[m.group(1)], [a.strip() for a in m.group(2).split(",")] if m.group(2).strip() else [], n, inside); continue
            if m: stop(src, n, f"`{m.group(1)}` is no inline function of this source")
            if target == "x86_64":
                m = re.fullmatch(r"(call|jmp)\s+(\w+)", s)
                if m and m.group(2) not in REGISTERS: s = f"{m.group(1)} CALL({m.group(2)})"          # a function, by the name a linker knows it by
            s = re.sub(r"@(\w+)", lambda g: labels.get(g.group(1), f".Lode_{fn}_{g.group(1)}"), s)
            s = re.sub(r"#([A-Za-z_]\w*)", lambda g: f".Lode_data_{g.group(1)}", s)     # `#name` is data; `#4` is a number
            s = re.sub(r"\s+", " ", s)
            if inside: kept(s, n, inside)
            out.append(s)
            if typed_lines is not None: typed_lines.append((n, typed))

    run(numbered, {}, {}, [], [])
    if meta is not None:
        meta["regs"] = dict(names)
        meta["frame"] = frame[0]
        meta["budget"] = dict(budget[0] or {})
    return out


def found(src, name, with_target=False, target=None):
    """(the data, the symbol, the numbered lines, the source's inline functions) of the function NAME of a source."""
    arch, data, inlines, fns = source(read_source(src), src, target=target)
    got = [(symbol, [(first + k, line) for k, line in enumerate(lines)]) for n, symbol, lines, first in fns if n == name]
    if len(got) != 1: sys.exit(f"{src}: no `fn {name}`")
    res = (data, got[0][0], got[0][1], inlines)
    return (arch, *res) if with_target else res


def instructions(text, name, src="the source", notes=None, target=None):
    """The instructions of the function NAME of a source's text, as expand() gives them."""
    arch, _, inlines, fns = source(text, src, target=target)
    got = [[(first + k, line) for k, line in enumerate(lines)] for n, _, lines, first in fns if n == name]
    if len(got) != 1: sys.exit(f"{src}: no `fn {name}`")
    return expand(src, name, got[0], inlines, notes, target=arch)


def assembly(src, name, symbol=None, target=None):
    """The assembly of a function of the source, with the data it names: its lines, the uses of inline
    functions and the fors expanded, under its symbol (or `symbol`, for a test's copy). No instruction is
    added or changed. Its other entries (`entry "NAME"`) are names of their own; and where the source has a
    `place`, how many bytes into the function it is, as four bytes in a section `.ode.place` that is not
    loaded (the assembler knows the number; place_of() gives the rest of the place's proof)."""
    target, data, own, lines, inlines = found(src, name, with_target=True, target=target)
    symbol = symbol or own
    notes = []
    ins = expand(src, name, lines, inlines, notes, target=target)
    notes = [note for note in notes if note[0] != "at"]         # (the places for proof-core's prover are no part of the object)
    for note in sorted(notes, key=lambda n: -n[1]):             # from the last, so the numbers before it stay
        ins[note[1]:note[1]] = [f".Lode_place_{name}:"] if note[0] == "place" else [f".global {note[2]}", f"{note[2]}:"]
    # A leading alignment directive belongs before the entry symbols, not
    # after them: padding inside a labelled entry changes the called code.
    alignment = ins.pop(0) if ins and ins[0].startswith(".p2align ") else ".p2align 4"
    used = [(n, ws) for n, ws in data if any(f".Lode_data_{n}]" in x or f".Lode_data_{n} " in x for x in ins)]
    if target == "arm64":
        text = ("// Printed by odec.py from " + src.split("/")[-1] + ". Not written or edited by hand.\n"
                ".text\n"
                f".globl {symbol}\n.type {symbol}, %function\n{alignment}\n{symbol}:\n")
        text += "".join((x + "\n") if x.endswith(":") else ("    " + x + "\n") for x in ins)
        text += f".size {symbol}, .-{symbol}\n"
        return text
    text = ("// Printed by odec.py from " + src.split("/")[-1] + ". Not written or edited by hand.\n"
            "#if defined(__ELF__) && defined(__linux__)\n.section .note.GNU-stack,\"\",%progbits\n#endif\n"
            "#ifdef __APPLE__\n#define CALL(f) _##f\n#else\n#define CALL(f) f@PLT\n#endif\n"
            ".intel_syntax noprefix\n" + ("#ifdef __APPLE__\n.static_data\n#else\n.section .rodata\n#endif\n" if used else ""))
    for n, ws in used:
        text += f".p2align 6\n.Lode_data_{n}:\n" + "".join(f"    .long {w}\n" for w in ws)
    text += f".text\n.text\n.global {symbol}\n.global _{symbol}\n{alignment}\n{symbol}:\n_{symbol}:\n"
    text += "".join((x + "\n") if x.endswith(":") else ("    " + x + "\n") for x in ins)
    if any(note[0] == "place" for note in notes):
        text += f"#if defined(__ELF__)\n.section .ode.place,\"\",@progbits\n    .long .Lode_place_{name} - {symbol}\n#endif\n"
    return text


def assemble(s_path, o_path, target="x86_64"):
    if target == "arm64":
        for cc in (["clang", "--target=aarch64-unknown-linux-gnu"], ["clang", "-target", "aarch64-linux-gnu"]):
            if shutil.which(cc[0]) and subprocess.run(cc + ["-c", "-o", o_path, s_path], capture_output=True).returncode == 0: return
        raise SystemExit(f"odec: no assembler here makes an AArch64 ELF object of {s_path}")
    for cc in (["clang", "--target=x86_64-unknown-linux-gnu"], ["cc"]):
        if shutil.which(cc[0]) and subprocess.run(cc + ["-c", "-o", o_path, s_path], capture_output=True).returncode == 0: return
    raise SystemExit(f"odec: no assembler here makes an x86-64 ELF object of {s_path}")


def elf(src, name, symbol, expanded, typed, notes, data, where=None, target="x86_64", locs=None):
    """A function's ELF object by the instruction table (`../core/asm.py` or `../arm64/asm.py`). Where the
    assembler refuses, the source line is named: that of the first instruction that the assembler refuses by
    itself, or that jumps to a label the function has not. `typed`: for each of `expanded`, (its line's
    number, the line as typed)."""
    asm_mod = _asm_mod(target)
    try: return asm_mod.build_elf(name, symbol, expanded, notes, data, where, locs=locs)
    except (ValueError, KeyError, IndexError) as e:
        labels = {x[:-1] for x in expanded if x.endswith(":")}
        for x, (n, was) in zip(expanded, typed):
            if x.endswith(":") or x.startswith("."): continue
            try: item = asm_mod.instruction(x)
            except ValueError as why:
                said = str(why)
                stop(src, n, f"`{was}`: " + (said[:-len(x) - 2] if said.endswith(": " + x) else said))
            if item[0] == "jump" and item[2] not in labels:
                is_ext_tail = (
                    ((target == "arm64" and item[1].row.name == "b") or (target != "arm64" and item[1] == "jmp"))
                    and not item[2].startswith(".")
                )
                if not is_ext_tail:
                    label = re.search(r"@\w+", was)
                    stop(src, n, f"`{was}`: the function has no label `{label.group(0) if label else item[2]}`")
        raise SystemExit(f"odec: {src}: fn {name}: {e}") from None


def compile_info(src, name, symbol=None, target=None):
    """Compile one function to ELF bytes and return its full metadata (target, symbol, ELF bytes, exact
    pc-to-source line_map, user register names, frame layout, label offsets, and per-entry places text)."""
    target, data, own, lines, inlines = found(src, name, with_target=True, target=target)
    sym = symbol or own
    notes, typed, meta = [], [], {}
    expanded = expand(src, name, lines, inlines, notes, typed, target=target, meta=meta)
    entries = {sym} | {note[2] for note in notes if note[0] == "entry"}
    for note in notes:
        if note[0] == "at" and note[2] is not None and note[2] not in entries:
            stop(src, note[4], f"fn {name}: a place for `{note[2]}`, which is no entry of the function")
    at_notes = [note for note in notes if note[0] == "at"]
    non_at = [note for note in notes if note[0] != "at"]
    elf_notes = non_at + [("at", note[1], f".Lode_at_{k}") for k, note in enumerate(at_notes)]
    where, locs = {}, []
    blob = elf(src, name, sym, expanded, typed, elf_notes, data, where=where, target=target, locs=locs)
    base = where[sym]
    line_map = []
    for off, blen, idx in locs:
        ln, was = typed[idx]
        line_map.append({
            "pc": off - base,
            "len": blen,
            "file": src,
            "line": ln,
            "typed": was,
            "asm": expanded[idx],
        })
    places_by_entry = {}
    for entry in sorted(entries):
        mine = [(k, note) for k, note in enumerate(at_notes) if (note[2] or sym) == entry]
        if mine:
            places_by_entry[entry] = "".join(
                f"place +0x{where[f'.Lode_at_{k}'] - where[entry]:x} {{\n"
                + "".join(f"    {line}\n" for line in note[3]) + "}\n"
                for k, note in mine
            )
        else:
            places_by_entry[entry] = ""
    frame_info = None
    if meta["frame"] is not None:
        fsize, ffields = meta["frame"]
        frame_info = {
            "size": fsize,
            "fields": [
                {"name": fn_, "offset": off, "count": cnt, "elem": elem, "bytes": cnt * elem}
                for fn_, (off, cnt, elem) in ffields.items()
            ],
        }
    code_bytes = (line_map[-1]["pc"] + line_map[-1]["len"]) if line_map else 0
    return {
        "target": target,
        "name": name,
        "symbol": sym,
        "elf": blob,
        "where": where,
        "line_map": line_map,
        "regs": meta["regs"],
        "frame": frame_info,
        "budget": meta["budget"],
        "places": places_by_entry,
        "code_bytes": code_bytes,
    }


def build(src, name, obj, symbol=None, target=None):
    """Write a function's ELF object using the instruction table."""
    target, data, own, lines, inlines = found(src, name, with_target=True, target=target)
    notes, typed = [], []
    expanded = expand(src, name, lines, inlines, notes, typed, target=target)
    blob = elf(src, name, symbol or own, expanded, typed, [note for note in notes if note[0] != "at"], data, target=target)
    with open(obj, "wb") as f: f.write(blob)


def places(src, name, entry=None, target=None):
    """What a function's source says holds at its places, as the prover of proof-core reads it (prove.prove):
    for each `place { LINES }` of the function, `place +0xN { LINES }`, N being the count of bytes from the
    function's first byte to the instruction the place stands before. With `entry` (the symbol of an
    `entry "SYMBOL"` of the function): the places written `place "SYMBOL" { LINES }`, counted from that
    entry. "" where there is none. The object is not changed by its places: build() leaves them out."""
    target, data, own, lines, inlines = found(src, name, with_target=True, target=target)
    notes, typed = [], []
    expanded = expand(src, name, lines, inlines, notes, typed, target=target)
    entries = {own} | {note[2] for note in notes if note[0] == "entry"}
    if (entry or own) not in entries: sys.exit(f"{src}: fn {name} has no entry `{entry}`")
    for note in notes:
        if note[0] == "at" and note[2] is not None and note[2] not in entries: stop(src, note[4], f"fn {name}: a place for `{note[2]}`, which is no entry of the function")
    mine = [note for note in notes if note[0] == "at" and (note[2] or own) == (entry or own)]
    if not mine: return ""
    where = {}
    elf(src, name, own, expanded, typed, [note for note in notes if note[0] != "at"] + [("at", note[1], f".Lode_at_{k}") for k, note in enumerate(mine)], data, where, target=target)
    return "".join(f"place +0x{where[f'.Lode_at_{k}'] - where[entry or own]:x} {{\n" + "".join(f"    {line}\n" for line in note[3]) + "}\n" for k, note in enumerate(mine))


def source_of(folder, name):
    """The source in `folder` that has `fn NAME`."""
    got = [os.path.join(folder, f) for f in sorted(os.listdir(folder)) if f.endswith(".ode") and re.search(rf"^fn\s+{name}\s+as\s", read_source(os.path.join(folder, f)), re.M)]
    if len(got) != 1: sys.exit(f"{folder}: {len(got)} sources have `fn {name}`")
    return got[0]


def place_of(src, name):
    """What a function's source says holds at its loop's place, as the proof kfn.py's verifier reads (without
    the place's number of bytes into the function, which build() writes in `.ode.place`); None if the source
    has no place. The lines of `place b { ... }`:
        keep rsp, rbp, r12            these registers hold what they held when the code first came back here
        keep zmm9                     a ZMM register, likewise
        keep [rsp + 0x800]            sixty-four bytes of the frame, likewise
        r13 = n - b                   a number that moves with the turns done (b) and a number among the arguments
        zmm0 .. zmm7 = h[b]           the words 0 .. 7 of the sequence's value after b turns, for lanes 0 to 15
        zmm8 .. zmm15 = h[b] lanes 16 the same, for the sixteen lanes from 16"""
    _, _, lines, inlines = found(src, name)
    notes = []
    expand(src, name, lines, inlines, notes)
    places = [note for note in notes if note[0] == "place"]
    if not places: return None
    if len(places) != 1: sys.exit(f"{src}: fn {name} has more than one place")
    _, _, b, lines = places[0]
    proof = dict(registers={}, vectors={}, frame={})
    for line in lines:
        m = re.fullmatch(r"keep\s+(.*)", line)
        if m:
            for x in [x.strip() for x in m.group(1).split(",")]:
                f = re.fullmatch(r"\[rsp(?:\s*\+\s*(\w+))?\]", x)
                if f: proof["frame"][str(int(f.group(1) or "0", 0))] = "keep"
                elif re.fullmatch(r"zmm\d+", x): proof["vectors"][x[3:]] = "keep"
                else: proof["registers"][x] = "keep"
            continue
        m = re.fullmatch(r"zmm(\d+)\s*\.\.\s*zmm(\d+)\s*=\s*h\[" + b + r"\](?:\s+lanes\s+(\d+))?", line)
        if m:
            first, last, lane = int(m.group(1)), int(m.group(2)), int(m.group(3) or "0")
            if last - first != 7: sys.exit(f"{src}: fn {name}: `{line}`: the value has eight words")
            for w in range(8): proof["vectors"][str(first + w)] = {"cv": [lane, w]}
            continue
        m = re.fullmatch(r"(\w+)\s*=\s*(.*)", line)
        if m:
            # a sum of terms: NUMBER, NAME, NUMBER * NAME, each with its sign
            lin = {"1": 0}
            for sign, term in re.findall(r"([+-]?)\s*([^+-]+)", m.group(2)):
                parts = [p.strip() for p in term.split("*")]
                k = -1 if sign == "-" else 1
                names = [p for p in parts if not re.fullmatch(r"\d+|0x[0-9a-fA-F]+", p)]
                for p in parts:
                    if p not in names: k *= int(p, 0)
                if len(names) > 1 or (names and not re.fullmatch(r"\w+", names[0])): sys.exit(f"{src}: fn {name}: `{line}`: not a sum of numbers and of names times numbers")
                key = "1" if not names else "b" if names[0] == b else names[0]
                lin[key] = lin.get(key, 0) + k
            proof["registers"][m.group(1)] = {"lin": {k: v for k, v in lin.items() if v or k == "1"}}
            continue
        sys.exit(f"{src}: fn {name}: a line of its place that is not understood: `{line}`")
    return proof


def main():
    a = sys.argv[1:]
    if len(a) == 3 and a[1] == "--all":
        os.makedirs(a[2], exist_ok=True)
        names = [n for n, _, _ in functions(read_source(a[0]), a[0])[1]]
        for n in names: build(a[0], n, os.path.join(a[2], n + ".o"))
        print(f"{len(names)} functions of {os.path.basename(a[0])}: objects in {a[2]}"); return
    if len(a) == 4 and a[0] == "--from": build(source_of(a[1], a[2]), a[2], a[3]); return
    if len(a) in (3, 4) and a[2] == "--places": sys.stdout.write(places(a[0], a[1], *a[3:])); return
    if len(a) == 3 and a[2] == "--map":
        info = compile_info(a[0], a[1])
        for row in info["line_map"]:
            print(f"+0x{row['pc']:04x} ({row['len']:2d} B)  line {row['line']:4d}  {row['typed']:<36s} | {row['asm']}")
        return
    if len(a) == 2: sys.stdout.write(assembly(a[0], a[1])); return
    if len(a) == 3: build(a[0], a[1], a[2]); return
    sys.exit(__doc__)


if __name__ == "__main__":
    main()
