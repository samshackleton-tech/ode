#!/usr/bin/env python3
"""Unified `.ode` source parser and extractor (closed per-file namespace).

A unified `.ode` file is the single coder-authored source file type in Ode. It holds:
  - Specification declarations: `const`, `def`, `sequence`, `layout`, `kind`
  - Optional read-only `data` and register-parameterized `inline fn` templates
  - Callable `fn` declarations with their contract clauses right on the `fn` header and one or
    more target implementation blocks `for x86_64` / `for arm64` (with optional per-target
    `needs`, `stack`, and `calling { in ... out = ... preserves ... preserves_vec ... }`).

Every `.ode` file is a closed local namespace (no implicit cross-file flat merging). Every
callable `fn` must carry a contract; contractless `fn` declarations are refused loudly.

From one unified `.ode` file, tools extract:
  - Pure semantic `.spec`/`.ocl` text (zero `calling` blocks, zero register names) for
    `ode_canon.canonicalize` -> the canonical nameless `<52-char-b32>.ocl` contract for Bob.
  - Full verifier spec text (including target `stack`, `needs`, and `calling`) for
    `proof-core/statement.py` and `proof-core/prove.py`.
  - Per-target assembly bodies compiled through `lang/odec.py` into ELF objects.
"""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _d in (HERE, os.path.join(ROOT, "kcheck")):
    if _d not in sys.path:
        sys.path.insert(0, _d)

import ode
import ode_hl

TARGETS = ("x86_64", "arm64")


class UnifiedErr(ValueError):
    pass


def _strip_line_comment(line):
    """Strip `// ...` comment outside double-quoted strings."""
    in_str = False
    for i, ch in enumerate(line):
        if ch == '"' and (i == 0 or line[i - 1] != "\\"):
            in_str = not in_str
        elif not in_str and ch == "/" and i + 1 < len(line) and line[i + 1] == "/":
            return line[:i]
    return line


def _find_matching_brace(text, open_pos, src="<ode>"):
    """Return index of the `}` matching `{` at `open_pos`, skipping `//` comments and strings."""
    assert text[open_pos] == "{"
    depth = 0
    i = open_pos
    n = len(text)
    in_str = False
    while i < n:
        ch = text[i]
        if in_str:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "/":
            nl = text.find("\n", i)
            i = n if nl == -1 else nl + 1
            continue
        if ch == '"':
            in_str = True
            i += 1
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    line = text.count("\n", 0, open_pos) + 1
    raise UnifiedErr(f"{src}: line {line}: missing closing `}}`")


def _skip_ws_and_comments(text, pos):
    n = len(text)
    while pos < n:
        if text[pos].isspace():
            pos += 1
        elif text[pos] == "/" and pos + 1 < n and text[pos + 1] == "/":
            nl = text.find("\n", pos)
            pos = n if nl == -1 else nl + 1
        else:
            break
    return pos


def _find_open_brace(text, pos):
    """Find next `{` outside comments and strings, or -1."""
    n = len(text)
    in_str = False
    i = pos
    while i < n:
        ch = text[i]
        if in_str:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "/":
            nl = text.find("\n", i)
            i = n if nl == -1 else nl + 1
            continue
        if ch == '"':
            in_str = True
            i += 1
            continue
        if ch == "{":
            return i
        i += 1
    return -1


def _find_matching_paren(text, open_pos, src="<ode>"):
    assert text[open_pos] == "("
    depth = 0
    i = open_pos
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == "/" and i + 1 < n and text[i + 1] == "/":
            nl = text.find("\n", i)
            i = n if nl == -1 else nl + 1
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    line = text.count("\n", 0, open_pos) + 1
    raise UnifiedErr(f"{src}: line {line}: missing closing `)`")


def is_unified(text):
    """Return True if `text` uses the unified `.ode` format (top-level `fn NAME(...)` or top-level
    spec declarations without standalone `contract` blocks).

    Inspects column-0 top-level lines only so indented lines inside legacy `fn ... as "..." { ... }`
    bodies are never misclassified.
    """
    has_unified_fn = False
    has_legacy_fn = False
    has_spec_def = False
    has_contract = False
    for line in text.split("\n"):
        if not line or line[0].isspace() or line.startswith("//"):
            continue
        if re.match(r'^fn\s+[A-Za-z_]\w*\s+as\s+"[^"]+"\s*\{\s*(?://.*)?$', line):
            has_legacy_fn = True
        elif re.match(r'^fn\s+[A-Za-z_]\w*(?:\s+as\s+"[^"]+")?\s*\(', line):
            has_unified_fn = True
        elif re.match(r"^fn\s+[A-Za-z_]\w*\s*\{", line):
            has_unified_fn = True
        elif re.match(r"^(use|const|def|sequence|layout|kind|lemma)\b", line):
            has_spec_def = True
        elif re.match(r"^contract\b", line):
            has_contract = True
    if has_legacy_fn and not has_unified_fn and not has_spec_def:
        return False
    return has_unified_fn or (has_spec_def and not has_contract)


def _dedent_body(body_text, body_start_line):
    raw_lines = body_text.split("\n")
    start_line = body_start_line
    if raw_lines and not raw_lines[0].strip():
        raw_lines = raw_lines[1:]
        start_line += 1
    if raw_lines and not raw_lines[-1].strip():
        raw_lines = raw_lines[:-1]
    non_empty = [ln for ln in raw_lines if ln.strip()]
    indent = min((len(ln) - len(ln.lstrip(" ")) for ln in non_empty), default=0)
    dedented = [ln[indent:] if len(ln) >= indent else ln.lstrip(" ") for ln in raw_lines]
    return dedented, start_line


def _expand_comma_requires(clauses_text):
    """Allow comma-separated `requires a <= b, b <= c` (splitting only at top-level commas, never `no_overlap`)."""
    out = []
    for raw in clauses_text.splitlines():
        code = _strip_line_comment(raw)
        s = code.strip()
        if s.startswith("requires ") and not s.startswith("requires no_overlap"):
            rest = s[len("requires "):]
            parts, cur, depth = [], [], 0
            for ch in rest:
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth = max(0, depth - 1)
                elif ch == "," and depth == 0:
                    parts.append("".join(cur).strip())
                    cur = []
                    continue
                cur.append(ch)
            parts.append("".join(cur).strip())
            if len(parts) > 1:
                for p in parts:
                    if p:
                        out.append(f"requires {p}")
                continue
        out.append(raw)
    return "\n".join(out)


def _rewrite_hl_lines(lines, first_line, mod_prefix, mod_exports, uses_map, src):
    """Rewrite `alias.member` references inside a High-Level Ode body (specs, calls, data)."""
    out = []
    for idx, ln in enumerate(lines):
        code = _strip_line_comment(ln)
        comment = ln[len(code):]
        line_no = first_line + idx

        def repl_qual(m):
            alias, member = m.group(1), m.group(2)
            if alias not in uses_map:
                return m.group(0)
            dep = uses_map[alias]
            if member not in dep["exports"]:
                avail = ", ".join(sorted(dep["exports"])) or "(none)"
                raise UnifiedErr(
                    f"{src}: line {line_no}: `{alias}.{member}` not found in `{dep['rel']}` (exports: {avail})"
                )
            exp = dep["exports"][member]
            if exp["kind"] == "fn":
                return dep["prefix"] + exp["symbol"]
            return dep["prefix"] + member

        code = re.sub(r"(?<!\.)\b([A-Za-z_]\w*)\.([A-Za-z_]\w*)\b", repl_qual, code)
        if mod_prefix:
            for nm, exp in mod_exports.items():
                if exp["kind"] in ("fn", "def", "const", "data"):
                    target_nm = mod_prefix + (exp["symbol"] if exp["kind"] == "fn" else nm)
                    code = re.sub(rf"(?<!\.)\b{re.escape(nm)}\b", target_nm, code)
        out.append(code + comment)
    return out


def _lower_all_hl(fns, data, src, c_abi_fn=None):
    """Lower every High-Level Ode implementation block deterministically into `odec` assembly + `hl_meta`,
    giving every `fn` (including `use`-imported top-level functions) Ode's fast calling convention
    with auto-derived exact `preserves` by default; only `c_abi_fn` (when packing for C FFI) uses C ABI."""
    fn_names = {f["name"] for f in fns} | {f["symbol"] for f in fns}
    data_by_arch = {}
    for darch, dname, _ in data:
        for a in (TARGETS if darch is None else (darch,)):
            data_by_arch.setdefault(a, set()).add(dname)
    # Every function called by another function (in this file OR across `use`-imported modules) gets
    # Ode's fast calling convention with exact `preserves`; `c_abi_fn` uses pure C ABI at the FFI boundary.
    called_by_other = set()
    for f in fns:
        all_txt = "\n".join("\n".join(im["lines"]) for im in f["impls"].values())
        for g in fns:
            if g["name"] != f["name"] and (
                re.search(rf"\b{re.escape(g['name'])}\s*\(", all_txt)
                or re.search(rf"\b{re.escape(g['symbol'])}\s*\(", all_txt)
            ):
                called_by_other.add(g["name"])
    callee_clobbers = {a: {} for a in TARGETS}
    callee_stack = {a: {} for a in TARGETS}
    for fn_rec in fns:
        has_fn_stack = bool(re.search(r"(?m)^\s*stack\b", fn_rec["clauses_text"]))
        raw_params = fn_rec.get("raw_params_text", fn_rec["params_text"])
        for key, im in fn_rec["impls"].items():
            if not im.get("hl"):
                continue
            arch = im["arch"]
            has_impl_stack = any(re.match(r"^\s*stack\b", ec) for ec in im["extra_clauses"])
            explicit_stack = has_fn_stack or has_impl_stack
            impl_needs = set(re.findall(r"(?m)^\s*needs\s+([A-Za-z0-9_]+)", fn_rec["clauses_text"]))
            for ec in im["extra_clauses"]:
                impl_needs.update(re.findall(r"(?m)^\s*needs\s+([A-Za-z0-9_]+)", ec))
            try:
                res = ode_hl.lower_hl_block(
                    fn_rec["name"], raw_params, im["lines"], im["first_line"], arch,
                    src=src, fn_names=fn_names, data_names=data_by_arch.get(arch, set()),
                    explicit_stack=explicit_stack,
                    callee_clobbers=callee_clobbers.get(arch),
                    needs=impl_needs,
                )
            except ode_hl.HLErr as exc:
                if im.get("portable"):
                    im["hl_err"] = str(exc)
                    continue
                raise UnifiedErr(str(exc)) from exc
            im["hl_lines"] = list(im["lines"])
            im["lines"] = res["lines"]
            im["hl_meta"] = res
            # Compute transitive stack budget across called functions in this `.ode` graph
            max_callee_stk = 0
            for ln in res["lines"]:
                mc = re.match(r"^\s*(?:call|bl|jmp|b)\s+([A-Za-z_]\w*)$", ln)
                if mc and mc.group(1) in callee_stack[arch]:
                    max_callee_stk = max(max_callee_stk, callee_stack[arch][mc.group(1)])
            eff_stack = res["total_stack"] + max_callee_stk
            res["total_stack"] = eff_stack
            callee_stack[arch][fn_rec["name"]] = eff_stack
            callee_stack[arch][fn_rec["symbol"]] = eff_stack
            if not explicit_stack:
                im["extra_clauses"] = list(im["extra_clauses"]) + [f"stack {eff_stack}"]
            else:
                stk_vals = [int(m.group(1)) for ec in im["extra_clauses"] for m in [re.match(r"^\s*stack\s+(\d+)\b", ec)] if m]
                if not stk_vals:
                    stk_vals = [int(m.group(1)) for m in re.finditer(r"(?m)^\s*stack\s+(\d+)\b", fn_rec["clauses_text"])]
                if stk_vals and eff_stack > stk_vals[-1]:
                    im["hl_err"] = (
                        f"{src}: fn `{fn_rec['name']}` ({arch}): lowered stack usage is {eff_stack} bytes, "
                        f"exceeding explicit `stack {stk_vals[-1]}`; omit `stack` to auto-compute or raise to `stack {eff_stack}`"
                    )
            # Attach Ode's fast calling convention (`preserves ...`) to every called/imported `fn`
            # (never on the explicit `--c-abi` FFI entry function).
            if fn_rec["name"] != c_abi_fn and fn_rec["name"] in called_by_other and im["calling_text"] is None and res.get("auto_calling"):
                im["calling_text"] = res["auto_calling"]
                callee_clobbers[arch][fn_rec["name"]] = res["clobbered"]
                callee_clobbers[arch][fn_rec["symbol"]] = res["clobbered"]


def _parse_for_blocks(body_text, fn_name, body_start_line, src):
    """Parse zero or more `for <arch>[:variant] ... { ... }` blocks OR a portable High-Level Ode body `{ ... }`."""
    pos = _skip_ws_and_comments(body_text, 0)
    n = len(body_text)
    if pos < n and not re.match(r"for\s+(?:x86_64|arm64)(?::[A-Za-z0-9_+.-]+)?\b", body_text[pos:]):
        dedented, start_line = _dedent_body(body_text, body_start_line)
        if ode_hl.is_hl_body(dedented):
            impls = {}
            for arch in TARGETS:
                impls[arch] = {
                    "arch": arch,
                    "variant": None,
                    "key": arch,
                    "extra_clauses": [],
                    "calling_text": None,
                    "lines": list(dedented),
                    "first_line": start_line,
                    "hl": True,
                    "portable": True,
                }
            return impls
    impls = {}
    while pos < n:
        line_no = body_start_line + body_text.count("\n", 0, pos)
        m = re.match(r"for\s+([A-Za-z0-9_]+)(?::([A-Za-z0-9_+.-]+))?\b", body_text[pos:])
        if not m:
            snippet = body_text[pos:pos + 40].splitlines()[0]
            raise UnifiedErr(
                f"{src}: line {line_no}: inside `fn {fn_name}`, expected `for <arch> ... {{ ... }}`, got {snippet!r}"
            )
        arch = m.group(1)
        variant = m.group(2)
        if arch not in TARGETS:
            raise UnifiedErr(
                f"{src}: line {line_no}: `fn {fn_name}`: unsupported target `{arch}` (expected one of {', '.join(TARGETS)})"
            )
        key = f"{arch}:{variant}" if variant else arch
        if key in impls:
            raise UnifiedErr(f"{src}: line {line_no}: `fn {fn_name}` defines `for {key}` more than once")
        cur = _skip_ws_and_comments(body_text, pos + m.end())

        # Scan optional clauses before the implementation body `{`:
        # `needs ...`, `stack ...`, `calling { ... }`
        calling_text = None
        extra_clauses = []
        while cur < n:
            cur = _skip_ws_and_comments(body_text, cur)
            if cur >= n:
                raise UnifiedErr(f"{src}: line {line_no}: `for {key}` missing implementation body `{{ ... }}`")
            if body_text[cur] == "{":
                break
            cm = re.match(r"calling\b", body_text[cur:])
            if cm:
                if calling_text is not None:
                    raise UnifiedErr(f"{src}: line {line_no}: `for {key}` says `calling` more than once")
                bopen = _skip_ws_and_comments(body_text, cur + cm.end())
                if bopen >= n or body_text[bopen] != "{":
                    raise UnifiedErr(f"{src}: line {line_no}: `calling` must be followed by `{{ ... }}`")
                bclose = _find_matching_brace(body_text, bopen, src)
                calling_text = body_text[cur:bclose + 1]
                cur = bclose + 1
                continue
            km = re.match(r"(needs|stack)\b", body_text[cur:])
            if km:
                # Consume clause up to next `needs`, `stack`, `calling`, or `{` at paren-depth 0.
                cstart = cur
                i = cur + km.end()
                pdepth = 0
                while i < n:
                    ch = body_text[i]
                    if ch == "/" and i + 1 < n and body_text[i + 1] == "/":
                        nl = body_text.find("\n", i)
                        i = n if nl == -1 else nl + 1
                        continue
                    if ch == "(":
                        pdepth += 1
                    elif ch == ")":
                        pdepth = max(0, pdepth - 1)
                    elif pdepth == 0:
                        if ch == "{":
                            break
                        if i > cstart and body_text[i - 1].isspace() and re.match(r"(?:needs|stack|calling)\b", body_text[i:]):
                            break
                    i += 1
                extra_clauses.append(body_text[cstart:i].strip())
                cur = i
                continue
            snippet = body_text[cur:cur + 35].splitlines()[0]
            raise UnifiedErr(
                f"{src}: line {line_no}: in `for {key}` header, expected `needs`, `stack`, `calling` or `{{`, got {snippet!r}"
            )

        bclose = _find_matching_brace(body_text, cur, src)
        asm_start_line = body_start_line + body_text.count("\n", 0, cur + 1)
        asm_body = body_text[cur + 1:bclose]
        # Strip leading/trailing empty lines while preserving exact source line numbers
        raw_lines = asm_body.split("\n")
        if raw_lines and not raw_lines[0].strip():
            raw_lines = raw_lines[1:]
            asm_start_line += 1
        if raw_lines and not raw_lines[-1].strip():
            raw_lines = raw_lines[:-1]
        # Dedent common leading whitespace so `place { ... }` / labels align cleanly for `odec.expand`
        non_empty = [ln for ln in raw_lines if ln.strip()]
        indent = min((len(ln) - len(ln.lstrip(" ")) for ln in non_empty), default=0)
        dedented = [ln[indent:] if len(ln) >= indent else ln.lstrip(" ") for ln in raw_lines]

        impls[key] = {
            "arch": arch,
            "variant": variant,
            "key": key,
            "extra_clauses": extra_clauses,
            "calling_text": calling_text,
            "lines": dedented,
            "first_line": asm_start_line,
            "hl": ode_hl.is_hl_body(dedented),
        }
        pos = _skip_ws_and_comments(body_text, bclose + 1)
    return impls


def _parse_single_unified(text, src="<ode>"):
    """Parse one unified `.ode` source file without resolving `use` links."""
    uses = []
    spec_defs = []
    data = []
    inlines = []
    fns = []
    fns_by_name = {}
    declared_names = {}
    exports = {}

    def claim(kind_lbl, name, line_no, allow_multi_kind=None, symbol=None):
        if name in declared_names:
            prev_kind, prev_line = declared_names[name]
            if allow_multi_kind is None or prev_kind != allow_multi_kind:
                raise UnifiedErr(
                    f"{src}: line {line_no}: duplicate name `{name}` ({kind_lbl}); already declared as {prev_kind} on line {prev_line}"
                )
        else:
            declared_names[name] = (kind_lbl, line_no)
        if kind_lbl != "use":
            exports[name] = {"kind": kind_lbl, "symbol": symbol or name}

    pos = _skip_ws_and_comments(text, 0)
    n = len(text)
    while pos < n:
        line_no = text.count("\n", 0, pos) + 1
        rest = text[pos:]

        # 0. `use ALIAS = "relative/path.ode"` (explicit linked local namespace)
        m = re.match(r'^use\s+([A-Za-z_]\w*)\s*=\s*"([^"]+)"\s*(?://[^\n]*)?(?:\n|$)', rest)
        if m:
            alias, rel_path = m.group(1), m.group(2)
            if alias in ("frame", "budget", "reg", "place", "for", "if", "loop", "else", "let"):
                raise UnifiedErr(f"{src}: line {line_no}: `{alias}` cannot be used as a module alias")
            claim("use", alias, line_no)
            uses.append((alias, rel_path, line_no))
            pos = _skip_ws_and_comments(text, pos + m.end())
            continue
        if re.match(r"^use\b", rest):
            snippet = rest[:50].splitlines()[0]
            raise UnifiedErr(
                f'{src}: line {line_no}: expected `use ALIAS = "path.ode"`, got {snippet!r}'
            )

        # 1. `def`, `sequence`, `layout` (brace-delimited spec blocks)
        m = re.match(r"^(def|sequence|layout)\s+([A-Za-z_]\w*)\b", rest)
        if m:
            claim(m.group(1), m.group(2), line_no)
            bopen = _find_open_brace(text, pos + m.end())
            if bopen == -1 or "=" in text[pos + m.end():bopen]:
                raise UnifiedErr(f"{src}: line {line_no}: `{m.group(1)} {m.group(2)}` body must be enclosed in `{{ ... }}`")
            bclose = _find_matching_brace(text, bopen, src)
            spec_defs.append((m.group(1), m.group(2), text[pos:bclose + 1], line_no))
            pos = _skip_ws_and_comments(text, bclose + 1)
            continue

        # 2. `const NAME = EXPR` (may span lines if brackets/parens are open)
        m = re.match(r"^const\s+([A-Za-z_]\w*)\s*=", rest)
        if m:
            claim("const", m.group(1), line_no)
            i = pos + m.end()
            depth = 0
            while i < n:
                ch = text[i]
                if ch == "/" and i + 1 < n and text[i + 1] == "/":
                    nl = text.find("\n", i)
                    if depth == 0:
                        i = n if nl == -1 else nl
                        break
                    i = n if nl == -1 else nl + 1
                    continue
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth = max(0, depth - 1)
                elif ch == "\n" and depth == 0:
                    break
                i += 1
            spec_defs.append(("const", m.group(1), text[pos:i].strip(), line_no))
            pos = _skip_ws_and_comments(text, i)
            continue

        # 3. `kind NAME: ...` or `lemma ...`
        m = re.match(r"^(kind|lemma)\s+([A-Za-z_]\w*)\b", rest)
        if m:
            nl = text.find("\n", pos)
            end = n if nl == -1 else nl
            if m.group(1) == "kind":
                claim("kind", m.group(2), line_no)
            spec_defs.append((m.group(1), m.group(2), _strip_line_comment(text[pos:end]).strip(), line_no))
            pos = _skip_ws_and_comments(text, end)
            continue

        # 4. `data [for ARCH] NAME = w0, w1, ...`
        m = re.match(r"^data\s+(?:for\s+(\w+)\s+)?([A-Za-z_]\w*)\s*=\s*([^\n]*)", rest)
        if m:
            darch = m.group(1)
            if darch is not None and darch not in TARGETS:
                raise UnifiedErr(f"{src}: line {line_no}: unsupported `data for {darch}`")
            claim("data", m.group(2), line_no, allow_multi_kind="data")
            words = [int(w.strip().replace("_", ""), 0) for w in _strip_line_comment(m.group(3)).split(",") if w.strip()]
            data.append((darch, m.group(2), words))
            pos = _skip_ws_and_comments(text, pos + m.end())
            continue

        # 5. `inline fn NAME [for ARCH] (...) ... { ... }`
        m = re.match(r"^inline\s+fn\s+([A-Za-z_]\w*)(?:\s+for\s+(\w+))?\b", rest)
        if m:
            iarch = m.group(2)
            if iarch is not None and iarch not in TARGETS:
                raise UnifiedErr(f"{src}: line {line_no}: unsupported `inline fn ... for {iarch}`")
            claim("inline", m.group(1), line_no, allow_multi_kind="inline")
            bopen = _find_open_brace(text, pos + m.end())
            if bopen == -1:
                raise UnifiedErr(f"{src}: line {line_no}: `inline fn {m.group(1)}` missing `{{`")
            bclose = _find_matching_brace(text, bopen, src)
            # Rewrite `inline fn NAME for ARCH (` -> `inline fn NAME (` for odec.inline_of
            raw_hdr = text[pos:bopen]
            if iarch is not None:
                raw_hdr = re.sub(r"^(inline\s+fn\s+[A-Za-z_]\w*)\s+for\s+\w+", r"\1", raw_hdr, count=1)
            inlines.append((iarch, m.group(1), raw_hdr + text[bopen:bclose + 1], line_no))
            pos = _skip_ws_and_comments(text, bclose + 1)
            continue

        # 6. `fn NAME [as "SYM"] (args...) <contract clauses> { for <arch> ... }`
        m = re.match(r'^fn\s+([A-Za-z_]\w*)(?:\s+as\s+"([^"]+)")?', rest)
        if m:
            fname = m.group(1)
            fsym = m.group(2) or fname
            claim("fn", fname, line_no, symbol=fsym)
            after_name = _skip_ws_and_comments(text, pos + m.end())
            if after_name >= n or text[after_name] != "(":
                raise UnifiedErr(
                    f"{src}: line {line_no}: `fn {fname}` has no parameter list and contract; "
                    f"every Ode `fn` must declare parameters and a contract: `fn {fname}(...) requires/returns/ensures ... stack N {{ ... }}`"
                )
            pclose = _find_matching_paren(text, after_name, src)
            raw_params_text = text[after_name + 1:pclose].strip()
            params_text, u8_reqs = ode_hl.normalize_contract_params(raw_params_text)
            # Accept BOTH `fn f(...) <clauses> { ... }` AND direct `fn f(...) <clauses> for <arch> ... { ... }`
            # without redundant outer double braces.
            scan = pclose + 1
            bopen = -1
            direct_for_pos = -1
            s_pdepth = 0
            while scan < n:
                ch = text[scan]
                if ch == "/" and scan + 1 < n and text[scan + 1] == "/":
                    nl = text.find("\n", scan)
                    scan = n if nl == -1 else nl + 1
                    continue
                if ch == "(":
                    s_pdepth += 1
                elif ch == ")":
                    s_pdepth = max(0, s_pdepth - 1)
                elif s_pdepth == 0:
                    if ch == "{":
                        bopen = scan
                        break
                    if (scan == pclose + 1 or text[scan - 1].isspace()) and re.match(
                        r"for\s+(?:x86_64|arm64)(?::[A-Za-z0-9_+.-]+)?\b", text[scan:]
                    ):
                        direct_for_pos = scan
                        break
                scan += 1
            if direct_for_pos != -1:
                clauses_raw = text[pclose + 1:direct_for_pos].strip()
                # Consume one or more consecutive `for <arch>[:variant] [needs/stack/calling...] { ... }` blocks
                cur_f = direct_for_pos
                end_f = direct_for_pos
                while cur_f < n:
                    cur_f = _skip_ws_and_comments(text, cur_f)
                    if cur_f >= n or not re.match(r"for\s+(?:x86_64|arm64)(?::[A-Za-z0-9_+.-]+)?\b", text[cur_f:]):
                        break
                    # Skip optional `calling { ... }` blocks in the `for` header, then find the body `{ ... }`
                    fm = re.match(r"for\s+(?:x86_64|arm64)(?::[A-Za-z0-9_+.-]+)?\b", text[cur_f:])
                    hpos = cur_f + fm.end()
                    while hpos < n:
                        hpos = _skip_ws_and_comments(text, hpos)
                        if hpos >= n:
                            raise UnifiedErr(f"{src}: line {line_no}: `fn {fname}` missing `{{` for target block")
                        if text[hpos] == "{":
                            break
                        cm = re.match(r"calling\b", text[hpos:])
                        if cm:
                            copen = _skip_ws_and_comments(text, hpos + cm.end())
                            if copen >= n or text[copen] != "{":
                                raise UnifiedErr(f"{src}: line {line_no}: `calling` must be followed by `{{ ... }}`")
                            hpos = _find_matching_brace(text, copen, src) + 1
                            continue
                        hpos += 1
                    fclose = _find_matching_brace(text, hpos, src)
                    end_f = fclose + 1
                    cur_f = end_f
                body_start_line = text.count("\n", 0, direct_for_pos) + 1
                body_text = text[direct_for_pos:end_f]
                bclose = end_f - 1
            else:
                if bopen == -1:
                    raise UnifiedErr(f"{src}: line {line_no}: `fn {fname}` missing `{{`")
                clauses_raw = text[pclose + 1:bopen].strip()
                bclose = _find_matching_brace(text, bopen, src)
                body_start_line = text.count("\n", 0, bopen + 1) + 1
                body_text = text[bopen + 1:bclose]
            clauses_raw = re.sub(r"^->\s*(?:u64|u8|number|void)\b\s*", "", clauses_raw)
            clauses_text = _expand_comma_requires(clauses_raw)
            if u8_reqs:
                clauses_text = ("\n".join(u8_reqs) + ("\n" + clauses_text if clauses_text else "")).strip()
            impls = _parse_for_blocks(body_text, fname, body_start_line, src)

            # Enforce non-empty contract clauses (refuse contractless `fn` loudly!)
            if not clauses_text and all(not im["extra_clauses"] for im in impls.values()):
                raise UnifiedErr(
                    f"{src}: line {line_no}: `fn {fname}` has no contract clauses; "
                    f"every Ode `fn` must state its contract (returns/ensures/writes and stack)"
                )

            fn_rec = {
                "name": fname,
                "symbol": fsym,
                "params_text": params_text,
                "raw_params_text": raw_params_text,
                "clauses_text": clauses_text,
                "line": line_no,
                "impls": impls,
            }
            fns.append(fn_rec)
            fns_by_name[fname] = fn_rec
            pos = _skip_ws_and_comments(text, bclose + 1)
            continue

        # 7. Reject stray `contract` blocks in unified `.ode` (contracts belong on `fn`!)
        if re.match(r"^contract\b", rest):
            raise UnifiedErr(
                f"{src}: line {line_no}: standalone `contract` block inside `.ode`; "
                f"write contract clauses directly on `fn NAME(...) <clauses> {{ ... }}`"
            )

        snippet = rest[:40].splitlines()[0]
        raise UnifiedErr(f"{src}: line {line_no}: unexpected top-level item in `.ode`: {snippet!r}")

    return {
        "uses": uses,
        "spec_defs": spec_defs,
        "data": data,
        "inlines": inlines,
        "fns": fns,
        "fns_by_name": fns_by_name,
        "exports": exports,
    }


def _collect_param_names(params_text):
    """Extract parameter names from `a: bytes, n: number` or `a, at`."""
    names = set()
    if not params_text:
        return names
    # Split on top-level commas
    depth = 0
    cur = []
    for ch in params_text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            part = "".join(cur).strip()
            m = re.match(r"^([A-Za-z_]\w*)\b", part)
            if m:
                names.add(m.group(1))
            cur = []
            continue
        cur.append(ch)
    part = "".join(cur).strip()
    m = re.match(r"^([A-Za-z_]\w*)\b", part)
    if m:
        names.add(m.group(1))
    return names


def _collect_local_binders(spec_text, initial=()):
    """Collect local binder names (`let x =`, `for i in`, `the least/greatest ... k`)."""
    binders = set(initial)
    for m in re.finditer(r"\b(?:let|for)\s+([A-Za-z_]\w*)\b", spec_text):
        binders.add(m.group(1))
    for m in re.finditer(r"\bthe\s+(?:least|greatest)\s+(?:number|power\s+of\s+two)\s+([A-Za-z_]\w*)\b", spec_text):
        binders.add(m.group(1))
    return binders


def _rewrite_spec_text(text, mod_prefix, mod_exports, uses_map, local_binders, src, base_line):
    """Token-aware rewriter for specification / contract / `place { ... }` text.

    - Rewrites `alias.member` (where `alias` is in `uses_map` and not shadowed by a local binder)
      to the target module's mangled identifier, refusing unknown members loudly.
    - Refuses bare `alias` (without `.member`) when not shadowed by a local binder.
    - For non-root modules (`mod_prefix != ""`), rewrites bare references to `mod_exports`
      (when not preceded by `.` and not in `local_binders`) to `mod_prefix + name`.
    """
    out = []
    i = 0
    n = len(text)
    prev_was_dot = False
    while i < n:
        ch = text[i]
        if ch == "/" and i + 1 < n and text[i + 1] == "/":
            nl = text.find("\n", i)
            end = n if nl == -1 else nl + 1
            out.append(text[i:end])
            i = end
            prev_was_dot = False
            continue
        if ch == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\" and j + 1 < n:
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            out.append(text[i:j])
            i = j
            prev_was_dot = False
            continue
        if ch.isalpha() or ch == "_":
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            ident = text[i:j]
            line_no = base_line + text.count("\n", 0, i)
            if not prev_was_dot and ident in uses_map and ident not in local_binders:
                if j < n and text[j] == "." and j + 1 < n and (text[j + 1].isalpha() or text[j + 1] == "_"):
                    k = j + 2
                    while k < n and (text[k].isalnum() or text[k] == "_"):
                        k += 1
                    member = text[j + 1:k]
                    dep = uses_map[ident]
                    if member not in dep["exports"]:
                        avail = ", ".join(sorted(dep["exports"])) or "(none)"
                        raise UnifiedErr(
                            f"{src}: line {line_no}: `{ident}.{member}` not found in `{dep['rel']}` (exports: {avail})"
                        )
                    out.append(dep["prefix"] + member)
                    i = k
                    prev_was_dot = False
                    continue
                raise UnifiedErr(
                    f"{src}: line {line_no}: module alias `{ident}` must be qualified as `{ident}.<name>`"
                )
            # Do not mangle record-literal field keys (`{ field: ... }`) or typed param names (`x: bytes`).
            k_ws = j
            while k_ws < n and text[k_ws] in " \t":
                k_ws += 1
            followed_by_colon = k_ws < n and text[k_ws] == ":" and (k_ws + 1 >= n or text[k_ws + 1] != "=")
            if not prev_was_dot and not followed_by_colon and mod_prefix and ident in mod_exports and ident not in local_binders:
                out.append(mod_prefix + ident)
            else:
                out.append(ident)
            i = j
            prev_was_dot = False
            continue
        out.append(ch)
        if ch == ".":
            prev_was_dot = True
        elif not ch.isspace():
            prev_was_dot = False
        i += 1
    return "".join(out)


def _rewrite_spec_decl(kind, name, raw_text, mod_prefix, mod_exports, uses_map, src, base_line):
    """Rewrite one top-level `const`/`def`/`sequence`/`layout`/`kind`/`lemma` declaration."""
    if kind in ("def", "sequence"):
        popen = raw_text.find("(")
        bopen = _find_open_brace(raw_text, 0)
        params = set()
        if popen != -1 and (bopen == -1 or popen < bopen):
            pclose = _find_matching_paren(raw_text, popen, src)
            params = _collect_param_names(raw_text[popen + 1:pclose])
            # For `sequence NAME(args) { h[0] = ... }`, also keep the sequence state name local.
            hdr = raw_text[:pclose + 1]
            body = raw_text[pclose + 1:]
            if mod_prefix:
                hdr = re.sub(
                    rf"^({kind}\s+){re.escape(name)}\b",
                    rf"\g<1>{mod_prefix}{name}",
                    hdr,
                    count=1,
                )
            binders = _collect_local_binders(body, params)
            if kind == "sequence":
                m_st = re.search(r"\{\s*([A-Za-z_]\w*)\s*\[", body)
                if m_st:
                    binders.add(m_st.group(1))
            return hdr + _rewrite_spec_text(body, mod_prefix, mod_exports, uses_map, binders, src, base_line)
    if kind == "layout":
        bopen = _find_open_brace(raw_text, 0)
        hdr = raw_text[:bopen + 1]
        body = raw_text[bopen + 1:]
        if mod_prefix:
            hdr = re.sub(rf"^(layout\s+){re.escape(name)}\b", rf"\g<1>{mod_prefix}{name}", hdr, count=1)
        # Inside layout `{ field: TYPE, ... }`, rewrite only type/size expressions after `:`.
        lines = body.split("\n")
        rewritten = []
        for idx, ln in enumerate(lines):
            if ":" in ln:
                left, right = ln.split(":", 1)
                right = _rewrite_spec_text(right, mod_prefix, mod_exports, uses_map, set(), src, base_line + idx)
                rewritten.append(left + ":" + right)
            else:
                rewritten.append(ln)
        return hdr + "\n".join(rewritten)
    if kind == "const":
        eq = raw_text.find("=")
        hdr = raw_text[:eq + 1]
        rhs = raw_text[eq + 1:]
        if mod_prefix:
            hdr = re.sub(rf"^(const\s+){re.escape(name)}\b", rf"\g<1>{mod_prefix}{name}", hdr, count=1)
        binders = _collect_local_binders(rhs)
        return hdr + _rewrite_spec_text(rhs, mod_prefix, mod_exports, uses_map, binders, src, base_line)
    # `kind` / `lemma`
    binders = _collect_local_binders(raw_text)
    return _rewrite_spec_text(raw_text, mod_prefix, mod_exports, uses_map, binders, src, base_line)


def _rewrite_asm_line(line, mod_prefix, mod_exports, uses_map, src, line_no):
    """Rewrite one non-place assembly / inline-body line for linked local namespaces."""
    # Split off trailing `// ...` comment so comments are untouched.
    code = _strip_line_comment(line)
    comment = line[len(code):]

    # 1. Replace every `alias.member` where `alias in uses_map`.
    def repl_qual(m):
        alias, member = m.group(1), m.group(2)
        if alias not in uses_map:
            return m.group(0)
        dep = uses_map[alias]
        if member not in dep["exports"]:
            avail = ", ".join(sorted(dep["exports"])) or "(none)"
            raise UnifiedErr(
                f"{src}: line {line_no}: `{alias}.{member}` not found in `{dep['rel']}` (exports: {avail})"
            )
        exp = dep["exports"][member]
        if exp["kind"] == "fn":
            return dep["prefix"] + exp["symbol"]
        return dep["prefix"] + member

    code = re.sub(r"(?<!\.)\b([A-Za-z_]\w*)\.([A-Za-z_]\w*)\b", repl_qual, code)

    # 2. For non-root modules, mangle local `fn` call/tail-call targets, local `inline fn` calls,
    #    and local `data` symbol references without ever touching mnemonics or registers.
    if mod_prefix:
        # `call target` / `bl target` / `jmp target` / `b target`
        m = re.match(r"^(\s*(?:call|bl|jmp|b)\s+)([A-Za-z_]\w*)(\s*)$", code)
        if m and m.group(2) in mod_exports and mod_exports[m.group(2)]["kind"] == "fn":
            code = m.group(1) + mod_prefix + mod_exports[m.group(2)]["symbol"] + m.group(3)
        else:
            # Local `inline fn` call `NAME(...)`
            m_inl = re.match(r"^(\s*)([A-Za-z_]\w*)(\s*\(.*\)\s*)$", code)
            if m_inl and m_inl.group(2) in mod_exports and mod_exports[m_inl.group(2)]["kind"] == "inline":
                code = m_inl.group(1) + mod_prefix + m_inl.group(2) + m_inl.group(3)
            else:
                # Local `data` references in operand positions (after whitespace/punctuation, not mnemonic at start)
                local_data = {k for k, v in mod_exports.items() if v["kind"] == "data"}
                if local_data:
                    m_op = re.match(r"^(\s*[A-Za-z_][\w.]*\s+)(.*)$", code)
                    if m_op:
                        head, ops = m_op.group(1), m_op.group(2)
                        pat = r"(?<!\.)\b(" + "|".join(re.escape(k) for k in sorted(local_data, key=len, reverse=True)) + r")\b"
                        ops = re.sub(pat, lambda mm: mod_prefix + mm.group(1), ops)
                        code = head + ops
    return code + comment


def _rewrite_asm_lines(lines, first_line, fn_params, mod_prefix, mod_exports, uses_map, src):
    """Rewrite assembly lines of a `for <arch>` block, routing `place { ... }` through spec rewriting."""
    out = []
    reg_aliases = set()
    i = 0
    n = len(lines)
    while i < n:
        ln = lines[i]
        stripped = _strip_line_comment(ln).strip()
        if re.match(r"^reg\b", stripped):
            for part in stripped[3:].split(","):
                mm = re.fullmatch(r"\s*(\w+)\s*=\s*(\w+)\s*", part)
                if mm:
                    reg_aliases.add(mm.group(1))
        if re.match(r"^place\s*\{", stripped):
            # Gather multi-line `place { ... }` block
            block_lines = [ln]
            depth = stripped.count("{") - stripped.count("}")
            j = i + 1
            while depth > 0 and j < n:
                s2 = _strip_line_comment(lines[j])
                depth += s2.count("{") - s2.count("}")
                block_lines.append(lines[j])
                j += 1
            joined = "\n".join(block_lines)
            bopen = joined.find("{")
            hdr = joined[:bopen + 1]
            rest = joined[bopen + 1:]
            binders = _collect_local_binders(rest, fn_params) | reg_aliases
            rew = hdr + _rewrite_spec_text(rest, mod_prefix, mod_exports, uses_map, binders, src, first_line + i)
            out.extend(rew.split("\n"))
            i = j
            continue
        out.append(_rewrite_asm_line(ln, mod_prefix, mod_exports, uses_map, src, first_line + i))
        i += 1
    return out


def parse_unified(text, src="<ode>", resolve_uses=True, c_abi_fn=None):
    """Parse a unified `.ode` source file (closed local namespace) and resolve any `use` links.

    Returns a dict:
      - `spec_defs`: list of raw top-level `const`/`def`/`sequence`/`layout`/`kind`/`lemma` blocks
      - `data`: list of `(arch_or_None, name, [words])`
      - `inlines`: list of `(arch_or_None, raw_inline_text, start_line)`
      - `fns`: list of function dicts in topological source order (dependencies before root):
          {name, symbol, params_text, clauses_text, line, impls: {key: impl_dict}}
      - `fns_by_name`: {name: fn_dict}
      - `root_fns`: list of function dicts declared directly in the root file
      - `pretty_names`: {mangled_name: "alias.name"} for human-readable glossaries
    """
    root_parsed = _parse_single_unified(text, src)
    if not resolve_uses or not root_parsed["uses"]:
        _lower_all_hl(root_parsed["fns"], root_parsed["data"], src, c_abi_fn=c_abi_fn)
        return {
            "spec_defs": [raw for _, _, raw, _ in root_parsed["spec_defs"]],
            "data": root_parsed["data"],
            "inlines": [(arch, raw, lno) for arch, _, raw, lno in root_parsed["inlines"]],
            "fns": root_parsed["fns"],
            "fns_by_name": root_parsed["fns_by_name"],
            "root_fns": list(root_parsed["fns"]),
            "pretty_names": {},
        }

    if not os.path.isfile(src):
        raise UnifiedErr(f"{src}: `use` requires a source file path on disk")

    root_real = os.path.realpath(src)
    mods = {}      # realpath -> module record
    order = []     # realpaths in post-order (dependencies before dependents, root last)
    visiting = []  # stack of realpaths for cycle detection

    def load_mod(path, raw_text=None):
        real = os.path.realpath(path)
        if real in visiting:
            cyc = " -> ".join(os.path.basename(p) for p in visiting[visiting.index(real):] + [real])
            raise UnifiedErr(f"{path}: circular `use` dependency: {cyc}")
        if real in mods:
            return mods[real]
        visiting.append(real)
        if raw_text is None:
            if not os.path.isfile(path):
                raise UnifiedErr(f"cannot open `use`d file `{path}`")
            with open(path, "r", encoding="utf-8") as f:
                raw_text = f.read()
        parsed = _parse_single_unified(raw_text, path)
        base_dir = os.path.dirname(os.path.abspath(path))
        dep_map = {}
        for alias, rel, lno in parsed["uses"]:
            dep_path = os.path.normpath(os.path.join(base_dir, rel))
            if not os.path.isfile(dep_path):
                raise UnifiedErr(f'{path}: line {lno}: `use {alias} = "{rel}"`: file not found ({dep_path})')
            dep_mod = load_mod(dep_path)
            dep_map[alias] = dep_mod
        visiting.pop()
        rec = {
            "path": path,
            "real": real,
            "rel": os.path.basename(path),
            "parsed": parsed,
            "exports": parsed["exports"],
            "dep_map": dep_map,
            "prefix": "",
        }
        mods[real] = rec
        order.append(real)
        return rec

    load_mod(src, raw_text=text)

    # Assign deterministic prefixes: imported modules get `m1__`, `m2__`, ...; root gets `""`.
    idx = 1
    for real in order:
        if real != root_real:
            mods[real]["prefix"] = f"m{idx}__"
            idx += 1

    # Record readable glossary names (`m1__foo` -> `alias.foo`) for root's direct uses.
    pretty_names = {}
    root_mod = mods[root_real]
    for alias, dep in root_mod["dep_map"].items():
        for exp_name in dep["exports"]:
            pretty_names[dep["prefix"] + exp_name] = f"{alias}.{exp_name}"

    merged_spec_defs = []
    merged_data = []
    merged_inlines = []
    merged_fns = []
    merged_fns_by_name = {}
    root_fns = []

    for real in order:
        mod = mods[real]
        p = mod["parsed"]
        pref = mod["prefix"]
        exps = mod["exports"]
        umap = mod["dep_map"]
        msrc = mod["path"]

        for kind, name, raw_blk, lno in p["spec_defs"]:
            merged_spec_defs.append(
                _rewrite_spec_decl(kind, name, raw_blk, pref, exps, umap, msrc, lno)
            )

        for darch, dname, words in p["data"]:
            merged_data.append((darch, pref + dname, words))

        for iarch, iname, raw_inl, lno in p["inlines"]:
            ilines = raw_inl.split("\n")
            if pref:
                ilines[0] = re.sub(
                    rf"^(inline\s+fn\s+){re.escape(iname)}\b",
                    rf"\g<1>{pref}{iname}",
                    ilines[0],
                    count=1,
                )
            rew_body = [ilines[0]] + [
                _rewrite_asm_line(ln, pref, exps, umap, msrc, lno + k)
                for k, ln in enumerate(ilines[1:], start=1)
            ]
            merged_inlines.append((iarch, "\n".join(rew_body), lno))

        for fn_rec in p["fns"]:
            fn_params = _collect_param_names(fn_rec["params_text"])
            new_name = pref + fn_rec["name"]
            new_sym = pref + fn_rec["symbol"]
            rew_params = _rewrite_spec_text(fn_rec["params_text"], pref, exps, umap, fn_params, msrc, fn_rec["line"])
            cl_binders = _collect_local_binders(fn_rec["clauses_text"], fn_params)
            rew_clauses = _rewrite_spec_text(fn_rec["clauses_text"], pref, exps, umap, cl_binders, msrc, fn_rec["line"])
            new_impls = {}
            for k, im in fn_rec["impls"].items():
                rew_extra = [
                    _rewrite_spec_text(ec, pref, exps, umap, _collect_local_binders(ec, fn_params), msrc, im["first_line"])
                    for ec in im["extra_clauses"]
                ]
                if im.get("hl"):
                    rew_lines = _rewrite_hl_lines(im["lines"], im["first_line"], pref, exps, umap, msrc)
                else:
                    rew_lines = _rewrite_asm_lines(im["lines"], im["first_line"], fn_params, pref, exps, umap, msrc)
                new_impls[k] = dict(im, extra_clauses=rew_extra, lines=rew_lines)
            new_fn = {
                "name": new_name,
                "symbol": new_sym,
                "params_text": rew_params,
                "raw_params_text": fn_rec.get("raw_params_text", fn_rec["params_text"]),
                "clauses_text": rew_clauses,
                "line": fn_rec["line"],
                "impls": new_impls,
            }
            merged_fns.append(new_fn)
            merged_fns_by_name[new_name] = new_fn
            if real == root_real:
                root_fns.append(new_fn)

    _lower_all_hl(merged_fns, merged_data, src, c_abi_fn=c_abi_fn)
    return {
        "spec_defs": merged_spec_defs,
        "data": merged_data,
        "inlines": merged_inlines,
        "fns": merged_fns,
        "fns_by_name": merged_fns_by_name,
        "root_fns": root_fns,
        "pretty_names": pretty_names,
    }


def _select_impl(fn_rec, target_key, src="<ode>"):
    """Select the `for <arch>[:variant]` block matching `target_key` (or None if contract-only)."""
    impls = fn_rec["impls"]
    if not impls:
        return None
    picked = None
    if target_key is None:
        if len(impls) == 1:
            picked = next(iter(impls.values()))
        else:
            raise UnifiedErr(
                f"{src}: `fn {fn_rec['name']}` has multiple targets ({', '.join(impls)}); specify `--target`"
            )
    elif target_key in impls:
        picked = impls[target_key]
    else:
        # If `target_key` has a variant like `x86_64:avx512`, fall back to base `x86_64` for helpers without that variant
        base = target_key.split(":", 1)[0]
        if base in impls:
            picked = impls[base]
    if picked is not None and picked.get("hl_err"):
        raise UnifiedErr(picked["hl_err"])
    return picked


def _contract_text_for(fn_rec, impl, include_calling=False):
    """Build a `contract SYM(params) { ... }` block for `fn_rec` and optional `impl`."""
    parts = []
    if fn_rec["clauses_text"]:
        parts.append(fn_rec["clauses_text"])
    if impl is not None:
        for cl in impl["extra_clauses"]:
            parts.append(cl)
        if include_calling and impl["calling_text"] is not None:
            parts.append(impl["calling_text"])
    body = "\n    ".join(parts)
    return f"contract {fn_rec['symbol']}({fn_rec['params_text']}) {{\n    {body}\n}}"


def extract_spec(parsed, target_key=None, fn_name=None, include_calling=False, src="<ode>"):
    """Extract Ode specification text from a parsed unified `.ode` file.

    - If `fn_name` is given: emits `spec_defs` + ONLY `fn_name`'s contract (used by `ode canon`).
    - If `fn_name` is None: emits `spec_defs` + contracts for every `fn` that has an implementation
      for `target_key` (or every `fn` if `target_key` is None), used by `statement.py`/`prove.py`.
    - When `include_calling=False` (for `.ocl` canonicalization): `calling { ... }` is NEVER emitted.
    """
    blocks = list(parsed["spec_defs"])
    if fn_name is not None:
        if fn_name not in parsed["fns_by_name"]:
            # Also allow lookup by linker symbol
            matches = [f for f in parsed["fns"] if f["symbol"] == fn_name]
            if not matches:
                raise UnifiedErr(f"{src}: function `{fn_name}` not found (have: {', '.join(f['name'] for f in parsed['fns'])})")
            fn_rec = matches[0]
        else:
            fn_rec = parsed["fns_by_name"][fn_name]
        impl = _select_impl(fn_rec, target_key, src)
        if target_key is not None and fn_rec["impls"] and impl is None:
            raise UnifiedErr(
                f"{src}: `fn {fn_rec['name']}` has no implementation for target `{target_key}` "
                f"(have: {', '.join(fn_rec['impls'])})"
            )
        ctext = _contract_text_for(fn_rec, impl, include_calling=include_calling)
        blocks.append(ctext)
        full = "\n\n".join(blocks) + "\n"
        # Validate via kcheck/ode.py immediately so contract errors report cleanly
        ode.Spec(full)
        return full, fn_rec["symbol"]

    for fn_rec in parsed["fns"]:
        impl = _select_impl(fn_rec, target_key, src)
        if target_key is not None and fn_rec["impls"] and impl is None:
            continue
        blocks.append(_contract_text_for(fn_rec, impl, include_calling=include_calling))
    full = "\n\n".join(blocks) + "\n"
    ode.Spec(full)
    return full, None


def target_source_view(parsed, target_key, src="<ode>"):
    """Return `(arch, data_list, inline_blocks, fns_list)` for `target_key`, ready for `odec`."""
    base_arch = target_key.split(":", 1)[0] if target_key else None
    if base_arch is None:
        arches = sorted({im["arch"] for f in parsed["fns"] for im in f["impls"].values()})
        if len(arches) != 1:
            raise UnifiedErr(
                f"{src}: source implements multiple architectures ({', '.join(arches)}); pass `--target`"
            )
        base_arch = arches[0]
        target_key = base_arch

    if base_arch not in TARGETS:
        raise UnifiedErr(f"{src}: unsupported target `{base_arch}`")

    data_out = [(nm, words) for darch, nm, words in parsed["data"] if darch is None or darch == base_arch]
    inlines_out = [(raw, lno) for iarch, raw, lno in parsed["inlines"] if iarch is None or iarch == base_arch]
    fns_out = []
    for fn_rec in parsed["fns"]:
        impl = _select_impl(fn_rec, target_key, src)
        if impl is None:
            continue
        fns_out.append((fn_rec["name"], fn_rec["symbol"], impl["lines"], impl["first_line"]))
    if not fns_out:
        raise UnifiedErr(f"{src}: no `fn` implementation found for target `{target_key}`")
    return base_arch, data_out, inlines_out, fns_out
