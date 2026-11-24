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
        elif re.match(r"^(const|def|sequence|layout|kind|lemma)\b", line):
            has_spec_def = True
        elif re.match(r"^contract\b", line):
            has_contract = True
    if has_legacy_fn and not has_unified_fn and not has_spec_def:
        return False
    return has_unified_fn or (has_spec_def and not has_contract)


def _parse_for_blocks(body_text, fn_name, body_start_line, src):
    """Parse zero or more `for <arch>[:variant] [needs ...] [stack ...] [calling { ... }] { asm }` blocks."""
    impls = {}
    pos = _skip_ws_and_comments(body_text, 0)
    n = len(body_text)
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
        }
        pos = _skip_ws_and_comments(body_text, bclose + 1)
    return impls


def parse_unified(text, src="<ode>"):
    """Parse a unified `.ode` source file (closed local namespace).

    Returns a dict:
      - `spec_defs`: list of raw top-level `const`/`def`/`sequence`/`layout`/`kind`/`lemma` blocks
      - `data`: list of `(arch_or_None, name, [words])`
      - `inlines`: list of `(arch_or_None, raw_inline_text, start_line)`
      - `fns`: list of function dicts in source order:
          {name, symbol, params_text, clauses_text, line, impls: {key: impl_dict}}
      - `fns_by_name`: {name: fn_dict}
    """
    spec_defs = []
    data = []
    inlines = []
    fns = []
    fns_by_name = {}
    declared_names = {}

    def claim(kind_lbl, name, line_no):
        if name in declared_names:
            prev_kind, prev_line = declared_names[name]
            raise UnifiedErr(
                f"{src}: line {line_no}: duplicate name `{name}` ({kind_lbl}); already declared as {prev_kind} on line {prev_line}"
            )
        declared_names[name] = (kind_lbl, line_no)

    pos = _skip_ws_and_comments(text, 0)
    n = len(text)
    while pos < n:
        line_no = text.count("\n", 0, pos) + 1
        rest = text[pos:]

        # 1. `def`, `sequence`, `layout` (brace-delimited spec blocks)
        m = re.match(r"^(def|sequence|layout)\s+([A-Za-z_]\w*)\b", rest)
        if m:
            claim(m.group(1), m.group(2), line_no)
            bopen = _find_open_brace(text, pos + m.end())
            if bopen == -1:
                raise UnifiedErr(f"{src}: line {line_no}: `{m.group(1)} {m.group(2)}` missing `{{`")
            bclose = _find_matching_brace(text, bopen, src)
            spec_defs.append(text[pos:bclose + 1])
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
            spec_defs.append(text[pos:i].strip())
            pos = _skip_ws_and_comments(text, i)
            continue

        # 3. `kind NAME: ...` or `lemma ...`
        m = re.match(r"^(kind|lemma)\s+([A-Za-z_]\w*)\b", rest)
        if m:
            nl = text.find("\n", pos)
            end = n if nl == -1 else nl
            spec_defs.append(_strip_line_comment(text[pos:end]).strip())
            pos = _skip_ws_and_comments(text, end)
            continue

        # 4. `data [for ARCH] NAME = w0, w1, ...`
        m = re.match(r"^data\s+(?:for\s+(\w+)\s+)?([A-Za-z_]\w*)\s*=\s*([^\n]*)", rest)
        if m:
            darch = m.group(1)
            if darch is not None and darch not in TARGETS:
                raise UnifiedErr(f"{src}: line {line_no}: unsupported `data for {darch}`")
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
            bopen = _find_open_brace(text, pos + m.end())
            if bopen == -1:
                raise UnifiedErr(f"{src}: line {line_no}: `inline fn {m.group(1)}` missing `{{`")
            bclose = _find_matching_brace(text, bopen, src)
            # Rewrite `inline fn NAME for ARCH (` -> `inline fn NAME (` for odec.inline_of
            raw_hdr = text[pos:bopen]
            if iarch is not None:
                raw_hdr = re.sub(r"^(inline\s+fn\s+[A-Za-z_]\w*)\s+for\s+\w+", r"\1", raw_hdr, count=1)
            inlines.append((iarch, raw_hdr + text[bopen:bclose + 1], line_no))
            pos = _skip_ws_and_comments(text, bclose + 1)
            continue

        # 6. `fn NAME [as "SYM"] (args...) <contract clauses> { for <arch> ... }`
        m = re.match(r'^fn\s+([A-Za-z_]\w*)(?:\s+as\s+"([^"]+)")?', rest)
        if m:
            fname = m.group(1)
            fsym = m.group(2) or fname
            claim("fn", fname, line_no)
            after_name = _skip_ws_and_comments(text, pos + m.end())
            if after_name >= n or text[after_name] != "(":
                raise UnifiedErr(
                    f"{src}: line {line_no}: `fn {fname}` has no parameter list and contract; "
                    f"every Ode `fn` must declare parameters and a contract: `fn {fname}(...) requires/returns/ensures ... stack N {{ ... }}`"
                )
            pclose = _find_matching_paren(text, after_name, src)
            params_text = text[after_name + 1:pclose].strip()
            bopen = _find_open_brace(text, pclose + 1)
            if bopen == -1:
                raise UnifiedErr(f"{src}: line {line_no}: `fn {fname}` missing `{{`")
            clauses_text = text[pclose + 1:bopen].strip()
            bclose = _find_matching_brace(text, bopen, src)
            body_start_line = text.count("\n", 0, bopen + 1) + 1
            body_text = text[bopen + 1:bclose]
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
        "spec_defs": spec_defs,
        "data": data,
        "inlines": inlines,
        "fns": fns,
        "fns_by_name": fns_by_name,
    }


def _select_impl(fn_rec, target_key, src="<ode>"):
    """Select the `for <arch>[:variant]` block matching `target_key` (or None if contract-only)."""
    impls = fn_rec["impls"]
    if not impls:
        return None
    if target_key is None:
        if len(impls) == 1:
            return next(iter(impls.values()))
        raise UnifiedErr(
            f"{src}: `fn {fn_rec['name']}` has multiple targets ({', '.join(impls)}); specify `--target`"
        )
    if target_key in impls:
        return impls[target_key]
    # If `target_key` has a variant like `x86_64:avx512`, fall back to base `x86_64` for helpers without that variant
    base = target_key.split(":", 1)[0]
    if base in impls:
        return impls[base]
    return None


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
