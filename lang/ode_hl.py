#!/usr/bin/env python3
"""High-Level Ode: Minimal Wirth-Style Structured Language and Deterministic 1-to-1 Lowering.

Compiles structured High-Level Ode function bodies (portable `{ ... }` or target-specialized
`for x86_64 { ... }` / `for arm64 { ... }`) deterministically 1-to-1 into exact `odec` assembly
lines targeting `core/x86.tab` and `arm64/arm64.tab`, together with:
  - Automatic `place { ... }` loop invariants inheriting dominating outer facts (`W1`)
  - Explicit exact (`+`, `-`, `*`) vs wrapping (`+%`, `-%`, `*%`) arithmetic emitting `wrap`
  - First-class branchless `select(cond, a, b)` lowering to `cmov*` / `csel` (`W3`)
  - Deterministic register placement, callee-save prologue/epilogue, and tail calls (`W4`)
  - Target typed SIMD ops (`u32x4`, `u32x16`) in exact written statement order (`W5`)
  - Full `var -> reg / spill` + line-by-line lowering metadata for instant `< 50 ms` `ode advise --asm`

This compiler is relied on for nothing in Bob's reliance set: it outputs ordinary ELF machine code
and proof hints, and Bob verifies only the compiled `.o` bytes via `odeverify` or `verify2.py`.
"""
import re
from dataclasses import dataclass, field


class HLErr(ValueError):
    pass


# ---------------------------------------------------------------------------
# Detection: distinguish High-Level Ode blocks from raw-assembly blocks
# ---------------------------------------------------------------------------

_RAW_ASM_RE = re.compile(
    r"^(?:"
    r"@[A-Za-z_]\w*:|"
    r"reg\s+\w+\s*=|"
    r"frame\s*\{|"
    r"place\s*(?:\"[^\"]*\"\s*)?\{|"
    r"ret\b|"
    r"(?:mov|movzx|lea|cmp|cmov[a-z]+|push|pop|call|jmp|je|jne|jb|jbe|ja|jae|jl|jle|jg|jge|"
    r"ldrb|ldrh|ldr|strb|strh|str|csel|bl|b(?:\.[a-z]+)?|ld1|st1|eor|orr|ushr|rev32|ext|"
    r"vmov[a-z0-9]*|vp[a-z0-9]+|pshuf[a-z]+|pblend[a-z]+|padd[a-z]+|pxor|pand|por|psll[a-z]+|psrl[a-z]+|"
    r"vzeroupper|add|sub|and|or|xor|shl|shr|lsl|lsr|mul|imul)\s+"
    r")"
)

_HL_START_RE = re.compile(
    r"^(?:let\s+|var\s+|buf\s+|while\s+|return(?:\s|$)|for\s+[A-Za-z_]\w*\s+in\s+|join(?:\s|$))"
)

_RAW_IF_CONDS = frozenset({
    "eq", "ne", "lt", "le", "gt", "ge", "lo", "ls", "hi", "hs",
    "ult", "ule", "ugt", "uge", "z", "nz", "b", "be", "a", "ae",
})


def is_hl_body(lines):
    """Return True if `lines` is a High-Level Ode block rather than raw assembly."""
    saw_hl = False
    for raw in lines:
        s = raw.split("//", 1)[0].strip()
        if not s or s in ("{", "}", "break", "continue"):
            continue
        if _RAW_ASM_RE.match(s):
            return False
        if _HL_START_RE.match(s):
            saw_hl = True
            continue
        if s.startswith("if "):
            m = re.fullmatch(r"if\s+([A-Za-z_]\w*)\s*\{", s)
            if m and m.group(1) in _RAW_IF_CONDS:
                return False
            saw_hl = True
            continue
        if any(op in s for op in ("+=", "-=", "+%=", "-%=", "&=", "|=", "^=", "<<=", ">>=", "select(", ".u16(", ".u32(", ".u64(", ".u32x4(", ".u32x16(")):
            saw_hl = True
    return saw_hl


# ---------------------------------------------------------------------------
# Tokenizer
# ---------------------------------------------------------------------------

_KEYWORDS = frozenset({
    "let", "var", "if", "else", "while", "for",
    "break", "continue", "return", "select", "u64", "u8", "u32x4", "u32x16",
})

_TWO_THREE_OPS = (
    "+%=", "-%=", "<<=", ">>=", "+=", "-=", "&=", "|=", "^=", ":=",
    "+%", "-%", "*%", "==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "..",
)


@dataclass
class Tok:
    kind: str    # "id", "num", "op", "kw", "eof"
    val: str
    line: int


def tokenize_hl(lines, first_line, src):
    """Tokenize High-Level Ode lines while preserving exact 1-based source line numbers."""
    toks = []
    for idx, raw in enumerate(lines):
        lno = first_line + idx
        s = raw.split("//", 1)[0]
        i = 0
        n = len(s)
        while i < n:
            ch = s[i]
            if ch.isspace():
                i += 1
                continue
            if ch == "\n":
                i += 1
                continue
            if ch.isdigit():
                j = i
                if s[i:i + 2] in ("0x", "0X"):
                    j += 2
                    while j < n and (s[j] in "0123456789abcdefABCDEF_"):
                        j += 1
                else:
                    while j < n and (s[j].isdigit() or s[j] == "_"):
                        j += 1
                toks.append(Tok("num", s[i:j].replace("_", ""), lno))
                i = j
                continue
            if ch.isalpha() or ch == "_":
                j = i + 1
                while j < n and (s[j].isalnum() or s[j] == "_"):
                    j += 1
                word = s[i:j]
                toks.append(Tok("kw" if word in _KEYWORDS else "id", word, lno))
                i = j
                continue
            matched = None
            for op in _TWO_THREE_OPS:
                if s.startswith(op, i):
                    matched = op
                    break
            if matched is not None:
                toks.append(Tok("op", matched, lno))
                i += len(matched)
                continue
            if ch in "+-*&|^!<>()[]{}:;=,.":
                toks.append(Tok("op", ch, lno))
                i += 1
                continue
            raise HLErr(f"{src}: line {lno}: unexpected character {ch!r}")
    toks.append(Tok("eof", "", first_line + len(lines)))
    return toks


# ---------------------------------------------------------------------------
# AST Nodes
# ---------------------------------------------------------------------------

@dataclass
class RawReg:
    reg: str
    line: int


def _replace_reg_var_expr(e, var_loc, old_reg, new_reg):
    if isinstance(e, Var) and var_loc.get(e.name) == ("reg", old_reg):
        return RawReg(new_reg, e.line)
    if isinstance(e, IndexLoad):
        return IndexLoad(e.buf, _replace_reg_var_expr(e.idx, var_loc, old_reg, new_reg), e.width, e.line)
    if isinstance(e, BinOp):
        return BinOp(e.op, _replace_reg_var_expr(e.left, var_loc, old_reg, new_reg), _replace_reg_var_expr(e.right, var_loc, old_reg, new_reg), e.line)
    if isinstance(e, Select):
        return Select(e.cond, _replace_reg_var_expr(e.then_e, var_loc, old_reg, new_reg), _replace_reg_var_expr(e.else_e, var_loc, old_reg, new_reg), e.line)
    return e


@dataclass
class Num:
    val: int
    line: int

@dataclass
class Var:
    name: str
    line: int

@dataclass
class IndexLoad:
    buf: str
    idx: object
    width: str   # "u8", "u16", "u32", "u64", "u32x4", "u32x16"
    line: int

@dataclass
class BinOp:
    op: str      # +, -, *, +%, -%, *%, &, |, ^, <<, >>
    left: object
    right: object
    line: int

@dataclass
class Cmp:
    op: str      # ==, !=, <, <=, >, >=
    left: object
    right: object
    line: int

@dataclass
class BoolOp:
    op: str      # &&, ||
    left: object
    right: object
    line: int

@dataclass
class NotOp:
    expr: object
    line: int

@dataclass
class Select:
    cond: object
    then_e: object
    else_e: object
    line: int

@dataclass
class Call:
    name: str
    args: list
    line: int

@dataclass
class LetStmt:
    name: str
    ty: str      # "u64", "u8", "u32x4", "u32x16", or None
    expr: object
    mutable: bool
    line: int

@dataclass
class BufStmt:
    name: str
    size: int
    align: int
    line: int

@dataclass
class AssignStmt:
    target: str
    op: str      # :=, +=, -=, +%=, -%=, &=, |=, ^=, <<=, >>=
    expr: object
    line: int

@dataclass
class StoreStmt:
    buf: str
    idx: object
    width: str   # "u8", "u32", "u64", "u32x4", "u32x16"
    expr: object
    line: int

@dataclass
class IfStmt:
    cond: object
    then_body: list
    else_body: list
    line: int

@dataclass
class WhileStmt:
    cond: object
    maintains: list   # list of raw spec strings
    writes: list      # list of (buf, mode, idx_str, rhs_str)
    decreases: str    # raw spec string or None
    body: list
    line: int

@dataclass
class ForStmt:
    var: str
    lo: object
    hi: object
    step: int
    unroll: bool
    maintains: list
    writes: list
    decreases: str
    body: list
    line: int

@dataclass
class ReturnStmt:
    expr: object      # may be None
    line: int

@dataclass
class BreakStmt:
    line: int

@dataclass
class ContinueStmt:
    line: int

@dataclass
class JoinStmt:
    facts: list
    line: int

@dataclass
class ExprStmt:
    expr: object      # e.g. store_u32x4(out, off, v) or helper(...)
    line: int


# ---------------------------------------------------------------------------
# Recursive-Descent Parser
# ---------------------------------------------------------------------------

class HLParser:
    def __init__(self, lines, first_line, src):
        self.lines = lines
        self.first_line = first_line
        self.src = src
        self.toks = tokenize_hl(lines, first_line, src)
        self.i = 0

    def cur(self):
        return self.toks[self.i]

    def peek(self, val=None, kind=None):
        t = self.toks[self.i]
        if kind is not None and t.kind != kind:
            return False
        if val is not None and t.val != val:
            return False
        return True

    def take(self, val=None, kind=None):
        t = self.toks[self.i]
        if (kind is not None and t.kind != kind) or (val is not None and t.val != val):
            want = val or kind
            raise HLErr(f"{self.src}: line {t.line}: expected {want!r}, got {t.val or t.kind!r}")
        self.i += 1
        return t

    def maybe(self, val):
        if self.toks[self.i].val == val:
            self.i += 1
            return True
        return False

    def _raw_spec_until(self, stop_words, stop_on_stmt=False):
        """Capture a raw Ode specification expression up to a clause/brace/comma/semicolon or next statement."""
        parts = []
        pdepth = 0
        bdepth = 0
        start_line = self.cur().line
        prev_line = start_line
        stmt_kws = {"let", "var", "buf", "if", "while", "for", "return", "break", "continue", "join", "}"}
        while not self.peek(kind="eof"):
            t = self.cur()
            if pdepth == 0 and bdepth == 0:
                if t.val in ("{", "}"):
                    break
                if t.val in stop_words and parts:
                    break
                if t.val == "," and "COMMA" in stop_words:
                    break
                if t.val == ";" and "SEMI" in stop_words:
                    break
                if stop_on_stmt and parts and t.line > prev_line and (t.val in stmt_kws or t.kind == "id"):
                    break
            if t.val == "(":
                pdepth += 1
            elif t.val == ")":
                pdepth = max(0, pdepth - 1)
            elif t.val == "[":
                bdepth += 1
            elif t.val == "]":
                bdepth = max(0, bdepth - 1)
            parts.append(t.val)
            prev_line = t.line
            self.i += 1
        if not parts:
            raise HLErr(f"{self.src}: line {start_line}: expected specification expression")
        return _join_spec_tokens(parts)

    def parse_block_stmts(self, until_brace=False):
        stmts = []
        while not self.peek(kind="eof"):
            if until_brace and self.peek("}"):
                break
            if self.maybe(";"):
                continue
            stmts.append(self.parse_stmt())
            self.maybe(";")
        return stmts

    def parse_block(self):
        self.take("{")
        stmts = self.parse_block_stmts(until_brace=True)
        self.take("}")
        return stmts

    def parse_loop_clauses(self):
        maintains = []
        writes = []
        decreases = None
        stop = {"maintains", "writes", "decreases"}
        while self.cur().val in stop:
            kw = self.take().val
            if kw == "maintains":
                while True:
                    expr = self._raw_spec_until(stop | {"COMMA"})
                    maintains.append(expr)
                    if not self.maybe(","):
                        break
            elif kw == "decreases":
                decreases = self._raw_spec_until(stop)
            elif kw == "writes":
                buf_nm = self.take(kind="id").val
                self.take("[")
                if self.maybe(".."):
                    idx_s = self._raw_spec_until({"BRANCH_END", "]"})
                    self.take("]")
                    self.take("=")
                    rhs_s = self._raw_spec_until(stop)
                    writes.append((buf_nm, "prefix", idx_s, rhs_s))
                else:
                    idx_s = self._raw_spec_until({".."})
                    self.take("..")
                    self.take("]")
                    self.take("=")
                    rhs_s = self._raw_spec_until(stop)
                    writes.append((buf_nm, "suffix", idx_s, rhs_s))
        return maintains, writes, decreases

    def parse_stmt(self):
        t = self.cur()
        if t.val in ("let", "var"):
            mutable = (t.val == "var")
            self.i += 1
            nm = self.take(kind="id").val
            ty = None
            if self.maybe(":"):
                ty = self.take().val
                if ty not in ("u64", "u8", "u32x4", "u32x16"):
                    raise HLErr(f"{self.src}: line {t.line}: unknown type `{ty}` (expected u64, u8, u32x4, u32x16)")
            if mutable:
                self.take(":=")
            else:
                if not (self.maybe(":=") or self.maybe("=")):
                    raise HLErr(f"{self.src}: line {self.cur().line}: expected `:=` or `=` after `let {nm}`")
            expr = self.parse_expr()
            return LetStmt(nm, ty, expr, mutable, t.line)

        if t.val == "buf" and self.toks[self.i + 1].kind == "id" and self.toks[self.i + 2].val == "[":
            self.i += 1
            nm = self.take(kind="id").val
            self.take("[")
            sz = int(self.take(kind="num").val, 0)
            self.take("]")
            align = 16
            if self.maybe("align"):
                align = int(self.take(kind="num").val, 0)
            return BufStmt(nm, sz, align, t.line)

        if t.val == "if":
            self.i += 1
            cond = self.parse_cond()
            then_b = self.parse_block()
            else_b = []
            if self.maybe("else"):
                if self.peek("if"):
                    else_b = [self.parse_stmt()]
                else:
                    else_b = self.parse_block()
            return IfStmt(cond, then_b, else_b, t.line)

        if t.val == "while":
            self.i += 1
            cond = self.parse_cond()
            maintains, writes, decreases = self.parse_loop_clauses()
            body = self.parse_block()
            return WhileStmt(cond, maintains, writes, decreases, body, t.line)

        if t.val == "for":
            self.i += 1
            vname = self.take(kind="id").val
            self.take("in")
            lo = self.parse_expr()
            self.take("..")
            hi = self.parse_expr()
            step = 1
            unroll = False
            if self.maybe("step"):
                step = int(self.take(kind="num").val, 0)
                if step <= 0:
                    raise HLErr(f"{self.src}: line {t.line}: `step` must be positive")
            if self.maybe("unroll"):
                unroll = True
            maintains, writes, decreases = self.parse_loop_clauses()
            body = self.parse_block()
            return ForStmt(vname, lo, hi, step, unroll, maintains, writes, decreases, body, t.line)

        if t.val == "return":
            self.i += 1
            if self.peek("}") or self.peek(";") or self.peek(kind="eof"):
                return ReturnStmt(None, t.line)
            return ReturnStmt(self.parse_expr(), t.line)

        if t.val == "break":
            self.i += 1
            return BreakStmt(t.line)

        if t.val == "continue":
            self.i += 1
            return ContinueStmt(t.line)

        if t.val == "join":
            self.i += 1
            facts = []
            while self.peek("maintains"):
                self.i += 1
                while True:
                    facts.append(self._raw_spec_until({"maintains", "COMMA", "SEMI"}, stop_on_stmt=True))
                    if not self.maybe(","):
                        break
            return JoinStmt(facts, t.line)

        # Assignment, store, or call statement
        if t.kind == "id":
            nxt = self.toks[self.i + 1]
            # 1. `out[idx] := expr`
            if nxt.val == "[":
                nm = self.take(kind="id").val
                self.take("[")
                idx_e = self.parse_expr()
                self.take("]")
                self.take(":=")
                val_e = self.parse_expr()
                return StoreStmt(nm, idx_e, "u8", val_e, t.line)
            # 2. `out.u32x4(idx) := expr` / `out.u32x16(idx) := expr` / `out.u32(idx) := expr` / `out.u64(idx) := expr`
            if nxt.val == "." and self.i + 2 < len(self.toks) and self.toks[self.i + 2].val in ("u32", "u64", "u32x4", "u32x16"):
                save = self.i
                nm = self.take(kind="id").val
                self.take(".")
                w = self.take().val
                self.take("(")
                idx_e = self.parse_expr()
                self.take(")")
                if self.maybe(":="):
                    val_e = self.parse_expr()
                    return StoreStmt(nm, idx_e, w, val_e, t.line)
                self.i = save
            # 3. `x op= expr`
            if nxt.val in (":=", "+=", "-=", "+%=", "-%=", "&=", "|=", "^=", "<<=", ">>="):
                nm = self.take(kind="id").val
                op = self.take().val
                val_e = self.parse_expr()
                return AssignStmt(nm, op, val_e, t.line)
            # 4. Bare function/intrinsic call statement
            expr = self.parse_expr()
            if isinstance(expr, Call):
                return ExprStmt(expr, t.line)
            raise HLErr(f"{self.src}: line {t.line}: expected assignment or call statement")

        raise HLErr(f"{self.src}: line {t.line}: unexpected token {t.val!r} at start of statement")

    # -- Boolean conditions --
    def parse_cond(self):
        return self._parse_or_cond()

    def _parse_or_cond(self):
        left = self._parse_and_cond()
        while self.maybe("||"):
            ln = self.toks[self.i - 1].line
            left = BoolOp("||", left, self._parse_and_cond(), ln)
        return left

    def _parse_and_cond(self):
        left = self._parse_atom_cond()
        while self.maybe("&&"):
            ln = self.toks[self.i - 1].line
            left = BoolOp("&&", left, self._parse_atom_cond(), ln)
        return left

    def _parse_atom_cond(self):
        t = self.cur()
        if self.maybe("!"):
            return NotOp(self._parse_atom_cond(), t.line)
        if self.peek("("):
            # Disambiguate `(cond)` vs `(expr) < expr` by speculative parse
            save = self.i
            self.i += 1
            try:
                c = self.parse_cond()
                self.take(")")
                if self.cur().val not in ("+", "-", "*", "+%", "-%", "*%", "&", "|", "^", "<<", ">>", "==", "!=", "<", "<=", ">", ">="):
                    return c
            except HLErr:
                pass
            self.i = save
        left = self.parse_expr()
        op_t = self.cur()
        if op_t.val not in ("==", "!=", "<", "<=", ">", ">="):
            raise HLErr(f"{self.src}: line {op_t.line}: expected comparison operator (==, !=, <, <=, >, >=), got {op_t.val!r}")
        self.i += 1
        right = self.parse_expr()
        return Cmp(op_t.val, left, right, op_t.line)

    # -- Expressions --
    def parse_expr(self):
        return self._parse_bitor()

    def _parse_bitor(self):
        e = self._parse_bitxor()
        while self.maybe("|"):
            e = BinOp("|", e, self._parse_bitxor(), self.toks[self.i - 1].line)
        return e

    def _parse_bitxor(self):
        e = self._parse_bitand()
        while self.maybe("^"):
            e = BinOp("^", e, self._parse_bitand(), self.toks[self.i - 1].line)
        return e

    def _parse_bitand(self):
        e = self._parse_shift()
        while self.maybe("&"):
            e = BinOp("&", e, self._parse_shift(), self.toks[self.i - 1].line)
        return e

    def _parse_shift(self):
        e = self._parse_add()
        while self.cur().val in ("<<", ">>"):
            op = self.take()
            e = BinOp(op.val, e, self._parse_add(), op.line)
        return e

    def _parse_add(self):
        e = self._parse_mul()
        while self.cur().val in ("+", "-", "+%", "-%"):
            op = self.take()
            e = BinOp(op.val, e, self._parse_mul(), op.line)
        return e

    def _parse_mul(self):
        e = self._parse_atom()
        while self.cur().val in ("*", "*%"):
            op = self.take()
            e = BinOp(op.val, e, self._parse_atom(), op.line)
        return e

    def _parse_atom(self):
        t = self.cur()
        if t.kind == "num":
            self.i += 1
            return Num(int(t.val, 0), t.line)
        if t.val == "-":
            self.i += 1
            nt = self.take(kind="num")
            return Num(-int(nt.val, 0), t.line)
        if t.val == "(":
            self.i += 1
            e = self.parse_expr()
            self.take(")")
            return e
        if t.val == "select":
            self.i += 1
            self.take("(")
            cond = self.parse_cond()
            self.take(",")
            te = self.parse_expr()
            self.take(",")
            fe = self.parse_expr()
            self.take(")")
            return Select(cond, te, fe, t.line)
        if t.kind == "id":
            self.i += 1
            nm = t.val
            # Qualified call `alias.fn(...)` or typed load `buf.u32(i)`
            if self.maybe("."):
                mem = self.take().val
                if mem in ("u16", "u32", "u64", "u32x4", "u32x16") and self.peek("("):
                    self.take("(")
                    idx_e = self.parse_expr()
                    self.take(")")
                    return IndexLoad(nm, idx_e, mem, t.line)
                nm = f"{nm}.{mem}"
            if self.maybe("["):
                idx_e = self.parse_expr()
                self.take("]")
                return IndexLoad(nm, idx_e, "u8", t.line)
            if self.maybe("("):
                args = []
                if not self.peek(")"):
                    while True:
                        args.append(self.parse_expr())
                        if not self.maybe(","):
                            break
                self.take(")")
                return Call(nm, args, t.line)
            return Var(nm, t.line)
        raise HLErr(f"{self.src}: line {t.line}: unexpected token {t.val or t.kind!r} in expression")


def _join_spec_tokens(parts):
    """Reconstruct readable Ode specification text from raw tokens."""
    out = []
    no_space_before = {")", "]", ",", "."}
    no_space_after = {"(", "[", "."}
    for tok in parts:
        if not out:
            out.append(tok)
            continue
        prev = out[-1].strip()
        last_ch = prev[-1] if prev else ""
        if tok in no_space_before or last_ch in no_space_after:
            out.append(tok)
        elif tok == "(" and (last_ch.isalnum() or last_ch == "_"):
            out.append(tok)
        elif tok == "[" and (last_ch.isalnum() or last_ch == "_" or last_ch == ")"):
            out.append(tok)
        else:
            out.append(" " + tok)
    return "".join(out)


# ---------------------------------------------------------------------------
# AST Helpers: Compile-time Unrolling, Variable/Call/Write-Set Analysis
# ---------------------------------------------------------------------------

def _subst_expr(e, vname, kval):
    if isinstance(e, Var) and e.name == vname:
        return Num(kval, e.line)
    if isinstance(e, IndexLoad):
        return IndexLoad(e.buf, _subst_expr(e.idx, vname, kval), e.width, e.line)
    if isinstance(e, BinOp):
        l = _subst_expr(e.left, vname, kval)
        r = _subst_expr(e.right, vname, kval)
        if isinstance(l, Num) and isinstance(r, Num):
            val = _const_eval_binop(e.op, l.val, r.val)
            if val is not None:
                return Num(val, e.line)
        return BinOp(e.op, l, r, e.line)
    if isinstance(e, Cmp):
        return Cmp(e.op, _subst_expr(e.left, vname, kval), _subst_expr(e.right, vname, kval), e.line)
    if isinstance(e, BoolOp):
        return BoolOp(e.op, _subst_expr(e.left, vname, kval), _subst_expr(e.right, vname, kval), e.line)
    if isinstance(e, NotOp):
        return NotOp(_subst_expr(e.expr, vname, kval), e.line)
    if isinstance(e, Select):
        return Select(_subst_expr(e.cond, vname, kval), _subst_expr(e.then_e, vname, kval), _subst_expr(e.else_e, vname, kval), e.line)
    if isinstance(e, Call):
        return Call(e.name, [_subst_expr(a, vname, kval) for a in e.args], e.line)
    return e


def _const_eval_binop(op, a, b):
    M64 = (1 << 64) - 1
    if op == "+": return a + b
    if op == "-": return a - b
    if op == "*": return a * b
    if op == "+%": return (a + b) & M64
    if op == "-%": return (a - b) & M64
    if op == "*%": return (a * b) & M64
    if op == "&": return a & b
    if op == "|": return a | b
    if op == "^": return a ^ b
    if op == "<<" and 0 <= b < 64: return a << b
    if op == ">>" and 0 <= b < 64: return a >> b
    return None


def _subst_stmts(stmts, vname, kval):
    out = []
    for st in stmts:
        if isinstance(st, LetStmt):
            out.append(LetStmt(st.name, st.ty, _subst_expr(st.expr, vname, kval), st.mutable, st.line))
        elif isinstance(st, AssignStmt):
            out.append(AssignStmt(st.target, st.op, _subst_expr(st.expr, vname, kval), st.line))
        elif isinstance(st, StoreStmt):
            out.append(StoreStmt(st.buf, _subst_expr(st.idx, vname, kval), st.width, _subst_expr(st.expr, vname, kval), st.line))
        elif isinstance(st, IfStmt):
            out.append(IfStmt(_subst_expr(st.cond, vname, kval), _subst_stmts(st.then_body, vname, kval), _subst_stmts(st.else_body, vname, kval), st.line))
        elif isinstance(st, WhileStmt):
            out.append(WhileStmt(_subst_expr(st.cond, vname, kval), st.maintains, st.writes, st.decreases, _subst_stmts(st.body, vname, kval), st.line))
        elif isinstance(st, ForStmt):
            out.append(ForStmt(st.var, _subst_expr(st.lo, vname, kval), _subst_expr(st.hi, vname, kval), st.step, st.unroll, st.maintains, st.writes, st.decreases, _subst_stmts(st.body, vname, kval), st.line))
        elif isinstance(st, ReturnStmt):
            out.append(ReturnStmt(_subst_expr(st.expr, vname, kval) if st.expr is not None else None, st.line))
        elif isinstance(st, ExprStmt):
            out.append(ExprStmt(_subst_expr(st.expr, vname, kval), st.line))
        else:
            out.append(st)
    return out


def _alpha_rename_blocks(stmts, param_names):
    """Give block-local `let`/`var` declarations that shadow or reuse a name in disjoint blocks
    distinct internal names (`name$k`) so linear-scan live ranges never bleed across disjoint scopes."""
    seen = set(param_names)
    seq = [0]

    def ren_expr(e, env):
        if isinstance(e, Var):
            return Var(env.get(e.name, e.name), e.line)
        if isinstance(e, IndexLoad):
            return IndexLoad(env.get(e.buf, e.buf), ren_expr(e.idx, env), e.width, e.line)
        if isinstance(e, BinOp):
            return BinOp(e.op, ren_expr(e.left, env), ren_expr(e.right, env), e.line)
        if isinstance(e, Cmp):
            return Cmp(e.op, ren_expr(e.left, env), ren_expr(e.right, env), e.line)
        if isinstance(e, BoolOp):
            return BoolOp(e.op, ren_expr(e.left, env), ren_expr(e.right, env), e.line)
        if isinstance(e, NotOp):
            return NotOp(ren_expr(e.expr, env), e.line)
        if isinstance(e, Select):
            return Select(ren_expr(e.cond, env), ren_expr(e.then_e, env), ren_expr(e.else_e, env), e.line)
        if isinstance(e, Call):
            return Call(e.name, [ren_expr(a, env) for a in e.args], e.line)
        return e

    def ren_spec(s, env):
        if not s:
            return s
        return re.sub(r"\b[A-Za-z_]\w*\b", lambda m: env.get(m.group(0), m.group(0)), s)

    def fresh(nm):
        if nm not in seen:
            seen.add(nm)
            return nm
        seq[0] += 1
        out = f"{nm}${seq[0]}"
        seen.add(out)
        return out

    def ren_block(body, outer_env):
        env = dict(outer_env)
        out = []
        for st in body:
            if isinstance(st, LetStmt):
                e2 = ren_expr(st.expr, env)
                nm2 = fresh(st.name)
                env[st.name] = nm2
                out.append(LetStmt(nm2, st.ty, e2, st.mutable, st.line))
            elif isinstance(st, BufStmt):
                nm2 = fresh(st.name)
                env[st.name] = nm2
                out.append(BufStmt(nm2, st.size, st.align, st.line))
            elif isinstance(st, AssignStmt):
                out.append(AssignStmt(env.get(st.target, st.target), st.op, ren_expr(st.expr, env), st.line))
            elif isinstance(st, StoreStmt):
                out.append(StoreStmt(env.get(st.buf, st.buf), ren_expr(st.idx, env), st.width, ren_expr(st.expr, env), st.line))
            elif isinstance(st, IfStmt):
                out.append(IfStmt(ren_expr(st.cond, env), ren_block(st.then_body, env), ren_block(st.else_body, env), st.line))
            elif isinstance(st, WhileStmt):
                out.append(WhileStmt(
                    ren_expr(st.cond, env),
                    [ren_spec(m, env) for m in st.maintains],
                    [(env.get(b, b), md, ren_spec(ix, env), ren_spec(rh, env)) for b, md, ix, rh in st.writes],
                    ren_spec(st.decreases, env),
                    ren_block(st.body, env),
                    st.line,
                ))
            elif isinstance(st, ForStmt):
                lo2 = ren_expr(st.lo, env)
                hi2 = ren_expr(st.hi, env)
                fenv = dict(env)
                v2 = fresh(st.var)
                fenv[st.var] = v2
                out.append(ForStmt(
                    v2, lo2, hi2, st.step, st.unroll,
                    [ren_spec(m, fenv) for m in st.maintains],
                    [(fenv.get(b, b), md, ren_spec(ix, fenv), ren_spec(rh, fenv)) for b, md, ix, rh in st.writes],
                    ren_spec(st.decreases, fenv),
                    ren_block(st.body, fenv),
                    st.line,
                ))
            elif isinstance(st, ReturnStmt):
                out.append(ReturnStmt(ren_expr(st.expr, env) if st.expr is not None else None, st.line))
            elif isinstance(st, JoinStmt):
                out.append(JoinStmt([ren_spec(f, env) for f in st.facts], st.line))
            elif isinstance(st, ExprStmt):
                out.append(ExprStmt(ren_expr(st.expr, env), st.line))
            else:
                out.append(st)
        return out

    return ren_block(stmts, {p: p for p in param_names})


def expand_unrolls(stmts, src):
    """Expand `for i in lo..hi unroll { ... }` at compile time."""
    out = []
    for st in stmts:
        if isinstance(st, ForStmt) and st.unroll:
            if not (isinstance(st.lo, Num) and isinstance(st.hi, Num)):
                raise HLErr(f"{src}: line {st.line}: `unroll` requires constant bounds")
            for k in range(st.lo.val, st.hi.val, st.step):
                out.extend(expand_unrolls(_subst_stmts(st.body, st.var, k), src))
        elif isinstance(st, IfStmt):
            out.append(IfStmt(st.cond, expand_unrolls(st.then_body, src), expand_unrolls(st.else_body, src), st.line))
        elif isinstance(st, WhileStmt):
            out.append(WhileStmt(st.cond, st.maintains, st.writes, st.decreases, expand_unrolls(st.body, src), st.line))
        elif isinstance(st, ForStmt):
            out.append(ForStmt(st.var, st.lo, st.hi, st.step, False, st.maintains, st.writes, st.decreases, expand_unrolls(st.body, src), st.line))
        else:
            out.append(st)
    return out


_INTRINSICS = frozenset({
    "load_u32x4", "store_u32x4", "load_u32x16", "store_u32x16", "broadcast_u32x16",
    "const_u32x4", "zeros_u32x16", "rotl32", "rotr32", "shl32", "shr32", "bswap32",
    "shuf32", "shuf32_pair", "shufi32x4", "unpacklo32", "unpackhi32", "unpacklo64", "unpackhi64",
    "blend32", "palignr", "ext4", "ext8", "ext12",
    "sha256rnds2", "sha256msg1", "sha256msg2", "sha256h", "sha256h2", "sha256su0", "sha256su1",
    "add_u32x16_data",
})

_VEC4_INTRINSICS = frozenset({
    "load_u32x4", "const_u32x4", "shuf32", "shuf32_pair", "blend32", "palignr",
    "ext4", "ext8", "ext12", "bswap32",
    "sha256rnds2", "sha256msg1", "sha256msg2", "sha256h", "sha256h2", "sha256su0", "sha256su1",
})

_VEC16_INTRINSICS = frozenset({
    "load_u32x16", "broadcast_u32x16", "zeros_u32x16", "shufi32x4", "add_u32x16_data",
})


def _written_vars(stmts):
    w = set()
    for st in stmts:
        if isinstance(st, LetStmt):
            w.add(st.name)
        elif isinstance(st, AssignStmt):
            w.add(st.target)
        elif isinstance(st, IfStmt):
            w |= _written_vars(st.then_body) | _written_vars(st.else_body)
        elif isinstance(st, WhileStmt):
            w |= _written_vars(st.body)
        elif isinstance(st, ForStmt):
            w.add(st.var)
            w |= _written_vars(st.body)
    return w


def _used_vars_expr(e):
    if isinstance(e, Var):
        return {e.name}
    if isinstance(e, IndexLoad):
        return {e.buf} | _used_vars_expr(e.idx)
    if isinstance(e, (BinOp, Cmp, BoolOp)):
        return _used_vars_expr(e.left) | _used_vars_expr(e.right)
    if isinstance(e, NotOp):
        return _used_vars_expr(e.expr)
    if isinstance(e, Select):
        return _used_vars_expr(e.cond) | _used_vars_expr(e.then_e) | _used_vars_expr(e.else_e)
    if isinstance(e, Call):
        u = set()
        for a in e.args:
            u |= _used_vars_expr(a)
        return u
    return set()


def _has_real_call_expr(e, fn_names):
    if isinstance(e, Call):
        if e.name not in _INTRINSICS and (fn_names is None or e.name in fn_names):
            return True
        return any(_has_real_call_expr(a, fn_names) for a in e.args)
    if isinstance(e, (BinOp, Cmp, BoolOp)):
        return _has_real_call_expr(e.left, fn_names) or _has_real_call_expr(e.right, fn_names)
    if isinstance(e, NotOp):
        return _has_real_call_expr(e.expr, fn_names)
    if isinstance(e, Select):
        return _has_real_call_expr(e.cond, fn_names) or _has_real_call_expr(e.then_e, fn_names) or _has_real_call_expr(e.else_e, fn_names)
    if isinstance(e, IndexLoad):
        return _has_real_call_expr(e.idx, fn_names)
    return False


def _expr_is_tail_call(e, fn_names, self_name=None):
    return (isinstance(e, Call) and e.name not in _INTRINSICS
            and (self_name is None or e.name != self_name)
            and (fn_names is None or e.name in fn_names)
            and not any(_has_real_call_expr(a, fn_names) for a in e.args))


def _analyze_calls_and_vars(stmts, param_names, fn_names, self_name=None):
    """Collect declared locals, inferred types, buffers, whether non-tail calls occur, and vars live across calls."""
    locals_order = []   # [(name, ty, mutable, line)]
    local_types = {}
    bufs = []           # [(name, size, align, line)]
    has_non_tail_call = [False]
    live_across_call = set()

    def infer_ty(e):
        if isinstance(e, IndexLoad):
            if e.width in ("u32x4", "u32x16"):
                return e.width
            return "u8" if e.width == "u8" else "u64"
        if isinstance(e, Var):
            return local_types.get(e.name, "u64")
        if isinstance(e, Call):
            if e.name in _VEC4_INTRINSICS:
                return "u32x4"
            if e.name in _VEC16_INTRINSICS:
                return "u32x16"
            if e.name in ("rotl32", "rotr32", "shl32", "shr32", "unpacklo32", "unpackhi32", "unpacklo64", "unpackhi64") and e.args:
                return infer_ty(e.args[0])
            return "u64"
        if isinstance(e, BinOp):
            lt = infer_ty(e.left)
            if lt in ("u32x4", "u32x16"):
                return lt
            rt = infer_ty(e.right)
            if rt in ("u32x4", "u32x16"):
                return rt
            return "u64"
        return "u64"

    def walk(body):
        for idx, st in enumerate(body):
            if isinstance(st, LetStmt):
                ty = st.ty or infer_ty(st.expr)
                if st.name not in local_types:
                    local_types[st.name] = ty
                    locals_order.append((st.name, ty, st.mutable, st.line))
                if _has_real_call_expr(st.expr, fn_names):
                    has_non_tail_call[0] = True
            elif isinstance(st, BufStmt):
                bufs.append((st.name, st.size, st.align, st.line))
                local_types[st.name] = "buf"
            elif isinstance(st, AssignStmt):
                if _has_real_call_expr(st.expr, fn_names):
                    has_non_tail_call[0] = True
            elif isinstance(st, StoreStmt):
                if _has_real_call_expr(st.idx, fn_names) or _has_real_call_expr(st.expr, fn_names):
                    has_non_tail_call[0] = True
            elif isinstance(st, IfStmt):
                if _has_real_call_expr(st.cond, fn_names):
                    has_non_tail_call[0] = True
                walk(st.then_body)
                walk(st.else_body)
            elif isinstance(st, WhileStmt):
                if _has_real_call_expr(st.cond, fn_names):
                    has_non_tail_call[0] = True
                walk(st.body)
            elif isinstance(st, ForStmt):
                if st.var not in local_types:
                    local_types[st.var] = "u64"
                    locals_order.append((st.var, "u64", True, st.line))
                if _has_real_call_expr(st.lo, fn_names) or _has_real_call_expr(st.hi, fn_names):
                    has_non_tail_call[0] = True
                walk(st.body)
            elif isinstance(st, ReturnStmt):
                if st.expr is not None and _has_real_call_expr(st.expr, fn_names):
                    if not _expr_is_tail_call(st.expr, fn_names, self_name):
                        has_non_tail_call[0] = True
            elif isinstance(st, ExprStmt):
                if _has_real_call_expr(st.expr, fn_names):
                    has_non_tail_call[0] = True

    walk(stmts)
    # Exact backward liveness across non-tail calls (2-pass loop fixed point):
    # only variables actually read AFTER a call get callee-saved registers!
    if has_non_tail_call[0]:
        def backward(body, live_out):
            live = set(live_out)
            for st in reversed(body):
                if isinstance(st, ReturnStmt):
                    if st.expr is None:
                        live = set()
                    elif _expr_is_tail_call(st.expr, fn_names, self_name):
                        live = _used_vars_expr(st.expr)
                    else:
                        live = _used_vars_expr(st.expr)
                elif isinstance(st, (BreakStmt, ContinueStmt, BufStmt, JoinStmt)):
                    pass
                elif isinstance(st, LetStmt):
                    after = live - {st.name}
                    if _has_real_call_expr(st.expr, fn_names):
                        live_across_call.update(after)
                    live = after | _used_vars_expr(st.expr)
                elif isinstance(st, AssignStmt):
                    after = (live - {st.target}) if st.op == ":=" else (live | {st.target})
                    if _has_real_call_expr(st.expr, fn_names):
                        live_across_call.update(after)
                    live = after | _used_vars_expr(st.expr)
                elif isinstance(st, StoreStmt):
                    if _has_real_call_expr(st.idx, fn_names) or _has_real_call_expr(st.expr, fn_names):
                        live_across_call.update(live | {st.buf})
                    live = live | {st.buf} | _used_vars_expr(st.idx) | _used_vars_expr(st.expr)
                elif isinstance(st, ExprStmt):
                    if _has_real_call_expr(st.expr, fn_names):
                        live_across_call.update(live)
                    live = live | _used_vars_expr(st.expr)
                elif isinstance(st, IfStmt):
                    lt = backward(st.then_body, live)
                    le = backward(st.else_body, live)
                    if _has_real_call_expr(st.cond, fn_names):
                        live_across_call.update(lt | le)
                    live = lt | le | _used_vars_expr(st.cond)
                elif isinstance(st, WhileStmt):
                    cur_in = set(live) | _used_vars_expr(st.cond)
                    for _ in range(2):
                        b_in = backward(st.body, cur_in)
                        if _has_real_call_expr(st.cond, fn_names):
                            live_across_call.update(b_in | cur_in)
                        cur_in = cur_in | b_in | _used_vars_expr(st.cond)
                    live = cur_in
                elif isinstance(st, ForStmt):
                    cur_in = set(live) | _used_vars_expr(st.hi) | {st.var}
                    for _ in range(2):
                        b_in = backward(st.body, cur_in)
                        cur_in = cur_in | b_in | _used_vars_expr(st.hi) | {st.var}
                    after_lo = cur_in - {st.var}
                    if _has_real_call_expr(st.lo, fn_names) or _has_real_call_expr(st.hi, fn_names):
                        live_across_call.update(after_lo)
                    live = after_lo | _used_vars_expr(st.lo) | _used_vars_expr(st.hi)
            return live

        backward(stmts, set())
    return locals_order, local_types, bufs, has_non_tail_call[0], live_across_call


def _stmts_always_exit(stmts):
    if not stmts:
        return False
    last = stmts[-1]
    if isinstance(last, (ReturnStmt, BreakStmt, ContinueStmt)):
        return True
    if isinstance(last, IfStmt) and last.else_body:
        return _stmts_always_exit(last.then_body) and _stmts_always_exit(last.else_body)
    return False


# ---------------------------------------------------------------------------
# Register Naming Tables
# ---------------------------------------------------------------------------

X86_ARGS = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]
X86_SCRATCH = ["r10", "r11", "rax"]          # reserved scratch (rax also return reg)
X86_CALLER_POOL = ["r9", "r8", "rcx", "rdx", "rsi", "rdi"]
X86_CALLEE_SAVED = ["rbx", "rbp", "r12", "r13", "r14", "r15"]

X86_REG32 = {
    "rax": "eax", "rcx": "ecx", "rdx": "edx", "rbx": "ebx",
    "rsp": "esp", "rbp": "ebp", "rsi": "esi", "rdi": "edi",
    "r8": "r8d", "r9": "r9d", "r10": "r10d", "r11": "r11d",
    "r12": "r12d", "r13": "r13d", "r14": "r14d", "r15": "r15d",
}
X86_REG8 = {
    "rax": "al", "rcx": "cl", "rdx": "dl", "rbx": "bl",
    "rsp": "spl", "rbp": "bpl", "rsi": "sil", "rdi": "dil",
    "r8": "r8b", "r9": "r9b", "r10": "r10b", "r11": "r11b",
    "r12": "r12b", "r13": "r13b", "r14": "r14b", "r15": "r15b",
}

ARM_ARGS = ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]
ARM_SCRATCH = ["x12", "x13", "x14", "x15"]    # 4 dedicated scratch regs
ARM_CALLER_POOL = ["x8", "x9", "x10", "x11", "x7", "x6", "x5", "x4", "x3", "x2", "x1"]
ARM_CALLEE_SAVED = ["x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28"]


def _arm_w(reg):
    assert reg.startswith("x")
    return "w" + reg[1:]


def _negate_cond(c):
    if isinstance(c, NotOp):
        return c.expr
    if isinstance(c, Cmp):
        inv = {"==": "!=", "!=": "==", "<": ">=", "<=": ">", ">": "<=", ">=": "<"}[c.op]
        return Cmp(inv, c.left, c.right, c.line)
    if isinstance(c, BoolOp):
        if c.op == "&&":
            return BoolOp("||", _negate_cond(c.left), _negate_cond(c.right), c.line)
        return BoolOp("&&", _negate_cond(c.left), _negate_cond(c.right), c.line)
    return NotOp(c, getattr(c, "line", 0))


def _extract_conjuncts(c):
    if isinstance(c, BoolOp) and c.op == "&&":
        return _extract_conjuncts(c.left) + _extract_conjuncts(c.right)
    if isinstance(c, NotOp):
        return _extract_conjuncts(_negate_cond(c.expr))
    if isinstance(c, Cmp):
        return [c]
    return []


def _pure_to_spec(e, bytes_params=()):
    """Convert a pure scalar expression (linear ops, power-of-two bitops, read-only `buf[idx]`) to `(spec_str, vars_used)`, or None."""
    if isinstance(e, Num):
        return str(e.val), set()
    if isinstance(e, Var):
        return e.name, {e.name}
    if isinstance(e, IndexLoad) and e.width == "u8" and e.buf in bytes_params:
        sub = _pure_to_spec(e.idx, bytes_params)
        if sub is not None:
            return f"{e.buf}[{sub[0]}]", ({e.buf} | sub[1])
        return None
    if isinstance(e, BinOp):
        if e.op in ("+", "-", "*"):
            l = _pure_to_spec(e.left, bytes_params)
            r = _pure_to_spec(e.right, bytes_params)
            if l is None or r is None:
                return None
            if e.op == "*" and not (isinstance(e.left, Num) or isinstance(e.right, Num)):
                return None
            return f"({l[0]} {e.op} {r[0]})", (l[1] | r[1])
        if e.op == "&" and isinstance(e.right, Num) and e.right.val > 0 and ((e.right.val + 1) & e.right.val) == 0:
            l = _pure_to_spec(e.left, bytes_params)
            if l is not None:
                return f"({l[0]} % {e.right.val + 1})", l[1]
        if e.op == ">>" and isinstance(e.right, Num) and 0 <= e.right.val < 64:
            l = _pure_to_spec(e.left, bytes_params)
            if l is not None:
                return f"({l[0]} / {1 << e.right.val})", l[1]
        if e.op == "<<" and isinstance(e.right, Num) and 0 <= e.right.val < 64:
            l = _pure_to_spec(e.left, bytes_params)
            if l is not None:
                return f"({l[0]} * {1 << e.right.val})", l[1]
    return None


def _linear_to_spec(e):
    return _pure_to_spec(e, ())


def _cmp_to_fact(c):
    """Convert a linear `Cmp` into `(fact_str, vars_used)` for `place` inheritance, or None."""
    if not isinstance(c, Cmp) or c.op == "!=":
        return None
    l = _linear_to_spec(c.left)
    r = _linear_to_spec(c.right)
    if l is None or r is None:
        return None
    ls, lv = l
    rs, rv = r
    vs = lv | rv
    if c.op == "==":
        return f"{ls} == {rs}", vs
    if c.op == "<=":
        return f"{ls} <= {rs}", vs
    if c.op == ">=":
        return f"{rs} <= {ls}", vs
    if c.op == "<":
        return f"{ls} + 1 <= {rs}", vs
    if c.op == ">":
        return f"{rs} + 1 <= {ls}", vs
    return None


# ---------------------------------------------------------------------------
# Deterministic Lowering Engine (`HLLower`)
# ---------------------------------------------------------------------------

class HLLower:
    def __init__(self, fn_name, params, arch, stmts, src, fn_names=None, data_names=None, explicit_stack=False, callee_clobbers=None, needs=()):
        self.fn_name = fn_name
        self.params = params          # [(name, kind_str)]
        self.param_names = [p[0] for p in params]
        self.param_set = set(self.param_names)
        self.arch = arch              # "x86_64" or "arm64"
        self.src = src
        self.fn_names = set(fn_names) if fn_names is not None else None
        self.data_names = set(data_names) if data_names is not None else set()
        self.explicit_stack = explicit_stack
        self.callee_clobbers = dict(callee_clobbers) if callee_clobbers else {}
        self.needs = set(needs) if needs else set()

        self.stmts = _alpha_rename_blocks(expand_unrolls(stmts, src), self.param_names)
        (self.locals_order, self.local_types, self.bufs,
         self.has_calls, self.live_across_call) = _analyze_calls_and_vars(
            self.stmts, self.param_names, self.fn_names, self_name=fn_name
        )
        # Param types (`u8` vs `u64` / `bytes`)
        self.param_types = {}
        for pname, pty in params:
            t = pty.strip()
            if "bytes" in t:
                self.param_types[pname] = "bytes"
            elif t == "u8":
                self.param_types[pname] = "u8"
            else:
                self.param_types[pname] = "u64"

        self.var_loc = {}        # name -> ("reg", reg) | ("spill", sp_offset) | ("buf", sp_offset)
        self.var_ty = {}         # name -> "u64" | "u8" | "u32x4" | "u32x16" | "bytes" | "buf"
        self.copied_params = []  # [(pname, entry_reg, saved_reg)]
        self.callee_saved = []   # list of callee-saved regs used
        self.vec_saved = []      # ARM64 callee-saved v8..v15 if any
        self.uses_zmm = False
        self.frame_bytes = 0     # local buffer + spill bytes (excluding saved regs)
        self.total_stack = 0     # exact stack budget for contract
        self.var_map = []        # [(name, role, loc_str, note)] for `ode advise --asm`

        self._allocate()

        self.out_lines = []      # [(src_line, text)]
        self.lbl_seq = 0
        self.loop_stack = []     # [(head_lbl, end_lbl, step_lbl_or_None)]
        self.active_facts = []   # [(fact_str, vars_used)]
        self.defined_vars = set(self.param_names)
        self.fn_written_vars = _written_vars(self.stmts)
        self.reg_owner = {self.var_loc[p][1]: p for p in self.param_names if self.var_loc[p][0] == "reg"}

    def _compute_interference(self):
        """Compute exact AST backward liveness and interference graph `interf[v]` for all locals.
        Two variables interfere iff one is live at a point where the other is defined/written,
        so disjoint `if/else` or early-return branches freely reuse the exact same registers!"""
        interf = {nm: set() for nm, _, _, _ in self.locals_order}
        local_set = set(interf.keys())

        def add_interf(v, live_set):
            if v not in local_set:
                return
            for u in live_set:
                if u in local_set and u != v:
                    interf[v].add(u)
                    interf[u].add(v)

        def spec_vars(s):
            if not s:
                return set()
            return {tok for tok in re.findall(r"\b[A-Za-z_]\w*(?:\$\d+)?\b", s) if tok in local_set}

        def back(body, live_out, brk_live=frozenset(), cont_live=frozenset()):
            live = set(live_out)
            for st in reversed(body):
                if isinstance(st, ReturnStmt):
                    live = (_used_vars_expr(st.expr) & local_set) if st.expr is not None else set()
                elif isinstance(st, BreakStmt):
                    live = set(brk_live)
                elif isinstance(st, ContinueStmt):
                    live = set(cont_live)
                elif isinstance(st, BufStmt):
                    pass
                elif isinstance(st, JoinStmt):
                    for f in st.facts:
                        live |= spec_vars(f)
                elif isinstance(st, LetStmt):
                    rhs_v = _used_vars_expr(st.expr) & local_set
                    add_interf(st.name, live | rhs_v)
                    live = (live - {st.name}) | rhs_v
                elif isinstance(st, AssignStmt):
                    rhs_v = _used_vars_expr(st.expr) & local_set
                    add_interf(st.target, live | rhs_v)
                    if st.op == ":=":
                        live = (live - {st.target}) | rhs_v
                    else:
                        live = live | ({st.target} & local_set) | rhs_v
                elif isinstance(st, StoreStmt):
                    live |= ((_used_vars_expr(st.idx) | _used_vars_expr(st.expr)) & local_set)
                elif isinstance(st, ExprStmt):
                    live |= (_used_vars_expr(st.expr) & local_set)
                elif isinstance(st, IfStmt):
                    lt = back(st.then_body, live, brk_live, cont_live)
                    le = back(st.else_body, live, brk_live, cont_live) if st.else_body else set(live)
                    live = lt | le | (_used_vars_expr(st.cond) & local_set)
                elif isinstance(st, WhileStmt):
                    clause_v = set()
                    for m in st.maintains: clause_v |= spec_vars(m)
                    for _, _, is_, rs_ in st.writes: clause_v |= spec_vars(is_) | spec_vars(rs_)
                    clause_v |= spec_vars(st.decreases)
                    head_in = set(live) | clause_v | (_used_vars_expr(st.cond) & local_set)
                    for _ in range(3):
                        b_in = back(st.body, head_in, brk_live=live, cont_live=head_in)
                        head_in = head_in | b_in | clause_v | (_used_vars_expr(st.cond) & local_set)
                    live = head_in
                elif isinstance(st, ForStmt):
                    clause_v = set()
                    for m in st.maintains: clause_v |= spec_vars(m)
                    for _, _, is_, rs_ in st.writes: clause_v |= spec_vars(is_) | spec_vars(rs_)
                    clause_v |= spec_vars(st.decreases)
                    hi_v = _used_vars_expr(st.hi) & local_set
                    head_in = set(live) | clause_v | hi_v | ({st.var} & local_set)
                    for _ in range(3):
                        step_in = head_in | ({st.var} & local_set)
                        add_interf(st.var, head_in)
                        b_in = back(st.body, step_in, brk_live=live, cont_live=step_in)
                        head_in = head_in | b_in | clause_v | hi_v | ({st.var} & local_set)
                    add_interf(st.var, head_in)
                    live = (head_in - {st.var}) | (_used_vars_expr(st.lo) & local_set) | hi_v
            return live

        back(self.stmts, set())
        return interf

    def _allocate(self):
        arg_regs = ARM_ARGS if self.arch == "arm64" else X86_ARGS
        if len(self.params) > len(arg_regs):
            raise HLErr(f"{self.src}: fn `{self.fn_name}` has {len(self.params)} parameters (max {len(arg_regs)} in ABI registers)")

        interf = self._compute_interference()
        # Collect all non-tail callees actually invoked so we know which caller-saved regs they preserve!
        called_fns = set()
        def _collect_callees_e(e):
            if isinstance(e, Call):
                if e.name not in _INTRINSICS and (self.fn_names is None or e.name in self.fn_names):
                    called_fns.add(e.name)
                for a in e.args:
                    _collect_callees_e(a)
            elif isinstance(e, (BinOp, Cmp, BoolOp)):
                _collect_callees_e(e.left); _collect_callees_e(e.right)
            elif isinstance(e, NotOp):
                _collect_callees_e(e.expr)
            elif isinstance(e, Select):
                _collect_callees_e(e.cond); _collect_callees_e(e.then_e); _collect_callees_e(e.else_e)
            elif isinstance(e, IndexLoad):
                _collect_callees_e(e.idx)
        def _collect_callees_s(body):
            for st in body:
                if isinstance(st, (LetStmt, AssignStmt, ExprStmt)):
                    _collect_callees_e(st.expr)
                elif isinstance(st, StoreStmt):
                    _collect_callees_e(st.idx); _collect_callees_e(st.expr)
                elif isinstance(st, IfStmt):
                    _collect_callees_e(st.cond); _collect_callees_s(st.then_body); _collect_callees_s(st.else_body)
                elif isinstance(st, WhileStmt):
                    _collect_callees_e(st.cond); _collect_callees_s(st.body)
                elif isinstance(st, ForStmt):
                    _collect_callees_e(st.lo); _collect_callees_e(st.hi); _collect_callees_s(st.body)
                elif isinstance(st, ReturnStmt) and st.expr is not None:
                    if not _expr_is_tail_call(st.expr, self.fn_names, self.fn_name):
                        _collect_callees_e(st.expr)
        _collect_callees_s(self.stmts)

        # Compute exact set of regs clobbered by any non-tail call (including call arg regs we overwrite!)
        default_clob = set(ARM_ARGS + ARM_SCRATCH + ARM_CALLER_POOL) if self.arch == "arm64" else set(X86_ARGS + X86_SCRATCH + X86_CALLER_POOL)
        if called_fns and all(c in self.callee_clobbers for c in called_fns):
            call_clob = set()
            for c in called_fns:
                call_clob |= self.callee_clobbers[c]
        else:
            call_clob = default_clob
        # Also mark arg regs written when marshaling call arguments as clobbered across calls
        max_call_args = [0]
        def _max_args_e(e):
            if isinstance(e, Call) and e.name not in _INTRINSICS:
                max_call_args[0] = max(max_call_args[0], len(e.args))
                for a in e.args: _max_args_e(a)
            elif isinstance(e, (BinOp, Cmp, BoolOp)): _max_args_e(e.left); _max_args_e(e.right)
            elif isinstance(e, NotOp): _max_args_e(e.expr)
            elif isinstance(e, Select): _max_args_e(e.cond); _max_args_e(e.then_e); _max_args_e(e.else_e)
            elif isinstance(e, IndexLoad): _max_args_e(e.idx)
        def _max_args_s(body):
            for st in body:
                if isinstance(st, (LetStmt, AssignStmt, ExprStmt)): _max_args_e(st.expr)
                elif isinstance(st, StoreStmt): _max_args_e(st.idx); _max_args_e(st.expr)
                elif isinstance(st, IfStmt): _max_args_e(st.cond); _max_args_s(st.then_body); _max_args_s(st.else_body)
                elif isinstance(st, WhileStmt): _max_args_e(st.cond); _max_args_s(st.body)
                elif isinstance(st, ForStmt): _max_args_e(st.lo); _max_args_e(st.hi); _max_args_s(st.body)
                elif isinstance(st, ReturnStmt) and st.expr is not None: _max_args_e(st.expr)
        _max_args_s(self.stmts)
        for k in range(min(max_call_args[0], len(arg_regs))):
            call_clob.add(arg_regs[k])

        used_regs = set()
        callee_pool_all = list(ARM_CALLEE_SAVED if self.arch == "arm64" else X86_CALLEE_SAVED)
        caller_pool_all = list(ARM_CALLER_POOL if self.arch == "arm64" else X86_CALLER_POOL)
        vec4_pool_all = ([f"v{k}" for k in range(0, 8)] + [f"v{k}" for k in range(16, 31)] + [f"v{k}" for k in range(8, 16)]
                         if self.arch == "arm64"
                         else [f"xmm{k}" for k in range(1, 16)])
        vec16_pool_all = [f"zmm{k}" for k in range(16, 32)] + [f"zmm{k}" for k in range(1, 16)]

        # 1. Assign parameters (only copy to another reg if live across call AND its ABI reg is clobbered!)
        param_regs = set()
        # First mark untouched params so copied params don't take their registers
        untouched_param_regs = {
            arg_regs[idx] for idx, (pname, _) in enumerate(self.params)
            if not (pname in self.live_across_call and arg_regs[idx] in call_clob)
        }
        caller_preserved = [r for r in caller_pool_all if r not in call_clob and r not in untouched_param_regs]
        for idx, (pname, _) in enumerate(self.params):
            areg = arg_regs[idx]
            pty = self.param_types[pname]
            self.var_ty[pname] = pty
            if pname in self.live_across_call and areg in call_clob:
                # Prefer a caller-saved register preserved by all callees (zero push/pop!), else callee-saved!
                if caller_preserved:
                    cs = caller_preserved.pop(0)
                elif callee_pool_all:
                    cs = callee_pool_all.pop(0)
                    self.callee_saved.append(cs)
                else:
                    cs = areg
                if cs != areg:
                    used_regs.add(cs)
                    param_regs.add(cs)
                    self.copied_params.append((pname, areg, cs))
                    self.var_loc[pname] = ("reg", cs)
                    self.var_map.append((pname, f"param ({pty})", cs, f"copied from {areg}"))
                    continue
            used_regs.add(areg)
            param_regs.add(areg)
            self.var_loc[pname] = ("reg", areg)
            self.var_map.append((pname, f"param ({pty})", areg, ""))

        caller_pool_avail = [r for r in caller_pool_all if r not in param_regs]
        call_safe_caller = [r for r in caller_pool_avail if r not in call_clob]

        # 2. Local `buf` stack arrays (aligned)
        off = 0
        for bname, bsz, balign, _ in self.bufs:
            if balign > 1:
                off = (off + balign - 1) // balign * balign
            self.var_loc[bname] = ("buf", off)
            self.var_ty[bname] = "buf"
            self.var_map.append((bname, f"buf[{bsz}]", f"[sp+{off}]", f"align {balign}"))
            off += bsz

        # 3. Deterministic greedy graph coloring in declaration order (zero hidden magic, exact branch reuse!)
        spill_count = 0
        callee_used_set = set(self.callee_saved)

        for nm, ty, mutable, _ in self.locals_order:
            self.var_ty[nm] = ty
            role = "var" if mutable else "let"
            forbidden = {
                self.var_loc[nb][1]
                for nb in interf.get(nm, ())
                if nb in self.var_loc and self.var_loc[nb][0] == "reg"
            }

            if ty in ("u64", "u8"):
                # For call-crossing locals: use callee-preserved caller-saved regs FIRST (0 pushes!), then callee-saved!
                order = (call_safe_caller + callee_pool_all if nm in self.live_across_call
                         else caller_pool_avail + callee_pool_all)
                reg = next((r for r in order if r not in forbidden), None)
                if reg is not None:
                    if reg in callee_pool_all and reg not in callee_used_set:
                        callee_used_set.add(reg)
                        self.callee_saved.append(reg)
                    used_regs.add(reg)
                    self.var_loc[nm] = ("reg", reg)
                    self.var_map.append((nm, f"{role} {ty}", reg, ""))
                else:
                    off = (off + 7) // 8 * 8
                    self.var_loc[nm] = ("spill", off)
                    self.var_map.append((nm, f"{role} {ty}", f"[sp+{off}]", "SPILL"))
                    off += 8
                    spill_count += 1
            elif ty == "u32x4":
                vreg = next((r for r in vec4_pool_all if r not in forbidden), None)
                if vreg is not None:
                    if self.arch == "arm64" and vreg in {f"v{k}" for k in range(8, 16)} and vreg not in self.vec_saved:
                        self.vec_saved.append(vreg)
                    self.var_loc[nm] = ("reg", vreg)
                    self.var_map.append((nm, f"{role} u32x4", vreg, ""))
                else:
                    off = (off + 15) // 16 * 16
                    self.var_loc[nm] = ("spill", off)
                    self.var_map.append((nm, f"{role} u32x4", f"[sp+{off}]", "SPILL"))
                    off += 16
                    spill_count += 1
            elif ty == "u32x16":
                if self.arch != "x86_64":
                    raise HLErr(f"{self.src}: `u32x16` is only available on `x86_64` (AVX-512)")
                self.uses_zmm = True
                vreg = next((r for r in vec16_pool_all if r not in forbidden), None)
                if vreg is not None:
                    self.var_loc[nm] = ("reg", vreg)
                    self.var_map.append((nm, f"{role} u32x16", vreg, ""))
                else:
                    off = (off + 63) // 64 * 64
                    self.var_loc[nm] = ("spill", off)
                    self.var_map.append((nm, f"{role} u32x16", f"[sp+{off}]", "SPILL"))
                    off += 64
                    spill_count += 1

        self.spills = spill_count

        # 4. Exact stack frame layout & alignment
        if self.arch == "x86_64":
            push_bytes = 8 * len(self.callee_saved)
            raw_frame = (off + 15) // 16 * 16 if off > 0 else 0
            # On entry to x86-64 fn, rsp ≡ 8 (mod 16). Before `call`, rsp must be ≡ 0 (mod 16).
            if self.has_calls and ((push_bytes + raw_frame + 8) % 16 != 0):
                raw_frame += 8
            self.frame_bytes = raw_frame
            self.total_stack = push_bytes + raw_frame + (8 if self.has_calls else 0)
        else:
            # AArch64: save x30 (if has_calls) + callee_saved scalars + 16-byte-aligned vec_saved (`v8..v15`) + local frame.
            save_slots = (1 if self.has_calls else 0) + len(self.callee_saved)
            scalar_save_bytes = save_slots * 8
            self.vec_save_base = (scalar_save_bytes + 15) // 16 * 16 if self.vec_saved else scalar_save_bytes
            save_bytes = self.vec_save_base + 16 * len(self.vec_saved)
            save_pad = (save_bytes + 15) // 16 * 16 if (save_bytes > 0 and off > 0) else save_bytes
            if save_pad > 0 and off > 0:
                # shift buf/spill offsets by save_pad
                for nm, (kind, o) in list(self.var_loc.items()):
                    if kind in ("buf", "spill"):
                        self.var_loc[nm] = (kind, o + save_pad)
                self.var_map = [
                    (nm, role, f"[sp+{self.var_loc[nm][1]}]" if self.var_loc[nm][0] in ("buf", "spill") else loc, note)
                    for nm, role, loc, note in self.var_map
                ]
            tot = save_pad + off
            if tot > 0:
                tot = (tot + 15) // 16 * 16
            self.frame_bytes = tot
            self.total_stack = tot

    def emit(self, line, text):
        self.out_lines.append((line, text))

    def fresh_label(self, prefix):
        self.lbl_seq += 1
        return f"@{prefix}_{self.lbl_seq}"

    def scratch(self, idx=0):
        return (ARM_SCRATCH if self.arch == "arm64" else X86_SCRATCH)[idx]

    def _emit_prologue(self, line):
        if self.arch == "x86_64":
            for r in self.callee_saved:
                self.emit(line, f"push {r}")
            if self.frame_bytes > 0:
                self.emit(line, f"sub rsp, {self.frame_bytes}")
            for _, areg, cs in self.copied_params:
                self.emit(line, f"mov {cs}, {areg}")
        else:
            if self.frame_bytes > 0:
                self.emit(line, f"sub sp, sp, {self.frame_bytes}")
            slot = 0
            if self.has_calls:
                self.emit(line, f"str x30, [sp, {slot}]")
                slot += 8
            for r in self.callee_saved:
                self.emit(line, f"str {r}, [sp, {slot}]")
                slot += 8
            vslot = self.vec_save_base
            for vr in self.vec_saved:
                self.emit(line, f"str q{vr[1:]}, [sp, {vslot}]")
                vslot += 16
            for _, areg, cs in self.copied_params:
                self.emit(line, f"mov {cs}, {areg}")

    def _emit_epilogue(self, line):
        if self.arch == "x86_64":
            if self.uses_zmm:
                self.emit(line, "vzeroupper")
            if self.frame_bytes > 0:
                self.emit(line, f"add rsp, {self.frame_bytes}")
            for r in reversed(self.callee_saved):
                self.emit(line, f"pop {r}")
        else:
            if self.frame_bytes > 0:
                slot = 0
                if self.has_calls:
                    self.emit(line, f"ldr x30, [sp, {slot}]")
                    slot += 8
                for r in self.callee_saved:
                    self.emit(line, f"ldr {r}, [sp, {slot}]")
                    slot += 8
                vslot = self.vec_save_base
                for vr in self.vec_saved:
                    self.emit(line, f"ldr q{vr[1:]}, [sp, {vslot}]")
                    vslot += 16
                self.emit(line, f"add sp, sp, {self.frame_bytes}")

    def _emit_imm(self, line, dst, val):
        if self.arch == "x86_64":
            if val == 0:
                self.emit(line, f"mov {dst}, 0")
            else:
                self.emit(line, f"mov {dst}, {val}")
        else:
            if 0 <= val <= 65535:
                self.emit(line, f"mov {dst}, {val}")
            else:
                self.emit(line, f"{dst} := {val}")

    def _load_var(self, line, name, dst):
        if name not in self.var_loc:
            raise HLErr(f"{self.src}: line {line}: unknown variable `{name}`")
        kind, val = self.var_loc[name]
        if kind == "reg":
            if val != dst:
                ty = self.var_ty[name]
                if ty == "u32x4":
                    if self.arch == "x86_64":
                        self.emit(line, f"vmovdqa {dst}, {val}")
                    else:
                        self.emit(line, f"orr {dst}.16b, {val}.16b, {val}.16b")
                elif ty == "u32x16":
                    self.emit(line, f"vmovdqa32 {dst}, {val}")
                else:
                    self.emit(line, f"mov {dst}, {val}")
            return dst
        if kind == "buf":
            if self.arch == "x86_64":
                self.emit(line, f"lea {dst}, [rsp + {val}]")
            else:
                self.emit(line, f"add {dst}, sp, {val}")
            return dst
        # spill
        ty = self.var_ty[name]
        if ty == "u32x4":
            if self.arch == "x86_64":
                self.emit(line, f"vmovdqu {dst}, [rsp + {val}]")
            else:
                self.emit(line, f"ldr q{dst[1:]}, [sp, {val}]")
        elif ty == "u32x16":
            self.emit(line, f"vmovdqa32 {dst}, [rsp + {val}]")
        else:
            if self.arch == "x86_64":
                self.emit(line, f"mov {dst}, qword ptr [rsp + {val}]")
            else:
                self.emit(line, f"ldr {dst}, [sp, {val}]")
        return dst

    def _store_var(self, line, name, src_reg):
        kind, val = self.var_loc[name]
        ty = self.var_ty[name]
        if kind == "reg":
            if src_reg != val:
                if ty == "u32x4":
                    if self.arch == "x86_64":
                        self.emit(line, f"vmovdqa {val}, {src_reg}")
                    else:
                        self.emit(line, f"orr {val}.16b, {src_reg}.16b, {src_reg}.16b")
                elif ty == "u32x16":
                    self.emit(line, f"vmovdqa32 {val}, {src_reg}")
                else:
                    self.emit(line, f"mov {val}, {src_reg}")
            return
        if ty == "u32x4":
            if self.arch == "x86_64":
                self.emit(line, f"vmovdqu [rsp + {val}], {src_reg}")
            else:
                self.emit(line, f"str q{src_reg[1:]}, [sp, {val}]")
        elif ty == "u32x16":
            self.emit(line, f"vmovdqa32 [rsp + {val}], {src_reg}")
        else:
            if self.arch == "x86_64":
                self.emit(line, f"mov qword ptr [rsp + {val}], {src_reg}")
            else:
                self.emit(line, f"str {src_reg}, [sp, {val}]")

    def _as_reg(self, e, scratch_idx):
        """Return a register holding scalar expr `e` (without copying if `e` is already in a reg)."""
        if isinstance(e, RawReg):
            return e.reg
        if isinstance(e, Var) and e.name in self.var_loc and self.var_loc[e.name][0] == "reg":
            return self.var_loc[e.name][1]
        r = self.scratch(scratch_idx)
        self._eval_scalar(e, r, scratch_idx)
        return r

    def _emit_addr(self, line, buf_name, idx_e, addr_reg, tmp_idx):
        """Compute `(base_reg, const_offset)` for `buf[idx_e]`."""
        if buf_name not in self.var_loc:
            raise HLErr(f"{self.src}: line {line}: unknown buffer `{buf_name}`")
        bkind, bval = self.var_loc[buf_name]
        if bkind == "buf":
            # Local stack buffer at sp + bval
            if isinstance(idx_e, Num):
                return ("sp" if self.arch == "arm64" else "rsp"), bval + idx_e.val
            ireg = self._as_reg(idx_e, tmp_idx)
            if self.arch == "x86_64":
                self.emit(line, f"lea {addr_reg}, [rsp + {bval}]")
                self.emit(line, f"lea {addr_reg}, [{addr_reg} + {ireg}]")
            else:
                self.emit(line, f"add {addr_reg}, sp, {bval}")
                self.emit(line, f"add {addr_reg}, {addr_reg}, {ireg}")
            return addr_reg, 0
        base_reg = bval
        if isinstance(idx_e, Num):
            return base_reg, idx_e.val
        # Check `var + const` pattern for 1-instruction `lea` / `add` + const disp!
        if isinstance(idx_e, BinOp) and idx_e.op == "+" and isinstance(idx_e.right, Num):
            disp = idx_e.right.val
            ireg = self._as_reg(idx_e.left, tmp_idx)
            if self.arch == "x86_64":
                self.emit(line, f"lea {addr_reg}, [{base_reg} + {ireg} + {disp}]")
                return addr_reg, 0
            self.emit(line, f"add {addr_reg}, {base_reg}, {ireg}")
            return addr_reg, disp
        ireg = self._as_reg(idx_e, tmp_idx)
        if self.arch == "x86_64":
            self.emit(line, f"lea {addr_reg}, [{base_reg} + {ireg}]")
        else:
            self.emit(line, f"add {addr_reg}, {base_reg}, {ireg}")
        return addr_reg, 0

    def _emit_add_sub(self, line, op, dst, lhs_reg, rhs_e, wrap=False, tmp_idx=1):
        """Emit exact or wrapping add/sub into `dst` (where `lhs_reg` holds left operand)."""
        is_add = op in ("+", "+%")
        mn = "add" if is_add else "sub"
        if isinstance(rhs_e, Num):
            k = rhs_e.val
            if self.arch == "x86_64":
                if lhs_reg != dst:
                    self.emit(line, f"mov {dst}, {lhs_reg}")
                if -(1 << 31) <= k < (1 << 31):
                    if wrap:
                        self.emit(line, "wrap")
                    self.emit(line, f"{mn} {dst}, {k}")
                else:
                    tr = self.scratch(tmp_idx)
                    self._emit_imm(line, tr, k)
                    if wrap:
                        self.emit(line, "wrap")
                    self.emit(line, f"{mn} {dst}, {tr}")
            else:
                if 0 <= k <= 4095:
                    if wrap:
                        self.emit(line, "wrap")
                    self.emit(line, f"{mn} {dst}, {lhs_reg}, {k}")
                else:
                    tr = self.scratch(tmp_idx)
                    self._emit_imm(line, tr, k)
                    if wrap:
                        self.emit(line, "wrap")
                    self.emit(line, f"{mn} {dst}, {lhs_reg}, {tr}")
            return
        rreg = self._as_reg(rhs_e, tmp_idx)
        if self.arch == "x86_64":
            if rreg == dst and lhs_reg != dst:
                tr = self.scratch(tmp_idx if self.scratch(tmp_idx) != dst else (tmp_idx + 1) % 3)
                self.emit(line, f"mov {tr}, {rreg}")
                rreg = tr
            if lhs_reg != dst:
                self.emit(line, f"mov {dst}, {lhs_reg}")
            if wrap:
                self.emit(line, "wrap")
            self.emit(line, f"{mn} {dst}, {rreg}")
        else:
            if wrap:
                self.emit(line, "wrap")
            self.emit(line, f"{mn} {dst}, {lhs_reg}, {rreg}")

    def _emit_const_mul(self, line, dst, lhs_reg, k, tmp_idx):
        """Lower constant multiplication `x * k` deterministically via shifts and adds (zero hidden mul)."""
        if k == 0:
            self._emit_imm(line, dst, 0)
            return
        if k == 1:
            if lhs_reg != dst:
                self.emit(line, f"mov {dst}, {lhs_reg}")
            return
        if k > 0 and (k & (k - 1)) == 0:
            sh = k.bit_length() - 1
            if self.arch == "x86_64":
                if lhs_reg != dst:
                    self.emit(line, f"mov {dst}, {lhs_reg}")
                self.emit(line, f"shl {dst}, {sh}")
            else:
                self.emit(line, f"lsl {dst}, {lhs_reg}, {sh}")
            return
        # Sum of power-of-two terms (e.g. * 3, * 10, * 12)
        bits = [b for b in range(64) if (k >> b) & 1]
        tr = self.scratch(tmp_idx)
        base = lhs_reg
        if base == dst:
            self.emit(line, f"mov {tr}, {lhs_reg}")
            base = tr
        first_b = bits[0]
        if first_b == 0:
            self.emit(line, f"mov {dst}, {base}")
        elif self.arch == "x86_64":
            self.emit(line, f"mov {dst}, {base}")
            self.emit(line, f"shl {dst}, {first_b}")
        else:
            self.emit(line, f"lsl {dst}, {base}, {first_b}")
        t2 = self.scratch((tmp_idx + 1) % (4 if self.arch == "arm64" else 3))
        if t2 in (dst, base):
            for cand in (ARM_SCRATCH if self.arch == "arm64" else X86_SCRATCH):
                if cand not in (dst, base):
                    t2 = cand
                    break
        for b in bits[1:]:
            if self.arch == "x86_64":
                self.emit(line, f"mov {t2}, {base}")
                self.emit(line, f"shl {t2}, {b}")
                self.emit(line, f"add {dst}, {t2}")
            else:
                self.emit(line, f"lsl {t2}, {base}, {b}")
                self.emit(line, f"add {dst}, {dst}, {t2}")

    def _eval_scalar(self, e, dst, s_idx=0):
        """Evaluate scalar expression `e` into register `dst`."""
        n_scr = 4 if self.arch == "arm64" else 3
        nxt_idx = (s_idx + 1) % n_scr
        if self.scratch(nxt_idx) == dst:
            nxt_idx = (nxt_idx + 1) % n_scr

        if isinstance(e, RawReg):
            if e.reg != dst:
                self.emit(e.line, f"mov {dst}, {e.reg}")
            return
        if isinstance(e, Num):
            self._emit_imm(e.line, dst, e.val)
            return
        if isinstance(e, Var):
            self._load_var(e.line, e.name, dst)
            return
        if isinstance(e, IndexLoad):
            addr_r = self.scratch(nxt_idx)
            base, disp = self._emit_addr(e.line, e.buf, e.idx, addr_r, nxt_idx)
            if e.width == "u8":
                if self.arch == "x86_64":
                    d_str = f" + {disp}" if disp else ""
                    self.emit(e.line, f"movzx {X86_REG32[dst]}, byte ptr [{base}{d_str}]")
                else:
                    self.emit(e.line, f"ldrb {_arm_w(dst)}, [{base}, {disp}]")
            elif e.width == "u16":
                # Two byte loads -> low | (high << 8) (little-endian)
                t_hi = self.scratch((nxt_idx + 1) % n_scr)
                if t_hi in (dst, base):
                    for cand in (ARM_SCRATCH if self.arch == "arm64" else X86_SCRATCH):
                        if cand not in (dst, base):
                            t_hi = cand
                            break
                if self.arch == "x86_64":
                    d0 = f" + {disp}" if disp else ""
                    d1 = f" + {disp + 1}"
                    self.emit(e.line, f"movzx {X86_REG32[dst]}, byte ptr [{base}{d0}]")
                    self.emit(e.line, f"movzx {X86_REG32[t_hi]}, byte ptr [{base}{d1}]")
                    self.emit(e.line, f"shl {t_hi}, 8")
                    self.emit(e.line, f"add {dst}, {t_hi}")
                else:
                    self.emit(e.line, f"ldrb {_arm_w(dst)}, [{base}, {disp}]")
                    self.emit(e.line, f"ldrb {_arm_w(t_hi)}, [{base}, {disp + 1}]")
                    self.emit(e.line, f"lsl {t_hi}, {t_hi}, 8")
                    self.emit(e.line, f"add {dst}, {dst}, {t_hi}")
            elif e.width == "u32":
                if self.arch == "x86_64":
                    d_str = f" + {disp}" if disp else ""
                    self.emit(e.line, f"mov {X86_REG32[dst]}, dword ptr [{base}{d_str}]")
                else:
                    self.emit(e.line, f"ldr {_arm_w(dst)}, [{base}, {disp}]")
            elif e.width == "u64":
                if self.arch == "x86_64":
                    d_str = f" + {disp}" if disp else ""
                    self.emit(e.line, f"mov {dst}, qword ptr [{base}{d_str}]")
                else:
                    self.emit(e.line, f"ldr {dst}, [{base}, {disp}]")
            else:
                raise HLErr(f"{self.src}: line {e.line}: cannot load `{e.width}` into scalar register")
            return
        if isinstance(e, BinOp):
            if e.op in ("+", "-", "+%", "-%"):
                wrap = e.op in ("+%", "-%")
                if isinstance(e.left, Var) and self.var_loc.get(e.left.name, (None,))[0] == "reg":
                    lreg = self.var_loc[e.left.name][1]
                else:
                    self._eval_scalar(e.left, dst, s_idx)
                    lreg = dst
                self._emit_add_sub(e.line, e.op, dst, lreg, e.right, wrap=wrap, tmp_idx=nxt_idx)
                return
            if e.op == "*":
                if isinstance(e.right, Num):
                    lreg = self._as_reg(e.left, s_idx)
                    self._emit_const_mul(e.line, dst, lreg, e.right.val, nxt_idx)
                    return
                if isinstance(e.left, Num):
                    rreg = self._as_reg(e.right, s_idx)
                    self._emit_const_mul(e.line, dst, rreg, e.left.val, nxt_idx)
                    return
                raise HLErr(f"{self.src}: line {e.line}: scalar `*` requires a constant factor (use shifts/adds for general multiplication)")
            if e.op in ("<<", ">>"):
                if not isinstance(e.right, Num):
                    raise HLErr(f"{self.src}: line {e.line}: shift amount must be a constant")
                k = e.right.val
                lreg = self._as_reg(e.left, s_idx) if (isinstance(e.left, Var) and self.var_loc.get(e.left.name, (None,))[0] == "reg") else None
                if lreg is None:
                    self._eval_scalar(e.left, dst, s_idx)
                    lreg = dst
                if self.arch == "x86_64":
                    if lreg != dst:
                        self.emit(e.line, f"mov {dst}, {lreg}")
                    self.emit(e.line, f"{'shl' if e.op == '<<' else 'shr'} {dst}, {k}")
                else:
                    self.emit(e.line, f"{'lsl' if e.op == '<<' else 'lsr'} {dst}, {lreg}, {k}")
                return
            if e.op in ("&", "|"):
                if isinstance(e.left, Var) and self.var_loc.get(e.left.name, (None,))[0] == "reg":
                    lreg = self.var_loc[e.left.name][1]
                else:
                    self._eval_scalar(e.left, dst, s_idx)
                    lreg = dst
                if self.arch == "x86_64":
                    mn = "and" if e.op == "&" else "or"
                    if isinstance(e.right, Num):
                        k = e.right.val
                        if lreg != dst:
                            self.emit(e.line, f"mov {dst}, {lreg}")
                        if -(1 << 31) <= k < (1 << 31):
                            self.emit(e.line, f"{mn} {dst}, {k}")
                        else:
                            tr = self.scratch(nxt_idx)
                            self._emit_imm(e.line, tr, k)
                            self.emit(e.line, f"{mn} {dst}, {tr}")
                    else:
                        rreg = self._as_reg(e.right, nxt_idx)
                        if lreg != dst:
                            self.emit(e.line, f"mov {dst}, {lreg}")
                        self.emit(e.line, f"{mn} {dst}, {rreg}")
                else:
                    mn = "and" if e.op == "&" else "orr"
                    if isinstance(e.right, Num):
                        tr = self.scratch(nxt_idx)
                        self._emit_imm(e.line, tr, e.right.val)
                        self.emit(e.line, f"{mn} {dst}, {lreg}, {tr}")
                    else:
                        rreg = self._as_reg(e.right, nxt_idx)
                        self.emit(e.line, f"{mn} {dst}, {lreg}, {rreg}")
                return
            raise HLErr(f"{self.src}: line {e.line}: unsupported scalar operator `{e.op}`")
        if isinstance(e, Select):
            self._eval_select(e, dst, s_idx)
            return
        if isinstance(e, Call):
            self._emit_call(e, dst)
            return
        raise HLErr(f"{self.src}: line {getattr(e, 'line', 0)}: unsupported scalar expression")

    def _emit_cmp(self, line, left_e, right_e, s_idx=0):
        """Emit `cmp a, b` and return whether operand order was kept (True)."""
        n_scr = 4 if self.arch == "arm64" else 3
        nxt = (s_idx + 1) % n_scr
        # If left is a constant and right is non-constant, swap and flip op at caller? No: just put left in scratch if needed.
        lreg = self._as_reg(left_e, s_idx)
        if isinstance(right_e, Num):
            k = right_e.val
            if self.arch == "x86_64" and -(1 << 31) <= k < (1 << 31):
                self.emit(line, f"cmp {lreg}, {k}")
                return
            if self.arch == "arm64" and 0 <= k <= 4095:
                self.emit(line, f"cmp {lreg}, {k}")
                return
            tr = self.scratch(nxt if self.scratch(nxt) != lreg else (nxt + 1) % n_scr)
            self._emit_imm(line, tr, k)
            self.emit(line, f"cmp {lreg}, {tr}")
            return
        rreg = self._as_reg(right_e, nxt if self.scratch(nxt) != lreg else (nxt + 1) % n_scr)
        self.emit(line, f"cmp {lreg}, {rreg}")

    def _eval_select(self, sel, dst, s_idx=0):
        """Lower `select(cond, t_expr, f_expr)` branchlessly to `cmp + cmov* / csel`."""
        c = sel.cond
        if isinstance(c, NotOp):
            self._eval_select(Select(c.expr, sel.else_e, sel.then_e, sel.line), dst, s_idx)
            return
        if isinstance(c, BoolOp):
            if c.op == "&&":
                # select(c1 && c2, T, F) == select(c1, select(c2, T, F), F)
                inner = Select(c.right, sel.then_e, sel.else_e, sel.line)
                self._eval_select(Select(c.left, inner, sel.else_e, sel.line), dst, s_idx)
                return
            # select(c1 || c2, T, F) == select(c1, T, select(c2, T, F))
            inner = Select(c.right, sel.then_e, sel.else_e, sel.line)
            self._eval_select(Select(c.left, sel.then_e, inner, sel.line), dst, s_idx)
            return
        assert isinstance(c, Cmp)
        # Normalize `K <= x` -> `x >= K` so immediate sits on RHS of `cmp`!
        cmp_l, cmp_op, cmp_r = c.left, c.op, c.right
        if isinstance(cmp_l, Num) and not isinstance(cmp_r, Num):
            flip = {"==": "==", "!=": "!=", "<": ">", "<=": ">=", ">": "<", ">=": "<="}[cmp_op]
            cmp_l, cmp_op, cmp_r = cmp_r, flip, cmp_l

        # Pick a free scratch register for `t_expr` (distinct from `dst` and `cmp_l`/`cmp_r` if in regs)
        pool = list(ARM_SCRATCH if self.arch == "arm64" else X86_SCRATCH)
        avoid = {dst}
        if isinstance(cmp_l, Var) and cmp_l.name in self.var_loc and self.var_loc[cmp_l.name][0] == "reg":
            avoid.add(self.var_loc[cmp_l.name][1])
        if isinstance(cmp_r, Var) and cmp_r.name in self.var_loc and self.var_loc[cmp_r.name][0] == "reg":
            avoid.add(self.var_loc[cmp_r.name][1])

        t_reg = None
        if isinstance(sel.then_e, Var) and self.var_loc.get(sel.then_e.name, (None,))[0] == "reg" and self.var_loc[sel.then_e.name][1] != dst:
            t_reg = self.var_loc[sel.then_e.name][1]
        else:
            for cand in pool:
                if cand not in avoid:
                    t_reg = cand
                    break
            if t_reg is None:
                t_reg = next(cand for cand in pool if cand != dst)
            self._eval_scalar(sel.then_e, t_reg, pool.index(t_reg) if t_reg in pool else 0)

        # Evaluate `f_expr` into `dst` (ZERO instructions when `f_expr` is already `dst`, e.g. `r := select(..., t, r)`!)
        if not (isinstance(sel.else_e, Var) and self.var_loc.get(sel.else_e.name) == ("reg", dst)):
            # Pick a scratch index that doesn't clobber `t_reg`
            f_sidx = next((idx for idx, r in enumerate(pool) if r not in (t_reg, dst)), 0)
            self._eval_scalar(sel.else_e, dst, f_sidx)

        # Emit `cmp` using scratch index avoiding `t_reg` and `dst`
        c_sidx = next((idx for idx, r in enumerate(pool) if r not in (t_reg, dst)), 0)
        self._emit_cmp(sel.line, cmp_l, cmp_r, c_sidx)

        if self.arch == "x86_64":
            cc = {"==": "e", "!=": "ne", "<": "b", "<=": "be", ">": "a", ">=": "ae"}[cmp_op]
            self.emit(sel.line, f"cmov{cc} {dst}, {t_reg}")
        else:
            cc = {"==": "eq", "!=": "ne", "<": "lo", "<=": "ls", ">": "hi", ">=": "hs"}[cmp_op]
            self.emit(sel.line, f"csel {dst}, {t_reg}, {dst}, {cc}")

    def _emit_branch(self, cond, target_lbl, jump_if_true, s_idx=0):
        """Emit macro-fused `cmp` + conditional branch (handling `&&`, `||`, `!`)."""
        if isinstance(cond, NotOp):
            self._emit_branch(cond.expr, target_lbl, not jump_if_true, s_idx)
            return
        if isinstance(cond, BoolOp):
            if (cond.op == "&&" and not jump_if_true) or (cond.op == "||" and jump_if_true):
                # Short-circuit directly to `target_lbl`
                self._emit_branch(cond.left, target_lbl, jump_if_true, s_idx)
                self._emit_branch(cond.right, target_lbl, jump_if_true, s_idx)
            else:
                fall = self.fresh_label("sc")
                self._emit_branch(cond.left, fall, not jump_if_true, s_idx)
                self._emit_branch(cond.right, target_lbl, jump_if_true, s_idx)
                self.emit(cond.line, f"{fall}:")
            return
        assert isinstance(cond, Cmp)
        cmp_l, cmp_op, cmp_r = cond.left, cond.op, cond.right
        if isinstance(cmp_l, Num) and not isinstance(cmp_r, Num):
            flip = {"==": "==", "!=": "!=", "<": ">", "<=": ">=", ">": "<", ">=": "<="}[cmp_op]
            cmp_l, cmp_op, cmp_r = cmp_r, flip, cmp_l
        if not jump_if_true:
            cmp_op = {"==": "!=", "!=": "==", "<": ">=", "<=": ">", ">": "<=", ">=": "<"}[cmp_op]
        self._emit_cmp(cond.line, cmp_l, cmp_r, s_idx)
        if self.arch == "x86_64":
            jcc = {"==": "je", "!=": "jne", "<": "jb", "<=": "jbe", ">": "ja", ">=": "jae"}[cmp_op]
            self.emit(cond.line, f"{jcc} {target_lbl}")
        else:
            bcc = {"==": "b.eq", "!=": "b.ne", "<": "b.lo", "<=": "b.ls", ">": "b.hi", ">=": "b.hs"}[cmp_op]
            self.emit(cond.line, f"{bcc} {target_lbl}")

    def _emit_call(self, call, dst=None, tail=False):
        arg_regs = ARM_ARGS if self.arch == "arm64" else X86_ARGS
        if len(call.args) > len(arg_regs):
            raise HLErr(f"{self.src}: line {call.line}: call `{call.name}` has too many arguments")
        # Safe parallel-move argument marshaling: never overwrite a register still read by another arg!
        pending = []  # list of [areg, expr, src_regs_set]
        for idx, ae in enumerate(call.args):
            areg = arg_regs[idx]
            if isinstance(ae, Var) and self.var_loc.get(ae.name) == ("reg", areg):
                continue
            sregs = {
                self.var_loc[v][1]
                for v in _used_vars_expr(ae)
                if v in self.var_loc and self.var_loc[v][0] == "reg"
            }
            pending.append([areg, ae, sregs])

        # Stage any complex (non-Var/Num) arg whose evaluation reads another pending arg's dest reg?
        # Wait: evaluating any pending arg `i` whose `areg` is NOT read by any OTHER pending arg `j`
        # is always safe! Repeat until done; break cycles with a scratch register.
        while pending:
            progressed = False
            for k in range(len(pending)):
                areg, ae, _ = pending[k]
                if not any(areg in pending[j][2] for j in range(len(pending)) if j != k):
                    self._eval_scalar(ae, areg, 0)
                    pending.pop(k)
                    progressed = True
                    break
            if not progressed:
                # Cycle among remaining args (e.g. swap `rdi` <-> `rsi`): park one reg in scratch(0)!
                # Pick a Var-arg in the cycle, save its current reg to scratch(0), rewrite refs to scratch(0).
                park_idx = next((k for k, (_, ae, _) in enumerate(pending) if isinstance(ae, Var)), 0)
                park_reg = pending[park_idx][0]
                tmp = self.scratch(0)
                self.emit(call.line, f"mov {tmp}, {park_reg}")
                # Now `park_reg` is free to be overwritten; any pending expr reading `park_reg` reads `tmp` instead!
                for j in range(len(pending)):
                    if park_reg in pending[j][2]:
                        pending[j][1] = _replace_reg_var_expr(pending[j][1], self.var_loc, park_reg, tmp)
                        pending[j][2].discard(park_reg)
                        pending[j][2].add(tmp)
                # Evaluate the arg whose dest is `park_reg` (if it itself wasn't using `tmp`? safe because `tmp` holds old `park_reg`!)
                areg, ae, _ = pending.pop(park_idx)
                self._eval_scalar(ae, areg, 1)

        if tail:
            self._emit_epilogue(call.line)
            self.emit(call.line, f"{'b' if self.arch == 'arm64' else 'jmp'} {call.name}")
            return
        self.emit(call.line, f"{'bl' if self.arch == 'arm64' else 'call'} {call.name}")
        ret_reg = "x0" if self.arch == "arm64" else "rax"
        if dst is not None and dst != ret_reg:
            self.emit(call.line, f"mov {dst}, {ret_reg}")

    # -- Vector Lowering (`u32x4` and `u32x16`) --
    def _vec_scratch(self, ty):
        if ty == "u32x16":
            return "zmm0"
        return "v31" if self.arch == "arm64" else "xmm0"

    def _as_vec_reg(self, e, ty):
        if isinstance(e, Var) and e.name in self.var_loc and self.var_loc[e.name][0] == "reg":
            return self.var_loc[e.name][1]
        vr = self._vec_scratch(ty)
        self._eval_vec(e, vr, ty)
        return vr

    def _eval_vec(self, e, dst, ty):
        line = getattr(e, "line", 0)
        if isinstance(e, Var):
            self._load_var(line, e.name, dst)
            return
        if isinstance(e, IndexLoad):
            base, disp = self._emit_addr(line, e.buf, e.idx, self.scratch(0), 0)
            if ty == "u32x4":
                if self.arch == "x86_64":
                    d_str = f" + {disp}" if disp else ""
                    self.emit(line, f"vmovdqu {dst}, [{base}{d_str}]")
                else:
                    self.emit(line, f"ldr q{dst[1:]}, [{base}, {disp}]")
            else:
                d_str = f" + {disp}" if disp else ""
                self.emit(line, f"vmovdqu32 {dst}, [{base}{d_str}]")
            return
        if isinstance(e, BinOp):
            lr = self._as_vec_reg(e.left, ty)
            rr = self._as_vec_reg(e.right, ty)
            if ty == "u32x16":
                if e.op in ("+", "+%"):
                    self.emit(line, f"vpaddd {dst}, {lr}, {rr}")
                elif e.op == "^":
                    self.emit(line, f"vpxord {dst}, {lr}, {rr}")
                else:
                    raise HLErr(f"{self.src}: line {line}: unsupported u32x16 op `{e.op}`")
            elif self.arch == "x86_64":
                op_map = {"+": "vpaddd", "+%": "vpaddd", "^": "vpxord", "&": "vpand", "|": "vpor"}
                if e.op not in op_map:
                    raise HLErr(f"{self.src}: line {line}: unsupported u32x4 op `{e.op}`")
                self.emit(line, f"{op_map[e.op]} {dst}, {lr}, {rr}")
            else:
                if e.op in ("+", "+%"):
                    self.emit(line, f"add {dst}.4s, {lr}.4s, {rr}.4s")
                elif e.op == "^":
                    self.emit(line, f"eor {dst}.16b, {lr}.16b, {rr}.16b")
                elif e.op == "&":
                    self.emit(line, f"and {dst}.16b, {lr}.16b, {rr}.16b")
                elif e.op == "|":
                    self.emit(line, f"orr {dst}.16b, {lr}.16b, {rr}.16b")
                else:
                    raise HLErr(f"{self.src}: line {line}: unsupported u32x4 op `{e.op}`")
            return
        if isinstance(e, Call):
            nm, args = e.name, e.args
            if nm == "load_u32x4":
                self._eval_vec(IndexLoad(args[0].name, args[1], "u32x4", line), dst, "u32x4")
                return
            if nm == "load_u32x16":
                self._eval_vec(IndexLoad(args[0].name, args[1], "u32x16", line), dst, "u32x16")
                return
            if nm == "zeros_u32x16":
                self.emit(line, f"vpxord {dst}, {dst}, {dst}")
                return
            if nm == "broadcast_u32x16":
                a0 = args[0]
                if isinstance(a0, IndexLoad) and a0.width == "u32":
                    base, disp = self._emit_addr(line, a0.buf, a0.idx, self.scratch(0), 0)
                    d_str = f" + {disp}" if disp else ""
                    self.emit(line, f"vpbroadcastd {dst}, dword ptr [{base}{d_str}]")
                elif isinstance(a0, Var) and a0.name in self.data_names:
                    self.emit(line, f"vpbroadcastd {dst}, dword ptr [rip + {a0.name}]")
                else:
                    sr = self._as_reg(a0, 0)
                    self.emit(line, f"vpbroadcastd {dst}, {X86_REG32[sr]}")
                return
            if nm == "const_u32x4":
                a0 = args[0]
                if self.arch == "x86_64":
                    self.emit(line, f"vmovaps {dst}, xmmword ptr [rip + {a0.name}]")
                else:
                    raise HLErr(f"{self.src}: line {line}: `const_u32x4` on arm64 uses `load_u32x4`")
                return
            if nm in ("rotl32", "rotr32"):
                k = args[1].val
                r = (32 - k) if nm == "rotl32" else k
                l = (32 - r)
                sr = self._as_vec_reg(args[0], ty)
                if ty == "u32x16" or (self.arch == "x86_64" and "avx512" in self.needs):
                    self.emit(line, f"vprord {dst}, {sr}, {r}")
                elif self.arch == "x86_64":
                    # Portable SSE/AVX rotate (or vprord if available; use vpslld+vpsrld+vpor for AVX2/SSE compatibility)
                    tmp = self._vec_scratch(ty)
                    if tmp == dst:
                        raise HLErr(f"{self.src}: line {line}: nested vector rotate needs a named `let`")
                    self.emit(line, f"vpslld {tmp}, {sr}, {l}")
                    self.emit(line, f"vpsrld {dst}, {sr}, {r}")
                    self.emit(line, f"vpor {dst}, {dst}, {tmp}")
                else:
                    if r == 16:
                        self.emit(line, f"rev32 {dst}.8h, {sr}.8h")
                    else:
                        tmp = self._vec_scratch(ty)
                        self.emit(line, f"shl {tmp}.4s, {sr}.4s, {l}")
                        self.emit(line, f"ushr {dst}.4s, {sr}.4s, {r}")
                        self.emit(line, f"orr {dst}.16b, {dst}.16b, {tmp}.16b")
                return
            if nm == "shufi32x4":
                a = self._as_vec_reg(args[0], ty)
                b = self._as_vec_reg(args[1], ty) if len(args) == 3 else a
                imm = args[-1].val
                self.emit(line, f"vshufi32x4 {dst}, {a}, {b}, {imm}")
                return
            if nm == "shuf32":
                a = self._as_vec_reg(args[0], ty)
                imm = args[1].val
                self.emit(line, f"vpshufd {dst}, {a}, {imm}")
                return
            if nm in ("ext4", "ext8", "ext12"):
                k = int(nm[3:])
                a = self._as_vec_reg(args[0], ty)
                b = self._as_vec_reg(args[1], ty)
                if self.arch == "arm64":
                    self.emit(line, f"ext {dst}.16b, {a}.16b, {b}.16b, {k}")
                else:
                    self.emit(line, f"vpalignr {dst}, {b}, {a}, {k}")
                return
            if nm in ("unpacklo32", "unpackhi32", "unpacklo64", "unpackhi64"):
                a = self._as_vec_reg(args[0], ty)
                b = self._as_vec_reg(args[1], ty)
                mn = {"unpacklo32": "vpunpckldq", "unpackhi32": "vpunpckhdq",
                      "unpacklo64": "vpunpcklqdq", "unpackhi64": "vpunpckhqdq"}[nm]
                self.emit(line, f"{mn} {dst}, {a}, {b}")
                return
            if nm == "add_u32x16_data":
                a = self._as_vec_reg(args[0], ty)
                self.emit(line, f"vpaddd {dst}, {a}, zmmword ptr [rip + {args[1].name}]")
                return
            raise HLErr(f"{self.src}: line {line}: unknown vector intrinsic `{nm}`")
        raise HLErr(f"{self.src}: line {line}: unsupported vector expression")

    # -- Automatic `place { ... }` Fact Substitution & Outer-Context Inheritance --
    def _subst_spec_vars(self, expr_str):
        """Substitute High-Level Ode local variable names (including `name$k`) with allocated registers."""
        def repl(m):
            tok = m.group(0)
            # Contract `bytes` regions and unmodified parameters ALWAYS keep their contract names in `place`!
            if tok in self.param_set and (
                self.param_types.get(tok) == "bytes"
                or tok not in self.fn_written_vars
            ):
                return tok
            if tok in self.var_loc and self.var_loc[tok][0] == "reg":
                return self.var_loc[tok][1]
            return tok
        return re.sub(r"\b[A-Za-z_]\w*(?:\$\d+)?\b", repl, expr_str)

    def _emit_loop_place(self, line, loop_written, maintains, writes, decreases, extra_facts=(), outer_vars=()):
        """Emit automatic `place { ... }` inheriting all invariant outer facts + user clauses."""
        place_lines = []
        seen = set()

        def add_fact(s):
            s = s.strip()
            if s and s not in seen:
                seen.add(s)
                place_lines.append(f"fact {s}")

        # 1. Copied parameters unmodified in the loop are preserved directly as `Lin.var entry_reg` by `keep`
        #    (do NOT emit `fact cs == param`, which would strip `cs` from `keep`!).

        # 2. Inherit all active dominating outer facts mentioning only unmodified variables whose
        #    registers are still live (not recycled by another variable and not written in the loop)!
        loop_written_regs = {self.var_loc[v][1] for v in loop_written if v in self.var_loc and self.var_loc[v][0] == "reg"}
        for fact_s, fvars in self.active_facts:
            if fvars & loop_written:
                continue
            ok = True
            for v in fvars:
                if v in self.param_set:
                    continue
                loc = self.var_loc.get(v)
                if loc is None or loc[0] != "reg":
                    ok = False
                    break
                if self.reg_owner.get(loc[1]) != v or loc[1] in loop_written_regs:
                    ok = False
                    break
            if ok:
                add_fact(self._subst_spec_vars(fact_s))

        # 3. Automatic `u8` range bounds ONLY for loop-carried outer byte variables (not body-local `let`s!)
        for v in sorted(loop_written):
            if v in outer_vars and self.var_ty.get(v) == "u8" and self.var_loc.get(v, (None,))[0] == "reg":
                r = self.var_loc[v][1]
                add_fact(f"0 <= {r}")
                add_fact(f"{r} <= 255")

        # 4. Extra structural loop facts (e.g., `for i in lo..hi` bounds)
        for ef in extra_facts:
            add_fact(self._subst_spec_vars(ef))

        # 5. User `maintains` clauses
        for mf in maintains:
            add_fact(self._subst_spec_vars(mf))

        # 6. User `writes` clauses
        for buf_nm, mode, idx_s, rhs_s in writes:
            idx_r = self._subst_spec_vars(idx_s)
            rhs_r = self._subst_spec_vars(rhs_s)
            if mode == "prefix":
                place_lines.append(f"wrote {buf_nm}[.. {idx_r}] = {rhs_r}")
            else:
                place_lines.append(f"wrote {buf_nm}[{idx_r} ..] = {rhs_r}")

        # 7. Termination measure
        if decreases is not None:
            place_lines.append(f"decreases {self._subst_spec_vars(decreases)}")

        self.emit(line, "place {")
        for pl in place_lines:
            self.emit(line, f"    {pl}")
        self.emit(line, "}")

    # -- Statement Lowering --
    def lower_stmts(self, stmts):
        saved_facts_len = len(self.active_facts)
        for st in stmts:
            self._lower_stmt(st)
        del self.active_facts[saved_facts_len:]

    def _lower_stmt(self, st):
        if isinstance(st, BufStmt):
            return
        if isinstance(st, LetStmt):
            ty = self.var_ty[st.name]
            kind, loc = self.var_loc[st.name]
            if ty in ("u32x4", "u32x16"):
                dst = loc if kind == "reg" else self._vec_scratch(ty)
                self._eval_vec(st.expr, dst, ty)
                if kind == "spill":
                    self._store_var(st.line, st.name, dst)
            else:
                dst = loc if kind == "reg" else self.scratch(0)
                self._eval_scalar(st.expr, dst, 0)
                if kind == "spill":
                    self._store_var(st.line, st.name, dst)
                # Record pure equality for immutable `let` (`x == expr`, including `a[0]`) so loops inherit it!
                if not st.mutable:
                    bparams = {p for p, t in self.param_types.items() if t == "bytes"}
                    pure = _pure_to_spec(st.expr, bparams)
                    if pure is not None:
                        self.active_facts.append((f"{st.name} == {pure[0]}", {st.name} | pure[1]))
            self.defined_vars.add(st.name)
            if kind == "reg":
                self.reg_owner[loc] = st.name
            return

        if isinstance(st, AssignStmt):
            if st.target not in self.var_loc:
                raise HLErr(f"{self.src}: line {st.line}: assignment to undeclared variable `{st.target}`")
            ty = self.var_ty[st.target]
            kind, loc = self.var_loc[st.target]
            if ty in ("u32x4", "u32x16"):
                dst = loc if kind == "reg" else self._vec_scratch(ty)
                if st.op == ":=":
                    self._eval_vec(st.expr, dst, ty)
                else:
                    bop = st.op[:-1]
                    self._eval_vec(BinOp(bop, Var(st.target, st.line), st.expr, st.line), dst, ty)
                if kind == "spill":
                    self._store_var(st.line, st.target, dst)
                return
            dst = loc if kind == "reg" else self.scratch(0)
            if st.op == ":=":
                self._eval_scalar(st.expr, dst, 0)
            else:
                bop = st.op[:-1]
                self._eval_scalar(BinOp(bop, Var(st.target, st.line), st.expr, st.line), dst, 0)
            if kind == "spill":
                self._store_var(st.line, st.target, dst)
            return

        if isinstance(st, StoreStmt):
            if st.width in ("u32x4", "u32x16"):
                vr = self._as_vec_reg(st.expr, st.width)
                base, disp = self._emit_addr(st.line, st.buf, st.idx, self.scratch(0), 0)
                if st.width == "u32x4":
                    if self.arch == "x86_64":
                        d_str = f" + {disp}" if disp else ""
                        self.emit(st.line, f"vmovdqu [{base}{d_str}], {vr}")
                    else:
                        self.emit(st.line, f"str q{vr[1:]}, [{base}, {disp}]")
                else:
                    d_str = f" + {disp}" if disp else ""
                    self.emit(st.line, f"vmovdqu32 [{base}{d_str}], {vr}")
                return
            # Scalar store (`out[i] := expr`)
            val_r = self._as_reg(st.expr, 0)
            addr_sidx = 1 if val_r == self.scratch(0) else 0
            base, disp = self._emit_addr(st.line, st.buf, st.idx, self.scratch(addr_sidx), addr_sidx)
            if st.width == "u8":
                if self.arch == "x86_64":
                    d_str = f" + {disp}" if disp else ""
                    self.emit(st.line, f"mov byte ptr [{base}{d_str}], {X86_REG8[val_r]}")
                else:
                    self.emit(st.line, f"strb {_arm_w(val_r)}, [{base}, {disp}]")
            elif st.width == "u32":
                if self.arch == "x86_64":
                    d_str = f" + {disp}" if disp else ""
                    self.emit(st.line, f"mov dword ptr [{base}{d_str}], {X86_REG32[val_r]}")
                else:
                    self.emit(st.line, f"str {_arm_w(val_r)}, [{base}, {disp}]")
            elif st.width == "u64":
                if self.arch == "x86_64":
                    d_str = f" + {disp}" if disp else ""
                    self.emit(st.line, f"mov qword ptr [{base}{d_str}], {val_r}")
                else:
                    self.emit(st.line, f"str {val_r}, [{base}, {disp}]")
            return

        if isinstance(st, ExprStmt):
            c = st.expr
            if isinstance(c, Call) and c.name in ("store_u32x4", "store_u32x16"):
                w = "u32x4" if c.name == "store_u32x4" else "u32x16"
                self._lower_stmt(StoreStmt(c.args[0].name, c.args[1], w, c.args[2], st.line))
                return
            self._emit_call(c, dst=None)
            return

        if isinstance(st, IfStmt):
            else_lbl = self.fresh_label("else")
            end_lbl = self.fresh_label("endif")
            then_facts = [f for cc in _extract_conjuncts(st.cond) if (f := _cmp_to_fact(cc)) is not None]
            else_facts = [f for cc in _extract_conjuncts(_negate_cond(st.cond)) if (f := _cmp_to_fact(cc)) is not None]
            if not st.else_body:
                self._emit_branch(st.cond, end_lbl, jump_if_true=False)
                saved = len(self.active_facts)
                self.active_facts.extend(then_facts)
                self.lower_stmts(st.then_body)
                del self.active_facts[saved:]
                self.emit(st.line, f"{end_lbl}:")
                # Crucial for W1: if `then` unconditionally exits (`if ihl < 20 { return 0 }`),
                # the negated condition (`ihl >= 20`) holds for the rest of the enclosing block!
                if _stmts_always_exit(st.then_body):
                    self.active_facts.extend(else_facts)
            else:
                self._emit_branch(st.cond, else_lbl, jump_if_true=False)
                saved = len(self.active_facts)
                self.active_facts.extend(then_facts)
                self.lower_stmts(st.then_body)
                del self.active_facts[saved:]
                if not _stmts_always_exit(st.then_body):
                    self.emit(st.line, f"{'b' if self.arch == 'arm64' else 'jmp'} {end_lbl}")
                self.emit(st.line, f"{else_lbl}:")
                saved2 = len(self.active_facts)
                self.active_facts.extend(else_facts)
                self.lower_stmts(st.else_body)
                del self.active_facts[saved2:]
                self.emit(st.line, f"{end_lbl}:")
            return

        if isinstance(st, WhileStmt):
            head_lbl = self.fresh_label("while")
            end_lbl = self.fresh_label("endwhile")
            wvars = _written_vars(st.body)
            self.emit(st.line, f"{head_lbl}:")
            self._emit_loop_place(st.line, wvars, st.maintains, st.writes, st.decreases, outer_vars=self.defined_vars)
            self._emit_branch(st.cond, end_lbl, jump_if_true=False)
            self.loop_stack.append((head_lbl, end_lbl, head_lbl))
            saved = len(self.active_facts)
            self.active_facts.extend(
                f for cc in _extract_conjuncts(st.cond) if (f := _cmp_to_fact(cc)) is not None
            )
            self.lower_stmts(st.body)
            del self.active_facts[saved:]
            self.loop_stack.pop()
            self.emit(st.line, f"{'b' if self.arch == 'arm64' else 'jmp'} {head_lbl}")
            self.emit(st.line, f"{end_lbl}:")
            return

        if isinstance(st, ForStmt):
            head_lbl = self.fresh_label("for")
            step_lbl = self.fresh_label("for_step")
            end_lbl = self.fresh_label("endfor")
            # Initialize loop counter `var := lo`
            kind, loc = self.var_loc[st.var]
            dst = loc if kind == "reg" else self.scratch(0)
            self._eval_scalar(st.lo, dst, 0)
            if kind == "spill":
                self._store_var(st.line, st.var, dst)
            wvars = _written_vars(st.body) | {st.var}
            extra = []
            lo_lin = _linear_to_spec(st.lo)
            hi_lin = _linear_to_spec(st.hi)
            if lo_lin is not None and not (lo_lin[1] & wvars):
                extra.append(f"{lo_lin[0]} <= {st.var}")
            if hi_lin is not None and not (hi_lin[1] & wvars):
                extra.append(f"{st.var} <= {hi_lin[0]}")
            dec = st.decreases
            if dec is None and hi_lin is not None and not (hi_lin[1] & wvars):
                dec = f"{hi_lin[0]} - {st.var}"
            self.emit(st.line, f"{head_lbl}:")
            self._emit_loop_place(st.line, wvars, st.maintains, st.writes, dec, extra_facts=extra, outer_vars=self.defined_vars)
            self.defined_vars.add(st.var)
            if kind == "reg":
                self.reg_owner[loc] = st.var
            # Loop guard: `i < hi` (or `i + step <= hi`? Standard: `i < hi` — matches `0..hi`)
            self._emit_branch(Cmp("<", Var(st.var, st.line), st.hi, st.line), end_lbl, jump_if_true=False)
            self.loop_stack.append((head_lbl, end_lbl, step_lbl))
            saved = len(self.active_facts)
            if hi_lin is not None:
                self.active_facts.append((f"{st.var} + 1 <= {hi_lin[0]}", {st.var} | hi_lin[1]))
            self.lower_stmts(st.body)
            del self.active_facts[saved:]
            self.loop_stack.pop()
            self.emit(st.line, f"{step_lbl}:")
            self._lower_stmt(AssignStmt(st.var, "+=", Num(st.step, st.line), st.line))
            self.emit(st.line, f"{'b' if self.arch == 'arm64' else 'jmp'} {head_lbl}")
            self.emit(st.line, f"{end_lbl}:")
            return

        if isinstance(st, BreakStmt):
            if not self.loop_stack:
                raise HLErr(f"{self.src}: line {st.line}: `break` outside loop")
            self.emit(st.line, f"{'b' if self.arch == 'arm64' else 'jmp'} {self.loop_stack[-1][1]}")
            return

        if isinstance(st, ContinueStmt):
            if not self.loop_stack:
                raise HLErr(f"{self.src}: line {st.line}: `continue` outside loop")
            self.emit(st.line, f"{'b' if self.arch == 'arm64' else 'jmp'} {self.loop_stack[-1][2]}")
            return

        if isinstance(st, JoinStmt):
            self._emit_loop_place(st.line, set(), st.facts, [], None, outer_vars=self.defined_vars)
            return

        if isinstance(st, ReturnStmt):
            if st.expr is not None:
                if _expr_is_tail_call(st.expr, self.fn_names, self.fn_name):
                    self._emit_call(st.expr, tail=True)
                    return
                ret_reg = "x0" if self.arch == "arm64" else "rax"
                self._eval_scalar(st.expr, ret_reg, 0)
            self._emit_epilogue(st.line)
            self.emit(st.line, "ret")
            return

        raise HLErr(f"{self.src}: unhandled statement {type(st).__name__}")

    def lower(self):
        first_ln = self.stmts[0].line if self.stmts else 1
        self._emit_prologue(first_ln)
        self.lower_stmts(self.stmts)
        # Void functions without trailing `return`
        if not self.out_lines or self.out_lines[-1][1] not in ("ret",) and not self.out_lines[-1][1].startswith(("jmp ", "b ")):
            last_ln = self.stmts[-1].line if self.stmts else first_ln
            self._emit_epilogue(last_ln)
            self.emit(last_ln, "ret")
        lines_out = [txt for _, txt in self.out_lines]
        clobbered = _compute_clobbered_regs(lines_out, self.arch, self.callee_saved, self.callee_clobbers)
        auto_calling = _build_auto_calling(self.params, self.arch, clobbered)
        return {
            "lines": lines_out,
            "line_nos": [ln for ln, _ in self.out_lines],
            "var_map": self.var_map,
            "spills": self.spills,
            "frame_bytes": self.frame_bytes,
            "total_stack": self.total_stack,
            "callee_saved": list(self.callee_saved),
            "clobbered": clobbered,
            "auto_calling": auto_calling,
            "arch": self.arch,
        }


def _compute_clobbered_regs(asm_lines, arch, callee_saved, callee_clobbers):
    """Return exact set of GPRs modified (and not restored) by `asm_lines`."""
    ret_reg = "x0" if arch == "arm64" else "rax"
    clob = {ret_reg}
    saved = set(callee_saved)
    reg_set = (set(ARM_ARGS + ARM_SCRATCH + ARM_CALLER_POOL + ARM_CALLEE_SAVED)
               if arch == "arm64"
               else set(X86_ARGS + X86_SCRATCH + X86_CALLER_POOL + X86_CALLEE_SAVED))
    r32_to_64 = {v: k for k, v in X86_REG32.items()}
    r8_to_64 = {v: k for k, v in X86_REG8.items()}
    in_place = False
    for raw in asm_lines:
        s = raw.strip()
        if s == "place {":
            in_place = True; continue
        if in_place:
            if s == "}": in_place = False
            continue
        if not s or s.startswith("@") or s in ("wrap", "ret", "vzeroupper"):
            continue
        m_call = re.match(r"^(?:call|bl|jmp|b)\s+([A-Za-z_]\w*)$", s)
        if m_call:
            cn = m_call.group(1)
            if cn in callee_clobbers:
                clob |= (callee_clobbers[cn] - saved)
            else:
                clob |= ((set(ARM_ARGS + ARM_SCRATCH + ARM_CALLER_POOL) if arch == "arm64"
                          else set(X86_ARGS + X86_SCRATCH + X86_CALLER_POOL)) - saved)
            continue
        if s.startswith(("cmp ", "j", "b.", "push ", "pop ", "str ", "strb ", "st1 ", "vmovdqu [", "vmovdqu32 [", "mov byte ptr", "mov dword ptr", "mov qword ptr")):
            continue
        # First operand of `op dst, ...` or `dst := ...`
        m_as = re.match(r"^([a-z0-9]+)\s*:=", s)
        if m_as:
            tok = m_as.group(1)
        else:
            m_op = re.match(r"^[a-z0-9.]+\s+([a-z0-9]+)\b", s)
            tok = m_op.group(1) if m_op else ""
        if arch == "arm64" and tok.startswith("w") and tok[1:].isdigit():
            tok = "x" + tok[1:]
        elif arch == "x86_64":
            tok = r32_to_64.get(tok, r8_to_64.get(tok, tok))
        if tok in reg_set and tok not in saved:
            clob.add(tok)
    return clob


def _build_auto_calling(params, arch, clobbered):
    """Build a C-ABI-compatible `calling { in ... out = ... preserves ... }` block advertising every untouched GPR."""
    arg_regs = ARM_ARGS if arch == "arm64" else X86_ARGS
    ret_reg = "x0" if arch == "arm64" else "rax"
    all_pres = (
        ["x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29",
         "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15"]
        if arch == "arm64"
        else ["rbx", "rbp", "r12", "r13", "r14", "r15", "rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"]
    )
    pres = [r for r in all_pres if r not in clobbered and r != ret_reg]
    if not pres:
        return None
    in_parts = ", ".join(f"{p[0]} = {arg_regs[i]}" for i, p in enumerate(params))
    lines = ["calling {"]
    if in_parts:
        lines.append(f"    in {in_parts}")
    lines.append(f"    out = {ret_reg}")
    lines.append(f"    preserves {', '.join(pres)}")
    lines.append("}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Public Entry Points
# ---------------------------------------------------------------------------

def parse_param_list(params_text):
    """Parse `a: n bytes, n: u64, c: u8` -> `[("a", "n bytes"), ("n", "u64"), ("c", "u8")]`."""
    out = []
    if not params_text.strip():
        return out
    for part in params_text.split(","):
        part = part.strip()
        if not part:
            continue
        if ":" not in part:
            continue
        nm, ty = part.split(":", 1)
        out.append((nm.strip(), ty.strip()))
    return out


def normalize_contract_params(params_text):
    """Normalize High-Level Ode types (`u64`, `u8`) in parameter lists to Ode spec `number`,
    returning `(normalized_params_text, extra_requires_lines)`."""
    if not params_text.strip():
        return params_text, []
    parts = []
    extra_req = []
    for raw in params_text.split(","):
        s = raw.strip()
        if not s:
            continue
        if ":" in s:
            nm, ty = [x.strip() for x in s.split(":", 1)]
            if ty == "u64":
                parts.append(f"{nm}: number")
            elif ty == "u8":
                parts.append(f"{nm}: number")
                extra_req.append(f"requires 0 <= {nm}")
                extra_req.append(f"requires {nm} <= 255")
            else:
                parts.append(s)
        else:
            parts.append(s)
    return ", ".join(parts), extra_req


def lower_hl_block(fn_name, params_text, lines, first_line, arch, src="<ode>", fn_names=None, data_names=None, explicit_stack=False, callee_clobbers=None, needs=()):
    """Parse and deterministically lower a High-Level Ode function body to `odec` assembly lines + metadata."""
    parser = HLParser(lines, first_line, src)
    stmts = parser.parse_block_stmts(until_brace=False)
    params = parse_param_list(params_text)
    lowerer = HLLower(fn_name, params, arch, stmts, src, fn_names=fn_names, data_names=data_names, explicit_stack=explicit_stack, callee_clobbers=callee_clobbers, needs=needs)
    res = lowerer.lower()
    # Group lowered asm lines by original High-Level Ode source line for `ode advise --asm`
    src_by_no = {first_line + i: raw.rstrip() for i, raw in enumerate(lines)}
    groups = []
    for ln, asm_txt in zip(res["line_nos"], res["lines"]):
        if groups and groups[-1][0] == ln:
            groups[-1][2].append(asm_txt)
        else:
            groups.append((ln, src_by_no.get(ln, ""), [asm_txt]))
    res["line_groups"] = groups
    return res


def format_asm_report(fn_name, hl_meta, line_map=None):
    """Format the `< 50 ms` `ode advise --asm` register/spill map and side-by-side lowering view."""
    out = []
    arch = hl_meta["arch"]
    spills = hl_meta["spills"]
    saved = ", ".join(hl_meta["callee_saved"]) if hl_meta["callee_saved"] else "none"
    out.append(f"High-Level Ode lowering ({fn_name}, {arch}): stack {hl_meta['total_stack']} B, "
               f"callee-saved: {saved}, spills: {spills}")
    if hl_meta["var_map"]:
        out.append("  variables:")
        for nm, role, loc, note in hl_meta["var_map"]:
            tail = f"  ({note})" if note else ""
            out.append(f"    {nm:<14s} {role:<18s} -> {loc}{tail}")
    out.append("  lowering (source -> exact instructions):")
    for ln, src_txt, asm_list in hl_meta["line_groups"]:
        s = src_txt.strip()
        if s:
            out.append(f"    {ln:4d} | {s}")
        for a in asm_list:
            out.append(f"         |   {a}")
    return "\n".join(out)
