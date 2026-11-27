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
import contextlib
import os
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
    r"^(?:let\s+|var\s+|stack\s+(?:var|let)\s+|buf\s+|while\s+|return(?:\s|$)|for\s+[A-Za-z_]\w*\s+in\s+|join(?:\s|$))"
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
        if _HL_START_RE.match(s):
            saw_hl = True
            continue
        if s.startswith("if "):
            m = re.fullmatch(r"if\s+([A-Za-z_]\w*)\s*\{", s)
            if m and m.group(1) in _RAW_IF_CONDS:
                return False
            saw_hl = True
            continue
        if any(op in s for op in (":=", "+=", "-=", "+%=", "-%=", "&=", "|=", "^=", "<<=", ">>=", "select(", ".u16(", ".u32(", ".u64(", ".u32x4(", ".u32x16(")):
            saw_hl = True
            continue
        if saw_hl and re.match(r"^place\s*\{", s):
            continue
        if _RAW_ASM_RE.match(s):
            return False
    return saw_hl


# ---------------------------------------------------------------------------
# Tokenizer
# ---------------------------------------------------------------------------

_KEYWORDS = frozenset({
    "let", "var", "if", "else", "while", "for",
    "break", "continue", "return", "select",
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
            if ch in "+-*/%&|^!<>()[]{}:;=,.":
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
    on_stack: bool = False

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

@dataclass
class BlockStmt:
    body: list        # lexical `{ ... }` block scope (flattened in `_alpha_rename_blocks`)
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
        if t.val in ("let", "var") or (t.val == "stack" and self.i + 1 < len(self.toks) and self.toks[self.i + 1].val in ("let", "var")):
            on_stack = False
            if t.val == "stack":
                on_stack = True
                self.i += 1
                t = self.cur()
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
            if self.cur().val in ("==", "!=", "<", "<=", ">", ">=", "&&", "||"):
                raise HLErr(
                    f"{self.src}: line {self.cur().line}: comparison `{self.cur().val}` cannot be used as a standalone "
                    f"value expression; write `select(<cond>, 1, 0)` (or put `<cond>` directly inside `if` / `select`)"
                )
            return LetStmt(nm, ty, expr, mutable, t.line, on_stack=on_stack)

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

        if t.val == "{":
            self.i += 1
            body = self.parse_block_stmts(until_brace=True)
            self.take("}")
            return BlockStmt(body, t.line)

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
            ret_e = self.parse_expr()
            if self.cur().val in ("==", "!=", "<", "<=", ">", ">=", "&&", "||"):
                raise HLErr(
                    f"{self.src}: line {self.cur().line}: comparison `{self.cur().val}` cannot be used as a standalone "
                    f"value expression; write `select(<cond>, 1, 0)` (or put `<cond>` directly inside `if` / `select`)"
                )
            return ReturnStmt(ret_e, t.line)

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

        if t.val == "place" and self.i + 1 < len(self.toks) and self.toks[self.i + 1].val == "{":
            self.i += 2
            facts = []
            while not self.peek("}") and not self.peek(kind="eof"):
                if self.maybe(";"):
                    continue
                if self.maybe("fact") or self.maybe("maintains"):
                    facts.append(self._raw_spec_until({"fact", "maintains", "}", "SEMI"}, stop_on_stmt=False))
                else:
                    fl = self.toks[self.i].line
                    parts = []
                    depth = 0
                    while not self.peek(kind="eof"):
                        cur = self.toks[self.i]
                        if depth == 0 and (cur.val in ("}", ";") or (parts and cur.line != fl)):
                            break
                        if cur.val in ("(", "["):
                            depth += 1
                        elif cur.val in (")", "]"):
                            depth = max(0, depth - 1)
                        parts.append(cur.val)
                        self.i += 1
                    txt = _join_spec_tokens(parts).strip()
                    if txt:
                        facts.append(txt)
                self.maybe(";")
            self.take("}")
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
                if self.cur().val in ("==", "!=", "<", "<=", ">", ">=", "&&", "||"):
                    raise HLErr(
                        f"{self.src}: line {self.cur().line}: comparison `{self.cur().val}` cannot be used as a standalone "
                        f"value expression; write `select(<cond>, 1, 0)` (or put `<cond>` directly inside `if` / `select`)"
                    )
                return AssignStmt(nm, op, val_e, t.line)
            # 4. Bare function/intrinsic call statement
            expr = self.parse_expr()
            if isinstance(expr, Call):
                return ExprStmt(expr, t.line)
            raise HLErr(f"{self.src}: line {t.line}: expected assignment or call statement")

        if t.val == "select":
            raise HLErr(
                f"{self.src}: line {t.line}: `select(...)` is an expression, not a statement "
                f"(bind it with `let x := select(...)`, `x := select(...)`, or `return select(...)`; "
                f"`inline fn` templates do not return values — pass a `var out: u64` parameter or use a contract-bearing `fn`)"
            )
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
        while self.cur().val in ("*", "*%", "/", "%"):
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
        c = _subst_expr(e.cond, vname, kval)
        cv = _const_eval_cond(c)
        if cv is True:
            return _subst_expr(e.then_e, vname, kval)
        if cv is False:
            return _subst_expr(e.else_e, vname, kval)
        return Select(c, _subst_expr(e.then_e, vname, kval), _subst_expr(e.else_e, vname, kval), e.line)
    if isinstance(e, Call):
        return Call(e.name, [_subst_expr(a, vname, kval) for a in e.args], e.line)
    return e


def _const_eval_cond(c):
    if isinstance(c, Cmp) and isinstance(c.left, Num) and isinstance(c.right, Num):
        a, b = c.left.val, c.right.val
        if c.op == "==": return a == b
        if c.op == "!=": return a != b
        if c.op == "<": return a < b
        if c.op == "<=": return a <= b
        if c.op == ">": return a > b
        if c.op == ">=": return a >= b
    if isinstance(c, BoolOp):
        lv = _const_eval_cond(c.left)
        rv = _const_eval_cond(c.right)
        if c.op == "&&":
            if lv is False or rv is False: return False
            if lv is True and rv is True: return True
        if c.op == "||":
            if lv is True or rv is True: return True
            if lv is False and rv is False: return False
    if isinstance(c, NotOp):
        v = _const_eval_cond(c.expr)
        if v is not None: return not v
    return None


def _const_eval_binop(op, a, b):
    M64 = (1 << 64) - 1
    if op == "+": return a + b
    if op == "-": return a - b
    if op == "*": return a * b
    if op == "/" and b > 0: return a // b
    if op == "%" and b > 0: return a % b
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
            out.append(LetStmt(st.name, st.ty, _subst_expr(st.expr, vname, kval), st.mutable, st.line, on_stack=st.on_stack))
        elif isinstance(st, AssignStmt):
            out.append(AssignStmt(st.target, st.op, _subst_expr(st.expr, vname, kval), st.line))
        elif isinstance(st, StoreStmt):
            out.append(StoreStmt(st.buf, _subst_expr(st.idx, vname, kval), st.width, _subst_expr(st.expr, vname, kval), st.line))
        elif isinstance(st, IfStmt):
            c = _subst_expr(st.cond, vname, kval)
            cv = _const_eval_cond(c)
            if cv is True:
                out.extend(_subst_stmts(st.then_body, vname, kval))
            elif cv is False:
                out.extend(_subst_stmts(st.else_body, vname, kval))
            else:
                out.append(IfStmt(c, _subst_stmts(st.then_body, vname, kval), _subst_stmts(st.else_body, vname, kval), st.line))
        elif isinstance(st, WhileStmt):
            out.append(WhileStmt(_subst_expr(st.cond, vname, kval), st.maintains, st.writes, st.decreases, _subst_stmts(st.body, vname, kval), st.line))
        elif isinstance(st, ForStmt):
            out.append(ForStmt(st.var, _subst_expr(st.lo, vname, kval), _subst_expr(st.hi, vname, kval), st.step, st.unroll, st.maintains, st.writes, st.decreases, _subst_stmts(st.body, vname, kval), st.line))
        elif isinstance(st, ReturnStmt):
            out.append(ReturnStmt(_subst_expr(st.expr, vname, kval) if st.expr is not None else None, st.line))
        elif isinstance(st, ExprStmt):
            out.append(ExprStmt(_subst_expr(st.expr, vname, kval), st.line))
        elif isinstance(st, BlockStmt):
            out.append(BlockStmt(_subst_stmts(st.body, vname, kval), st.line))
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
                out.append(LetStmt(nm2, st.ty, e2, st.mutable, st.line, on_stack=st.on_stack))
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
            elif isinstance(st, BlockStmt):
                # Flatten lexical `{ ... }` scope with its own alpha-renamed child env so locals stay disjoint!
                out.extend(ren_block(st.body, env))
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
        elif isinstance(st, BlockStmt):
            out.append(BlockStmt(expand_unrolls(st.body, src), st.line))
        else:
            out.append(st)
    return out


_INTRINSICS = frozenset({
    "load_u32x4", "store_u32x4", "load_u32x16", "store_u32x16", "broadcast_u32x16",
    "const_u32x4", "zeros_u32x16", "rotl32", "rotr32", "shl32", "shr32",
    "shuf32", "shufps", "shufi32x4",
    "unpacklo32", "unpackhi32", "unpacklo64", "unpackhi64",
    "uzp1_32", "uzp2_32", "pack_u64x2", "u32x4",
    "blend32", "ext4", "ext8", "ext12",
    "add_u32x16_data",
})

_VEC4_INTRINSICS = frozenset({
    "load_u32x4", "const_u32x4", "shuf32", "shufps", "blend32",
    "uzp1_32", "uzp2_32", "pack_u64x2", "u32x4",
    "ext4", "ext8", "ext12",
})

_VEC16_INTRINSICS = frozenset({
    "load_u32x16", "broadcast_u32x16", "zeros_u32x16", "shufi32x4", "add_u32x16_data",
})


# ---------------------------------------------------------------------------
# Wirth-style High-Level `inline fn` with `var` (by-reference) parameters
# ---------------------------------------------------------------------------

@dataclass
class HLInline:
    name: str
    params: list   # [(param_name, param_ty, is_var)]
    stmts: list
    line: int


def is_hl_inline(raw_text):
    """Return True if an `inline fn ... { ... }` declaration is a High-Level Ode inline
    (typed HL params / `var` params and no raw-asm `distinct(...)`/`changes ...` clauses)."""
    bopen = raw_text.find("{")
    if bopen == -1:
        return False
    hdr = raw_text[:bopen]
    if re.search(r"\b(?:distinct|changes)\b", hdr):
        return False
    p1 = hdr.find("(")
    p2 = hdr.rfind(")")
    if p1 != -1 and p2 > p1:
        params_s = hdr[p1 + 1:p2]
        if re.search(r"\bvar\s+[A-Za-z_]\w*\s*:", params_s):
            return True
        if re.search(r":\s*(?:(?:[A-Za-z0-9_]+\s+)?bytes|ptr|u64|u32|u8|u32x4|u32x16)\b", params_s):
            return True
    body_lines = raw_text[bopen + 1:raw_text.rfind("}")].splitlines()
    return is_hl_body(body_lines)


def parse_hl_inline(raw_text, first_line, src="<ode>"):
    """Parse a High-Level Ode `inline fn NAME([var] p: ty, ...) { <HL stmts> }`."""
    bopen = raw_text.find("{")
    bclose = raw_text.rfind("}")
    if bopen == -1 or bclose <= bopen:
        raise HLErr(f"{src}: line {first_line}: malformed `inline fn` block")
    hdr = raw_text[:bopen]
    m = re.match(r"^\s*inline\s+fn\s+([A-Za-z_]\w*)\s*(?:for\s+\w+\s*)?\((.*)\)\s*$", hdr, re.S)
    if not m:
        if "->" in hdr:
            raise HLErr(
                f"{src}: line {first_line}: High-Level `inline fn` is a statement template with no return type "
                f"(`{hdr.strip()}`); pass a `var out: u64` parameter to write a result, or use a contract-bearing `fn ... returns ...`"
            )
        raise HLErr(f"{src}: line {first_line}: invalid High-Level `inline fn` header `{hdr.strip()}`")
    name = m.group(1)
    pstr = m.group(2).strip()
    params = []
    seen = set()
    if pstr:
        for raw_p in pstr.split(","):
            ps = raw_p.strip()
            if not ps:
                continue
            pm = re.fullmatch(
                r"(var\s+)?([A-Za-z_]\w*)\s*:\s*(?:([A-Za-z0-9_]+)\s+bytes|([A-Za-z0-9_]+))",
                ps,
            )
            if not pm:
                raise HLErr(f"{src}: line {first_line}: inline fn `{name}`: invalid parameter `{ps}` (expected `[var] name: type`)")
            is_var = bool(pm.group(1))
            pname = pm.group(2)
            pty = "bytes" if pm.group(3) is not None else pm.group(4)
            if pname in seen:
                raise HLErr(f"{src}: line {first_line}: inline fn `{name}`: duplicate parameter `{pname}`")
            seen.add(pname)
            params.append((pname, pty, is_var))
    body_start_line = first_line + raw_text[:bopen].count("\n")
    body_text = raw_text[bopen + 1:bclose]
    body_lines = body_text.split("\n")
    parser = HLParser(body_lines, body_start_line, src)
    stmts = parser.parse_block_stmts(until_brace=False)
    return HLInline(name, params, stmts, first_line)


def _subst_inline_expr(e, vmap, emap, call_line):
    if isinstance(e, Var):
        if e.name in emap:
            return emap[e.name]
        return Var(vmap.get(e.name, e.name), call_line)
    if isinstance(e, Num):
        return Num(e.val, call_line)
    if isinstance(e, RawReg):
        return RawReg(e.reg, call_line)
    if isinstance(e, IndexLoad):
        buf = vmap.get(e.buf, e.buf)
        if e.buf in emap and isinstance(emap[e.buf], Var):
            buf = emap[e.buf].name
        return IndexLoad(buf, _subst_inline_expr(e.idx, vmap, emap, call_line), e.width, call_line)
    if isinstance(e, BinOp):
        l = _subst_inline_expr(e.left, vmap, emap, call_line)
        r = _subst_inline_expr(e.right, vmap, emap, call_line)
        if isinstance(l, Num) and isinstance(r, Num):
            val = _const_eval_binop(e.op, l.val, r.val)
            if val is not None:
                return Num(val, call_line)
        return BinOp(e.op, l, r, call_line)
    if isinstance(e, Cmp):
        return Cmp(e.op, _subst_inline_expr(e.left, vmap, emap, call_line), _subst_inline_expr(e.right, vmap, emap, call_line), call_line)
    if isinstance(e, BoolOp):
        return BoolOp(e.op, _subst_inline_expr(e.left, vmap, emap, call_line), _subst_inline_expr(e.right, vmap, emap, call_line), call_line)
    if isinstance(e, NotOp):
        return NotOp(_subst_inline_expr(e.expr, vmap, emap, call_line), call_line)
    if isinstance(e, Select):
        return Select(
            _subst_inline_expr(e.cond, vmap, emap, call_line),
            _subst_inline_expr(e.then_e, vmap, emap, call_line),
            _subst_inline_expr(e.else_e, vmap, emap, call_line),
            call_line,
        )
    if isinstance(e, Call):
        return Call(e.name, [_subst_inline_expr(a, vmap, emap, call_line) for a in e.args], call_line)
    return e


def _expr_to_spec_str(e):
    """Best-effort rendering of an HL argument expression for substitution inside `maintains`/`writes`/`decreases`."""
    if isinstance(e, Var):
        return e.name
    if isinstance(e, Num):
        return str(e.val)
    if isinstance(e, IndexLoad) and e.width == "u8":
        ix = _expr_to_spec_str(e.idx)
        return f"{e.buf}[{ix}]" if ix is not None else None
    if isinstance(e, BinOp) and e.op in ("+", "-", "*", "+%", "-%"):
        a = _expr_to_spec_str(e.left)
        b = _expr_to_spec_str(e.right)
        if a is not None and b is not None:
            op = e.op.rstrip("%")
            return f"({a} {op} {b})"
    return None


def _subst_inline_clause(text, vmap, emap):
    """Substitute `inline fn` parameter names inside `maintains` / `writes` / `decreases` strings."""
    if not text:
        return text
    repl = {}
    for k, v in vmap.items():
        repl[k] = v
    for k, expr in emap.items():
        if k not in repl:
            rendered = _expr_to_spec_str(expr)
            if rendered is not None:
                repl[k] = rendered
    if not repl:
        return text
    def _sub_tok(m):
        nm = m.group(0)
        return repl.get(nm, nm)
    return re.sub(r"(?<!\.)\b[A-Za-z_][A-Za-z0-9_]*\b(?!\s*\()", _sub_tok, text)


def _subst_inline_stmts(stmts, vmap, emap, prefix, call_line):
    out = []
    cur_vmap = dict(vmap)
    for st in stmts:
        if isinstance(st, LetStmt):
            ne = _subst_inline_expr(st.expr, cur_vmap, emap, call_line)
            new_nm = f"{prefix}{st.name}"
            cur_vmap[st.name] = new_nm
            out.append(LetStmt(new_nm, st.ty, ne, st.mutable, call_line, on_stack=st.on_stack))
        elif isinstance(st, AssignStmt):
            tgt = cur_vmap.get(st.target, st.target)
            out.append(AssignStmt(tgt, st.op, _subst_inline_expr(st.expr, cur_vmap, emap, call_line), call_line))
        elif isinstance(st, StoreStmt):
            buf = cur_vmap.get(st.buf, st.buf)
            if st.buf in emap and isinstance(emap[st.buf], Var):
                buf = emap[st.buf].name
            out.append(StoreStmt(buf, _subst_inline_expr(st.idx, cur_vmap, emap, call_line), st.width, _subst_inline_expr(st.expr, cur_vmap, emap, call_line), call_line))
        elif isinstance(st, IfStmt):
            out.append(IfStmt(
                _subst_inline_expr(st.cond, cur_vmap, emap, call_line),
                _subst_inline_stmts(st.then_body, cur_vmap, emap, prefix, call_line),
                _subst_inline_stmts(st.else_body, cur_vmap, emap, prefix, call_line),
                call_line,
            ))
        elif isinstance(st, WhileStmt):
            out.append(WhileStmt(
                _subst_inline_expr(st.cond, cur_vmap, emap, call_line),
                [_subst_inline_clause(m, cur_vmap, emap) for m in st.maintains],
                [_subst_inline_clause(w, cur_vmap, emap) for w in st.writes],
                _subst_inline_clause(st.decreases, cur_vmap, emap) if st.decreases else None,
                _subst_inline_stmts(st.body, cur_vmap, emap, prefix, call_line),
                call_line,
            ))
        elif isinstance(st, ForStmt):
            nv = f"{prefix}{st.var}"
            inner_vm = dict(cur_vmap)
            inner_vm[st.var] = nv
            out.append(ForStmt(
                nv,
                _subst_inline_expr(st.lo, cur_vmap, emap, call_line),
                _subst_inline_expr(st.hi, cur_vmap, emap, call_line),
                st.step, st.unroll,
                [_subst_inline_clause(m, inner_vm, emap) for m in st.maintains],
                [_subst_inline_clause(w, inner_vm, emap) for w in st.writes],
                _subst_inline_clause(st.decreases, inner_vm, emap) if st.decreases else None,
                _subst_inline_stmts(st.body, inner_vm, emap, prefix, call_line),
                call_line,
            ))
        elif isinstance(st, JoinStmt):
            out.append(JoinStmt(
                [_subst_inline_clause(f, cur_vmap, emap) for f in st.facts],
                call_line,
            ))
        elif isinstance(st, ExprStmt):
            out.append(ExprStmt(_subst_inline_expr(st.expr, cur_vmap, emap, call_line), call_line))
        elif isinstance(st, ReturnStmt):
            out.append(ReturnStmt(_subst_inline_expr(st.expr, cur_vmap, emap, call_line) if st.expr is not None else None, call_line))
        elif isinstance(st, BlockStmt):
            out.append(BlockStmt(_subst_inline_stmts(st.body, cur_vmap, emap, prefix, call_line), call_line))
        else:
            out.append(st)
    return out


def _expand_hl_inlines(stmts, hl_inlines, src, depth=0, seq=None):
    """Hygienically expand High-Level `inline fn` calls in exact statement order."""
    if not hl_inlines:
        return stmts
    if seq is None:
        seq = [0]
    if depth > 16:
        raise HLErr(f"{src}: `inline fn` expansion exceeded max depth 16 (recursive inline fn?)")
    out = []
    for st in stmts:
        if isinstance(st, ExprStmt) and isinstance(st.expr, Call) and st.expr.name in hl_inlines:
            inl = hl_inlines[st.expr.name]
            args = st.expr.args
            if len(args) != len(inl.params):
                raise HLErr(
                    f"{src}: line {st.line}: inline fn `{inl.name}` takes {len(inl.params)} argument(s), got {len(args)}"
                )
            seq[0] += 1
            pfx = f"__inl_{seq[0]}_"
            vmap, emap, preamble = {}, {}, []
            for (pname, pty, is_var), a in zip(inl.params, args):
                if is_var:
                    if not isinstance(a, Var):
                        raise HLErr(
                            f"{src}: line {st.line}: inline fn `{inl.name}` parameter `var {pname}: {pty}` requires a variable argument"
                        )
                    vmap[pname] = a.name
                elif isinstance(a, (Var, Num)):
                    emap[pname] = a
                else:
                    tmp_nm = f"{pfx}arg_{pname}"
                    preamble.append(LetStmt(tmp_nm, pty, a, False, st.line))
                    vmap[pname] = tmp_nm
            expanded = preamble + _subst_inline_stmts(inl.stmts, vmap, emap, pfx, st.line)
            out.extend(_expand_hl_inlines(expanded, hl_inlines, src, depth + 1, seq))
        elif isinstance(st, IfStmt):
            out.append(IfStmt(
                st.cond,
                _expand_hl_inlines(st.then_body, hl_inlines, src, depth, seq),
                _expand_hl_inlines(st.else_body, hl_inlines, src, depth, seq),
                st.line,
            ))
        elif isinstance(st, WhileStmt):
            out.append(WhileStmt(
                st.cond, st.maintains, st.writes, st.decreases,
                _expand_hl_inlines(st.body, hl_inlines, src, depth, seq),
                st.line,
            ))
        elif isinstance(st, ForStmt):
            out.append(ForStmt(
                st.var, st.lo, st.hi, st.step, st.unroll, st.maintains, st.writes, st.decreases,
                _expand_hl_inlines(st.body, hl_inlines, src, depth, seq),
                st.line,
            ))
        elif isinstance(st, BlockStmt):
            out.append(BlockStmt(_expand_hl_inlines(st.body, hl_inlines, src, depth, seq), st.line))
        else:
            out.append(st)
    return out


def _mutated_vars(stmts):
    """Return set of variable names that are mutable (`var`, `:=`, `+=`, `for` counter) anywhere in `stmts`."""
    w = set()
    for st in stmts:
        if isinstance(st, LetStmt) and st.mutable:
            w.add(st.name)
        elif isinstance(st, AssignStmt):
            w.add(st.target)
        elif isinstance(st, ForStmt):
            w.add(st.var)
            w |= _mutated_vars(st.body)
        elif isinstance(st, IfStmt):
            w |= _mutated_vars(st.then_body) | _mutated_vars(st.else_body)
        elif isinstance(st, WhileStmt):
            w |= _mutated_vars(st.body)
    return w


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


def _collect_real_calls_expr(e, fn_names):
    out = []
    if isinstance(e, Call):
        for a in e.args:
            out.extend(_collect_real_calls_expr(a, fn_names))
        if e.name not in _INTRINSICS and (fn_names is None or e.name in fn_names):
            out.append(e)
    elif isinstance(e, (BinOp, Cmp, BoolOp)):
        out.extend(_collect_real_calls_expr(e.left, fn_names))
        out.extend(_collect_real_calls_expr(e.right, fn_names))
    elif isinstance(e, NotOp):
        out.extend(_collect_real_calls_expr(e.expr, fn_names))
    elif isinstance(e, Select):
        out.extend(_collect_real_calls_expr(e.cond, fn_names))
        out.extend(_collect_real_calls_expr(e.then_e, fn_names))
        out.extend(_collect_real_calls_expr(e.else_e, fn_names))
    elif isinstance(e, IndexLoad):
        out.extend(_collect_real_calls_expr(e.idx, fn_names))
    return out


def _analyze_calls_and_vars(stmts, param_names, fn_names, self_name=None):
    """Collect declared locals, inferred types, explicit stack vars, buffers, and exact per-variable crossed non-tail calls."""
    locals_order = []   # [(name, ty, mutable, line)]
    local_types = {}
    stack_vars = set()  # names declared with explicit `stack var` / `stack let`
    bufs = []           # [(name, size, align, line)]
    has_non_tail_call = [False]
    live_across_call = set()
    var_crossed_calls = {}  # var_name -> list[Call]

    def record_crossed(vset, calls):
        if not calls:
            return
        live_across_call.update(vset)
        for v in vset:
            lst = var_crossed_calls.setdefault(v, [])
            for c in calls:
                if c not in lst:
                    lst.append(c)

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
                if st.on_stack:
                    stack_vars.add(st.name)
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
    # Exact backward liveness across non-tail calls (fixed point):
    # tracks the exact set of Call nodes each variable is live across!
    if has_non_tail_call[0]:
        def backward(body, live_out, brk_live=frozenset(), cont_live=frozenset()):
            live = set(live_out)
            for st in reversed(body):
                if isinstance(st, ReturnStmt):
                    if st.expr is None:
                        live = set()
                    elif _expr_is_tail_call(st.expr, fn_names, self_name):
                        live = _used_vars_expr(st.expr)
                    else:
                        cs = _collect_real_calls_expr(st.expr, fn_names)
                        if cs and not isinstance(st.expr, Call):
                            record_crossed(_used_vars_expr(st.expr), cs)
                        live = _used_vars_expr(st.expr)
                elif isinstance(st, BreakStmt):
                    live = set(brk_live)
                elif isinstance(st, ContinueStmt):
                    live = set(cont_live)
                elif isinstance(st, (BufStmt, JoinStmt)):
                    pass
                elif isinstance(st, LetStmt):
                    after = live - {st.name}
                    cs = _collect_real_calls_expr(st.expr, fn_names)
                    if cs:
                        extra = _used_vars_expr(st.expr) if not isinstance(st.expr, Call) else set()
                        record_crossed(after | extra, cs)
                    live = after | _used_vars_expr(st.expr)
                elif isinstance(st, AssignStmt):
                    after = (live - {st.target}) if st.op == ":=" else (live | {st.target})
                    cs = _collect_real_calls_expr(st.expr, fn_names)
                    if cs:
                        extra = _used_vars_expr(st.expr) if not isinstance(st.expr, Call) else set()
                        record_crossed(after | extra, cs)
                    live = after | _used_vars_expr(st.expr)
                elif isinstance(st, StoreStmt):
                    cs = _collect_real_calls_expr(st.idx, fn_names) + _collect_real_calls_expr(st.expr, fn_names)
                    if cs:
                        record_crossed(live | {st.buf} | _used_vars_expr(st.idx) | _used_vars_expr(st.expr), cs)
                    live = live | {st.buf} | _used_vars_expr(st.idx) | _used_vars_expr(st.expr)
                elif isinstance(st, ExprStmt):
                    cs = _collect_real_calls_expr(st.expr, fn_names)
                    if cs:
                        extra = _used_vars_expr(st.expr) if not isinstance(st.expr, Call) else set()
                        record_crossed(live | extra, cs)
                    live = live | _used_vars_expr(st.expr)
                elif isinstance(st, IfStmt):
                    lt = backward(st.then_body, live, brk_live, cont_live)
                    le = backward(st.else_body, live, brk_live, cont_live)
                    cs = _collect_real_calls_expr(st.cond, fn_names)
                    if cs:
                        record_crossed(lt | le | _used_vars_expr(st.cond), cs)
                    live = lt | le | _used_vars_expr(st.cond)
                elif isinstance(st, WhileStmt):
                    cur_in = set(live) | _used_vars_expr(st.cond)
                    while True:
                        prev_in = set(cur_in)
                        b_in = backward(st.body, cur_in, brk_live=live, cont_live=cur_in)
                        cs = _collect_real_calls_expr(st.cond, fn_names)
                        if cs:
                            record_crossed(b_in | cur_in | _used_vars_expr(st.cond), cs)
                        cur_in = cur_in | b_in | _used_vars_expr(st.cond)
                        if cur_in == prev_in:
                            break
                    backward(st.body, cur_in, brk_live=live, cont_live=cur_in)
                    live = cur_in
                elif isinstance(st, ForStmt):
                    cur_in = set(live) | _used_vars_expr(st.hi) | {st.var}
                    while True:
                        prev_in = set(cur_in)
                        b_in = backward(st.body, cur_in, brk_live=live, cont_live=cur_in)
                        cur_in = cur_in | b_in | _used_vars_expr(st.hi) | {st.var}
                        if cur_in == prev_in:
                            break
                    backward(st.body, cur_in, brk_live=live, cont_live=cur_in)
                    after_lo = cur_in - {st.var}
                    cs = _collect_real_calls_expr(st.lo, fn_names) + _collect_real_calls_expr(st.hi, fn_names)
                    if cs:
                        record_crossed(after_lo | _used_vars_expr(st.lo) | _used_vars_expr(st.hi), cs)
                    live = after_lo | _used_vars_expr(st.lo) | _used_vars_expr(st.hi)
            return live

        backward(stmts, set())
    return locals_order, local_types, stack_vars, bufs, has_non_tail_call[0], live_across_call, var_crossed_calls


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
        if e.op in ("/", "%") and isinstance(e.right, Num) and e.right.val > 0 and (e.right.val & (e.right.val - 1)) == 0:
            l = _pure_to_spec(e.left, bytes_params)
            if l is not None:
                return f"({l[0]} {e.op} {e.right.val})", l[1]
    return None


def _linear_to_spec(e):
    return _pure_to_spec(e, ())


def _cmp_to_fact(c, bytes_params=()):
    """Convert a linear `Cmp` into `(fact_str, vars_used)` for `place` inheritance, or None."""
    if not isinstance(c, Cmp) or c.op == "!=":
        return None
    l = _pure_to_spec(c.left, bytes_params)
    r = _pure_to_spec(c.right, bytes_params)
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
# Constant `let` Folding & Liveness Helpers
# ---------------------------------------------------------------------------

def _const_eval_expr(e, env):
    if isinstance(e, Num):
        return e.val
    if isinstance(e, Var) and e.name in env:
        return env[e.name]
    if isinstance(e, BinOp):
        lv = _const_eval_expr(e.left, env)
        rv = _const_eval_expr(e.right, env)
        if lv is not None and rv is not None:
            v = _const_eval_binop(e.op, lv, rv)
            if v is not None and 0 <= v < (1 << 64):
                return v
    return None


def _subst_consts_expr(e, env):
    if not env:
        return e
    if isinstance(e, Var) and e.name in env:
        return Num(env[e.name], e.line)
    if isinstance(e, IndexLoad):
        return IndexLoad(e.buf, _subst_consts_expr(e.idx, env), e.width, e.line)
    if isinstance(e, BinOp):
        l = _subst_consts_expr(e.left, env)
        r = _subst_consts_expr(e.right, env)
        if isinstance(l, Num) and isinstance(r, Num):
            v = _const_eval_binop(e.op, l.val, r.val)
            if v is not None and 0 <= v < (1 << 64):
                return Num(v, e.line)
        return BinOp(e.op, l, r, e.line)
    if isinstance(e, Cmp):
        return Cmp(e.op, _subst_consts_expr(e.left, env), _subst_consts_expr(e.right, env), e.line)
    if isinstance(e, BoolOp):
        return BoolOp(e.op, _subst_consts_expr(e.left, env), _subst_consts_expr(e.right, env), e.line)
    if isinstance(e, NotOp):
        return NotOp(_subst_consts_expr(e.expr, env), e.line)
    if isinstance(e, Select):
        return Select(_subst_consts_expr(e.cond, env), _subst_consts_expr(e.then_e, env), _subst_consts_expr(e.else_e, env), e.line)
    if isinstance(e, Call):
        return Call(e.name, [_subst_consts_expr(a, env) for a in e.args], e.line)
    return e


def _fold_const_lets(stmts):
    """Fold pure immutable scalar constant `let m := <const>` bindings directly into `Num(k)` so
    constant masks/shifts (`c & m`, `x >> sh`) use immediate operands and zero physical registers."""
    mutated = _mutated_vars(stmts)
    const_vals = {}

    def walk(body, env):
        out = []
        cur = dict(env)
        for st in body:
            if isinstance(st, LetStmt):
                ex = _subst_consts_expr(st.expr, cur)
                if (not st.mutable) and (not st.on_stack) and st.name not in mutated and st.ty in (None, "u64", "u8"):
                    kv = _const_eval_expr(ex, cur)
                    if kv is not None:
                        cur[st.name] = kv
                        const_vals[st.name] = kv
                        continue
                out.append(LetStmt(st.name, st.ty, ex, st.mutable, st.line, on_stack=st.on_stack))
            elif isinstance(st, AssignStmt):
                out.append(AssignStmt(st.target, st.op, _subst_consts_expr(st.expr, cur), st.line))
            elif isinstance(st, StoreStmt):
                out.append(StoreStmt(st.buf, _subst_consts_expr(st.idx, cur), st.width, _subst_consts_expr(st.expr, cur), st.line))
            elif isinstance(st, IfStmt):
                out.append(IfStmt(_subst_consts_expr(st.cond, cur), walk(st.then_body, cur), walk(st.else_body, cur), st.line))
            elif isinstance(st, WhileStmt):
                out.append(WhileStmt(_subst_consts_expr(st.cond, cur), st.maintains, st.writes, st.decreases, walk(st.body, cur), st.line))
            elif isinstance(st, ForStmt):
                out.append(ForStmt(st.var, _subst_consts_expr(st.lo, cur), _subst_consts_expr(st.hi, cur), st.step, st.unroll, st.maintains, st.writes, st.decreases, walk(st.body, cur), st.line))
            elif isinstance(st, ReturnStmt):
                out.append(ReturnStmt(_subst_consts_expr(st.expr, cur) if st.expr is not None else None, st.line))
            elif isinstance(st, ExprStmt):
                out.append(ExprStmt(_subst_consts_expr(st.expr, cur), st.line))
            else:
                out.append(st)
        return out

    return walk(stmts, {}), const_vals


def _expr_brief(e):
    """Short human-readable source preview of an expression for interactive register diagnostics."""
    if isinstance(e, Num):
        return str(e.val)
    if isinstance(e, Var):
        return e.name
    if isinstance(e, RawReg):
        return e.reg
    if isinstance(e, IndexLoad):
        return f"{e.buf}[{_expr_brief(e.idx)}]"
    if isinstance(e, BinOp):
        return f"({_expr_brief(e.left)} {e.op} {_expr_brief(e.right)})"
    if isinstance(e, (Cmp, BoolOp)):
        return f"({_expr_brief(e.left)} {e.op} {_expr_brief(e.right)})"
    if isinstance(e, NotOp):
        return f"!{_expr_brief(e.expr)}"
    if isinstance(e, Select):
        return f"select({_expr_brief(e.cond)}, ...)"
    if isinstance(e, Call):
        return f"{e.name}(...)"
    return "expr"


def _clobber_sensitive_vars(e):
    """Variables read inside `e` that must NOT share a register with `dst` because `e` may write `dst`
    before finishing reading them. Simple unary/single-var ops (`x`, `x & K`, `x << K`, `buf[x]`) can
    safely overwrite dead `x` in place, saving both registers and `mov` instructions."""
    if isinstance(e, (Num, Var, RawReg)):
        return set()
    if isinstance(e, IndexLoad) and e.width in ("u8", "u32", "u64"):
        if isinstance(e.idx, (Num, Var)):
            return set()
    if isinstance(e, BinOp) and e.op in ("+", "-", "+%", "-%", "*", "/", "%", "<<", ">>", "&", "|"):
        if isinstance(e.left, Var) and isinstance(e.right, Num):
            return set()
        if e.op in ("+", "+%", "*") and isinstance(e.left, Num) and isinstance(e.right, Var):
            return set()
        if e.op in ("+", "-", "+%", "-%", "*", "&", "|") and isinstance(e.left, Var) and isinstance(e.right, Var):
            return {e.right.name} if e.right.name != e.left.name else set()
    return _used_vars_expr(e)


# ---------------------------------------------------------------------------
# Deterministic Lowering Engine (`HLLower`)
# ---------------------------------------------------------------------------

class HLLower:
    def __init__(self, fn_name, params, arch, stmts, src, fn_names=None, data_names=None, explicit_stack=False, callee_clobbers=None, needs=(), hl_inlines=None):
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
        self.hl_inlines = dict(hl_inlines) if hl_inlines else {}

        expanded = _expand_hl_inlines(stmts, self.hl_inlines, src)
        expanded = expand_unrolls(expanded, src)
        expanded = _expand_hl_inlines(expanded, self.hl_inlines, src)
        self.stmts = _alpha_rename_blocks(expanded, self.param_names)
        self.stmts, self.const_vals = _fold_const_lets(self.stmts)
        self._live_temps = {}  # reg -> description of held temporary value
        (self.locals_order, self.local_types, self.stack_vars, self.bufs,
         self.has_calls, self.live_across_call, self.var_crossed_calls) = _analyze_calls_and_vars(
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
        self.uses_zmm = False
        self.frame_bytes = 0     # local buffer + spill bytes (excluding saved regs)
        self.total_stack = 0     # exact stack budget for contract
        self.var_map = []        # [(name, role, loc_str, note)] for `ode advise --asm`
        self.fn_written_vars = _written_vars(self.stmts)
        self.fn_mutated_vars = _mutated_vars(self.stmts)

        self._allocate()

        self.out_lines = []      # [(src_line, text)]
        self._last_place_end = None   # out_lines index right after previous `place { ... }` at current PC
        self.lbl_seq = 0
        self.loop_stack = []     # [(head_lbl, end_lbl, step_lbl_or_None)]
        self.active_facts = []   # [(fact_str, vars_used)]
        self.pure_aliases = {}   # immutable `let` var -> (spec_expr_str, vars_used)
        self.defined_vars = set(self.param_names)
        self.reg_owner = {self.var_loc[p][1]: p for p in self.param_names if self.var_loc[p][0] == "reg"}

    def _compute_interference(self):
        """Compute exact AST backward liveness and interference graph `interf[v]` for all locals and parameters.
        Two variables interfere iff one is live at a point where the other is defined/written,
        so disjoint `if/else` or early-return branches AND dead parameters freely release their registers!"""
        interf = {nm: set() for nm, _, _, _ in self.locals_order}
        for pn in self.param_names:
            interf.setdefault(pn, set())
        tracked_set = set(interf.keys())

        def add_interf(v, live_set):
            if v not in tracked_set:
                return
            for u in live_set:
                if u in tracked_set and u != v:
                    interf[v].add(u)
                    interf[u].add(v)

        def spec_vars(s):
            if not s:
                return set()
            # Unmodified contract parameters are bound to their entry symbols in `place` by Core.lean
            # and never need their entry machine register kept live across a loop!
            return {
                tok for tok in re.findall(r"\b[A-Za-z_]\w*(?:\$\d+)?\b", s)
                if tok in tracked_set and not (tok in self.param_set and tok not in self.fn_written_vars)
            }

        def back(body, live_out, brk_live=frozenset(), cont_live=frozenset()):
            live = set(live_out)
            for st in reversed(body):
                if isinstance(st, ReturnStmt):
                    live = (_used_vars_expr(st.expr) & tracked_set) if st.expr is not None else set()
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
                    rhs_v = _used_vars_expr(st.expr) & tracked_set
                    add_interf(st.name, live | (_clobber_sensitive_vars(st.expr) & tracked_set))
                    live = (live - {st.name}) | rhs_v
                elif isinstance(st, AssignStmt):
                    rhs_v = _used_vars_expr(st.expr) & tracked_set
                    if st.op == ":=":
                        add_interf(st.target, live | (_clobber_sensitive_vars(st.expr) & tracked_set))
                        live = (live - {st.target}) | rhs_v
                    else:
                        add_interf(st.target, live | rhs_v)
                        live = live | ({st.target} & tracked_set) | rhs_v
                elif isinstance(st, StoreStmt):
                    live |= (({st.buf} | _used_vars_expr(st.idx) | _used_vars_expr(st.expr)) & tracked_set)
                elif isinstance(st, ExprStmt):
                    live |= (_used_vars_expr(st.expr) & tracked_set)
                elif isinstance(st, IfStmt):
                    lt = back(st.then_body, live, brk_live, cont_live)
                    le = back(st.else_body, live, brk_live, cont_live) if st.else_body else set(live)
                    live = lt | le | (_used_vars_expr(st.cond) & tracked_set)
                elif isinstance(st, WhileStmt):
                    clause_v = set()
                    for m in st.maintains: clause_v |= spec_vars(m)
                    for _, _, is_, rs_ in st.writes: clause_v |= spec_vars(is_) | spec_vars(rs_)
                    clause_v |= spec_vars(st.decreases)
                    head_in = set(live) | clause_v | (_used_vars_expr(st.cond) & tracked_set)
                    while True:
                        prev = set(head_in)
                        b_in = back(st.body, head_in, brk_live=live, cont_live=head_in)
                        head_in = head_in | b_in | clause_v | (_used_vars_expr(st.cond) & tracked_set)
                        if head_in == prev:
                            break
                    back(st.body, head_in, brk_live=live, cont_live=head_in)
                    live = head_in
                elif isinstance(st, ForStmt):
                    clause_v = set()
                    for m in st.maintains: clause_v |= spec_vars(m)
                    for _, _, is_, rs_ in st.writes: clause_v |= spec_vars(is_) | spec_vars(rs_)
                    clause_v |= spec_vars(st.decreases)
                    hi_v = _used_vars_expr(st.hi) & tracked_set
                    head_in = set(live) | clause_v | hi_v | ({st.var} & tracked_set)
                    while True:
                        prev = set(head_in)
                        step_in = head_in | ({st.var} & tracked_set)
                        add_interf(st.var, head_in)
                        b_in = back(st.body, step_in, brk_live=live, cont_live=step_in)
                        head_in = head_in | b_in | clause_v | hi_v | ({st.var} & tracked_set)
                        if head_in == prev:
                            break
                    step_in = head_in | ({st.var} & tracked_set)
                    add_interf(st.var, head_in)
                    back(st.body, step_in, brk_live=live, cont_live=step_in)
                    live = (head_in - {st.var}) | (_used_vars_expr(st.lo) & tracked_set) | hi_v
            return live

        back(self.stmts, set())
        return interf

    def _allocate(self):
        arg_regs = ARM_ARGS if self.arch == "arm64" else X86_ARGS
        if len(self.params) > len(arg_regs):
            raise HLErr(f"{self.src}: fn `{self.fn_name}` has {len(self.params)} parameters (max {len(arg_regs)} in ABI registers)")

        interf = self._compute_interference()
        default_clob = (set(ARM_ARGS + ARM_SCRATCH + ARM_CALLER_POOL) if self.arch == "arm64"
                        else set(X86_ARGS + X86_SCRATCH + X86_CALLER_POOL))

        def _call_clob_for_param(pname, idx):
            """True iff parameter `pname` in `arg_regs[idx]` is clobbered by any non-tail call it crosses."""
            areg = arg_regs[idx]
            crossed = self.var_crossed_calls.get(pname, ())
            if not crossed:
                return False
            for c in crossed:
                c_clob = self.callee_clobbers.get(c.name, default_clob)
                if areg in c_clob:
                    return True
                # Overwritten by call argument marshaling ONLY when arg `idx` is NOT pass-through `Var(pname)`!
                if idx < len(c.args):
                    ae = c.args[idx]
                    if not (isinstance(ae, Var) and ae.name == pname):
                        return True
            return False

        used_regs = set()
        callee_pool_all = list(ARM_CALLEE_SAVED if self.arch == "arm64" else X86_CALLEE_SAVED)
        caller_pool_all = list(ARM_CALLER_POOL if self.arch == "arm64" else X86_CALLER_POOL)
        # On AArch64, v8..v15 are callee-saved (`vecIntact` in Core.lean) and remain untouched;
        # v0..v7 and v16..v29 (22 regs) are caller-saved vector registers (v30, v31 are scratch).
        vec4_pool_all = ([f"v{k}" for k in range(0, 8)] + [f"v{k}" for k in range(16, 30)]
                         if self.arch == "arm64"
                         else [f"xmm{k}" for k in range(1, 15)])
        vec16_pool_all = [f"zmm{k}" for k in range(16, 31)] + [f"zmm{k}" for k in range(1, 16)]

        # 1. Assign parameters: pass-through params preserved by their crossed callees stay in-place (zero copy/push!)
        param_regs = set()
        kept_in_place = {}  # pname -> areg (unchanged across crossed calls)
        param_needs_copy = {pname: _call_clob_for_param(pname, idx) for idx, (pname, _) in enumerate(self.params)}
        untouched_param_regs = {
            arg_regs[idx] for idx, (pname, _) in enumerate(self.params)
            if not param_needs_copy[pname]
        }
        # Union of callee clobbers across all calls for picking a safe caller-saved target for copied params
        def _clob_for_crossed(crossed, include_pass_through=True):
            if not crossed:
                return set()
            clob = set()
            for c in crossed:
                clob |= self.callee_clobbers.get(c.name, default_clob)
                for k in range(min(len(c.args), len(arg_regs))):
                    ae = c.args[k]
                    if include_pass_through and isinstance(ae, Var) and kept_in_place.get(ae.name) == arg_regs[k]:
                        continue
                    clob.add(arg_regs[k])
            return clob

        # First record pass-through / non-copied params so copied params and locals know `kept_in_place`
        for idx, (pname, _) in enumerate(self.params):
            if not param_needs_copy[pname]:
                kept_in_place[pname] = arg_regs[idx]

        copied_caller_taken = set()
        for idx, (pname, _) in enumerate(self.params):
            areg = arg_regs[idx]
            pty = self.param_types[pname]
            self.var_ty[pname] = pty
            if param_needs_copy[pname]:
                p_clob = _clob_for_crossed(self.var_crossed_calls.get(pname, ()))
                safe_caller = [r for r in caller_pool_all if r not in p_clob and r not in untouched_param_regs and r not in copied_caller_taken]
                if safe_caller:
                    cs = safe_caller[0]
                    copied_caller_taken.add(cs)
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

        # Parameter registers stay in `caller_pool_avail` guarded strictly by `interf` so once a parameter dies,
        # its entry register is deterministically reclaimed by later locals.
        caller_pool_avail = list(caller_pool_all)
        self._free_named_scalar_count = 0

        # 2. Local `buf` stack arrays (aligned)
        off = 0
        for bname, bsz, balign, _ in self.bufs:
            if balign > 1:
                off = (off + balign - 1) // balign * balign
            self.var_loc[bname] = ("buf", off)
            self.var_ty[bname] = "buf"
            self.var_map.append((bname, f"buf[{bsz}]", f"[sp+{off}]", f"align {balign}"))
            off += bsz

        # 3. Deterministic greedy graph coloring in declaration order (zero silent spills; use `stack var` explicitly!)
        callee_used_set = set(self.callee_saved)

        def _pretty_var(v):
            base = re.sub(r"^__inl_\d+_", "", v)
            base = re.sub(r"\$\d+$", "", base)
            return base

        def _refuse_spill(nm, ty, role, line, eligible_pool, live_pairs, across_call=False):
            disp = _pretty_var(nm)
            disp_tag = " (from inline fn)" if nm.startswith("__inl_") else ""
            lines = [
                f"{self.src}: line {line}: `{role} {disp}: {ty}`{disp_tag} has no free register in fn `{self.fn_name}` on {self.arch} "
                f"(all {len(eligible_pool)} eligible registers are occupied; silent stack spilling is disabled)"
            ]
            if across_call:
                lines.append(f"  note: `{disp}` is live across a function call, so only call-preserved registers ({', '.join(eligible_pool)}) are eligible")
            if live_pairs:
                lines.append("  simultaneously live variables:")
                for vnm, vreg in live_pairs:
                    tag = " [across call]" if vnm in self.live_across_call else ""
                    vdisp = _pretty_var(vnm) + (" (inlined)" if vnm.startswith("__inl_") else "")
                    lines.append(f"    {vdisp} = {vreg}{tag}")
            lines.append("  how to fix:")
            lines.append("    - narrow an earlier `let` lifetime (move it closer to use or inside the branch that uses it)")
            lines.append("    - reuse an existing `var` instead of keeping another variable live")
            lines.append(f"    - or declare a cold variable explicitly on the stack: `stack var {disp}: {ty} := ...`")
            raise HLErr("\n".join(lines))

        for nm, ty, mutable, line in self.locals_order:
            self.var_ty[nm] = ty
            role = "var" if mutable else "let"
            if nm in self.stack_vars:
                if ty == "u32x16":
                    if self.arch != "x86_64":
                        raise HLErr(f"{self.src}: `u32x16` is only available on `x86_64` (AVX-512)")
                    self.uses_zmm = True
                    off = (off + 63) // 64 * 64
                    sz = 64
                elif ty == "u32x4":
                    off = (off + 15) // 16 * 16
                    sz = 16
                else:
                    off = (off + 7) // 8 * 8
                    sz = 8
                self.var_loc[nm] = ("spill", off)
                self.var_map.append((nm, f"stack {role} {ty}", f"[sp+{off}]", "stack var"))
                off += sz
                continue

            forbidden = {
                self.var_loc[nb][1]
                for nb in interf.get(nm, ())
                if nb in self.var_loc and self.var_loc[nb][0] == "reg"
            }

            if ty in ("u64", "u8"):
                # Exact per-variable call clobbers: use call-safe caller-saved regs FIRST (0 pushes!), then callee-saved!
                crossed = self.var_crossed_calls.get(nm, ())
                across_call = bool(crossed)
                if across_call:
                    nm_clob = _clob_for_crossed(crossed)
                    safe_caller = [r for r in caller_pool_avail if r not in nm_clob]
                    order = safe_caller + callee_pool_all
                else:
                    order = caller_pool_avail + callee_pool_all
                reg = next((r for r in order if r not in forbidden), None)
                if reg is not None:
                    if reg in callee_pool_all and reg not in callee_used_set:
                        callee_used_set.add(reg)
                        self.callee_saved.append(reg)
                    used_regs.add(reg)
                    self.var_loc[nm] = ("reg", reg)
                    self.var_map.append((nm, f"{role} {ty}", reg, ""))
                else:
                    live_pairs = [
                        (nb, self.var_loc[nb][1])
                        for nb in sorted(interf.get(nm, ()))
                        if nb in self.var_loc and self.var_loc[nb][0] == "reg" and self.var_loc[nb][1] in order
                    ]
                    _refuse_spill(nm, ty, role, line, order, live_pairs, across_call=across_call)
            elif ty == "u32x4":
                vreg = next((r for r in vec4_pool_all if r not in forbidden), None)
                if vreg is not None:
                    self.var_loc[nm] = ("reg", vreg)
                    self.var_map.append((nm, f"{role} u32x4", vreg, ""))
                else:
                    live_pairs = [
                        (nb, self.var_loc[nb][1])
                        for nb in sorted(interf.get(nm, ()))
                        if nb in self.var_loc and self.var_loc[nb][0] == "reg" and self.var_loc[nb][1] in vec4_pool_all
                    ]
                    _refuse_spill(nm, ty, role, line, vec4_pool_all, live_pairs)
            elif ty == "u32x16":
                if self.arch != "x86_64":
                    raise HLErr(f"{self.src}: `u32x16` is only available on `x86_64` (AVX-512)")
                self.uses_zmm = True
                vreg = next((r for r in vec16_pool_all if r not in forbidden), None)
                if vreg is not None:
                    self.var_loc[nm] = ("reg", vreg)
                    self.var_map.append((nm, f"{role} u32x16", vreg, ""))
                else:
                    live_pairs = [
                        (nb, self.var_loc[nb][1])
                        for nb in sorted(interf.get(nm, ()))
                        if nb in self.var_loc and self.var_loc[nb][0] == "reg" and self.var_loc[nb][1] in vec16_pool_all
                    ]
                    _refuse_spill(nm, ty, role, line, vec16_pool_all, live_pairs)

        self.spills = 0
        all_named_scalar = set(caller_pool_all) | set(callee_pool_all)
        self._free_named_scalar_count = len(all_named_scalar - used_regs)

        # 4. Exact stack frame layout & alignment
        if self.arch == "x86_64":
            push_bytes = 8 * len(self.callee_saved)
            need_align16 = self.uses_zmm or any(b[2] >= 16 for b in self.bufs)
            raw_frame = (off + 15) // 16 * 16 if (off > 0 and need_align16) else ((off + 7) // 8 * 8 if off > 0 else 0)
            if self.has_calls and need_align16 and ((push_bytes + raw_frame + 8) % 16 != 0):
                raw_frame += 8
            self.frame_bytes = raw_frame
            self.total_stack = push_bytes + raw_frame + (8 if self.has_calls else 0)
        else:
            # AArch64: save x30 (if has_calls) + callee_saved scalars + local frame.
            save_slots = (1 if self.has_calls else 0) + len(self.callee_saved)
            save_bytes = save_slots * 8
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
        s = text.strip()
        if s and not s.startswith("@") and not s.startswith("place ") and not s.startswith("fact ") and not s.startswith("wrote ") and not s.startswith("decreases ") and s not in ("{", "}", "wrap"):
            self._last_place_end = None
        self.out_lines.append((line, text))

    def fresh_label(self, prefix):
        self.lbl_seq += 1
        return f"@{prefix}_{self.lbl_seq}"

    def _scratch_pool(self):
        return ARM_SCRATCH if self.arch == "arm64" else X86_SCRATCH

    @contextlib.contextmanager
    def _temp_reg(self, line=0, avoid=(), why="intermediate value"):
        """Wirth scratch-register stack: allocate one free scratch GPR and release it on exit,
        or fail immediately with a live-register snapshot asking the cOder to bind a `let`."""
        pool = self._scratch_pool()
        r = next((cand for cand in pool if cand not in self._live_temps and cand not in avoid), None)
        if r is None:
            lines = [
                f"{self.src}: line {line}: expression needs another temporary register on {self.arch} "
                f"(fixed scratch pool: {', '.join(pool)})"
            ]
            if self._live_temps:
                lines.append("  currently held scratch registers:")
                for treg in pool:
                    if treg in self._live_temps:
                        lines.append(f"    {treg} holds: {self._live_temps[treg]}")
            if avoid:
                lines.append(f"  reserved for output/operand: {', '.join(avoid)}")
            lines.append(f"  needed for: {why}")
            lines.append(f"  unused named scalar registers in fn `{self.fn_name}`: {self._free_named_scalar_count}")
            lines.append(f"  fix: bind one subexpression with `let tmp := ...` before line {line}.")
            raise HLErr("\n".join(lines))
        self._live_temps[r] = why
        try:
            yield r
        finally:
            self._live_temps.pop(r, None)

    @contextlib.contextmanager
    def _protect(self, reg, why="held operand"):
        """Hold `reg` in `_live_temps` while nested subexpressions run if `reg` belongs to the scratch pool."""
        added = reg in self._scratch_pool() and reg not in self._live_temps
        if added:
            self._live_temps[reg] = why
        try:
            yield reg
        finally:
            if added:
                self._live_temps.pop(reg, None)

    @contextlib.contextmanager
    def _hold_expr(self, e, avoid=(), why=None):
        """Yield a register holding scalar expr `e` (zero-copy if already in a named reg not in `avoid`),
        protected in `_live_temps` until the `with` block exits."""
        desc = why or f"`{_expr_brief(e)}`"
        if isinstance(e, RawReg) and e.reg not in avoid:
            with self._protect(e.reg, why=desc):
                yield e.reg
            return
        if isinstance(e, Var) and e.name in self.var_loc and self.var_loc[e.name][0] == "reg":
            vr = self.var_loc[e.name][1]
            if vr not in avoid:
                yield vr
                return
        with self._temp_reg(getattr(e, "line", 0), avoid=avoid, why=desc) as tr:
            self._eval_scalar(e, tr)
            yield tr

    def _expr_reads_reg(self, e, reg):
        """True if scalar expression `e` reads any variable or buffer base currently located in `reg`."""
        if isinstance(e, Var):
            return self.var_loc.get(e.name) == ("reg", reg)
        if isinstance(e, RawReg):
            return e.reg == reg
        if isinstance(e, IndexLoad):
            return self.var_loc.get(e.buf) == ("reg", reg) or self._expr_reads_reg(e.idx, reg)
        if isinstance(e, (BinOp, Cmp, BoolOp)):
            return self._expr_reads_reg(e.left, reg) or self._expr_reads_reg(e.right, reg)
        if isinstance(e, NotOp):
            return self._expr_reads_reg(e.expr, reg)
        if isinstance(e, Select):
            return (
                self._expr_reads_reg(e.cond, reg)
                or self._expr_reads_reg(e.then_e, reg)
                or self._expr_reads_reg(e.else_e, reg)
            )
        if isinstance(e, Call):
            return any(self._expr_reads_reg(a, reg) for a in e.args)
        return False

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
                self.emit(line, f"add sp, sp, {self.frame_bytes}")

    def _emit_imm(self, line, dst, val):
        if self.arch == "x86_64":
            x = val & ((1 << 64) - 1)
            if x < (1 << 31):
                self.emit(line, f"mov {dst}, {x}")
                return
            # Build arbitrary 64-bit constant using mov + shl + add (all immediates fit signed 32-bit in x86.tab)
            chunks = []
            while x >= (1 << 31):
                chunks.append((31, x & ((1 << 31) - 1)))
                x >>= 31
            self.emit(line, f"mov {dst}, {x}")
            pending_sh = 0
            for sh, lo in reversed(chunks):
                pending_sh += sh
                if lo:
                    self.emit(line, f"shl {dst}, {pending_sh}")
                    self.emit(line, f"add {dst}, {lo}")
                    pending_sh = 0
            if pending_sh:
                self.emit(line, f"shl {dst}, {pending_sh}")
        else:
            x = val & ((1 << 64) - 1)
            if x <= 65535:
                self.emit(line, f"mov {dst}, {x}")
                return
            # Build arbitrary 64-bit constant using mov + lsl + add (zero extra scratch regs, all in arm64.tab)
            chunks = []
            while x > 65535:
                chunks.append((12, x & 0xfff))
                x >>= 12
            self.emit(line, f"mov {dst}, {x}")
            pending_sh = 0
            for sh, lo in reversed(chunks):
                pending_sh += sh
                if lo:
                    self.emit(line, f"lsl {dst}, {dst}, {pending_sh}")
                    self.emit(line, f"add {dst}, {dst}, {lo}")
                    pending_sh = 0
            if pending_sh:
                self.emit(line, f"lsl {dst}, {dst}, {pending_sh}")

    def _load_var(self, line, name, dst):
        if name not in self.var_loc:
            raise HLErr(f"{self.src}: line {line}: unknown variable `{name}`")
        kind, val = self.var_loc[name]
        if kind == "reg":
            if val != dst:
                ty = self.var_ty[name]
                if ty in ("u32x4", "u32x16"):
                    if not (dst.startswith(("xmm", "zmm", "v"))):
                        raise HLErr(
                            f"{self.src}: line {line}: vector variable `{name}` (type `{ty}`) cannot be loaded "
                            f"into scalar register `{dst}`"
                        )
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
            self.emit(line, f"vmovdqu32 {dst}, [rsp + {val}]")
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
            self.emit(line, f"vmovdqu32 [rsp + {val}], {src_reg}")
        else:
            if self.arch == "x86_64":
                self.emit(line, f"mov qword ptr [rsp + {val}], {src_reg}")
            else:
                self.emit(line, f"str {src_reg}, [sp, {val}]")

    @contextlib.contextmanager
    def _emit_addr_held(self, line, buf_name, idx_e, avoid=(), reuse_dst=None, allow_sp=True, align_req=1):
        """Compute `(base_reg, const_offset)` for `buf[idx_e]`, protecting any allocated scratch `base_reg`.
        If `reuse_dst` is a scratch register allocated for the enclosing load (not read by `buf`/`idx_e`),
        evaluate `idx_e` directly into `reuse_dst` so an empty output register is never wasted.
        On `arm64`, `allow_sp=False` materializes `add r, sp, disp` because `arm64.tab` only has
        `[sp, N]` forms for 64-bit (`ldr`/`str`) and 128-bit (`ldr q`/`str q`), not `w` or byte loads/stores;
        `align_req` ensures immediate displacements on `arm64` are multiples of 4/8/16 (materializing
        `add tmp, base, disp` with offset 0 whenever `disp % align_req != 0` or `disp < 0`)."""
        if buf_name not in self.var_loc:
            raise HLErr(f"{self.src}: line {line}: unknown buffer `{buf_name}`")
        def _fold_const(ex):
            if isinstance(ex, BinOp):
                l, r = _fold_const(ex.left), _fold_const(ex.right)
                if isinstance(l, Num) and isinstance(r, Num):
                    v = _const_eval_binop(ex.op, l.val, r.val)
                    if v is not None and 0 <= v < (1 << 64):
                        return Num(v, ex.line)
                return BinOp(ex.op, l, r, ex.line)
            return ex
        idx_e = _fold_const(idx_e)
        bkind, bval = self.var_loc[buf_name]
        addr_why = f"address of `{buf_name}[{_expr_brief(idx_e)}]`"
        can_reuse = (
            reuse_dst is not None
            and reuse_dst in self._scratch_pool()
            and reuse_dst not in avoid
            and (bkind == "buf" or bval != reuse_dst)
            and not self._expr_reads_reg(idx_e, reuse_dst)
        )
        def _arm_needs_mat(d):
            return self.arch == "arm64" and d != 0 and (d < 0 or (align_req > 1 and d % align_req != 0) or d > 4095)
        if bkind == "buf":
            if isinstance(idx_e, Num):
                total_off = bval + idx_e.val
                if (allow_sp and not _arm_needs_mat(total_off)) or self.arch != "arm64":
                    yield ("sp" if self.arch == "arm64" else "rsp"), total_off
                    return
                if can_reuse and 0 <= total_off <= 4095:
                    self.emit(line, f"add {reuse_dst}, sp, {total_off}")
                    yield reuse_dst, 0
                    return
                with self._temp_reg(line, avoid=avoid, why=addr_why) as addr_reg:
                    if 0 <= total_off <= 4095:
                        self.emit(line, f"add {addr_reg}, sp, {total_off}")
                    else:
                        self._emit_imm(line, addr_reg, total_off)
                        self.emit(line, f"add {addr_reg}, sp, {addr_reg}")
                    yield addr_reg, 0
                return
            with self._hold_expr(idx_e, why=f"index `{_expr_brief(idx_e)}` of `{buf_name}`") as ireg:
                with self._temp_reg(line, avoid=avoid, why=addr_why) as addr_reg:
                    if self.arch == "x86_64":
                        self.emit(line, f"lea {addr_reg}, [rsp + {bval}]")
                        self.emit(line, f"lea {addr_reg}, [{addr_reg} + {ireg}]")
                    else:
                        self.emit(line, f"add {addr_reg}, sp, {bval}")
                        self.emit(line, f"add {addr_reg}, {addr_reg}, {ireg}")
                    yield addr_reg, 0
            return
        base_reg = bval
        if isinstance(idx_e, Num):
            disp = idx_e.val
            if not _arm_needs_mat(disp):
                yield base_reg, disp
                return
            if can_reuse and 0 <= disp <= 4095:
                self.emit(line, f"add {reuse_dst}, {base_reg}, {disp}")
                yield reuse_dst, 0
                return
            with self._temp_reg(line, avoid=avoid, why=addr_why) as addr_reg:
                if 0 <= disp <= 4095:
                    self.emit(line, f"add {addr_reg}, {base_reg}, {disp}")
                else:
                    self._emit_imm(line, addr_reg, disp)
                    self.emit(line, f"add {addr_reg}, {base_reg}, {addr_reg}")
                yield addr_reg, 0
            return
        if isinstance(idx_e, BinOp) and idx_e.op == "+" and isinstance(idx_e.right, Num):
            disp = idx_e.right.val
            if can_reuse and not (isinstance(idx_e.left, Var) and self.var_loc.get(idx_e.left.name, (None,))[0] == "reg"):
                self._eval_scalar(idx_e.left, reuse_dst)
                if self.arch == "x86_64":
                    self.emit(line, f"lea {reuse_dst}, [{base_reg} + {reuse_dst} + {disp}]")
                    yield reuse_dst, 0
                else:
                    self.emit(line, f"add {reuse_dst}, {base_reg}, {reuse_dst}")
                    if _arm_needs_mat(disp):
                        self._emit_add_sub(line, "+", reuse_dst, reuse_dst, Num(disp, line))
                        yield reuse_dst, 0
                    else:
                        yield reuse_dst, disp
                return
            with self._hold_expr(idx_e.left, why=f"index `{_expr_brief(idx_e.left)}` of `{buf_name}`") as ireg:
                if ireg in self._scratch_pool() and ireg not in avoid:
                    if self.arch == "x86_64":
                        self.emit(line, f"lea {ireg}, [{base_reg} + {ireg} + {disp}]")
                        yield ireg, 0
                    else:
                        self.emit(line, f"add {ireg}, {base_reg}, {ireg}")
                        if _arm_needs_mat(disp):
                            self._emit_add_sub(line, "+", ireg, ireg, Num(disp, line))
                            yield ireg, 0
                        else:
                            yield ireg, disp
                    return
                with self._temp_reg(line, avoid=avoid, why=addr_why) as addr_reg:
                    if self.arch == "x86_64":
                        self.emit(line, f"lea {addr_reg}, [{base_reg} + {ireg} + {disp}]")
                        yield addr_reg, 0
                    else:
                        self.emit(line, f"add {addr_reg}, {base_reg}, {ireg}")
                        if _arm_needs_mat(disp):
                            self._emit_add_sub(line, "+", addr_reg, addr_reg, Num(disp, line))
                            yield addr_reg, 0
                        else:
                            yield addr_reg, disp
            return
        if can_reuse and not (isinstance(idx_e, Var) and self.var_loc.get(idx_e.name, (None,))[0] == "reg"):
            self._eval_scalar(idx_e, reuse_dst)
            if self.arch == "x86_64":
                self.emit(line, f"lea {reuse_dst}, [{base_reg} + {reuse_dst}]")
            else:
                self.emit(line, f"add {reuse_dst}, {base_reg}, {reuse_dst}")
            yield reuse_dst, 0
            return
        with self._hold_expr(idx_e, why=f"index `{_expr_brief(idx_e)}` of `{buf_name}`") as ireg:
            if ireg in self._scratch_pool() and ireg not in avoid:
                if self.arch == "x86_64":
                    self.emit(line, f"lea {ireg}, [{base_reg} + {ireg}]")
                else:
                    self.emit(line, f"add {ireg}, {base_reg}, {ireg}")
                yield ireg, 0
                return
            with self._temp_reg(line, avoid=avoid, why=addr_why) as addr_reg:
                if self.arch == "x86_64":
                    self.emit(line, f"lea {addr_reg}, [{base_reg} + {ireg}]")
                else:
                    self.emit(line, f"add {addr_reg}, {base_reg}, {ireg}")
                yield addr_reg, 0

    def _emit_scalar_store(self, line, width, base, disp, val_r):
        if width == "u8":
            if self.arch == "x86_64":
                d_str = f" + {disp}" if disp else ""
                self.emit(line, f"mov byte ptr [{base}{d_str}], {X86_REG8[val_r]}")
            else:
                self.emit(line, f"strb {_arm_w(val_r)}, [{base}, {disp}]")
        elif width == "u32":
            if self.arch == "x86_64":
                d_str = f" + {disp}" if disp else ""
                self.emit(line, f"mov dword ptr [{base}{d_str}], {X86_REG32[val_r]}")
            else:
                self.emit(line, f"str {_arm_w(val_r)}, [{base}, {disp}]")
        elif width == "u64":
            if self.arch == "x86_64":
                d_str = f" + {disp}" if disp else ""
                self.emit(line, f"mov qword ptr [{base}{d_str}], {val_r}")
            else:
                self.emit(line, f"str {val_r}, [{base}, {disp}]")

    def _emit_add_sub(self, line, op, dst, lhs_reg, rhs_e, wrap=False):
        """Emit exact or wrapping add/sub into `dst` (with `lhs_reg` protected across `rhs_e` evaluation)."""
        is_add = op in ("+", "+%")
        mn = "add" if is_add else "sub"
        with self._protect(lhs_reg):
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
                        with self._temp_reg(line, avoid=(dst,)) as tr:
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
                        with self._temp_reg(line, avoid=(dst, lhs_reg)) as tr:
                            self._emit_imm(line, tr, k)
                            if wrap:
                                self.emit(line, "wrap")
                            self.emit(line, f"{mn} {dst}, {lhs_reg}, {tr}")
                return
            avoid_r = (dst,) if (self.arch == "x86_64" and lhs_reg != dst) else ()
            with self._hold_expr(rhs_e, avoid=avoid_r) as rreg:
                if self.arch == "x86_64":
                    if lhs_reg != dst:
                        self.emit(line, f"mov {dst}, {lhs_reg}")
                    if wrap:
                        self.emit(line, "wrap")
                    self.emit(line, f"{mn} {dst}, {rreg}")
                else:
                    if wrap:
                        self.emit(line, "wrap")
                    self.emit(line, f"{mn} {dst}, {lhs_reg}, {rreg}")

    def _emit_const_mul(self, line, dst, lhs_reg, k):
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
        bits = [b for b in range(64) if (k >> b) & 1]
        hi_b = bits[-1]
        rest_bits = list(reversed(bits[:-1]))

        def emit_body(base):
            if self.arch == "x86_64":
                self.emit(line, f"mov {dst}, {base}")
                if hi_b > 0:
                    self.emit(line, f"shl {dst}, {hi_b}")
            else:
                if hi_b > 0:
                    self.emit(line, f"lsl {dst}, {base}, {hi_b}")
                else:
                    self.emit(line, f"mov {dst}, {base}")
            if any(b > 0 for b in rest_bits):
                with self._protect(dst):
                    with self._temp_reg(line, avoid=(dst, base)) as t2:
                        for b in rest_bits:
                            if b == 0:
                                if self.arch == "x86_64":
                                    self.emit(line, f"add {dst}, {base}")
                                else:
                                    self.emit(line, f"add {dst}, {dst}, {base}")
                            elif self.arch == "x86_64":
                                self.emit(line, f"mov {t2}, {base}")
                                self.emit(line, f"shl {t2}, {b}")
                                self.emit(line, f"add {dst}, {t2}")
                            else:
                                self.emit(line, f"lsl {t2}, {base}, {b}")
                                self.emit(line, f"add {dst}, {dst}, {t2}")
            else:
                for b in rest_bits:
                    if self.arch == "x86_64":
                        self.emit(line, f"add {dst}, {base}")
                    else:
                        self.emit(line, f"add {dst}, {dst}, {base}")

        if lhs_reg == dst:
            with self._protect(dst):
                with self._temp_reg(line, avoid=(dst,)) as base:
                    self.emit(line, f"mov {base}, {lhs_reg}")
                    emit_body(base)
        else:
            with self._protect(lhs_reg):
                emit_body(lhs_reg)

    def _eval_scalar(self, e, dst):
        """Evaluate scalar expression `e` into register `dst` using the Wirth scratch-register stack."""
        if isinstance(e, RawReg):
            if e.reg != dst:
                self.emit(e.line, f"mov {dst}, {e.reg}")
            return
        if isinstance(e, Num):
            self._emit_imm(e.line, dst, e.val)
            return
        if isinstance(e, Var):
            ty = self.var_ty.get(e.name)
            if ty in ("u32x4", "u32x16"):
                raise HLErr(
                    f"{self.src}: line {e.line}: vector variable `{e.name}` (type `{ty}`) cannot be used "
                    f"in a scalar `u64` context (keep it in `{ty}` vector operations or store with `.{ty}(off) := {e.name}`)"
                )
            self._load_var(e.line, e.name, dst)
            return
        if isinstance(e, IndexLoad):
            reuse = dst if e.width in ("u8", "u32", "u64") else None
            allow_sp = (self.arch != "arm64" or e.width == "u64")
            align_req = {"u32": 4, "u64": 8}.get(e.width, 1)
            with self._emit_addr_held(e.line, e.buf, e.idx, reuse_dst=reuse, allow_sp=allow_sp, align_req=align_req) as (base, disp):
                if e.width == "u8":
                    if self.arch == "x86_64":
                        d_str = f" + {disp}" if disp else ""
                        self.emit(e.line, f"movzx {X86_REG32[dst]}, byte ptr [{base}{d_str}]")
                    else:
                        self.emit(e.line, f"ldrb {_arm_w(dst)}, [{base}, {disp}]")
                elif e.width == "u16":
                    with self._protect(dst):
                        with self._temp_reg(e.line, avoid=(dst, base)) as t_hi:
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
                lhs_e, rhs_e = e.left, e.right
                if isinstance(lhs_e, Var) and self.var_loc.get(lhs_e.name, (None,))[0] == "reg":
                    lreg = self.var_loc[lhs_e.name][1]
                    self._emit_add_sub(e.line, e.op, dst, lreg, rhs_e, wrap=wrap)
                elif self._expr_reads_reg(rhs_e, dst):
                    with self._temp_reg(e.line, avoid=(dst,), why=f"left side `{_expr_brief(lhs_e)}` of `{e.op}`") as tr:
                        self._eval_scalar(lhs_e, tr)
                        self._emit_add_sub(e.line, e.op, dst, tr, rhs_e, wrap=wrap)
                else:
                    self._eval_scalar(lhs_e, dst)
                    with self._protect(dst, why=f"left side `{_expr_brief(lhs_e)}` of `{e.op}`"):
                        self._emit_add_sub(e.line, e.op, dst, dst, rhs_e, wrap=wrap)
                return
            if e.op == "*":
                if isinstance(e.right, Num):
                    fac, k = e.left, e.right.val
                elif isinstance(e.left, Num):
                    fac, k = e.right, e.left.val
                else:
                    raise HLErr(f"{self.src}: line {e.line}: scalar `*` requires a constant factor (use shifts/adds for general multiplication)")
                if isinstance(fac, Var) and self.var_loc.get(fac.name, (None,))[0] == "reg":
                    self._emit_const_mul(e.line, dst, self.var_loc[fac.name][1], k)
                else:
                    self._eval_scalar(fac, dst)
                    self._emit_const_mul(e.line, dst, dst, k)
                return
            if e.op in ("/", "%"):
                if not isinstance(e.right, Num) or e.right.val <= 0 or (e.right.val & (e.right.val - 1)) != 0:
                    raise HLErr(
                        f"{self.src}: line {e.line}: scalar `{e.op}` requires a power-of-two constant "
                        f"({'use >> k' if e.op == '/' else 'use & (m - 1)'})"
                    )
                if e.op == "/":
                    self._eval_scalar(BinOp(">>", e.left, Num(e.right.val.bit_length() - 1, e.line), e.line), dst)
                else:
                    self._eval_scalar(BinOp("&", e.left, Num(e.right.val - 1, e.line), e.line), dst)
                return
            if e.op in ("<<", ">>"):
                if not isinstance(e.right, Num):
                    raise HLErr(f"{self.src}: line {e.line}: shift amount must be a constant")
                k = e.right.val
                if isinstance(e.left, Var) and self.var_loc.get(e.left.name, (None,))[0] == "reg":
                    lreg = self.var_loc[e.left.name][1]
                else:
                    self._eval_scalar(e.left, dst)
                    lreg = dst
                if k == 0:
                    if lreg != dst:
                        self.emit(e.line, f"mov {dst}, {lreg}")
                    return
                if self.arch == "x86_64":
                    if lreg != dst:
                        self.emit(e.line, f"mov {dst}, {lreg}")
                    self.emit(e.line, f"{'shl' if e.op == '<<' else 'shr'} {dst}, {k}")
                else:
                    self.emit(e.line, f"{'lsl' if e.op == '<<' else 'lsr'} {dst}, {lreg}, {k}")
                return
            if e.op in ("&", "|"):
                lhs_e, rhs_e = e.left, e.right

                def emit_bitop(lreg):
                    with self._protect(lreg, why=f"left side `{_expr_brief(lhs_e)}` of `{e.op}`"):
                        if self.arch == "x86_64":
                            mn = "and" if e.op == "&" else "or"
                            if isinstance(rhs_e, Num):
                                k = rhs_e.val
                                if lreg != dst:
                                    self.emit(e.line, f"mov {dst}, {lreg}")
                                if -(1 << 31) <= k < (1 << 31):
                                    self.emit(e.line, f"{mn} {dst}, {k}")
                                else:
                                    with self._temp_reg(e.line, avoid=(dst,), why=f"immediate `{k}` for `{e.op}`") as tr2:
                                        self._emit_imm(e.line, tr2, k)
                                        self.emit(e.line, f"{mn} {dst}, {tr2}")
                            else:
                                avoid_r = (dst,) if lreg != dst else ()
                                with self._hold_expr(rhs_e, avoid=avoid_r, why=f"right side `{_expr_brief(rhs_e)}` of `{e.op}`") as rreg:
                                    if lreg != dst:
                                        self.emit(e.line, f"mov {dst}, {lreg}")
                                    self.emit(e.line, f"{mn} {dst}, {rreg}")
                        else:
                            mn = "and" if e.op == "&" else "orr"
                            if isinstance(rhs_e, Num):
                                with self._temp_reg(e.line, avoid=(dst, lreg), why=f"immediate `{rhs_e.val}` for `{e.op}`") as tr2:
                                    self._emit_imm(e.line, tr2, rhs_e.val)
                                    self.emit(e.line, f"{mn} {dst}, {lreg}, {tr2}")
                            else:
                                with self._hold_expr(rhs_e, why=f"right side `{_expr_brief(rhs_e)}` of `{e.op}`") as rreg:
                                    self.emit(e.line, f"{mn} {dst}, {lreg}, {rreg}")

                if isinstance(lhs_e, Var) and self.var_loc.get(lhs_e.name, (None,))[0] == "reg":
                    emit_bitop(self.var_loc[lhs_e.name][1])
                elif self._expr_reads_reg(rhs_e, dst):
                    with self._temp_reg(e.line, avoid=(dst,), why=f"left side `{_expr_brief(lhs_e)}` of `{e.op}`") as tr:
                        self._eval_scalar(lhs_e, tr)
                        emit_bitop(tr)
                else:
                    self._eval_scalar(lhs_e, dst)
                    emit_bitop(dst)
                return
            if e.op == "^":
                raise HLErr(
                    f"{self.src}: line {e.line}: bitwise XOR (`^`) is supported on vector types (`u32x4`, `u32x16`); "
                    f"for scalar `u64` values use `&`, `|`, `<<`, `>>`, `+`, `-` (or annotate vector locals `: u32x4`)"
                )
            raise HLErr(f"{self.src}: line {e.line}: unsupported scalar operator `{e.op}`")
        if isinstance(e, Select):
            self._eval_select(e, dst)
            return
        if isinstance(e, Call):
            self._emit_call(e, dst)
            return
        raise HLErr(f"{self.src}: line {getattr(e, 'line', 0)}: unsupported scalar expression")

    def _emit_cmp(self, line, left_e, right_e):
        """Emit `cmp a, b` cleanly via the scratch-register stack."""
        with self._hold_expr(left_e) as lreg:
            if isinstance(right_e, Num):
                k = right_e.val
                if self.arch == "x86_64" and -(1 << 31) <= k < (1 << 31):
                    self.emit(line, f"cmp {lreg}, {k}")
                    return
                if self.arch == "arm64" and 0 <= k <= 4095:
                    self.emit(line, f"cmp {lreg}, {k}")
                    return
                with self._temp_reg(line, avoid=(lreg,)) as tr:
                    self._emit_imm(line, tr, k)
                    self.emit(line, f"cmp {lreg}, {tr}")
                return
            with self._hold_expr(right_e) as rreg:
                self.emit(line, f"cmp {lreg}, {rreg}")

    def _speculative_wrap(self, e):
        """Convert speculative `+`/`-` inside `select(cond, T, F)` arms into wrapping `+%`/`-%`
        so dead arms (e.g. `c - 97` when `c == 65`) never fail overflow/underflow before `cmov`/`csel`."""
        if isinstance(e, BinOp):
            op = "+%" if e.op == "+" else ("-%" if e.op == "-" else e.op)
            return BinOp(op, self._speculative_wrap(e.left), self._speculative_wrap(e.right), e.line)
        if isinstance(e, Select):
            return Select(e.cond, self._speculative_wrap(e.then_e), self._speculative_wrap(e.else_e), e.line)
        return e

    def _eval_select(self, sel, dst):
        """Lower `select(cond, t_expr, f_expr)` branchlessly to `cmp + cmov* / csel`
        in one fixed deterministic order: `else_e`, then `then_e`, then `cmp`, then `cmov`/`csel`."""
        sel = Select(sel.cond, self._speculative_wrap(sel.then_e), self._speculative_wrap(sel.else_e), sel.line)
        c = sel.cond
        if isinstance(c, NotOp):
            self._eval_select(Select(c.expr, sel.else_e, sel.then_e, sel.line), dst)
            return
        if isinstance(c, BoolOp):
            if c.op == "&&":
                if isinstance(sel.else_e, (Var, Num, RawReg)):
                    inner = Select(c.right, sel.then_e, sel.else_e, sel.line)
                    self._eval_select(Select(c.left, inner, sel.else_e, sel.line), dst)
                    return
                need_tmp_out = (
                    self._expr_reads_reg(c.left, dst)
                    or self._expr_reads_reg(c.right, dst)
                    or self._expr_reads_reg(sel.then_e, dst)
                )
                if need_tmp_out:
                    with self._temp_reg(sel.line, avoid=(dst,), why=f"else arm `{_expr_brief(sel.else_e)}` of `select`") as out_reg:
                        self._eval_scalar(sel.else_e, out_reg)
                        inner = Select(c.right, sel.then_e, RawReg(out_reg, sel.line), sel.line)
                        self._eval_select(Select(c.left, inner, RawReg(out_reg, sel.line), sel.line), out_reg)
                        self.emit(sel.line, f"mov {dst}, {out_reg}")
                else:
                    self._eval_scalar(sel.else_e, dst)
                    with self._protect(dst, why=f"else arm `{_expr_brief(sel.else_e)}` of `select`"):
                        inner = Select(c.right, sel.then_e, RawReg(dst, sel.line), sel.line)
                        self._eval_select(Select(c.left, inner, RawReg(dst, sel.line), sel.line), dst)
                return
            inner = Select(c.right, sel.then_e, sel.else_e, sel.line)
            self._eval_select(Select(c.left, sel.then_e, inner, sel.line), dst)
            return
        assert isinstance(c, Cmp)
        cmp_l, cmp_op, cmp_r = c.left, c.op, c.right
        if isinstance(cmp_l, Num) and not isinstance(cmp_r, Num):
            flip = {"==": "==", "!=": "!=", "<": ">", "<=": ">=", ">": "<", ">=": "<="}[cmp_op]
            cmp_l, cmp_op, cmp_r = cmp_r, flip, cmp_l

        else_is_dst = (
            (isinstance(sel.else_e, Var) and self.var_loc.get(sel.else_e.name) == ("reg", dst))
            or (isinstance(sel.else_e, RawReg) and sel.else_e.reg == dst)
        )
        dst_read_later = (
            self._expr_reads_reg(cmp_l, dst)
            or self._expr_reads_reg(cmp_r, dst)
            or self._expr_reads_reg(sel.then_e, dst)
        )

        def emit_into(out_reg):
            out_is_else = (
                (isinstance(sel.else_e, Var) and self.var_loc.get(sel.else_e.name) == ("reg", out_reg))
                or (isinstance(sel.else_e, RawReg) and sel.else_e.reg == out_reg)
            )
            if not out_is_else:
                self._eval_scalar(sel.else_e, out_reg)
            with self._protect(out_reg, why=f"else arm `{_expr_brief(sel.else_e)}` of `select`"):
                with self._hold_expr(sel.then_e, avoid=(out_reg,), why=f"then arm `{_expr_brief(sel.then_e)}` of `select`") as t_reg:
                    self._emit_cmp(sel.line, cmp_l, cmp_r)
                    if self.arch == "x86_64":
                        cc = {"==": "e", "!=": "ne", "<": "b", "<=": "be", ">": "a", ">=": "ae"}[cmp_op]
                        self.emit(sel.line, f"cmov{cc} {out_reg}, {t_reg}")
                    else:
                        cc = {"==": "eq", "!=": "ne", "<": "lo", "<=": "ls", ">": "hi", ">=": "hs"}[cmp_op]
                        self.emit(sel.line, f"csel {out_reg}, {t_reg}, {out_reg}, {cc}")

        if not else_is_dst and dst_read_later:
            with self._temp_reg(sel.line, avoid=(dst,), why=f"result of `select({_expr_brief(c)}, ...)`") as out_reg:
                emit_into(out_reg)
                self.emit(sel.line, f"mov {dst}, {out_reg}")
        else:
            emit_into(dst)

    def _emit_branch(self, cond, target_lbl, jump_if_true):
        """Emit macro-fused `cmp` + conditional branch (handling `&&`, `||`, `!`)."""
        if isinstance(cond, NotOp):
            self._emit_branch(cond.expr, target_lbl, not jump_if_true)
            return
        if isinstance(cond, BoolOp):
            if (cond.op == "&&" and not jump_if_true) or (cond.op == "||" and jump_if_true):
                self._emit_branch(cond.left, target_lbl, jump_if_true)
                self._emit_branch(cond.right, target_lbl, jump_if_true)
            else:
                fall = self.fresh_label("sc")
                self._emit_branch(cond.left, fall, not jump_if_true)
                self._emit_branch(cond.right, target_lbl, jump_if_true)
                self.emit(cond.line, f"{fall}:")
            return
        assert isinstance(cond, Cmp)
        cmp_l, cmp_op, cmp_r = cond.left, cond.op, cond.right
        if isinstance(cmp_l, Num) and not isinstance(cmp_r, Num):
            flip = {"==": "==", "!=": "!=", "<": ">", "<=": ">=", ">": "<", ">=": "<="}[cmp_op]
            cmp_l, cmp_op, cmp_r = cmp_r, flip, cmp_l
        if not jump_if_true:
            cmp_op = {"==": "!=", "!=": "==", "<": ">=", "<=": ">", ">": "<=", ">=": "<"}[cmp_op]
        self._emit_cmp(cond.line, cmp_l, cmp_r)
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

        parked_temps = []
        try:
            while pending:
                progressed = False
                for k in range(len(pending)):
                    areg, ae, _ = pending[k]
                    if not any(areg in pending[j][2] for j in range(len(pending)) if j != k):
                        self._eval_scalar(ae, areg)
                        pending.pop(k)
                        progressed = True
                        break
                if not progressed:
                    park_idx = next((k for k, (_, ae, _) in enumerate(pending) if isinstance(ae, Var)), 0)
                    park_reg = pending[park_idx][0]
                    pool = self._scratch_pool()
                    tmp = next((cand for cand in pool if cand not in self._live_temps), None)
                    if tmp is None:
                        raise HLErr(f"{self.src}: line {call.line}: call argument cycle exceeds scratch pool")
                    self._live_temps[tmp] = f"parked arg reg `{park_reg}` for call `{call.name}`"
                    parked_temps.append(tmp)
                    self.emit(call.line, f"mov {tmp}, {park_reg}")
                    for j in range(len(pending)):
                        if park_reg in pending[j][2]:
                            pending[j][1] = _replace_reg_var_expr(pending[j][1], self.var_loc, park_reg, tmp)
                            pending[j][2].discard(park_reg)
                            pending[j][2].add(tmp)
                    areg, ae, _ = pending.pop(park_idx)
                    self._eval_scalar(ae, areg)
        finally:
            for tmp in parked_temps:
                self._live_temps.pop(tmp, None)

        if tail:
            self._emit_epilogue(call.line)
            self.emit(call.line, f"{'b' if self.arch == 'arm64' else 'jmp'} {call.name}")
            return
        self.emit(call.line, f"{'bl' if self.arch == 'arm64' else 'call'} {call.name}")
        ret_reg = "x0" if self.arch == "arm64" else "rax"
        if dst is not None and dst != ret_reg:
            self.emit(call.line, f"mov {dst}, {ret_reg}")

    # -- Vector Lowering (`u32x4` and `u32x16`) --
    def _vec_scratch(self, ty, idx=0):
        if ty == "u32x16":
            return ("zmm0", "zmm31")[idx & 1]
        return ("v31", "v30")[idx & 1] if self.arch == "arm64" else ("xmm0", "xmm15")[idx & 1]

    def _as_vec_reg(self, e, ty, s_idx=0):
        if isinstance(e, Var) and e.name in self.var_loc and self.var_loc[e.name][0] == "reg":
            return self.var_loc[e.name][1]
        vr = self._vec_scratch(ty, s_idx)
        self._eval_vec(e, vr, ty, s_idx)
        return vr

    def _vec_expr_uses_reg(self, e, reg):
        if isinstance(e, Var):
            return self.var_loc.get(e.name) == ("reg", reg)
        if isinstance(e, BinOp):
            return self._vec_expr_uses_reg(e.left, reg) or self._vec_expr_uses_reg(e.right, reg)
        if isinstance(e, Call):
            return any(self._vec_expr_uses_reg(a, reg) for a in e.args)
        return False

    def _eval_vec(self, e, dst, ty, s_idx=0):
        line = getattr(e, "line", 0)
        if isinstance(e, Var):
            self._load_var(line, e.name, dst)
            return
        if isinstance(e, IndexLoad):
            if ty == "u32x16" and self.arch != "x86_64":
                raise HLErr(f"{self.src}: line {line}: `u32x16` (512-bit AVX-512) is only supported on `x86_64`; use `u32x4` on `arm64`")
            with self._emit_addr_held(line, e.buf, e.idx, align_req=(16 if ty == "u32x4" else 1)) as (base, disp):
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
            if e.op in (">>", "<<"):
                if not isinstance(e.right, Num):
                    raise HLErr(f"{self.src}: line {line}: vector shift `{e.op}` requires a constant shift count in 0..31")
                k = e.right.val
                if not (0 <= k < 32):
                    raise HLErr(f"{self.src}: line {line}: vector shift count `{k}` must be in 0..31")
                if ty != "u32x4":
                    raise HLErr(f"{self.src}: line {line}: vector shift `{e.op}` is supported on `u32x4` (not `{ty}`)")
                if isinstance(e.left, Var) and e.left.name in self.var_loc and self.var_loc[e.left.name][0] == "reg":
                    sr = self.var_loc[e.left.name][1]
                else:
                    self._eval_vec(e.left, dst, ty, s_idx)
                    sr = dst
                if k == 0:
                    if dst != sr:
                        if self.arch == "x86_64":
                            self.emit(line, f"vmovdqa {dst}, {sr}")
                        else:
                            self.emit(line, f"orr {dst}.16b, {sr}.16b, {sr}.16b")
                    return
                if self.arch == "x86_64":
                    mn = "vpsrld" if e.op == ">>" else "vpslld"
                    self.emit(line, f"{mn} {dst}, {sr}, {k}")
                else:
                    mn = "ushr" if e.op == ">>" else "shl"
                    self.emit(line, f"{mn} {dst}.4s, {sr}.4s, {k}")
                return
            if not isinstance(e.left, Var) and not self._vec_expr_uses_reg(e.right, dst):
                self._eval_vec(e.left, dst, ty, s_idx)
                lr = dst
            else:
                lr = self._as_vec_reg(e.left, ty, s_idx)
            nxt = 1 - (s_idx & 1)
            if self._vec_scratch(ty, nxt) == lr:
                nxt = 1 - nxt
            rr = self._as_vec_reg(e.right, ty, nxt)
            if ty == "u32x16":
                if e.op in ("+", "+%"):
                    self.emit(line, f"vpaddd {dst}, {lr}, {rr}")
                elif e.op == "^":
                    self.emit(line, f"vpxord {dst}, {lr}, {rr}")
                else:
                    raise HLErr(f"{self.src}: line {line}: unsupported u32x16 op `{e.op}`")
            elif self.arch == "x86_64":
                xor_mn = "vpxord" if "avx512" in self.needs else "vpxor"
                op_map = {"+": "vpaddd", "+%": "vpaddd", "^": xor_mn, "&": "vpand", "|": "vpor"}
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
                self._eval_vec(IndexLoad(args[0].name, args[1], "u32x4", line), dst, "u32x4", s_idx)
                return
            if nm == "load_u32x16":
                if self.arch != "x86_64":
                    raise HLErr(f"{self.src}: line {line}: `load_u32x16` (AVX-512) is only supported on `x86_64`")
                self._eval_vec(IndexLoad(args[0].name, args[1], "u32x16", line), dst, "u32x16", s_idx)
                return
            if nm == "zeros_u32x16":
                if self.arch != "x86_64":
                    raise HLErr(f"{self.src}: line {line}: `zeros_u32x16` (AVX-512) is only supported on `x86_64`")
                self.emit(line, f"vpxord {dst}, {dst}, {dst}")
                return
            if nm == "broadcast_u32x16":
                if self.arch != "x86_64":
                    raise HLErr(f"{self.src}: line {line}: `broadcast_u32x16` (AVX-512) is only supported on `x86_64`")
                if len(args) != 1:
                    raise HLErr(f"{self.src}: line {line}: `broadcast_u32x16(val)` takes 1 scalar argument")
                a0 = args[0]
                if isinstance(a0, IndexLoad) and a0.width == "u32":
                    with self._emit_addr_held(line, a0.buf, a0.idx) as (base, disp):
                        d_str = f" + {disp}" if disp else ""
                        self.emit(line, f"vpbroadcastd {dst}, dword ptr [{base}{d_str}]")
                elif isinstance(a0, Var) and a0.name in self.data_names:
                    self.emit(line, f"vpbroadcastd {dst}, dword ptr [rip + #{a0.name}]")
                else:
                    with self._hold_expr(a0) as sr:
                        self.emit(line, f"vpbroadcastd {dst}, {X86_REG32[sr]}")
                return
            if nm == "const_u32x4":
                if len(args) == 1 and isinstance(args[0], Var) and args[0].name in self.data_names:
                    if self.arch == "x86_64":
                        self.emit(line, f"vmovaps {dst}, xmmword ptr [rip + #{args[0].name}]")
                        return
                    raise HLErr(f"{self.src}: line {line}: `const_u32x4` from `data` is x86-64 only; on `arm64` use `u32x4(w0, w1, w2, w3)` or `pack_u64x2(lo, hi)`")
                raise HLErr(
                    f"{self.src}: line {line}: `const_u32x4` expects a `data` label (x86-64 `vmovaps [rip + #label]`); "
                    f"for 4 constant 32-bit words use `u32x4(w0, w1, w2, w3)` or `pack_u64x2(lo, hi)`"
                )
            if nm == "u32x4":
                if len(args) != 4 or not all(isinstance(a, Num) for a in args):
                    raise HLErr(f"{self.src}: line {line}: `u32x4(w0, w1, w2, w3)` requires 4 constant 32-bit integers (for runtime scalars use `pack_u64x2(lo, hi)`)")
                w0, w1, w2, w3 = (a.val & 0xFFFFFFFF for a in args)
                lo64 = w0 | (w1 << 32)
                hi64 = w2 | (w3 << 32)
                self._eval_vec(Call("pack_u64x2", [Num(lo64, line), Num(hi64, line)], line), dst, "u32x4", s_idx)
                return
            if nm == "pack_u64x2":
                if len(args) != 2:
                    raise HLErr(f"{self.src}: line {line}: `pack_u64x2(lo, hi)` takes 2 scalar u64 arguments")
                vtmp = self._vec_scratch("u32x4", 0)
                if vtmp == dst:
                    vtmp = self._vec_scratch("u32x4", 1)
                with self._hold_expr(args[0], why="low 64-bit lane of `pack_u64x2`") as lo_r:
                    if self.arch == "x86_64":
                        self.emit(line, f"vmovq {dst}, {lo_r}")
                    else:
                        self.emit(line, f"fmov d{dst[1:]}, {lo_r}")
                with self._hold_expr(args[1], why="high 64-bit lane of `pack_u64x2`") as hi_r:
                    if self.arch == "x86_64":
                        self.emit(line, f"vmovq {vtmp}, {hi_r}")
                        self.emit(line, f"vpunpcklqdq {dst}, {dst}, {vtmp}")
                    else:
                        self.emit(line, f"fmov d{vtmp[1:]}, {hi_r}")
                        self.emit(line, f"zip1 {dst}.2d, {dst}.2d, {vtmp}.2d")
                return
            if nm in ("rotl32", "rotr32"):
                k = args[1].val
                r = (32 - k) if nm == "rotl32" else k
                l = (32 - r)
                if isinstance(args[0], Var) and args[0].name in self.var_loc and self.var_loc[args[0].name][0] == "reg":
                    sr = self.var_loc[args[0].name][1]
                else:
                    # Evaluate compound/spilled operand directly into `dst` so `tmp` (from 2-reg scratch pool)
                    # is guaranteed distinct from both `sr` and `dst`!
                    self._eval_vec(args[0], dst, ty, s_idx)
                    sr = dst
                if ty == "u32x16" or (self.arch == "x86_64" and "avx512" in self.needs):
                    self.emit(line, f"vprord {dst}, {sr}, {r}")
                elif self.arch == "x86_64":
                    tmp = self._vec_scratch(ty, 0)
                    if tmp in (dst, sr):
                        tmp = self._vec_scratch(ty, 1)
                    self.emit(line, f"vpslld {tmp}, {sr}, {l}")
                    self.emit(line, f"vpsrld {dst}, {sr}, {r}")
                    self.emit(line, f"vpor {dst}, {dst}, {tmp}")
                else:
                    if r == 16:
                        self.emit(line, f"rev32 {dst}.8h, {sr}.8h")
                    else:
                        tmp = self._vec_scratch(ty, 0)
                        if tmp in (dst, sr):
                            tmp = self._vec_scratch(ty, 1)
                        self.emit(line, f"shl {tmp}.4s, {sr}.4s, {l}")
                        self.emit(line, f"ushr {dst}.4s, {sr}.4s, {r}")
                        self.emit(line, f"orr {dst}.16b, {dst}.16b, {tmp}.16b")
                return
            if nm in ("shl32", "shr32"):
                op = "<<" if nm == "shl32" else ">>"
                if len(args) != 2:
                    raise HLErr(f"{self.src}: line {line}: `{nm}(vec, imm)` takes 2 arguments")
                self._eval_vec(BinOp(op, args[0], args[1], line), dst, ty, s_idx)
                return
            if nm == "shufi32x4":
                if self.arch != "x86_64":
                    raise HLErr(f"{self.src}: line {line}: `shufi32x4` (AVX-512) is only supported on `x86_64`")
                a = self._as_vec_reg(args[0], ty, s_idx)
                b = self._as_vec_reg(args[1], ty, 1 - (s_idx & 1)) if len(args) == 3 else a
                imm = args[-1].val
                self.emit(line, f"vshufi32x4 {dst}, {a}, {b}, {imm}")
                return
            if nm == "shuf32":
                if self.arch != "x86_64":
                    raise HLErr(
                        f"{self.src}: line {line}: `shuf32` (`vpshufd`) is x86-64 only; on `arm64` use 1-instruction "
                        f"NEON ops directly (`ext4`/`ext8`/`ext12` for lane rotations, `unpacklo32`/`unpackhi32`, "
                        f"`unpacklo64`/`unpackhi64`, `uzp1_32`/`uzp2_32`)"
                    )
                if len(args) != 2 or not isinstance(args[1], Num):
                    raise HLErr(f"{self.src}: line {line}: `shuf32(vec, imm)` requires a constant 8-bit lane mask")
                a = self._as_vec_reg(args[0], ty, s_idx)
                imm = args[1].val & 0xFF
                self.emit(line, f"vpshufd {dst}, {a}, {imm}")
                return
            if nm == "shufps":
                if self.arch != "x86_64":
                    raise HLErr(f"{self.src}: line {line}: `shufps` is x86-64 only; on `arm64` use `unpacklo32`/`unpackhi32`/`unpacklo64`/`unpackhi64`/`uzp1_32`/`uzp2_32`/`ext4`/`ext8`/`ext12`")
                a = self._as_vec_reg(args[0], ty, s_idx)
                b = self._as_vec_reg(args[1], ty, 1 - (s_idx & 1))
                imm = args[2].val
                self.emit(line, f"vshufps {dst}, {a}, {b}, {imm}")
                return
            if nm == "blend32":
                if self.arch != "x86_64":
                    raise HLErr(f"{self.src}: line {line}: `blend32` is x86-64 only; on `arm64` use `unpacklo32`/`unpackhi32`/`unpacklo64`/`unpackhi64`/`uzp1_32`/`uzp2_32`/`ext4`/`ext8`/`ext12`")
                a = self._as_vec_reg(args[0], ty, s_idx)
                b = self._as_vec_reg(args[1], ty, 1 - (s_idx & 1))
                imm = args[2].val
                self.emit(line, f"vpblendd {dst}, {a}, {b}, {imm}")
                return
            if nm in ("uzp1_32", "uzp2_32"):
                a = self._as_vec_reg(args[0], ty, s_idx)
                b = self._as_vec_reg(args[1], ty, 1 - (s_idx & 1))
                if self.arch == "arm64":
                    mn = "uzp1" if nm == "uzp1_32" else "uzp2"
                    self.emit(line, f"{mn} {dst}.4s, {a}.4s, {b}.4s")
                else:
                    imm = 136 if nm == "uzp1_32" else 221
                    self.emit(line, f"vshufps {dst}, {a}, {b}, {imm}")
                return
            if nm in ("ext4", "ext8", "ext12"):
                k = int(nm[3:])
                a = self._as_vec_reg(args[0], ty, s_idx)
                b = self._as_vec_reg(args[1], ty, 1 - (s_idx & 1))
                if self.arch == "arm64":
                    self.emit(line, f"ext {dst}.16b, {a}.16b, {b}.16b, {k}")
                else:
                    self.emit(line, f"vpalignr {dst}, {b}, {a}, {k}")
                return
            if nm in ("unpacklo32", "unpackhi32", "unpacklo64", "unpackhi64"):
                a = self._as_vec_reg(args[0], ty, s_idx)
                b = self._as_vec_reg(args[1], ty, 1 - (s_idx & 1))
                if self.arch == "arm64":
                    mn, suf = {
                        "unpacklo32": ("zip1", "4s"), "unpackhi32": ("zip2", "4s"),
                        "unpacklo64": ("zip1", "2d"), "unpackhi64": ("zip2", "2d"),
                    }[nm]
                    self.emit(line, f"{mn} {dst}.{suf}, {a}.{suf}, {b}.{suf}")
                elif nm == "unpackhi64" and ty == "u32x4":
                    # `x86.tab` has `vshufps xmm` (`0xEE` = lanes(a.2, a.3, b.2, b.3)); `vpunpckhqdq` is ZMM-only.
                    self.emit(line, f"vshufps {dst}, {a}, {b}, 238")
                else:
                    mn = {"unpacklo32": "vpunpckldq", "unpackhi32": "vpunpckhdq",
                          "unpacklo64": "vpunpcklqdq", "unpackhi64": "vpunpckhqdq"}[nm]
                    self.emit(line, f"{mn} {dst}, {a}, {b}")
                return
            if nm == "add_u32x16_data":
                if self.arch != "x86_64":
                    raise HLErr(f"{self.src}: line {line}: `add_u32x16_data` (AVX-512) is only supported on `x86_64`")
                a = self._as_vec_reg(args[0], ty, s_idx)
                self.emit(line, f"vpaddd {dst}, {a}, zmmword ptr [rip + #{args[1].name}]")
                return
            raise HLErr(
                f"{self.src}: line {line}: unknown vector intrinsic `{nm}` "
                f"(portable u32x4 ops: `pack_u64x2(lo,hi)`, `v >> k`, `v << k`, `rotl32(v,k)`, `rotr32(v,k)`, "
                f"`unpacklo32`/`unpackhi32`/`unpacklo64`/`unpackhi64`, `uzp1_32`/`uzp2_32`, `ext4`/`ext8`/`ext12`; "
                f"x86-64 only: `const_u32x4(data_label)`, `shuf32(v,imm)`, `shufps`, `blend32`)"
            )
        raise HLErr(f"{self.src}: line {line}: unsupported vector expression")

    # -- Automatic `place { ... }` Fact Substitution & Outer-Context Inheritance --
    def _subst_spec_vars(self, expr_str, line=0):
        """Substitute High-Level Ode local variable names (including `name$k`) with allocated registers."""
        def repl(m):
            tok = m.group(0)
            # Contract `bytes` regions and unmodified parameters ALWAYS keep their contract names in `place`!
            if tok in self.param_set and (
                self.param_types.get(tok) == "bytes"
                or tok not in self.fn_written_vars
            ):
                return tok
            if tok in self.const_vals:
                return str(self.const_vals[tok])
            if tok in self.var_loc:
                if self.var_loc[tok][0] == "reg":
                    return self.var_loc[tok][1]
                if self.var_loc[tok][0] == "spill":
                    raise HLErr(
                        f"{self.src}: line {line}: `stack var {tok}` cannot be named directly in `maintains`/`writes`/`decreases`; "
                        f"keep loop-invariant variables in registers and mark a cold non-invariant temporary `stack var` instead"
                    )
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
        #    registers are still live (expanding dead pure immutable `let` aliases lazily so facts like
        #    `let hlen := ihl << 2; if hlen > n { return 0 }` survive as `(ihl * 4) <= n` after `hlen` is recycled)!
        loop_written_regs = {self.var_loc[v][1] for v in loop_written if v in self.var_loc and self.var_loc[v][0] == "reg"}
        for fact_s, fvars in self.active_facts:
            cur_s, cur_v = fact_s, set(fvars)
            ok = True
            for _step in range(5):
                if cur_v & loop_written:
                    ok = False
                    break
                dead = []
                for v in cur_v:
                    if v in self.param_set and (self.param_types.get(v) == "bytes" or v not in self.fn_written_vars):
                        continue
                    loc = self.var_loc.get(v)
                    if loc is None or loc[0] != "reg" or self.reg_owner.get(loc[1]) != v or loc[1] in loop_written_regs:
                        dead.append(v)
                if not dead:
                    break
                expanded_any = False
                for v in dead:
                    alias = self.pure_aliases.get(v)
                    if alias is None or (alias[1] & loop_written):
                        ok = False
                        break
                    cur_s = re.sub(rf"\b{re.escape(v)}\b", f"({alias[0]})", cur_s)
                    cur_v.discard(v)
                    cur_v |= alias[1]
                    expanded_any = True
                if not ok or not expanded_any:
                    break
            else:
                ok = False
            if ok and not (cur_v & loop_written):
                # Skip tautologies like `(ihl * 4) == (ihl * 4)` after self-alias expansion
                m_eq = re.fullmatch(r"\s*(.+?)\s*==\s*(.+?)\s*", cur_s)
                if not (m_eq and m_eq.group(1).strip("()") == m_eq.group(2).strip("()")):
                    add_fact(self._subst_spec_vars(cur_s))

        # 3. Automatic `u8` range bounds ONLY for loop-carried outer byte variables (not body-local `let`s!)
        for v in sorted(loop_written):
            if v in outer_vars and self.var_ty.get(v) == "u8" and self.var_loc.get(v, (None,))[0] == "reg":
                r = self.var_loc[v][1]
                add_fact(f"0 <= {r}")
                add_fact(f"{r} <= 255")

        # 4. Extra structural loop facts (e.g., `for i in lo..hi` bounds)
        for ef in extra_facts:
            add_fact(self._subst_spec_vars(ef))

        # 5. User `maintains` clauses (split top-level `&&` ONLY at paren depth 0 outside `if ... then`;
        # give crisp diagnostics on top-level `||` and top-level `!=`)
        def _split_top_level_and(s):
            parts, cur = [], []
            depth = 0
            if_depth = 0
            i = 0
            n = len(s)
            while i < n:
                ch = s[i]
                if ch == "(":
                    depth += 1
                    cur.append(ch); i += 1
                elif ch == ")":
                    depth = max(0, depth - 1)
                    cur.append(ch); i += 1
                elif s[i:i+2] == "&&" and depth == 0 and if_depth == 0:
                    parts.append("".join(cur).strip())
                    cur = []; i += 2
                else:
                    if ch.isalpha() or ch == "_":
                        j = i
                        while j < n and (s[j].isalnum() or s[j] == "_"):
                            j += 1
                        w = s[i:j]
                        if w == "if":
                            if_depth += 1
                        elif w == "then" and if_depth > 0:
                            if_depth -= 1
                        cur.append(w); i = j
                    else:
                        cur.append(ch); i += 1
            tail = "".join(cur).strip()
            if tail:
                parts.append(tail)
            return parts

        def _has_top_level_op(s, op):
            depth = 0
            if_depth = 0
            i, n = 0, len(s)
            while i < n:
                ch = s[i]
                if ch == "(":
                    depth += 1; i += 1
                elif ch == ")":
                    depth = max(0, depth - 1); i += 1
                elif s[i:i+len(op)] == op and depth == 0 and if_depth == 0:
                    return True
                elif ch.isalpha() or ch == "_":
                    j = i
                    while j < n and (s[j].isalnum() or s[j] == "_"):
                        j += 1
                    w = s[i:j]
                    if w == "if":
                        if_depth += 1
                    elif w == "then" and if_depth > 0:
                        if_depth -= 1
                    i = j
                else:
                    i += 1
            return False

        for mf in maintains:
            if _has_top_level_op(mf, "||"):
                raise HLErr(
                    f"{self.src}: line {line}: `maintains` cannot use `||` (`{mf.strip()}`); "
                    f"write linear bounds instead (for example `0 <= x, x <= 1` instead of `x == 0 || x == 1`)"
                )
            for part in _split_top_level_and(mf):
                if not part:
                    continue
                if _has_top_level_op(part, "!="):
                    raise HLErr(
                        f"{self.src}: line {line}: `maintains` cannot state `!=` (`{part}`); "
                        f"note that `join` and loops already inherit `!=` facts automatically from earlier `if x == c {{ return ... }}` guards, so you do not need to repeat `!=` in `maintains`"
                    )
                add_fact(self._subst_spec_vars(part, line=line))

        # 6. User `writes` clauses (canonicalize `writes out[.. j] = spec.fn(args)[i]` / `[.. j]` -> `spec.fn(args)`)
        for buf_nm, mode, idx_s, rhs_s in writes:
            idx_r = self._subst_spec_vars(idx_s)
            rhs_r = self._subst_spec_vars(rhs_s).strip()
            rhs_r = re.sub(r"\[\s*(?:i|\.\.[^\]]*)\s*\]\s*$", "", rhs_r).strip()
            if mode == "prefix":
                place_lines.append(f"wrote {buf_nm}[.. {idx_r}] = {rhs_r}")
            else:
                place_lines.append(f"wrote {buf_nm}[{idx_r} ..] = {rhs_r}")

        # 7. Termination measure
        dec_line = f"decreases {self._subst_spec_vars(decreases)}" if decreases is not None else None
        if dec_line is not None:
            place_lines.append(dec_line)

        # Avoid emitting two `place { ... }` blocks at the exact same PC (e.g. `join` right before `while`):
        # insert a `nop` immediately after the previous `place` (before any intervening loop header label)
        # so the two places occupy distinct PCs and the loop back-edge jumps only to the loop's own place.
        if self._last_place_end is not None:
            self.out_lines.insert(self._last_place_end, (line, "nop"))

        self.out_lines.append((line, "place {"))
        for pl in place_lines:
            self.out_lines.append((line, f"    {pl}"))
        self.out_lines.append((line, "}"))
        self._last_place_end = len(self.out_lines)

    # -- Statement Lowering --
    def lower_stmts(self, stmts):
        saved_facts_len = len(self.active_facts)
        for st in stmts:
            self._lower_stmt(st)
            assert not self._live_temps, f"scratch-register leak after statement on line {getattr(st, 'line', 0)}: {self._live_temps}"
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
                if kind == "reg":
                    self._eval_scalar(st.expr, loc)
                else:
                    with self._temp_reg(st.line) as tr:
                        self._eval_scalar(st.expr, tr)
                        self._store_var(st.line, st.name, tr)
                if not st.mutable:
                    bparams = {p for p, t in self.param_types.items() if t == "bytes"}
                    pure = _pure_to_spec(st.expr, bparams)
                    if pure is not None:
                        self.active_facts.append((f"{st.name} == {pure[0]}", {st.name} | pure[1]))
                        if not (pure[1] & self.fn_mutated_vars):
                            self.pure_aliases[st.name] = pure
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
            expr = st.expr if st.op == ":=" else BinOp(st.op[:-1], Var(st.target, st.line), st.expr, st.line)
            if kind == "reg":
                self._eval_scalar(expr, loc)
            else:
                with self._temp_reg(st.line) as tr:
                    self._eval_scalar(expr, tr)
                    self._store_var(st.line, st.target, tr)
            return

        if isinstance(st, StoreStmt):
            if st.width in ("u32x4", "u32x16"):
                if st.width == "u32x16" and self.arch != "x86_64":
                    raise HLErr(f"{self.src}: line {st.line}: `u32x16` store (AVX-512) is only supported on `x86_64`; use `u32x4` on `arm64`")
                vr = self._as_vec_reg(st.expr, st.width)
                with self._emit_addr_held(st.line, st.buf, st.idx, align_req=(16 if st.width == "u32x4" else 1)) as (base, disp):
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
            if st.width == "u32":
                raise HLErr(
                    f"{self.src}: line {st.line}: 32-bit scalar store `{st.buf}.u32(...) := ...` is not supported yet; "
                    f"use `.u32x4(off) := ...`, `.u64(off) := ...` "
                    f"on a stack `buf`, or byte stores `out[i] := ...` on an output buffer"
                )
            if st.width == "u8" and self.var_loc.get(st.buf, (None,))[0] == "buf":
                raise HLErr(
                    f"{self.src}: line {st.line}: 1-byte store `{st.buf}[...] := ...` to a stack `buf` is not supported by the verifier's frame model; "
                    f"use `{st.buf}.u64(off) := ...`, `{st.buf}.u32x4(off) := ...`, or `stack var`"
                )
            # Fixed deterministic store order: evaluate value first, then address, then store.
            allow_sp = (self.arch != "arm64" or st.width == "u64")
            align_req = {"u32": 4, "u64": 8}.get(st.width, 1)
            with self._hold_expr(st.expr, why=f"value `{_expr_brief(st.expr)}` for store to `{st.buf}`") as val_r:
                with self._emit_addr_held(st.line, st.buf, st.idx, allow_sp=allow_sp, align_req=align_req) as (base, disp):
                    self._emit_scalar_store(st.line, st.width, base, disp, val_r)
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
            bparams = {p for p, pt in self.param_types.items() if pt == "bytes"}
            then_facts = [f for cc in _extract_conjuncts(st.cond) if (f := _cmp_to_fact(cc, bparams)) is not None]
            else_facts = [f for cc in _extract_conjuncts(_negate_cond(st.cond)) if (f := _cmp_to_fact(cc, bparams)) is not None]
            if not st.else_body:
                self._emit_branch(st.cond, end_lbl, jump_if_true=False)
                saved = len(self.active_facts)
                saved_owner = dict(self.reg_owner)
                self.active_facts.extend(then_facts)
                self.lower_stmts(st.then_body)
                del self.active_facts[saved:]
                if _stmts_always_exit(st.then_body):
                    # Dead `then` branch never falls through: restore register owners from before `if`!
                    self.reg_owner = saved_owner
                self.emit(st.line, f"{end_lbl}:")
                # Crucial for W1: if `then` unconditionally exits (`if ihl < 20 { return 0 }`),
                # the negated condition (`ihl >= 20`) holds for the rest of the enclosing block!
                if _stmts_always_exit(st.then_body):
                    self.active_facts.extend(else_facts)
            else:
                self._emit_branch(st.cond, else_lbl, jump_if_true=False)
                saved = len(self.active_facts)
                saved_owner = dict(self.reg_owner)
                self.active_facts.extend(then_facts)
                self.lower_stmts(st.then_body)
                del self.active_facts[saved:]
                if not _stmts_always_exit(st.then_body):
                    self.emit(st.line, f"{'b' if self.arch == 'arm64' else 'jmp'} {end_lbl}")
                self.emit(st.line, f"{else_lbl}:")
                self.reg_owner = dict(saved_owner)
                saved2 = len(self.active_facts)
                self.active_facts.extend(else_facts)
                self.lower_stmts(st.else_body)
                del self.active_facts[saved2:]
                if not (_stmts_always_exit(st.then_body) and _stmts_always_exit(st.else_body)):
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
            if kind == "reg":
                self._eval_scalar(st.lo, loc)
            else:
                with self._temp_reg(st.line) as tr:
                    self._eval_scalar(st.lo, tr)
                    self._store_var(st.line, st.var, tr)
            wvars = _written_vars(st.body) | {st.var}
            extra = []
            lo_lin = _linear_to_spec(st.lo)
            hi_lin = _linear_to_spec(st.hi)
            if lo_lin is not None and not (lo_lin[1] & wvars):
                extra.append(f"{lo_lin[0]} <= {st.var}")
            if hi_lin is not None and not (hi_lin[1] & wvars):
                extra.append(f"{st.var} <= {hi_lin[0]}")
            if st.step > 1 and isinstance(st.lo, Num):
                extra.append(f"({st.var} % {st.step}) == {st.lo.val % st.step}")
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
                self._eval_scalar(st.expr, ret_reg)
            self._emit_epilogue(st.line)
            self.emit(st.line, "ret")
            return

        raise HLErr(f"{self.src}: unhandled statement {type(st).__name__}")

    def lower(self):
        first_ln = self.stmts[0].line if self.stmts else 1
        self._emit_prologue(first_ln)
        self.lower_stmts(self.stmts)
        # Void functions without trailing `return`
        if not _stmts_always_exit(self.stmts):
            if not self.out_lines or (self.out_lines[-1][1] not in ("ret",) and not self.out_lines[-1][1].startswith(("jmp ", "b "))):
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


def lower_hl_block(fn_name, params_text, lines, first_line, arch, src="<ode>", fn_names=None, data_names=None, explicit_stack=False, callee_clobbers=None, needs=(), hl_inlines=None):
    """Parse and deterministically lower a High-Level Ode function body to `odec` assembly lines + metadata."""
    parser = HLParser(lines, first_line, src)
    stmts = parser.parse_block_stmts(until_brace=False)
    params = parse_param_list(params_text)
    lowerer = HLLower(fn_name, params, arch, stmts, src, fn_names=fn_names, data_names=data_names, explicit_stack=explicit_stack, callee_clobbers=callee_clobbers, needs=needs, hl_inlines=hl_inlines)
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
