"""The specification language, and W32: their one meaning.

A specification:

    (spec (name blake3-g)
      (inputs (a b c d x y))                       ; words, or (len nat), (m words)
      (uses ((compress #hash)))                    ; callees, by hash
      (funs ((f (p (q nat)) body) ...))            ; local functions, may recurse
      (steps ((a1 (add (add a b) x)) ((u v) (f a b)) ...))
      (outputs (a2 b2 c2 d2)))

Values have three sorts: *words* (u32), *naturals* (lengths, counts,
indices), and *lists*. Expressions:

    words     an integer literal; (add w w) (xor w w) (rotr w n) mod 2**32;
              (word n), a natural mod 2**32
    naturals  (n+ n n) (n- n n) (n* n n) (ndiv n n) (nmin n n) (nmax n n);
              (n= n n) (n< n n), 1 or 0; (count list)
    lists     (list e ...) (concat l ...) (slice l start count) (at l i)
    control   (if n e e) (let ((x e) ...) e) (require n e)
    calls     (f e ...) for a local function or a callee in (uses ...);
              a callee's definition is fetched only if the call is expanded

An integer literal is a natural where a natural is expected (an operand
of a natural operator, a condition, an index, a parameter declared
(p nat)) and a word elsewhere; no value ever changes sort. A
step binds one name, or destructures a list into several. A function's
body sees its parameters and the spec's inputs. Outputs are words or
lists of words, flattened in order.

Every evaluation is definite: it yields one value or fails, and it runs
within BUDGET steps. Naturals are always concrete -- the inputs fix them
-- so conditions are decided while words stay whatever the algebra
makes them. One evaluator gives the language its meaning; an *algebra*
says what a word is: an integer (running), a DAG node (proving,
ode/check.py), or a W32 step (compiling, ode/produce.py). They cannot
disagree about what a specification means.

A W32 program (w32 (inputs ...) (steps ...) (outputs ...)) is the
portable machine: word inputs, each step one operation on atoms, or a
call by certificate ((o ...) (call #certificate a ...)) to another
proved program. decode_w32 reads its binary form.
"""
import struct as _struct

from .canon import Bytes, Sym, field

MASK = 0xFFFFFFFF
BUDGET = 50_000_000  # evaluation steps; a definite computation stays within it
WORD_OPS = ("add", "xor", "rotr")
NAT_OPS = ("n+", "n-", "n*", "ndiv", "nmin", "nmax", "n=", "n<")


class Nat(int):
    """A natural number: a length, count, or index. Never a word."""
    __slots__ = ()


def inputs_of(defn):
    return field(defn, "inputs")


def steps_of(defn):
    return field(defn, "steps")


def outputs_of(defn):
    return field(defn, "outputs")


def uses_of(defn):
    """{alias: hash} for a spec's callees."""
    return {u[0]: u[1] for u in field(defn, "uses") or []}


def input_sorts(defn):
    """[(name, sort)] with sort 'word', 'nat', or 'words'."""
    out = []
    for i in inputs_of(defn):
        if isinstance(i, Sym):
            out.append((i, "word"))
        elif (isinstance(i, list) and len(i) == 2 and isinstance(i[0], Sym)
              and i[1] in ("nat", "words")):
            out.append((i[0], str(i[1])))
        else:
            raise ValueError(f"bad input {i!r}")
    return out


def word_input_names(defn, at):
    """The names of the word inputs at an instantiation, in order: the
    inputs of the W32 program that implements the spec there."""
    names = []
    for name, sort in input_sorts(defn):
        if sort == "word":
            names.append(name)
        elif sort == "words":
            names += [Sym(f"{name}.{i}") for i in range(at[name])]
    return names


def instantiation(defn, at):
    """Check an instantiation ({name: natural or list length}) fits the
    spec's non-word inputs exactly; return it."""
    want = {n for n, s in input_sorts(defn) if s != "word"}
    if set(at) != want or not all(isinstance(v, int) and v >= 0
                                  for v in at.values()):
        raise ValueError(f"instantiation must give exactly {sorted(want)}")
    return at


def validate_spec(defn):
    if not isinstance(defn, list) or not defn or defn[0] != "spec":
        raise ValueError("not a spec definition")
    if not isinstance(field(defn, "name"), Sym):
        raise ValueError("spec needs a symbol name")
    names = [n for n, _ in input_sorts(defn)]
    for u in field(defn, "uses") or []:
        if not (isinstance(u, list) and len(u) == 2 and isinstance(u[0], Sym)
                and isinstance(u[1], Bytes) and len(u[1]) == 32):
            raise ValueError(f"bad use {u!r}")
    for f in field(defn, "funs") or []:
        if not (isinstance(f, list) and len(f) == 3 and isinstance(f[0], Sym)
                and isinstance(f[1], list)):
            raise ValueError(f"bad function {f!r}")
        _params(f[1])
    _validate_steps(steps_of(defn), outputs_of(defn), names)
    return defn


def _params(params):
    """[(name, sort)]: a plain name takes any value; (p nat) a natural."""
    out = []
    for p in params:
        if isinstance(p, Sym):
            out.append((p, "any"))
        elif isinstance(p, list) and len(p) == 2 and isinstance(p[0], Sym) \
                and p[1] == "nat":
            out.append((p[0], "nat"))
        else:
            raise ValueError(f"bad parameter {p!r}")
    return out


def _validate_steps(steps, outputs, names):
    if not isinstance(steps, list) or not isinstance(outputs, list) or not outputs:
        raise ValueError("program needs steps and outputs")
    if len(set(names)) != len(names):
        raise ValueError("duplicate input name")
    defined = set(names)
    for step in steps:
        if not (isinstance(step, list) and len(step) == 2):
            raise ValueError(f"bad step {step!r}")
        targets = step[0] if isinstance(step[0], list) else [step[0]]
        if not targets or not all(isinstance(t, Sym) for t in targets):
            raise ValueError(f"bad step {step!r}")
        for t in targets:
            if t in defined:
                raise ValueError(f"step redefines {t} (SSA: one assignment)")
            defined.add(t)
    for o in outputs:
        if not isinstance(o, Sym) or o not in defined:
            raise ValueError(f"bad output {o!r}")


class Concrete:
    """Words are integers: running."""

    def __init__(self, certified=None, bound=None):
        self.certified = certified or {}  # certificate hash -> runner
        self.bound = bound or {}          # spec hash -> runner of a proved callee

    def const(self, v):
        return v

    def add(self, a, b):
        return (a + b) & MASK

    def xor(self, a, b):
        return a ^ b

    def rotr(self, a, n):
        n %= 32
        return ((a >> n) | (a << (32 - n))) & MASK if n else a

    def spec_call(self, h, callee, args, ev):
        if h in self.bound:
            return self.bound[h](args)
        return ev.apply_spec(callee, args)

    def cert_call(self, h, args, n_out):
        return self.certified[h](args)


class Evaluator:
    """The language's meaning, over an algebra; resolve(hash) -> definition."""

    def __init__(self, algebra, resolve=None):
        self.alg, self.resolve, self.steps = algebra, resolve, 0

    def _tick(self):
        self.steps += 1
        if self.steps > BUDGET:
            raise ValueError(f"evaluation exceeds its budget of {BUDGET} steps")

    # -- whole programs ------------------------------------------------
    def apply_spec(self, defn, args):
        """A spec called with word arguments (callees take words only)."""
        defn = defn.get() if isinstance(defn, _Lazy) else defn
        sorts = input_sorts(defn)
        if any(s != "word" for _, s in sorts) or len(args) != len(sorts):
            raise ValueError("a callee takes exactly its word inputs")
        return self.run_spec(defn, dict(zip((n for n, _ in sorts), args)))

    def run_spec(self, defn, env):
        """Evaluate a spec's steps in env; return its flattened outputs."""
        ctx = _Context(defn, self, env)
        env = dict(env)
        for name, e in steps_of(defn):
            v = ctx.ev(e, env, "any")
            if isinstance(name, list):
                if not isinstance(v, list) or len(v) != len(name):
                    raise ValueError(f"cannot bind {len(name)} names to {v!r}")
                env.update(zip(name, v))
            else:
                env[name] = v
        out = []
        for o in outputs_of(defn):
            v = env[o]
            out += v if isinstance(v, list) else [v]
        if any(isinstance(w, (list, Nat)) for w in out):
            raise ValueError("outputs must be words")
        return out

    def run_w32(self, defn, env):
        """Evaluate a W32 program; its calls are calls by certificate."""
        env = dict(env)
        for name, e in steps_of(defn):
            self._tick()
            if isinstance(name, list):
                args = [self.atom(a, env) for a in e[2:]]
                env.update(zip(name, self.alg.cert_call(e[1], args, len(name))))
            elif isinstance(e, (int, Sym)):
                env[name] = self.atom(e, env)
            elif e[0] == "rotr":
                env[name] = self.alg.rotr(self.atom(e[1], env), e[2])
            else:
                op = self.alg.add if e[0] == "add" else self.alg.xor
                env[name] = op(self.atom(e[1], env), self.atom(e[2], env))
        return [env[o] for o in outputs_of(defn)]

    def atom(self, a, env):
        return self.alg.const(a) if isinstance(a, int) else env[a]


class _Context:
    """Evaluation of one spec's expressions: its functions and callees."""

    def __init__(self, defn, ev, inputs):
        self.ev_, self.alg, self.inputs = ev, ev.alg, inputs
        self.funs = {f[0]: f for f in field(defn, "funs") or []}
        self.uses = uses_of(defn)

    def nat(self, e, env):
        v = self.ev(e, env, "nat")
        if not isinstance(v, Nat):
            raise ValueError(f"expected a natural, got {v!r} from {e!r}")
        return v

    def word(self, e, env):
        v = self.ev(e, env, "word")
        if isinstance(v, (Nat, list)):
            raise ValueError(f"expected a word, got {v!r} from {e!r}")
        return v

    def lst(self, e, env):
        v = self.ev(e, env, "any")
        if not isinstance(v, list):
            raise ValueError(f"expected a list, got {v!r} from {e!r}")
        return v

    def ev(self, e, env, sort):
        self.ev_._tick()
        alg = self.alg
        if isinstance(e, int):
            return Nat(e) if sort == "nat" else alg.const(_u32(e))
        if isinstance(e, Sym):
            if e not in env:
                raise ValueError(f"unknown name {e}")
            return env[e]
        if not (isinstance(e, list) and e and isinstance(e[0], Sym)):
            raise ValueError(f"bad expression {e!r}")
        op, args = e[0], e[1:]
        if op in ("add", "xor"):
            _arity(e, 2)
            f = alg.add if op == "add" else alg.xor
            return f(self.word(args[0], env), self.word(args[1], env))
        if op == "rotr":
            _arity(e, 2)
            n = args[1]
            if not (isinstance(n, int) and 0 <= n < 32):
                raise ValueError("rotr takes a word and a count in 0..31")
            return alg.rotr(self.word(args[0], env), n)
        if op == "word":
            _arity(e, 1)
            return alg.const(self.nat(args[0], env) & MASK)
        if op in NAT_OPS:
            _arity(e, 2)
            a, b = self.nat(args[0], env), self.nat(args[1], env)
            return Nat(_nat_op(op, a, b))
        if op == "count":
            _arity(e, 1)
            return Nat(len(self.lst(args[0], env)))
        if op == "list":
            return [self.word(a, env) for a in args]
        if op == "concat":
            out = []
            for a in args:
                out += self.lst(a, env)
            return out
        if op == "slice":
            _arity(e, 3)
            xs = self.lst(args[0], env)
            i, k = self.nat(args[1], env), self.nat(args[2], env)
            if i + k > len(xs):
                raise ValueError(f"slice {i}+{k} past a list of {len(xs)}")
            return xs[i:i + k]
        if op == "at":
            _arity(e, 2)
            xs, i = self.lst(args[0], env), self.nat(args[1], env)
            if i >= len(xs):
                raise ValueError(f"index {i} past a list of {len(xs)}")
            return xs[i]
        if op == "if":
            _arity(e, 3)
            return self.ev(args[1] if self.nat(args[0], env) else args[2], env, sort)
        if op == "require":
            _arity(e, 2)
            if not self.nat(args[0], env):
                raise ValueError(f"requirement fails: {args[0]!r}")
            return self.ev(args[1], env, sort)
        if op == "let":
            _arity(e, 2)
            inner = dict(env)
            for binding in args[0]:
                inner[binding[0]] = self.ev(binding[1], inner, "any")
            return self.ev(args[1], inner, sort)
        if op in self.funs:
            _, params, body = self.funs[op]
            params = _params(params)
            if len(args) != len(params):
                raise ValueError(f"{op} takes {len(params)} arguments")
            vals = [self.nat(a, env) if s == "nat" else self.ev(a, env, "any")
                    for a, (_, s) in zip(args, params)]
            local = dict(self.inputs)
            local.update(zip((p for p, _ in params), vals))
            return self.ev(body, local, sort)
        if op in self.uses:
            h = self.uses[op]
            vals = []
            for a in args:  # a callee takes words; a list argument spreads
                v = self.ev(a, env, "word")
                vals += v if isinstance(v, list) else [v]
            return self.alg.spec_call(h, _Lazy(self.ev_.resolve, h), vals, self.ev_)
        raise ValueError(f"unknown operation {op}")


class _Lazy:
    """A callee's definition, fetched only if an algebra expands the call."""

    def __init__(self, resolve, h):
        self.resolve, self.h = resolve, h

    def get(self):
        if self.resolve is None:
            raise ValueError(f"callee {self.h.hex()} is not available")
        return self.resolve(self.h)


def _arity(e, n):
    if len(e) != n + 1:
        raise ValueError(f"{e[0]} takes {n} operands")


def _u32(v):
    if not 0 <= v <= MASK:
        raise ValueError(f"word literal {v} out of range")
    return v


def _nat_op(op, a, b):
    if op == "n+":
        return a + b
    if op == "n-":
        if a < b:
            raise ValueError(f"n- would go below zero: {a} - {b}")
        return a - b
    if op == "n*":
        return a * b
    if op == "ndiv":
        if b == 0:
            raise ValueError("ndiv by zero")
        return a // b
    if op == "nmin":
        return min(a, b)
    if op == "nmax":
        return max(a, b)
    if op == "n=":
        return int(a == b)
    return int(a < b)


def run(defn, at, values, resolve=None, certified=None, bound=None):
    """Run a spec (at an instantiation) or a W32 program on word values.
    bound ({spec hash: runner}) runs callees by their proved programs."""
    ev = Evaluator(Concrete(certified, bound), resolve)
    if defn[0] == "w32":
        return ev.run_w32(defn, dict(zip(inputs_of(defn), values)))
    env, values = {}, list(values)
    for name, sort in input_sorts(defn):
        if sort == "word":
            env[name] = values.pop(0)
        elif sort == "nat":
            env[name] = Nat(at[name])
        else:
            env[name], values = values[:at[name]], values[at[name]:]
    if values:
        raise ValueError("too many input words")
    return ev.run_spec(defn, env)


# --- W32: validation and the binary form (written by produce.emit_w32) --

def validate_w32(defn):
    if not isinstance(defn, list) or not defn or defn[0] != "w32":
        raise ValueError("not a w32 definition")
    inputs = inputs_of(defn)
    if not isinstance(inputs, list) or not all(isinstance(i, Sym) for i in inputs):
        raise ValueError("W32 inputs are word names")
    _validate_steps(steps_of(defn), outputs_of(defn), inputs)
    defined = set(inputs)
    for name, e in steps_of(defn):
        if isinstance(name, list):
            if not (isinstance(e, list) and len(e) >= 2 and e[0] == "call"
                    and isinstance(e[1], Bytes) and len(e[1]) == 32):
                raise ValueError(f"bad W32 call {e!r}")
            operands = e[2:]
        elif isinstance(e, (int, Sym)):
            operands = [e]
        elif isinstance(e, list) and len(e) == 3 and e[0] in WORD_OPS:
            operands = [e[1]] if e[0] == "rotr" else e[1:]
            if e[0] == "rotr" and not (isinstance(e[2], int) and 0 <= e[2] < 32):
                raise ValueError("rotr count must be 0..31")
        else:
            raise ValueError(f"W32 step not a single operation: {e!r}")
        for a in operands:
            if isinstance(a, int):
                _u32(a)
            elif a not in defined:
                raise ValueError(f"unknown name {a}")
        defined.update(name if isinstance(name, list) else [name])
    return defn


_W_DECODE = {0: "copy", 1: "add", 2: "xor", 3: "rotr", 4: "call"}


def decode_w32(data, input_names):
    """Bytes -> W32 program: exactly the program the bytes run.

    Header: inputs u16, names defined u32, outputs u16, output name
    indices u32 each. Steps: opcode (0 copy, 1 add, 2 xor, 3 rotr, 4 call);
    an operand is tag 0 + name index u32 (inputs first) or tag 1 + a u32
    constant; rotr's count is a u8; a call is a 32-byte certificate hash,
    u16 argument count, operands, and u16 output count.
    """
    assert isinstance(data, bytes)
    pos = 0

    def take(n):
        nonlocal pos
        if pos + n > len(data):
            raise ValueError("truncated W32 binary")
        b, pos = data[pos:pos + n], pos + n
        return b

    (n_inputs,) = _struct.unpack("<H", take(2))
    if n_inputs != len(input_names):
        raise ValueError("W32 binary input count mismatch")
    (n_steps,) = _struct.unpack("<I", take(4))
    (n_outputs,) = _struct.unpack("<H", take(2))
    out_idx = [_struct.unpack("<I", take(4))[0] for _ in range(n_outputs)]
    prefix = "s"  # step names must not collide with any input name
    while any(str(n).startswith(prefix) for n in input_names):
        prefix += "s"
    names = list(input_names) + [Sym(f"{prefix}{i}") for i in range(n_steps)]

    def operand():
        tag = take(1)[0]
        if tag == 1:
            return _struct.unpack("<I", take(4))[0]
        if tag == 0:
            (i,) = _struct.unpack("<I", take(4))
            if i >= len(names):
                raise ValueError("operand index out of range")
            return names[i]
        raise ValueError("bad operand tag")

    steps, defined = [], 0
    while defined < n_steps:
        op = _W_DECODE.get(take(1)[0])
        if op is None:
            raise ValueError("bad W32 opcode")
        here = len(input_names) + defined
        if op == "call":
            h = Bytes(take(32))
            (n_args,) = _struct.unpack("<H", take(2))
            args = [operand() for _ in range(n_args)]
            (n_outs,) = _struct.unpack("<H", take(2))
            if n_outs == 0 or defined + n_outs > n_steps:
                raise ValueError("bad W32 call output count")
            steps.append([names[here:here + n_outs], [Sym("call"), h] + args])
            defined += n_outs
            continue
        if op == "copy":
            e = operand()
        elif op == "rotr":
            e = [Sym("rotr"), operand(), take(1)[0]]
        else:
            e = [Sym(op), operand(), operand()]
        steps.append([names[here], e])
        defined += 1
    if pos != len(data):
        raise ValueError("trailing bytes in W32 binary")
    if any(i >= len(names) for i in out_idx):
        raise ValueError("output index out of range")
    defn = [Sym("w32"), [Sym("inputs"), list(input_names)], [Sym("steps"), steps],
            [Sym("outputs"), [names[i] for i in out_idx]]]
    validate_w32(defn)
    return defn
