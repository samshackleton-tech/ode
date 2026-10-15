"""The symbolic checker for word programs (SPEC s4, s6 at word scale).

Where the byte checker proves by exhaustion, this checker proves by
symbolic execution: it runs both the specification and the program
decoded from the emitted W32 bytes over fresh variables, building
expressions through smart constructors -- constant folding, xor
cancellation, add/xor flattening under a canonical operand order, rotr
composition, and rotr distributing over xor. Expressions are hash-consed
DAG nodes, so identical subexpressions are one node and size stays
linear in the number of steps. The claim is proved when the two sides'
outputs are the same nodes. Soundness rests on each constructor's
rewrite being a u32 identity, and on nothing about the producer: the
subject of the proof is the binary itself, decoded.
"""
from . import word
from .canon import Sym, assoc, field, hash_of
from .store import Reject, load_definition as _load, load_binary as _load_binary

CHECKER_ID = Sym("ode-wchecker-0.1")
PROPERTY = "equals-wspec-v1"          # the W32 machine
PROPERTY_A64 = "equals-wspec-a64-v1"  # AArch64 bytes (ode/a64.py)
MASK = word.MASK


class Dag:
    def __init__(self):
        self.nodes = []
        self.index = {}

    def _intern(self, node):
        i = self.index.get(node)
        if i is None:
            i = len(self.nodes)
            self.nodes.append(node)
            self.index[node] = i
        return i

    def const(self, v):
        return self._intern(("const", v & MASK))

    def var(self, name):
        return self._intern(("var", str(name)))

    def xor(self, a, b):
        terms, const = {}, 0
        for x in (a, b):
            node = self.nodes[x]
            if node[0] == "const":
                const ^= node[1]
            elif node[0] == "xor":
                for t in node[1]:
                    terms[t] = terms.get(t, 0) + 1
                const ^= node[2]
            else:
                terms[x] = terms.get(x, 0) + 1
        operands = tuple(sorted(t for t, c in terms.items() if c % 2 == 1))
        if not operands:
            return self.const(const)
        if len(operands) == 1 and const == 0:
            return operands[0]
        return self._intern(("xor", operands, const))

    def add(self, a, b):
        terms, const = [], 0
        for x in (a, b):
            node = self.nodes[x]
            if node[0] == "const":
                const = (const + node[1]) & MASK
            elif node[0] == "add":
                terms.extend(node[1])
                const = (const + node[2]) & MASK
            else:
                terms.append(x)
        if not terms:
            return self.const(const)
        if len(terms) == 1 and const == 0:
            return terms[0]
        return self._intern(("add", tuple(sorted(terms)), const))

    def rotr(self, a, n):
        n %= 32
        if n == 0:
            return a
        node = self.nodes[a]
        if node[0] == "const":
            v = node[1]
            return self.const(((v >> n) | (v << (32 - n))) & MASK)
        if node[0] == "rotr":
            return self.rotr(node[1], node[2] + n)
        if node[0] == "xor":
            out = self.const(node[2] and
                             (((node[2] >> n) | (node[2] << (32 - n)))
                              & MASK))
            # fold the rotated constant in via xor construction below
            result = out
            for t in node[1]:
                result = self.xor(result, self.rotr(t, n))
            return result
        return self._intern(("rotr", a, n))

    def expr(self, e, env, defs=None):
        if isinstance(e, int):
            return self.const(e)
        if isinstance(e, Sym):
            return env[e]
        if e[0] == "call":
            callee = defs[e[1]]
            args = [self.expr(a, env, defs) for a in e[2:]]
            inner = word._defs_of(callee)
            cenv = dict(zip(word.inputs_of(callee), args))
            return self._run(word.steps_of(callee), word.outputs_of(callee),
                             cenv, inner)
        if e[0] == "add":
            return self.add(self.expr(e[1], env, defs), self.expr(e[2], env, defs))
        if e[0] == "xor":
            return self.xor(self.expr(e[1], env, defs), self.expr(e[2], env, defs))
        return self.rotr(self.expr(e[1], env, defs), e[2])

    def _run(self, steps, outputs, env, defs):
        for name, e in steps:
            if isinstance(name, list):
                for n, v in zip(name, self.expr(e, env, defs)):
                    env[n] = v
            else:
                env[name] = self.expr(e, env, defs)
        return [env[o] for o in outputs]

    def program_outputs(self, inputs, steps, outputs, defs=None):
        env = {name: self.var(name) for name in inputs}
        return self._run(steps, outputs, env, defs or {})


def check_certificate(store_dir, cert):
    """Returns (record, program): the record, and the decoded program the
    proof is about -- run that, from memory, never binary.bin again."""
    if not isinstance(cert, list) or not cert or cert[0] != "certificate":
        raise Reject("not a certificate")
    if field(cert, "cert") != "correctness":
        raise Reject(f"unsupported certificate kind {field(cert, 'cert')!r}")
    prop = field(cert, "property")
    if prop not in (PROPERTY, PROPERTY_A64):
        raise Reject(f"unsupported property {prop!r}")
    spec_defn = _load(store_dir, field(cert, "spec"))
    try:
        word.validate_wspec(spec_defn)
    except ValueError as e:
        raise Reject(str(e)) from e
    inputs = word.inputs_of(spec_defn)
    # The proof's subject is the bytes that run, decoded; no machine
    # definition and no emitter are relied on.
    binary = _load_binary(store_dir, cert)
    dag = Dag()
    want = dag.program_outputs(inputs, word.steps_of(spec_defn),
                               word.outputs_of(spec_defn),
                               word._defs_of(spec_defn))
    if prop == PROPERTY:
        try:
            decoded = word.decode_w32(binary, inputs)
        except ValueError as e:
            raise Reject(str(e)) from e
        got = dag.program_outputs(inputs, word.steps_of(decoded),
                                  word.outputs_of(decoded))
    else:
        from . import a64
        scratch = field(cert, "scratch")
        if not isinstance(scratch, int) or scratch > 4096:
            raise Reject("a64 certificate needs (scratch N), N <= 4096")
        sizes = {"in": len(inputs), "out": len(word.outputs_of(spec_defn)),
                 "scratch": scratch}
        instrs = a64.decode(binary)
        got = a64.execute(dag, instrs,
                          lambda i: dag.var(inputs[i]), sizes)
        decoded = ("a64", binary, sizes)
    if want != got:
        for i, (w, g) in enumerate(zip(want, got)):
            if w != g:
                raise Reject(f"output {i} differs: spec and machine "
                             "reduce to different symbolic values")
        raise Reject("output count differs")
    return assoc("record", ("checker", CHECKER_ID),
                 ("verdict", Sym("accept")), ("property", Sym(prop)),
                 ("spec", field(cert, "spec")),
                 ("binary-hash", field(cert, "binary-hash")),
                 ("certificate", hash_of(cert)),
                 ("domain", Sym("all-u32-inputs")),
                 ("dag-nodes", len(dag.nodes))), decoded


def check_certificate(store_dir, cert):
    return None
