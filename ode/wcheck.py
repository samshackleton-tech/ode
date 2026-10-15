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
rewrite being a u32 identity, and on nothing about the producer: any
machine definition arriving with honestly recomputed hashes is still
recomputed here from its bytes.
"""
from . import word
from .blake3 import blake3_hex
from .canon import Sym, assoc, field, hash_of
from .checker import Reject, _load

CHECKER_ID = Sym("ode-wchecker-0.1")
PROPERTY = "equals-wspec-v1"
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

    def expr(self, e, env):
        if isinstance(e, int):
            return self.const(e)
        if isinstance(e, Sym):
            return env[e]
        if e[0] == "add":
            return self.add(self.expr(e[1], env), self.expr(e[2], env))
        if e[0] == "xor":
            return self.xor(self.expr(e[1], env), self.expr(e[2], env))
        return self.rotr(self.expr(e[1], env), e[2])

    def program_outputs(self, inputs, steps, outputs):
        env = {name: self.var(name) for name in inputs}
        for name, e in steps:
            env[name] = self.expr(e, env)
        return [env[o] for o in outputs]


def check_certificate(store_dir, cert):
    """Returns a checker record or raises Reject."""
    if not isinstance(cert, list) or not cert or cert[0] != "certificate":
        raise Reject("not a certificate")
    if field(cert, "cert") != "correctness":
        raise Reject(f"unsupported certificate kind {field(cert, 'cert')!r}")
    if field(cert, "property") != PROPERTY:
        raise Reject(f"unsupported property {field(cert, 'property')!r}")
    spec_defn = _load(store_dir, field(cert, "spec"))
    machine_defn = _load(store_dir, field(cert, "machine"))
    try:
        word.validate_wspec(spec_defn)
        word.validate_wmachine(machine_defn)
    except ValueError as e:
        raise Reject(str(e)) from e
    inputs = word.inputs_of(spec_defn)
    if word.inputs_of(machine_defn) != inputs:
        raise Reject("spec and machine disagree on inputs")
    if field(cert, "inputs") != len(inputs):
        raise Reject("certificate names the wrong input count")
    binary_hex = field(cert, "binary-hex")
    if not isinstance(binary_hex, Sym):
        raise Reject("certificate carries no binary")
    try:
        binary = bytes.fromhex(str(binary_hex))
    except ValueError as e:
        raise Reject("binary is not hex") from e
    if blake3_hex(binary) != field(cert, "binary-hash"):
        raise Reject("binary does not hash to the certificate's binary-hash")
    if word.emit_w32(machine_defn) != binary:
        raise Reject("binary is not the emitter's output for the machine "
                     "definition")
    try:
        decoded = word.decode_w32(binary, inputs)
    except ValueError as e:
        raise Reject(str(e)) from e
    # The proof: one DAG, both sides, outputs must be identical nodes.
    dag = Dag()
    want = dag.program_outputs(inputs, word.steps_of(spec_defn),
                               word.outputs_of(spec_defn))
    got = dag.program_outputs(inputs, word.steps_of(decoded),
                              word.outputs_of(decoded))
    if want != got:
        for i, (w, g) in enumerate(zip(want, got)):
            if w != g:
                raise Reject(f"output {i} differs: spec and machine "
                             "reduce to different symbolic values")
        raise Reject("output count differs")
    return assoc("record", ("checker", CHECKER_ID),
                 ("verdict", Sym("accept")), ("property", Sym(PROPERTY)),
                 ("spec", field(cert, "spec")),
                 ("machine", field(cert, "machine")),
                 ("binary-hash", field(cert, "binary-hash")),
                 ("certificate", Sym(hash_of(cert))),
                 ("domain", Sym("all-u32-inputs")),
                 ("dag-nodes", len(dag.nodes)))


def check_store(store_dir):
    import os
    from .canon import read_canonical
    with open(os.path.join(store_dir, "certificate.sexp"), "rb") as f:
        cert = read_canonical(f.read())
    return check_certificate(store_dir, cert)
