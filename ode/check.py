"""The checker (reliance R1): a certificate's bytes compute its spec.

It proves by symbolic evaluation: the specification and the program
decoded from the binary -- W32, or AArch64 (ode/a64.py) -- are both
evaluated over fresh variables in one algebra, the DAG below, whose
smart constructors build canonical expressions -- constant folding, xor
cancellation, add/xor flattening under a canonical operand order, rotr
composition, and rotr distributing over xor. Expressions are hash-consed
DAG nodes, so identical subexpressions are one node and size stays
linear in the number of steps. The claim is proved when the two sides'
outputs are the same nodes. Soundness rests on each constructor's
rewrite being a u32 identity, and on nothing about the producer: the
subject of the proof is the binary itself, decoded.

Calls by certificate: when a W32 program calls another program by its
certificate, the checker checks that certificate (once per run) and
represents the call as an opaque node, call(spec, args), for the spec
the callee is proved to compute. A spec's own call to that same spec
becomes the same node -- congruence: the same function of the same
arguments is the same value -- so a proved callee is checked once, not
re-expanded at every call. A spec call the implementation does not make
by certificate is expanded, as before.

The same rule, at the top: a certificate with property
spec-with-callees-v1 says "run this specification itself, with each
callee bound to this certified implementation". The checker checks each
bound certificate, for all inputs, and that it proves exactly the spec
the (uses ...) entry names; then running the specification with the
bound programs computes the specification -- by congruence, at every
instantiation at once. The glue runs in the evaluator; the callees run
as their proved code.
"""
from . import word
from .canon import Bytes, Sym, assoc, field, hash_of
from .store import Reject, load_definition as _load, load_binary as _load_binary

CHECKER_ID = Sym("ode-checker-0.3")
PROPERTIES = ("equals-spec-w32-v1", "equals-spec-a64-v1", "spec-with-callees-v1")
MASK = word.MASK


class Dag:
    def __init__(self):
        self.nodes = []
        self.index = {}
        self.opaque = {}   # spec hash -> output count, for proved callees
        self.spec_of = {}  # callee certificate hash -> its spec hash

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

    def call(self, spec_hash, args, n_out):
        """The outputs of an opaque call to a proved function."""
        node = self._intern(("call", spec_hash, tuple(args)))
        return [self._intern(("out", node, k)) for k in range(n_out)]

    # -- the algebra the evaluator uses (ode/word.py) -------------------
    def spec_call(self, h, callee, args, ev):
        if h in self.opaque:
            return self.call(h, args, self.opaque[h])
        return ev.apply_spec(callee, args)

    def cert_call(self, cert_hash, args, n_out):
        return self.call(self.spec_of[cert_hash], args, n_out)


def check_certificate(store_dir, cert, _seen=None):
    """Returns (record, program). The program is what the proof is about,
    decoded from the bytes read once: run it with run(program, values),
    never the binary file again -- a store's owner may change it."""
    seen = {} if _seen is None else _seen  # certificate hash -> (program, spec)
    if not isinstance(cert, list) or not cert or cert[0] != "certificate":
        raise Reject("not a certificate")
    if field(cert, "cert") != "correctness":
        raise Reject(f"unsupported certificate kind {field(cert, 'cert')!r}")
    prop = field(cert, "property")
    if prop not in PROPERTIES:
        raise Reject(f"unsupported property {prop!r}")
    spec_defn = _load(store_dir, field(cert, "spec"))
    if prop == "spec-with-callees-v1":
        return _check_spec_with_callees(store_dir, cert, spec_defn, seen)
    try:
        word.validate_spec(spec_defn)
        at = word.instantiation(spec_defn, {p[0]: p[1] for p in field(cert, "at") or []})
        inputs = word.word_input_names(spec_defn, at)
    except (ValueError, TypeError, IndexError) as e:
        raise Reject(f"spec or instantiation: {e}") from e
    binary = _load_binary(store_dir, cert)

    def resolve(h):
        callee = _load(store_dir, h)
        try:
            return word.validate_spec(callee)
        except ValueError as e:
            raise Reject(f"callee {h.hex()}: {e}") from e

    dag = Dag()
    callees = {}
    if prop == "equals-spec-w32-v1":
        try:
            decoded = word.decode_w32(binary, inputs)
        except ValueError as e:
            raise Reject(str(e)) from e
        for name, e in word.steps_of(decoded):
            if isinstance(name, list):  # a call by certificate
                callee, callee_spec = _callee(store_dir, e[1], seen)
                if (len(e) - 2, len(name)) != (callee[2]["in"], callee[2]["out"]):
                    raise Reject("call arity differs from the callee's spec")
                callees[e[1]] = callee
                dag.spec_of[e[1]] = callee_spec
                dag.opaque[callee_spec] = callee[2]["out"]
    env, it = {}, iter(inputs)
    for name, sort in word.input_sorts(spec_defn):
        if sort == "word":
            env[name] = dag.var(next(it))
        elif sort == "nat":
            env[name] = word.Nat(at[name])
        else:
            env[name] = [dag.var(next(it)) for _ in range(at[name])]
    try:
        want = word.Evaluator(dag, resolve).run_spec(spec_defn, env)
        sizes = {"in": len(inputs), "out": len(want)}
        if prop == "equals-spec-w32-v1":
            got = word.Evaluator(dag).run_w32(
                decoded, {n: dag.var(n) for n in inputs})
            program = ("w32", decoded, sizes, callees)
        else:
            from . import a64
            scratch = field(cert, "scratch")
            if not isinstance(scratch, int) or not 0 <= scratch <= 4096:
                raise Reject("a64 certificate needs (scratch N), 0 <= N <= 4096")
            sizes["scratch"] = scratch
            got = a64.execute(dag, a64.decode(binary),
                              lambda i: dag.var(inputs[i]), sizes)
            program = ("a64", binary, sizes, {})
    except (ValueError, TypeError, IndexError, KeyError, RecursionError) as e:
        raise Reject(f"evaluation fails: {type(e).__name__}: {e}") from e
    if want != got:
        for i, (w, g) in enumerate(zip(want, got)):
            if w != g:
                raise Reject(f"output {i} differs: spec and machine "
                             "reduce to different symbolic values")
        raise Reject("output count differs")
    return assoc("record", ("checker", CHECKER_ID),
                 ("verdict", Sym("accept")), ("property", Sym(prop)),
                 ("spec", field(cert, "spec")),
                 ("at", field(cert, "at") or []),
                 ("binary-hash", field(cert, "binary-hash")),
                 ("certificate", hash_of(cert)),
                 ("domain", Sym("all-u32-inputs")),
                 ("dag-nodes", len(dag.nodes))), program


def _check_spec_with_callees(store_dir, cert, spec_defn, seen):
    try:
        word.validate_spec(spec_defn)
    except ValueError as e:
        raise Reject(f"spec: {e}") from e
    binding = {}
    for pair in field(cert, "callees") or []:
        if not (isinstance(pair, list) and len(pair) == 2
                and all(isinstance(x, Bytes) and len(x) == 32 for x in pair)):
            raise Reject("callees entries are (#spec-hash #certificate-hash)")
        binding[pair[0]] = pair[1]
    uses = set(word.uses_of(spec_defn).values())
    if set(binding) != uses:
        raise Reject("callees must bind exactly the spec's (uses ...)")
    bound = {}
    for spec_hash, cert_hash in binding.items():
        program, proved = _callee(store_dir, cert_hash, seen)
        if proved != spec_hash:
            raise Reject(f"bound certificate {cert_hash.hex()} proves another spec")
        if program[0] == "spec":
            raise Reject("a bound callee must be proved code, not another binding")
        bound[spec_hash] = program
    record = assoc("record", ("checker", CHECKER_ID), ("verdict", Sym("accept")),
                   ("property", Sym("spec-with-callees-v1")),
                   ("spec", field(cert, "spec")), ("at", []),
                   ("binary-hash", Bytes(bytes(32))),
                   ("certificate", hash_of(cert)),
                   ("domain", Sym("every-instantiation")), ("dag-nodes", 0))
    return record, ("spec", spec_defn, {"in": None, "out": None}, bound)


def _callee(store_dir, cert_hash, seen):
    """Check a callee's certificate once per run: (program, spec hash)."""
    if cert_hash in seen:
        if seen[cert_hash] is None:
            raise Reject("a certificate calls itself")
        return seen[cert_hash]
    seen[cert_hash] = None  # in progress: a cycle is a reject
    cert = _load(store_dir, cert_hash)
    _, program = check_certificate(store_dir, cert, seen)
    seen[cert_hash] = (program, field(cert, "spec"))
    return seen[cert_hash]


def run(program, values, at=None):
    """Run a proved program: W32 by interpretation, AArch64 natively, a
    spec with bound callees in the evaluator (at its instantiation)."""
    isa, body, sizes, callees = program
    if isa == "spec":
        if any(not (isinstance(v, int) and 0 <= v < 2 ** 32) for v in values):
            raise ValueError("inputs must be u32 words")
        at = dict(at or {})
        lists = [n for n, s in word.input_sorts(body) if s == "words"]
        n_words = sum(1 for _, s in word.input_sorts(body) if s == "word")
        if len(lists) == 1 and lists[0] not in at:
            at[lists[0]] = len(values) - n_words
        word.instantiation(body, at)
        return word.run(body, at, values, bound={
            h: (lambda args, p=p: run(p, args)) for h, p in callees.items()})
    if len(values) != sizes["in"] or any(
            not (isinstance(v, int) and 0 <= v < 2 ** 32) for v in values):
        raise ValueError(f"inputs must be {sizes['in']} u32 words")
    if isa == "w32":
        return word.run(body, {}, values, certified={
            h: (lambda args, p=p: run(p, args)) for h, p in callees.items()})
    from . import native
    return native.Function(body, sizes["in"], sizes["out"],
                           sizes["scratch"])(values)
