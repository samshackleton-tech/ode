"""Equations and induction: Ode's first proof-object kernel.

See KERNEL.md for the complete grammar, rules, semantics, and boundary.
verify(theory, goal, proof) checks a proof of the *caller's* goal in the
caller's theory. It performs no proof search or program execution. Every
conclusion is inferred from a rule; the proof cannot introduce axioms.
The evaluator and symbolic executor in check.py are outside this kernel.
"""
from .canon import Bytes, Sym, canonical_bytes, hash_of

VERSION = 2
MAX_DEPTH = 128
MAX_INPUT_BYTES = 1_000_000
DEFAULT_WORK = 1_000_000


class Reject(ValueError):
    """A malformed object, invalid derivation, or exhausted work budget."""


def require(ok, message):
    if not ok:
        raise Reject(message)


class Kernel:
    """One invocation's term arena and deterministic work accounting."""

    def __init__(self, work):
        require(type(work) is int and 0 < work <= DEFAULT_WORK, "invalid work budget")
        self.remaining = self.limit = work
        self.nodes, self.ids = [], {}
        self.sorts = {Sym("Nat")}
        self.signature = {Sym("zero"): ((), Sym("Nat")),
                          Sym("succ"): ((Sym("Nat"),), Sym("Nat"))}
        self.definitions = {}
        self.lemmas = []  # closed, universally quantified equations, checked in order
        self.rules = 0

    def spend(self, n=1):
        self.remaining -= n
        require(self.remaining >= 0, "kernel work budget exhausted")

    def scan(self, value):
        """Bound syntax before hashing, parsing terms, or running rules."""
        todo = [(value, 0)]
        while todo:
            self.spend()
            v, depth = todo.pop()
            require(depth <= MAX_DEPTH, "syntax exceeds depth limit")
            if type(v) is list:
                todo.extend((x, depth + 1) for x in v)
            elif type(v) is Sym:
                require(0 < len(v) <= 128, "symbol exceeds length limit")
            elif type(v) is Bytes:
                require(len(v) == 32, "expected a 32-byte identity")
            else:
                require(type(v) is int and 0 <= v < 2**64, "invalid syntax atom")
        try:
            data = canonical_bytes(value)
        except (ValueError, UnicodeError) as e:
            raise Reject(f"invalid canonical value: {e}") from e
        require(len(data) <= MAX_INPUT_BYTES, "object exceeds byte limit")

    def intern(self, tag, name, args, sort):
        self.spend(1 + len(args))
        key = (tag, name, tuple(args), sort)
        if key not in self.ids:
            depth = 1 + max((self.nodes[i][4] for i in args), default=0)
            require(depth <= MAX_DEPTH, "term exceeds depth limit")
            self.ids[key] = len(self.nodes)
            self.nodes.append((*key, depth))
        return self.ids[key]

    def app(self, name, args):
        require(type(name) is Sym and name in self.signature, f"unknown function {name!r}")
        sorts, result = self.signature[name]
        require(len(args) == len(sorts), f"wrong arity for {name}")
        require(all(self.nodes[a][3] == s for a, s in zip(args, sorts)),
                f"argument sort mismatch for {name}")
        return self.intern("app", name, args, result)

    def parameters(self, declarations):
        require(type(declarations) is list, "parameters must be a list")
        env = {}
        for p in declarations:
            require(type(p) is list and len(p) == 2, "parameter is (name sort)")
            name, sort = p
            require(type(name) is Sym and name not in env, "invalid or duplicate parameter")
            require(type(sort) is Sym and sort in self.sorts, "unknown parameter sort")
            env[name] = self.intern("var", name, (), sort)
        return env

    def term(self, expression, env):
        self.spend()
        if type(expression) is Sym:
            require(expression in env, f"unbound variable {expression}")
            return env[expression]
        require(type(expression) is list and expression, "term is a variable or application")
        return self.app(expression[0], [self.term(a, env) for a in expression[1:]])

    def equation(self, expression, env):
        require(type(expression) is list and len(expression) == 3 and expression[0] == "eq",
                "expected (eq left right)")
        a, b = (self.term(t, env) for t in expression[1:])
        require(self.nodes[a][3] == self.nodes[b][3], "equation sort mismatch")
        return a, b

    def substitute(self, root, mapping):
        """Simultaneous, sort-preserving substitution on a DAG, visited once.
        Replacement terms are returned as-is (never recursively substituted).
        """
        self.spend(len(mapping))
        require(all(self.nodes[v][0] == "var" and self.nodes[v][3] == self.nodes[t][3]
                    for v, t in mapping.items()), "substitution sort mismatch")
        memo = dict(mapping)
        todo = [root]
        while todo:
            self.spend()
            i = todo[-1]
            if i in memo:
                todo.pop()
                continue
            tag, name, args, sort, _ = self.nodes[i]
            pending = [a for a in args if a not in memo]
            if pending:
                todo.extend(pending)
            else:
                memo[i] = i if tag == "var" else self.app(name, [memo[a] for a in args])
                todo.pop()
        return memo[root]

    def load_theory(self, theory):
        header(theory, "theory", 5)
        require(type(theory[2]) is list, "sorts must be a list")
        for s in theory[2]:
            require(type(s) is Sym and s not in self.sorts, "duplicate or invalid sort")
            self.sorts.add(s)
        require(type(theory[3]) is list and type(theory[4]) is list,
                "symbols and definitions must be lists")
        for decl in theory[3]:
            self.declare(decl)
        for definition in theory[4]:
            require(type(definition) is list and len(definition) == 5,
                    "definition is (name parameters result zero-body (predecessor step-body))")
            name, params, result, base, step = definition
            env = self.parameters(params)
            require(params and params[0][1] == "Nat", "definition's first parameter must be Nat")
            require(type(step) is list and len(step) == 2 and type(step[0]) is Sym,
                    "step must name its predecessor")
            pred = step[0]
            require(pred not in env, "predecessor must be fresh")
            # The counter itself is unavailable in either branch. Only the
            # predecessor is available in the step. Self is unavailable in zero.
            tail = dict(list(env.items())[1:])
            base_term = self.term(base, tail)
            self.declare([name, [p[1] for p in params], result])
            k = self.intern("var", pred, (), Sym("Nat"))
            step_env = dict(tail)
            step_env[pred] = k
            step_term = self.term(step[1], step_env)
            require(self.nodes[base_term][3] == result == self.nodes[step_term][3],
                    "definition result sort mismatch")
            # All self calls must decrease the first argument exactly to k.
            todo, visited = [step_term], set()
            while todo:
                self.spend()
                i = todo.pop()
                if i in visited:
                    continue
                visited.add(i)
                tag, f, args, _, _ = self.nodes[i]
                if tag == "app" and f == name:
                    require(args and args[0] == k, "recursive call does not decrease to predecessor")
                todo.extend(args)
            self.definitions[name] = (tuple(tail.values()), k, base_term, step_term)

    def declare(self, decl):
        require(type(decl) is list and len(decl) == 3, "symbol is (name argument-sorts result)")
        name, args, result = decl
        require(type(name) is Sym and name not in self.signature, "duplicate or invalid function")
        require(type(args) is list and all(type(s) is Sym and s in self.sorts for s in args),
                "unknown argument sort")
        require(type(result) is Sym and result in self.sorts, "unknown result sort")
        self.signature[name] = (tuple(args), result)

    def unfold(self, term):
        tag, f, args, _, _ = self.nodes[term]
        require(tag == "app" and f in self.definitions, "unfold needs a defined function")
        params, k, base, step = self.definitions[f]
        head = self.nodes[args[0]]
        require(head[0] == "app" and head[1] in ("zero", "succ"),
                "unfold needs a zero or successor counter")
        mapping = dict(zip(params, args[1:]))
        body = base
        if head[1] == "succ":
            mapping[k] = head[2][0]
            body = step
        return term, self.substitute(body, mapping)

    def block(self, steps, env, ih=None):
        """Each step infers an equation. Only backwards references exist.
        ih is (generalized parameters, equation) and exists only in the
        induction step; its counter is fixed, never substitutable.
        """
        require(type(steps) is list and steps, "proof block must contain steps")
        proved = []

        def ref(i):
            require(type(i) is int and 0 <= i < len(proved), "proof reference is not an earlier step")
            return proved[i]

        for instruction in steps:
            self.spend()
            self.rules += 1
            require(type(instruction) is list and instruction and type(instruction[0]) is Sym,
                    "invalid proof instruction")
            rule, *args = instruction
            if rule == "refl" and len(args) == 1:
                t = self.term(args[0], env)
                eq = t, t
            elif rule == "sym" and len(args) == 1:
                a, b = ref(args[0])
                eq = b, a
            elif rule == "trans" and len(args) == 2:
                a, b = ref(args[0])
                c, d = ref(args[1])
                require(b == c, "transitivity middle terms differ")
                eq = a, d
            elif rule == "cong" and args:
                pairs = [ref(i) for i in args[1:]]
                eq = (self.app(args[0], [p[0] for p in pairs]),
                      self.app(args[0], [p[1] for p in pairs]))
            elif rule == "unfold" and args:
                eq = self.unfold(self.term(args, env))
            elif rule == "lemma" and args:
                i = args[0]
                require(type(i) is int and 0 <= i < len(self.lemmas),
                        "lemma reference is not an earlier proved lemma")
                eq = self.instance(self.lemmas[i], args[1:], env)
            elif rule == "ih":
                require(ih is not None, "induction hypothesis outside step")
                eq = self.instance(ih, args, env)
            else:
                raise Reject(f"unknown rule or wrong arity: {rule}")
            proved.append(eq)
        return proved[-1]

    def instance(self, theorem, args, env):
        params, conclusion = theorem
        require(len(args) == len(params), "theorem argument count")
        mapping = dict(zip(params, [self.term(t, env) for t in args]))
        return tuple(self.substitute(t, mapping) for t in conclusion)

    def prove(self, declarations, equation, form):
        """Discharge a closed universally quantified equation. The local
        hypothesis of an induction never becomes an exported lemma.
        """
        env = self.parameters(declarations)
        conclusion = self.equation(equation, env)
        require(type(form) is list and form, "missing derivation")
        if form[0] == "derive" and len(form) == 2:
            require(self.block(form[1], env) == conclusion,
                    "proof concludes a different equation")
        elif form[0] == "induct" and len(form) == 5:
            _, n, pred, base, step = form
            require(type(n) is Sym and n in env and self.nodes[env[n]][3] == "Nat",
                    "induction variable must be a declared Nat")
            require(type(pred) is Sym and pred not in env, "induction predecessor must be fresh")
            tail = {v: t for v, t in env.items() if v != n}
            zero = self.app(Sym("zero"), [])
            p = self.intern("var", pred, (), Sym("Nat"))
            successor = self.app(Sym("succ"), [p])
            expected_base = tuple(self.substitute(t, {env[n]: zero}) for t in conclusion)
            require(self.block(base, tail) == expected_base,
                    "induction base proves a different equation")
            hypothesis = tuple(self.substitute(t, {env[n]: p}) for t in conclusion)
            expected_step = tuple(self.substitute(t, {env[n]: successor}) for t in conclusion)
            ih = tuple(tail.values()), hypothesis
            step_env = dict(tail)
            step_env[pred] = p
            require(self.block(step, step_env, ih) == expected_step,
                    "induction step proves a different equation")
        else:
            raise Reject("expected derive or induct")
        return tuple(env.values()), conclusion


def header(obj, kind, size):
    require(type(obj) is list and len(obj) == size and obj[0] == kind,
            f"expected {kind} with exactly {size - 1} fields")
    require(type(obj[1]) is int and obj[1] == VERSION, f"unsupported {kind} version")


def verify(theory, goal, proof, work=DEFAULT_WORK):
    """Check exact goal and theory supplied by the relying party.

    Reject on any broken contract. Returns deterministic counts and the
    identities of the three objects; performs no I/O and reads no clock.
    """
    k = Kernel(work)
    for obj in (theory, goal, proof):
        k.scan(obj)
    k.load_theory(theory)
    header(goal, "goal", 5)
    require(goal[2] == hash_of(theory), "goal names a different theory")
    header(proof, "proof", 5)
    require(proof[2] == hash_of(goal), "proof names a different goal")
    require(type(proof[3]) is list, "lemmas must be a list")
    for lemma in proof[3]:
        require(type(lemma) is list and len(lemma) == 4 and lemma[0] == "lemma",
                "lemma is (lemma parameters equation derivation)")
        # Append only after the entire lemma is proved. This forbids self
        # reference, forward reference, and exporting an induction hypothesis.
        k.lemmas.append(k.prove(*lemma[1:]))
    k.prove(goal[3], goal[4], proof[4])
    return {"theory": hash_of(theory), "goal": hash_of(goal), "proof": hash_of(proof),
            "rules": k.rules, "lemmas": len(k.lemmas), "terms": len(k.nodes), "work": k.limit - k.remaining}
