"""The producer: specification -> W32 program -> W32 or AArch64 bytes.

Everything here is outside the reliance set: the checker (ode/check.py)
proves whatever bytes arrive, so any other producer -- smarter, faster,
or hostile -- changes no verdict. compile_spec inlines calls into a
straight-line W32 program; emit_w32 and emit_a64 turn it into bytes;
build writes a store a relying party can check.

The AArch64 emitter is naive and honest: every value lives in a scratch
word, each step loads its operands into w9/w10, computes into w11, and
stores. Register allocation and NEON are the obvious next producers.
"""
import os
import struct as _struct

from . import word
from .blake3 import blake3
from .canon import Bytes, Sym, assoc, canonical_bytes, hash_of, parse


def put_definition(store_dir, defn):
    """File a definition in a store under its hash; return the hash."""
    h = hash_of(defn)
    with open(os.path.join(store_dir, h.hex() + ".sexp"), "wb") as f:
        f.write(canonical_bytes(defn))
    return h


_W_OPS = {"copy": 0, "add": 1, "xor": 2, "rotr": 3}


def _operand(e, index):
    if isinstance(e, int):
        return b"\x01" + _struct.pack("<I", e)
    return b"\x00" + _struct.pack("<I", index[e])


def emit_w32(defn) -> bytes:
    word.validate_w32(defn)
    inputs, steps, outputs = word.inputs_of(defn), word.steps_of(defn), word.outputs_of(defn)
    names = list(inputs)
    for name, _ in steps:
        names += name if isinstance(name, list) else [name]
    index = {n: i for i, n in enumerate(names)}
    out = bytearray()
    out += _struct.pack("<H", len(inputs))
    out += _struct.pack("<I", len(names) - len(inputs))
    out += _struct.pack("<H", len(outputs))
    for o in outputs:
        out += _struct.pack("<I", index[o])
    for name, e in steps:
        if isinstance(name, list):  # a call by certificate
            out.append(4)
            out += bytes(e[1])
            out += _struct.pack("<H", len(e) - 2)
            for a in e[2:]:
                out += _operand(a, index)
            out += _struct.pack("<H", len(name))
        elif isinstance(e, (int, Sym)):
            out.append(0)
            out += _operand(e, index)
        elif e[0] == "rotr":
            out.append(3)
            out += _operand(e[1], index)
            out.append(e[2])
        else:
            out.append(_W_OPS[e[0]])
            out += _operand(e[1], index)
            out += _operand(e[2], index)
    return bytes(out)





class Emitter:
    """Words are W32 atoms: each operation appends one step. Evaluating a
    spec in this algebra compiles it (ode/word.py gives the meaning)."""

    def __init__(self, input_names, certified):
        prefix = "t"  # fresh names collide with no input name
        while any(str(n).startswith(prefix) for n in input_names):
            prefix += "t"
        self.prefix, self.n, self.steps = prefix, 0, []
        self.certified = certified  # spec hash -> (certificate hash, outputs)

    def _fresh(self, n):
        names = [Sym(f"{self.prefix}{self.n + i}") for i in range(n)]
        self.n += n
        return names

    def _step(self, e):
        """One single-operation step; its name."""
        name = self._fresh(1)[0]
        self.steps.append([name, e])
        return name

    def const(self, v):
        return v

    def add(self, a, b):
        return self._step([Sym("add"), a, b])

    def xor(self, a, b):
        return self._step([Sym("xor"), a, b])

    def rotr(self, a, n):
        return a if n % 32 == 0 else self._step([Sym("rotr"), a, n % 32])

    def spec_call(self, h, callee, args, ev):
        if h in self.certified:
            cert_hash, n_out = self.certified[h]
            names = self._fresh(n_out)
            self.steps.append([names, [Sym("call"), cert_hash] + list(args)])
            return names
        return ev.apply_spec(callee, args)


def compile_spec(spec_defn, at=None, certified=None, resolve=None):
    """A straight-line W32 program computing the spec at an instantiation.

    A call to a callee in certified ({spec hash: (certificate hash, output
    count)}) becomes a call by certificate; every other call is inlined.
    """
    word.validate_spec(spec_defn)
    at = word.instantiation(spec_defn, at or {})
    inputs = word.word_input_names(spec_defn, at)
    em = Emitter(inputs, certified or {})
    env, it = {}, iter(inputs)
    for name, sort in word.input_sorts(spec_defn):
        if sort == "word":
            env[name] = next(it)
        elif sort == "nat":
            env[name] = word.Nat(at[name])
        else:
            env[name] = [next(it) for _ in range(at[name])]
    outs = word.Evaluator(em, resolve).run_spec(spec_defn, env)
    names = []
    for o in outs:  # outputs must be names: copy constants into a step
        names.append(em._step(o) if isinstance(o, int) else o)
    return assoc("w32", ("inputs", inputs), ("steps", em.steps), ("outputs", names))


RET = 0xD65F03C0


def _ldr(rt, base, idx):
    assert idx < 4096
    return 0xB9400000 | (idx << 10) | (base << 5) | rt


def _str(rt, base, idx):
    assert idx < 4096
    return 0xB9000000 | (idx << 10) | (base << 5) | rt


def _load(r, atom, where):
    if isinstance(atom, int):
        out = [0x52800000 | ((atom & 0xFFFF) << 5) | r]
        if atom >> 16:
            out.append(0x72800000 | (1 << 21) | ((atom >> 16) << 5) | r)
        return out
    base, idx = where[atom]
    return [_ldr(r, base, idx)]


REGS = tuple(range(3, 18))  # the data registers ode/a64.py allows


def emit_a64(machine_defn):
    """A W32 program (no calls) -> (AArch64 bytes, scratch words).

    Register allocation over straight-line code: values live in w3..w17;
    when a register is needed, the value used furthest in the future is
    evicted (Belady's rule, optimal for straight-line code). Inputs and
    constants are reloaded rather than spilled; a computed value still
    live is spilled to a scratch word, and slots are reused once a value
    dies.
    """
    word.validate_w32(machine_defn)
    inputs = word.inputs_of(machine_defn)
    steps = list(word.steps_of(machine_defn))
    outputs = word.outputs_of(machine_defn)
    alias, ops = {}, []  # copies cost nothing: a name may stand for another
    for name, e in steps:
        if isinstance(name, list):
            raise ValueError("emit_a64 compiles programs without calls")
        if isinstance(e, (int, Sym)):
            alias[name] = alias.get(e, e) if isinstance(e, Sym) else e
        else:
            args = [alias.get(x, x) if isinstance(x, Sym) else x
                    for x in (e[1:2] if e[0] == "rotr" else e[1:3])]
            ops.append((name, e[0], args, e[2] if e[0] == "rotr" else None))
    outs = [alias.get(o, o) if isinstance(o, Sym) else o for o in outputs]
    uses = {}
    for t, (_, _, args, _) in enumerate(ops):
        for a in args:
            if isinstance(a, Sym):
                uses.setdefault(a, []).append(t)
    end = len(ops)
    for o in outs:
        if isinstance(o, Sym):
            uses.setdefault(o, []).append(end)
    in_index = {n: i for i, n in enumerate(inputs)}
    reg_of, holder = {}, {r: None for r in REGS}  # value <-> register
    slot_of, free_slots, n_slots = {}, [], [0]
    code = []

    def next_use(v, t):
        for u in uses.get(v, ()):
            if u >= t:
                return u
        return None

    def free_reg(t, pinned):
        for r in REGS:
            if holder[r] is None and r not in pinned:
                return r
        victim = max((r for r in REGS if r not in pinned),
                     key=lambda r: (next_use(holder[r], t) is None and 10**9)
                     or next_use(holder[r], t))
        v = holder[victim]
        if next_use(v, t) is not None and v not in in_index and v not in slot_of:
            slot = free_slots.pop() if free_slots else n_slots[0]
            if slot == n_slots[0]:
                n_slots[0] += 1
            slot_of[v] = slot
            code.append(_str(victim, 2, slot))
        del reg_of[v]
        holder[victim] = None
        return victim

    def into_reg(a, t, pinned):
        if isinstance(a, int):
            r = free_reg(t, pinned)
            code.extend(_load(r, a, {}))
            return r  # a constant occupies no lasting register
        if a in reg_of:
            return reg_of[a]
        r = free_reg(t, pinned)
        code.append(_ldr(r, 0, in_index[a]) if a in in_index
                    else _ldr(r, 2, slot_of[a]))
        reg_of[a], holder[r] = r, a
        return r

    def release_dead(t):
        for r in REGS:
            v = holder[r]
            if v is not None and next_use(v, t) is None:
                holder[r] = None
                del reg_of[v]
        for v in list(slot_of):
            if next_use(v, t) is None:
                free_slots.append(slot_of.pop(v))

    for t, (name, op, args, count) in enumerate(ops):
        pinned = {reg_of[a] for a in args if isinstance(a, Sym) and a in reg_of}
        regs = []
        for a in args:  # operand registers stay pinned until the op runs
            r = into_reg(a, t, pinned)
            pinned.add(r)
            regs.append(r)
        release_dead(t + 1)  # operands used for the last time free up now
        d = free_reg(t + 1, set())
        if op == "rotr":
            code.append(0x13800000 | (regs[0] << 16) | (count << 10) | (regs[0] << 5) | d)
        else:
            base = 0x0B000000 if op == "add" else 0x4A000000
            code.append(base | (regs[1] << 16) | (regs[0] << 5) | d)
        reg_of[name], holder[d] = d, name
    for k, o in enumerate(outs):
        code.append(_str(into_reg(o, end, set()), 1, k))
    code.append(RET)
    return b"".join(w.to_bytes(4, "little") for w in code), n_slots[0]


def build(spec_defn, store_dir, isa="w32", at=None, library=None):
    """Write a store: the spec, its callees, binaries, certificates, and
    certificate.sexp naming the top one.

    library ({hash: definition}) supplies callees named in (uses ...).
    For W32 each callee is built and certified first and called by
    certificate, so a checker proves it once; AArch64 makes no calls yet,
    so there callees are inlined.
    """
    os.makedirs(store_dir, exist_ok=True)
    library = library or {}

    def resolve(h):
        put_definition(store_dir, library[h])
        return library[h]

    cert_hash, binary = _certify(spec_defn, store_dir, isa, at or {}, resolve)
    with open(os.path.join(store_dir, "certificate.sexp"), "wb") as f:
        f.write(canonical_bytes(_load_cert(store_dir, cert_hash)))
    return {"spec": hash_of(spec_defn).hex(), "certificate": cert_hash.hex(),
            "binary_hash": blake3(binary).hex(), "binary_len": len(binary)}


def bind(spec_defn, store_dir, isa="a64", library=None):
    """Write a store whose certificate covers every instantiation: the spec
    itself, with each callee bound to a certified implementation in isa."""
    os.makedirs(store_dir, exist_ok=True)
    library = library or {}

    def resolve(h):
        put_definition(store_dir, library[h])
        return library[h]

    pairs = []
    for h in sorted(word.uses_of(spec_defn).values()):
        ch, _ = _certify(resolve(h), store_dir, isa, {}, resolve)
        pairs.append([h, ch])
    cert = assoc("certificate", ("cert", Sym("correctness")),
                 ("property", Sym("spec-with-callees-v1")),
                 ("spec", put_definition(store_dir, spec_defn)), ("callees", pairs))
    cert_hash = put_definition(store_dir, cert)
    with open(os.path.join(store_dir, "certificate.sexp"), "wb") as f:
        f.write(canonical_bytes(cert))
    return {"spec": hash_of(spec_defn).hex(), "certificate": cert_hash.hex()}


def _load_cert(store_dir, h):
    with open(os.path.join(store_dir, h.hex() + ".sexp"), "rb") as f:
        return parse(f.read())


def _certify(spec_defn, store_dir, isa, at, resolve):
    certified = {}
    if isa == "w32":
        for h in word.uses_of(spec_defn).values():
            callee = resolve(h)
            ch, _ = _certify(callee, store_dir, isa, {}, resolve)
            n_out = len(word.run(callee, {}, [0] * len(word.inputs_of(callee)),
                                 resolve))
            certified[h] = (ch, n_out)
    program = compile_spec(spec_defn, at, certified, resolve)
    if isa == "w32":
        binary, extra = emit_w32(program), ()
    elif isa == "a64":
        binary, scratch = emit_a64(program)
        extra = (("scratch", scratch),)
    else:
        raise ValueError(f"unknown isa {isa!r}")
    with open(os.path.join(store_dir, blake3(binary).hex() + ".bin"), "wb") as f:
        f.write(binary)
    at_field = (("at", [[Sym(k), v] for k, v in sorted(at.items())]),) if at else ()
    cert = assoc("certificate", ("cert", Sym("correctness")),
                 ("property", Sym(f"equals-spec-{isa}-v1")),
                 ("spec", put_definition(store_dir, spec_defn)), *at_field,
                 ("binary-hash", Bytes(blake3(binary))), *extra)
    return put_definition(store_dir, cert), binary


def library_of(directory):
    """Every .sexp definition in a directory, by hash: a producer's library."""
    lib = {}
    for name in sorted(os.listdir(directory)):
        if name.endswith(".sexp"):
            with open(os.path.join(directory, name), "rb") as f:
                try:
                    d = parse(f.read())
                except ValueError:
                    continue
            lib[hash_of(d)] = d
    return lib
