"""AArch64, the first real machine layer (SPEC s3.3, reliance R4).

A binary is one function with the C signature

    void f(const uint32_t *in /*x0*/, uint32_t *out /*x1*/,
           uint32_t *scratch /*x2*/);

made only of these eight instruction forms (32-bit variants), each
matched exactly against its encoding in the Arm Architecture Reference
Manual; any other word is a reject:

    LDR  Wt, [Xn, #imm]      0xB9400000  Xn is x0, x1, or x2
    STR  Wt, [Xn, #imm]      0xB9000000  Xn is x1 or x2 (inputs are read-only)
    MOVZ Wd, #imm16, LSL #s  0x52800000  s is 0 or 16
    MOVK Wd, #imm16, LSL #s  0x72800000  Wd must hold a known constant
    ADD  Wd, Wn, Wm          0x0B000000  no shift
    EOR  Wd, Wn, Wm          0x4A000000  no shift
    ROR  Wd, Wn, #r          0x13800000  EXTR Wd, Wn, Wn, #r
    RET                      0xD65F03C0  the last word, and only there

Data registers are w3..w17 (caller-saved, never the argument bases), so
the function keeps the platform calling convention. There are no
branches and every address is a base plus a constant, so the trace and
every address it touches depend on nothing but the code: the
constant-time shape, by construction. Every access is checked against
the region sizes (inputs and outputs from the specification, scratch
from the certificate).

The model below *is* reliance R4: it says what each form does. It is
cross-checked against this CPU on random states (tests/test_a64.py).
"""
from .store import Reject

DATA_REGS = range(3, 18)
REGION = {0: "in", 1: "out", 2: "scratch"}


def _f(w, lo, n):
    return (w >> lo) & ((1 << n) - 1)


def decode(code):
    """Bytes -> list of (form, fields). Rejects any word not in the table."""
    if len(code) % 4 or not code:
        raise Reject("a64: code is not a whole number of instructions")
    words = [int.from_bytes(code[i:i + 4], "little")
             for i in range(0, len(code), 4)]
    out = []
    for k, w in enumerate(words):
        rd, rn, rm = _f(w, 0, 5), _f(w, 5, 5), _f(w, 16, 5)
        if w == 0xD65F03C0:
            if k != len(words) - 1:
                raise Reject("a64: RET only as the last instruction")
            out.append(("ret",))
            continue
        top = w & 0xFFC00000
        if top in (0xB9400000, 0xB9000000):
            form = "ldr" if top == 0xB9400000 else "str"
            if rd not in DATA_REGS or rn not in (REGION if form == "ldr" else (1, 2)):
                raise Reject(f"a64: {form} with registers outside the contract at {k}")
            out.append((form, rd, REGION[rn], _f(w, 10, 12)))
            continue
        if (w & 0xFF800000) in (0x52800000, 0x72800000):
            hw = _f(w, 21, 2)
            if hw > 1 or rd not in DATA_REGS:
                raise Reject(f"a64: bad move at {k}")
            form = "movz" if (w & 0xFF800000) == 0x52800000 else "movk"
            out.append((form, rd, _f(w, 5, 16), hw * 16))
            continue
        if (w & 0xFFE0FC00) in (0x0B000000, 0x4A000000):
            if not all(r in DATA_REGS for r in (rd, rn, rm)):
                raise Reject(f"a64: data register outside w3..w17 at {k}")
            out.append(("add" if (w & 0xFF000000) == 0x0B000000 else "eor",
                        rd, rn, rm))
            continue
        if (w & 0xFFE00000) == 0x13800000 and _f(w, 15, 1) == 0:
            if rn != rm or not all(r in DATA_REGS for r in (rd, rn)):
                raise Reject(f"a64: EXTR other than ROR at {k}")
            out.append(("ror", rd, rn, _f(w, 10, 5)))
            continue
        raise Reject(f"a64: instruction {w:08x} at {k} is outside the model")
    if not out or out[-1] != ("ret",):
        raise Reject("a64: function must end with RET")
    return out


def execute(dag, instrs, read_in, sizes):
    """Run instrs on dag; read_in(i) gives input word i. Returns out[]."""
    regs = {}
    mem = {"out": {}, "scratch": {}}

    def reg(r):
        if r not in regs:
            raise Reject(f"a64: w{r} read before it is written")
        return regs[r]

    for ins in instrs:
        form = ins[0]
        if form in ("ldr", "str"):
            _, rt, region, idx = ins
            if idx >= sizes[region]:
                raise Reject(f"a64: {region}[{idx}] is outside its "
                             f"{sizes[region]} words")
            if form == "ldr":
                if region == "in":
                    regs[rt] = read_in(idx)
                elif idx in mem[region]:
                    regs[rt] = mem[region][idx]
                else:
                    raise Reject(f"a64: {region}[{idx}] read before written")
            else:
                mem[region][idx] = reg(rt)
        elif form == "movz":
            regs[ins[1]] = dag.const(ins[2] << ins[3])
        elif form == "movk":
            node = dag.nodes[reg(ins[1])]
            if node[0] != "const":
                raise Reject("a64: MOVK on a value that is not a constant")
            v = (node[1] & ~(0xFFFF << ins[3])) | (ins[2] << ins[3])
            regs[ins[1]] = dag.const(v)
        elif form == "add":
            regs[ins[1]] = dag.add(reg(ins[2]), reg(ins[3]))
        elif form == "eor":
            regs[ins[1]] = dag.xor(reg(ins[2]), reg(ins[3]))
        elif form == "ror":
            regs[ins[1]] = dag.rotr(reg(ins[2]), ins[3])
    outs = []
    for k in range(sizes["out"]):
        if k not in mem["out"]:
            raise Reject(f"a64: out[{k}] is never written")
        outs.append(mem["out"][k])
    return outs
