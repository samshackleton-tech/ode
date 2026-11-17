#!/usr/bin/env python3
"""shadow: the table beside today's verifier, on a real verification, instruction by instruction.

    python3 shadow.py [FUNCTION]            the hash file ../kcheck/b3hashr.o (default: all its functions)
    python3 shadow.py --file PROGRAM.o      a file of byte programs (../kcheck/programs/NAME/odeNAME.o)
    python3 shadow.py ... --list            also list, by instruction, where the two do not go together

kcheck's verifier (kfn.py, and kbyte.py on it) runs every path of every function as it always does. Before
each instruction, a copy of the machine is given to step.py, which does the instruction by the table; then
the verifier does it its own way, and the two machines are compared whole: registers, vector registers,
flags, memory, facts, where the next instruction is, the stack used. Each instruction step is one of:

    same        both did it and left the same machine; or both split the path the same way; or both refused
    DIFFERS     both did it, and left different machines (or split the path differently): a fault in one
    refused     the table has no answer where the verifier has one (a row or a rule is missing)
    answered    the table has an answer where the verifier refuses (the table's rule is wider)

Exit 1 if anything differs or is refused: the table cannot yet take the verifier's place on that file."""
import os, runpy, sys
HERE = os.path.dirname(os.path.abspath(__file__))
KCHECK = os.path.join(HERE, "..", "kcheck")
sys.path.insert(0, KCHECK); sys.path.insert(0, HERE)
import kfn
from kterms import Fail
import step

COUNT = {"same": 0, "DIFFERS": 0, "refused": 0, "answered": 0, "calls": 0}
WHERE = {"DIFFERS": {}, "refused": {}, "answered": {}}


def differences(a, b):
    """The parts in which two machines differ."""
    va, vb = vars(a), vars(b)
    # (things of the specification that are made anew at each step and have no equality of their own are compared as they print)
    out = [k for k in sorted(set(va) | set(vb)) if k not in ("memo", "facts") and va.get(k) != vb.get(k) and repr(va.get(k)) != repr(vb.get(k))]
    return out + [f"facts.{k}" for k in ("ge", "ne", "eq", "below", "bad") if getattr(a.facts, k) != getattr(b.facts, k)]


def note(kind, ins, why):
    COUNT[kind] += 1
    if kind != "same":
        head = " ".join(map(str, ins))
        WHERE[kind].setdefault(head if kind == "DIFFERS" else ins[0], [0, f"{head}: {why}"])[0] += 1


def shadowed(one):
    def both(self):
        ins = self.rows[self.pc][1] if self.pc in self.rows else ["(no instruction)"]
        if ins[0] == ".call":
            # a call is the machine's own rule, the same code for both, and it names new unknowns by counting:
            # done twice it would not leave the same names. Only what comes after the call is the table's.
            COUNT["calls"] += 1
            return one(self)
        probe = self.clone()
        try: step.step(probe); mine = ("did",)
        except kfn.Fork as f: mine = ("split", f.kind, f.x)
        except Fail as e: mine = ("refused", str(e))
        try: one(self)
        except kfn.Fork as f:
            theirs = ("split", f.kind, f.x)
            note("same" if mine == theirs else "refused" if mine[0] == "refused" else "DIFFERS", ins, f"the table: {mine}; the verifier: {theirs}")
            raise
        except Fail as e:
            note("same" if mine[0] == "refused" else "answered", ins, f"the verifier: {e}")
            raise
        if mine[0] == "did":
            d = differences(probe, self)
            note("DIFFERS" if d else "same", ins, "they differ in " + ", ".join(d) + "".join(f"\n      {k}: the table {vars(probe).get(k)!r}\n      {' ' * len(k)}  the verifier {vars(self).get(k)!r}" for k in d[:3] if not k.startswith("facts.") and k not in ("mem", "back")))
        else: note("refused" if mine[0] == "refused" else "DIFFERS", ins, f"the table: {mine[1] if mine[0] == 'refused' else mine}")
    return both


def main():
    a = sys.argv[1:]
    listing = "--list" in a
    if listing: a.remove("--list")
    kfn.Machine.one = shadowed(kfn.Machine.one)
    os.chdir(KCHECK)
    if a[:1] == ["--file"]: script, sys.argv = os.path.join("programs", "check_file.py"), ["check_file.py", os.path.relpath(os.path.join(os.path.dirname(HERE), a[1]) if not os.path.isabs(a[1]) and not os.path.exists(a[1]) else a[1])]
    else: script, sys.argv = "check_binary.py", ["check_binary.py", "b3hashr.o"] + a[:1] + ["--spec", "blake3.spec", "--no-ends"]
    try: runpy.run_path(script, run_name="__main__")
    except SystemExit as e: print("the verification's exit:", e.code)
    total = sum(COUNT.values())
    if listing:
        for kind in ("DIFFERS", "refused", "answered"):
            for head, (n, why) in sorted(WHERE[kind].items(), key=lambda t: -t[1][0]): print(f"  {kind} {n:6}  {head if kind != 'DIFFERS' else ''}  e.g. {why}"[:900])
    print(f"shadow: {total} instruction steps by the verifier and by the table: {COUNT['same']} the same, {COUNT['DIFFERS']} differ, "
          f"{COUNT['refused']} the table refuses, {COUNT['answered']} the table answers where the verifier refuses; {COUNT['calls']} are calls (the machine's own rule: not compared)")
    sys.exit(1 if COUNT["DIFFERS"] or COUNT["refused"] else 0)


if __name__ == "__main__":
    main()
