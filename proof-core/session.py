"""The prover's talk with `odeprove` (ProveMain.lean): what the verifier says of a proof that grows and shrinks.

    s = Session(statement_path, head_lines, name)
    s.ask(lines)        what `odeverify` would say of head_lines + lines; lines are those of NAME's part
    s.close()

`odeprove` keeps a process waiting at the end of every batch of lines it was given, so asking about a
proof that begins as the last one did costs only the lines that are new. The session keeps the batches
given; for a new question it goes back to the last batch the new lines still begin with and sends the rest.
A machine allows only so many processes: after DEPTH batches the session begins again, from the lines so far.
Nobody relies on this: the finished proof is given to `odeverify`."""
import os, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
EXE = os.path.join(HERE, ".lake", "build", "bin", "odeprove")
import statement
TABLE = statement.TABLES["x86-64"]         # (a statement of functions for AArch64 is given AArch64's table: statement.table_for)
DEPTH = 100000


def whole(lines):
    """Do these lines end where a line of the proof ends? (An arithmetic proof is `p`, its `s` lines, then `q`.)"""
    return not lines or lines[-1].split()[:1] not in (["p"], ["s"])


class Session:
    def __init__(self, statement_path, head, name, only=False, with_pc=False):
        self.statement, self.head, self.name, self.only, self.with_pc, self.sent, self.begun, self.p, self.file = statement_path, list(head), name, only, with_pc, 0, 0, None, None
        self.begin([])

    def begin(self, base):
        """A new `odeprove`, the lines `base` of NAME's part being in what it starts from."""
        self.close()
        f = tempfile.NamedTemporaryFile("w", suffix=".head", delete=False)
        with f: f.write("".join(l + "\n" for l in self.head + base))
        self.file, self.base, self.batches, self.said = f.name, list(base), [], []      # said[k]: what was said after batch k
        self.begun += 1
        cmd = [EXE] + (["--only"] if self.only else []) + (["--with-pc"] if self.with_pc else []) + [statement.table_for(self.statement), self.statement, self.file, self.name]
        self.p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        self.first, more = self.read()
        if not more: self.end()                      # nothing waits: what it starts from is refused, or shows everything

    def read(self):
        """What was said, and whether a process now waits at the end of the lines given."""
        said = []
        while True:
            l = self.p.stdout.readline()
            if l == "": raise RuntimeError("odeprove ended: " + "".join(said)[-300:])
            if l in (".more\n", ".end\n"): return "".join(said), l == ".more\n"
            said.append(l)

    def ask(self, lines):
        if not whole(lines): raise ValueError("the lines end inside an arithmetic proof")
        if lines[:len(self.base)] != self.base: self.begin([])
        if self.p is None:
            if lines == self.base: return self.first
            self.begin([])                           # (what it started from ended the talk: from the head again)
            if self.p is None: return self.first
        keep, at = 0, len(self.base)                 # the batches the new lines begin with
        for b in self.batches:
            if lines[at:at + len(b)] != b: break
            keep, at = keep + 1, at + len(b)
        for _ in self.batches[keep:]:
            self.p.stdin.write("back\n"); self.p.stdin.flush()
            if self.p.stdout.readline() != ".back\n": raise RuntimeError("odeprove did not go back")
        del self.batches[keep:], self.said[keep:]
        new = lines[at:]
        if not new: return self.said[-1] if self.said else self.first
        self.p.stdin.write(f"lines {len(new)}\n" + "".join(l + "\n" for l in new)); self.p.stdin.flush()
        self.sent += len(new)
        said, more = self.read()
        if more:
            self.batches.append(new); self.said.append(said)
            if len(self.batches) > DEPTH: self.begin(lines)
        return said

    def end(self):
        if self.p is not None:
            self.p.stdin.close(); self.p.stdout.close(); self.p.wait(); self.p = None

    def close(self):
        self.end()
        if self.file and os.path.exists(self.file): os.remove(self.file)
        self.file = None
