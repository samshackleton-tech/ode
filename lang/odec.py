#!/usr/bin/env python3
"""odec: Ode source to assembly, and to an object.

    python3 odec.py SOURCE.ode NAME            prints the assembly of the function NAME
    python3 odec.py SOURCE.ode NAME OUT.o      makes the object (an assembler, clang, takes the assembly)
    python3 odec.py SOURCE.ode --all FOLDER    makes FOLDER/NAME.o for every function of the source
    python3 odec.py --from FOLDER NAME OUT.o   makes the object of the function NAME of whichever source in FOLDER has it

Ode has one layer: a function is the instructions its coder chose, one a line, as an assembler takes them
(Intel syntax). Nothing is chosen here: no register, no instruction, no layout. The source:

    data NAME = NUMBER, NUMBER, ...     32-bit words of read-only data, on a 64-byte boundary; `#NAME` is its address
    fn NAME as "SYMBOL" {               a function, under the name SYMBOL that a linker sees
      INSTRUCTION                       an instruction (`call SYMBOL` calls a function by its linker name)
      @LABEL:                           a place a jump names: `jmp @LABEL`
      def NAME(A, B) { LINES }          LINES, wherever `NAME(x, y)` is then written, with `$A` and `$B` replaced
      for I in 0..8 { LINES }           LINES eight times, with `$I` replaced by 0 to 7
      place B { LINES }                 what holds here after B turns of a loop: the loop's proof is written from it
      entry "SYMBOL"                    the function is entered here too, under that name
      .p2align N                        (first line) the boundary the function starts on; 16 bytes without it
    }
    // a comment

The forms that expand (def, for) do so in the one way written above. What the verifier is given is the
object's bytes; nothing here is relied on."""
import os, re, shutil, subprocess, sys

REGISTERS = set("rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split())


def read_source(src):
    with open(src) as f:
        return f.read()


def functions(text, src="the source"):
    """(the data, the functions) of a source: [(name, [words])], [(name, symbol, lines)]."""
    data, fns, lines, i = [], [], text.split("\n"), 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^data\s+(\w+)\s*=\s*(.*)$", line)
        if m:
            data.append((m.group(1), [int(w.strip().replace("_", ""), 0) for w in m.group(2).split("//")[0].split(",")])); i += 1; continue
        m = re.match(r'^fn\s+(\w+)\s+as\s+"(\w+)"\s*\{\s*$', line)
        if m:
            j = i + 1
            while lines[j] != "}":
                j += 1
            fns.append((m.group(1), m.group(2), lines[i + 1:j])); i = j + 1; continue
        if line.split("//")[0].strip(): sys.exit(f"{src}: line {i + 1} is neither data, a function nor a comment: {line.strip()}")
        i += 1
    return data, fns


def expand(name, lines, defs, env, notes=None):
    """A function's lines as instructions: defs and fors expanded, `$x`, `@label` and `#data` replaced.
    What is no instruction is left out of them and, where `notes` is a list, put there with the number of
    the instruction it stands before: ("place", number, the count's name, its lines) for
    `place b { ... }` (what holds there after b turns of the loop: the proof of the loop is written from it);
    ("entry", number, NAME) for `entry "NAME"` (the function is entered there too, under that name)."""
    out, i = [], 0
    def block(start):
        depth, j = 1, start
        while depth:
            s = lines[j].split("//")[0].strip()
            depth += s.endswith("{"); depth -= s == "}"; j += 1
        return lines[start:j - 1], j
    while i < len(lines):
        s = lines[i].split("//")[0].strip(); i += 1
        if not s:
            continue
        m = re.fullmatch(r"def\s+(\w+)\(([^)]*)\)\s*\{", s)
        if m:
            body, i = block(i); defs[m.group(1)] = ([a.strip() for a in m.group(2).split(",") if a.strip()], body); continue
        m = re.fullmatch(r"for\s+(\w+)\s+in\s+(\d+)\.\.(\d+)\s*\{", s)
        if m:
            body, i = block(i)
            for k in range(int(m.group(2)), int(m.group(3))):
                out += expand(name, body, defs, {**env, m.group(1): str(k)})
            continue
        m = re.fullmatch(r"place\s+(\w+)\s*\{", s)
        if m:
            assert not env, f"fn {name}: a place inside a def or a for"
            body, i = block(i)
            if notes is not None: notes.append(("place", len(out), m.group(1), [l.split("//")[0].strip() for l in body if l.split("//")[0].strip()]))
            continue
        m = re.fullmatch(r'entry\s+"(\w+)"', s)
        if m:
            assert not env, f"fn {name}: an entry inside a def or a for"
            if notes is not None: notes.append(("entry", len(out), m.group(1)))
            continue
        for k, v in env.items():
            s = re.sub(r"\$" + k + r"\b", v, s)
        m = re.fullmatch(r"(\w+)\((.*)\)", s)
        if m and m.group(1) in defs:
            params, body = defs[m.group(1)]
            args = [a.strip() for a in m.group(2).split(",")] if m.group(2).strip() else []
            assert len(args) == len(params), f"{m.group(1)}: {len(params)} arguments"
            out += expand(name, body, defs, dict(zip(params, args))); continue
        m = re.fullmatch(r"call\s+(\w+)", s)
        if m and m.group(1) not in REGISTERS: s = f"call CALL({m.group(1)})"          # a function, by the name a linker knows it by
        s = re.sub(r"@(\w+)", lambda g: f".Lode_{name}_{g.group(1)}", s)
        s = re.sub(r"#([A-Za-z_]\w*)", lambda g: f".Lode_data_{g.group(1)}", s)     # `#name` is data; `#4` is a number
        out.append(re.sub(r"\s+", " ", s))
    return out


def found(src, name):
    data, fns = functions(read_source(src), src)
    got = [(symbol, lines) for n, symbol, lines in fns if n == name]
    if len(got) != 1: sys.exit(f"{src}: no `fn {name}`")
    return data, got[0][0], got[0][1]


def assembly(src, name, symbol=None):
    """The assembly of a function of the source, with the data it names: its lines, defs and fors expanded,
    under its symbol (or `symbol`, for a test's copy). No instruction is added or changed. Its other
    entries (`entry "NAME"`) are names of their own; and where the source has a `place`, how many bytes into
    the function it is, as four bytes in a section `.ode.place` that is not loaded (the assembler knows the
    number; place_of() gives the rest of the place's proof)."""
    data, own, lines = found(src, name)
    symbol = symbol or own
    notes = []
    ins = expand(name, lines, {}, {}, notes)
    for note in sorted(notes, key=lambda n: -n[1]):             # from the last, so the numbers before it stay
        ins[note[1]:note[1]] = [f".Lode_place_{name}:"] if note[0] == "place" else [f".global {note[2]}", f"{note[2]}:"]
    # A leading alignment directive belongs before the entry symbols, not
    # after them: padding inside a labelled entry changes the called code.
    alignment = ins.pop(0) if ins and ins[0].startswith(".p2align ") else ".p2align 4"
    used = [(n, ws) for n, ws in data if any(f".Lode_data_{n}]" in x or f".Lode_data_{n} " in x for x in ins)]
    text = ("// Printed by odec.py from " + src.split("/")[-1] + ". Not written or edited by hand.\n"
            "#if defined(__ELF__) && defined(__linux__)\n.section .note.GNU-stack,\"\",%progbits\n#endif\n"
            "#ifdef __APPLE__\n#define CALL(f) _##f\n#else\n#define CALL(f) f@PLT\n#endif\n"
            ".intel_syntax noprefix\n" + ("#ifdef __APPLE__\n.static_data\n#else\n.section .rodata\n#endif\n" if used else ""))
    for n, ws in used:
        text += f".p2align 6\n.Lode_data_{n}:\n" + "".join(f"    .long {w}\n" for w in ws)
    text += f".text\n.text\n.global {symbol}\n.global _{symbol}\n{alignment}\n{symbol}:\n_{symbol}:\n"
    text += "".join((x + "\n") if x.endswith(":") else ("    " + x + "\n") for x in ins)
    if any(note[0] == "place" for note in notes):
        text += f"#if defined(__ELF__)\n.section .ode.place,\"\",@progbits\n    .long .Lode_place_{name} - {symbol}\n#endif\n"
    return text


def assemble(s_path, o_path):
    for cc in (["clang", "--target=x86_64-unknown-linux-gnu"], ["cc"]):
        if shutil.which(cc[0]) and subprocess.run(cc + ["-c", "-o", o_path, s_path], capture_output=True).returncode == 0: return
    raise SystemExit(f"odec: no assembler here makes an x86-64 ELF object of {s_path}")


def build(src, name, obj, symbol=None):
    """The object of a function of the source: its assembly beside it (OBJ's name with .S), assembled."""
    s_path = obj[:-2] + ".S" if obj.endswith(".o") else obj + ".S"
    with open(s_path, "w") as f: f.write(assembly(src, name, symbol))
    assemble(s_path, obj)


def source_of(folder, name):
    """The source in `folder` that has `fn NAME`."""
    got = [os.path.join(folder, f) for f in sorted(os.listdir(folder)) if f.endswith(".ode") and re.search(rf"^fn\s+{name}\s+as\s", read_source(os.path.join(folder, f)), re.M)]
    if len(got) != 1: sys.exit(f"{folder}: {len(got)} sources have `fn {name}`")
    return got[0]


def place_of(src, name):
    """What a function's source says holds at its loop's place, as the proof kfn.py's verifier reads (without
    the place's number of bytes into the function, which the assembler knows: assembly()); None if the source
    has no place. The lines of `place b { ... }`:
        keep rsp, rbp, r12            these registers hold what they held when the code first came back here
        keep zmm9                     a ZMM register, likewise
        keep [rsp + 0x800]            sixty-four bytes of the frame, likewise
        r13 = n - b                   a number that moves with the turns done (b) and a number among the arguments
        zmm0 .. zmm7 = h[b]           the words 0 .. 7 of the sequence's value after b turns, for lanes 0 to 15
        zmm8 .. zmm15 = h[b] lanes 16 the same, for the sixteen lanes from 16"""
    _, _, lines = found(src, name)
    notes = []
    expand(name, lines, {}, {}, notes)
    places = [note for note in notes if note[0] == "place"]
    if not places: return None
    if len(places) != 1: sys.exit(f"{src}: fn {name} has more than one place")
    _, _, b, lines = places[0]
    proof = dict(registers={}, vectors={}, frame={})
    for line in lines:
        m = re.fullmatch(r"keep\s+(.*)", line)
        if m:
            for x in [x.strip() for x in m.group(1).split(",")]:
                f = re.fullmatch(r"\[rsp(?:\s*\+\s*(\w+))?\]", x)
                if f: proof["frame"][str(int(f.group(1) or "0", 0))] = "keep"
                elif re.fullmatch(r"zmm\d+", x): proof["vectors"][x[3:]] = "keep"
                else: proof["registers"][x] = "keep"
            continue
        m = re.fullmatch(r"zmm(\d+)\s*\.\.\s*zmm(\d+)\s*=\s*h\[" + b + r"\](?:\s+lanes\s+(\d+))?", line)
        if m:
            first, last, lane = int(m.group(1)), int(m.group(2)), int(m.group(3) or "0")
            if last - first != 7: sys.exit(f"{src}: fn {name}: `{line}`: the value has eight words")
            for w in range(8): proof["vectors"][str(first + w)] = {"cv": [lane, w]}
            continue
        m = re.fullmatch(r"(\w+)\s*=\s*(.*)", line)
        if m:
            # a sum of terms: NUMBER, NAME, NUMBER * NAME, each with its sign
            lin = {"1": 0}
            for sign, term in re.findall(r"([+-]?)\s*([^+-]+)", m.group(2)):
                parts = [p.strip() for p in term.split("*")]
                k = -1 if sign == "-" else 1
                names = [p for p in parts if not re.fullmatch(r"\d+|0x[0-9a-fA-F]+", p)]
                for p in parts:
                    if p not in names: k *= int(p, 0)
                if len(names) > 1 or (names and not re.fullmatch(r"\w+", names[0])): sys.exit(f"{src}: fn {name}: `{line}`: not a sum of numbers and of names times numbers")
                key = "1" if not names else "b" if names[0] == b else names[0]
                lin[key] = lin.get(key, 0) + k
            proof["registers"][m.group(1)] = {"lin": {k: v for k, v in lin.items() if v or k == "1"}}
            continue
        sys.exit(f"{src}: fn {name}: a line of its place that is not understood: `{line}`")
    return proof


def main():
    a = sys.argv[1:]
    if len(a) == 3 and a[1] == "--all":
        os.makedirs(a[2], exist_ok=True)
        names = [n for n, _, _ in functions(read_source(a[0]), a[0])[1]]
        for n in names: build(a[0], n, os.path.join(a[2], n + ".o"))
        print(f"{len(names)} functions of {os.path.basename(a[0])}: assembly and objects in {a[2]}"); return
    if len(a) == 4 and a[0] == "--from": build(source_of(a[1], a[2]), a[2], a[3]); return
    if len(a) == 2: sys.stdout.write(assembly(a[0], a[1])); return
    if len(a) == 3: build(a[0], a[1], a[2]); return
    sys.exit(__doc__)


if __name__ == "__main__":
    main()
