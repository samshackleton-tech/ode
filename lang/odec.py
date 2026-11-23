#!/usr/bin/env python3
"""odec: Ode source to assembly, and to an object.

    python3 odec.py SOURCE.ode NAME            prints the assembly of the function NAME
    python3 odec.py SOURCE.ode NAME OUT.o      makes the object from the instruction table, without clang
    python3 odec.py SOURCE.ode --all FOLDER    makes FOLDER/NAME.o for every function of the source
    python3 odec.py --from FOLDER NAME OUT.o   makes the object of the function NAME of whichever source in FOLDER has it

Ode has one layer: a function is the instructions its coder chose, one a line, as an assembler takes them
(Intel syntax). Nothing is chosen here: no register, no instruction, no layout. The source:

    target x86_64                       the processor the source is written for; x86_64 where the line is missing
    data NAME = NUMBER, NUMBER, ...     32-bit words of read-only data, on a 64-byte boundary; `#NAME` is its address
    inline fn NAME(P: CLASS, Q: CLASS) distinct(P, Q) changes P {
      LINES                             an inline function: wherever a function says `NAME(r, s)`, LINES stand,
    }                                   with the register r for P and s for Q (more below; its head may go over lines)
    fn NAME as "SYMBOL" {               a function, under the name SYMBOL that a linker sees
      INSTRUCTION                       an instruction (`call SYMBOL` calls a function by its linker name)
      @LABEL:                           a place a jump names: `jmp @LABEL`
      NAME(r, s)                        a use of the inline function NAME: its instructions, here
      for I in 0..8 { LINES }           LINES eight times, with `$I` replaced by 0 to 7
      place B { LINES }                 what holds here after B turns of a loop: the loop's proof is written from it
      entry "SYMBOL"                    the function is entered here too, under that name
      .p2align N                        (first line) the boundary the function starts on; 16 bytes without it
    }
    // a comment

An inline function says, of each register it takes, which class it is of (gpr, gpr32, xmm, zmm). It may say
which of them must differ: `distinct(P, Q, ...)`, as often as needed; no two of those named in one may be
given the same register, or two parts of one register. And it says which it changes: `changes P, ...`;
without that, none. Its lines name a register only by a parameter. These are refused, each at its line: a
use that gives a register of another class; a use that gives one register for two that must differ; a line
of the inline function that names a register outright; and a line that changes a register which `changes`
does not list (what an instruction changes is read from its row of the instruction table; the flags and
bytes of memory are not registers, and `changes` does not speak of them). A use puts the inline function's
instructions there and nothing else: no call, no return, no move. A label in an inline function is each
use's own. An inline function may be used in a `for` and in another inline function; it may hold a `for`
but no `place`, `entry` or `call`.

The forms that expand (a use of an inline function, a `for`) do so in the one way written above. What the
verifier is given is the object's bytes; nothing here is relied on."""
import itertools, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
G64 = "rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15".split()
G32 = "eax ecx edx ebx esp ebp esi edi r8d r9d r10d r11d r12d r13d r14d r15d".split()
G16 = "ax cx dx bx sp bp si di r8w r9w r10w r11w r12w r13w r14w r15w".split()
G8 = "al cl dl bl spl bpl sil dil r8b r9b r10b r11b r12b r13b r14b r15b".split()
REGISTERS = set(G64)
TARGETS = ("x86_64",)
# The classes a parameter of an inline function may be of; and, for every name of a register, the whole
# register it is or is a part of (`eax` and `al` are parts of `rax`; `xmm3` is a part of `zmm3`).
CLASSES = {"gpr": set(G64), "gpr32": set(G32), "xmm": {f"xmm{i}" for i in range(32)}, "zmm": {f"zmm{i}" for i in range(32)}}
WHOLE = {n: G64[i] for names in (G64, G32, G16, G8, ("ah", "ch", "dh", "bh")) for i, n in enumerate(names)}
WHOLE.update({f"{p}mm{i}": f"zmm{i}" for p in "xyz" for i in range(32)})
WHOLE.update({f"k{i}": f"k{i}" for i in range(8)})


def read_source(src):
    with open(src) as f:
        return f.read()


def stop(src, n, msg):
    raise SystemExit(f"{src}: line {n}: {msg}")


class Inline:
    """An inline function: its name, the number of its first line, its parameters [(name, class)], the lists
    of parameters that must differ, the parameters it changes, its lines [(number, text)], its labels."""
    def __init__(self, name, line, params, distinct, changes, body):
        self.name, self.line, self.params, self.distinct, self.changes, self.body = name, line, params, distinct, changes, body
        self.labels = {m.group(1) for _, l in body for m in [re.fullmatch(r"@(\w+):", l.split("//")[0].strip())] if m}


def inline_of(src, n, name, params, clauses, body):
    """The inline function a source's lines say, or a refusal of what in it cannot be read."""
    ps = []
    for p in [p.strip() for p in params.split(",")] if params.strip() else []:
        m = re.fullmatch(r"(\w+)\s*:\s*(\w+)", p)
        if not m: stop(src, n, f"inline fn {name}: a parameter is `NAME: CLASS`, not `{p}`")
        if m.group(2) not in CLASSES: stop(src, n, f"inline fn {name}: `{m.group(2)}` is no class of register ({', '.join(CLASSES)})")
        if m.group(1) in WHOLE: stop(src, n, f"inline fn {name}: a parameter cannot have a register's name, `{m.group(1)}`")
        if m.group(1) in [q for q, _ in ps]: stop(src, n, f"inline fn {name}: two parameters are named `{m.group(1)}`")
        ps.append((m.group(1), m.group(2)))
    names, distinct, changes, rest = [p for p, _ in ps], [], [], clauses.strip()
    def listed(text, what):
        got = [x.strip() for x in text.split(",")]
        for x in got:
            if x not in names: stop(src, n, f"inline fn {name}: `{what}` names `{x}`, which is not a parameter")
            if got.count(x) > 1: stop(src, n, f"inline fn {name}: `{what}` names `{x}` twice")
        return got
    while True:
        m = re.match(r"distinct\(\s*(\w+(?:\s*,\s*\w+)+)\s*\)\s*", rest)
        if not m: break
        distinct.append(listed(m.group(1), "distinct")); rest = rest[m.end():]
    m = re.fullmatch(r"changes\s+(\w+(?:\s*,\s*\w+)*)", rest)
    if m: changes = listed(m.group(1), "changes")
    elif rest: stop(src, n, f"inline fn {name}: after the parameters comes `distinct(P, Q)`, then `changes P, ...`, not `{rest}`")
    for k, line in body:
        s = line.split("//")[0].strip()
        if re.match(r"(place\s+\w+\s*\{|entry\s)", s): stop(src, k, f"inline fn {name}: a place or an entry inside an inline function")
        for word in re.findall(r"(?<![@#$\w])[A-Za-z_]\w*", s):
            if word in WHOLE: stop(src, k, f"inline fn {name}: the line names the register `{word}`; an inline function takes each register it uses as a parameter")
    return Inline(name, n, ps, distinct, changes, body)


def source(text, src="the source"):
    """A source read: (its target, its data, its inline functions, its functions), as
    (name, [(name, [words])], {name: Inline}, [(name, symbol, lines, the number of the first of them)])."""
    target, data, inlines, fns, lines, i = None, [], {}, [], text.split("\n"), 0
    def closing(i):                     # the `}` that stands alone at the start of a line, after line i
        j = i + 1
        while j < len(lines) and lines[j] != "}": j += 1
        if j == len(lines): stop(src, i + 1, "the `}` that ends this, alone at the start of a line, is missing")
        return j
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^target\s+(\w+)\s*$", line.split("//")[0])
        if m:
            if target is not None or inlines or fns: stop(src, i + 1, "`target` stands once, before the functions")
            if m.group(1) not in TARGETS: stop(src, i + 1, f"odec.py makes code for {', '.join(TARGETS)} only, not for {m.group(1)}")
            target = m.group(1); i += 1; continue
        m = re.match(r"^data\s+(\w+)\s*=\s*(.*)$", line)
        if m:
            data.append((m.group(1), [int(w.strip().replace("_", ""), 0) for w in m.group(2).split("//")[0].split(",")])); i += 1; continue
        if re.match(r"^inline\s+fn\b", line):
            head, h = line.split("//")[0].rstrip(), i                # the head may go on over lines, to the one that ends with `{`
            while not head.endswith("{"):
                h += 1
                if h == len(lines) or lines[h] == "}": stop(src, i + 1, "the head of an inline fn ends with `{`")
                head += " " + lines[h].split("//")[0].strip()
            m = re.match(r"^inline\s+fn\s+(\w+)\s*\((.*?)\)(.*)\{$", head)
            if not m: stop(src, i + 1, "the head of an inline fn is `inline fn NAME(P: CLASS, ...) distinct(P, Q) changes P, ... {`")
            j = closing(h)
            if m.group(1) in inlines: stop(src, i + 1, f"a second inline fn {m.group(1)}")
            inlines[m.group(1)] = inline_of(src, i + 1, m.group(1), m.group(2), m.group(3), [(k + 1, lines[k]) for k in range(h + 1, j)])
            i = j + 1; continue
        m = re.match(r'^fn\s+(\w+)\s+as\s+"(\w+)"\s*\{\s*$', line)
        if m:
            j = closing(i)
            fns.append((m.group(1), m.group(2), lines[i + 1:j], i + 2)); i = j + 1; continue
        if line.split("//")[0].strip(): sys.exit(f"{src}: line {i + 1} is neither data, a function nor a comment: {line.strip()}")
        i += 1
    for f in inlines.values():
        for p, _ in f.params:
            if p in inlines: stop(src, f.line, f"inline fn {f.name}: the parameter `{p}` has an inline function's name")
    return target or TARGETS[0], data, inlines, fns


def functions(text, src="the source"):
    """(the data, the functions) of a source: [(name, [words])], [(name, symbol, lines)]."""
    _, data, _, fns = source(text, src)
    return data, [(name, symbol, lines) for name, symbol, lines, _ in fns]


WRITTEN = {}


def written(line):
    """The registers an instruction changes, each by the name of the whole register, as its row of the
    instruction table says. (The flags and bytes of memory are not among them.)"""
    if line not in WRITTEN:
        core = os.path.join(HERE, "..", "core")
        if core not in sys.path: sys.path.insert(0, core)
        import asm, decode, table
        item, regs = asm.instruction(line), set()
        if item[0] != "jump":
            got = decode.decode(item[1], 0, 0, lambda kind, start, end: itertools.repeat("0"))
            if got is None: raise ValueError("the instruction table does not read back the bytes it writes for this")
            row, bind = table.find(decode.HEADS, table.parse_row(got[1]))
            for st in row.effect:
                if st[0] == "call": raise ValueError("a call inside an inline function: not here yet")
                if st[0] != "set" or st[1][0] != "name" or st[1][1] in ("zf", "cf"): continue
                place = st[1][1]
                if place in table.REGISTERS: regs.add(WHOLE[bind[place]])
                elif place in table.VECTORS: regs.add(f"zmm{bind[place]}")
                elif place in table.WIDE: regs.add(f"zmm{bind[table.WIDE[place]]}")
                elif place in table.MASKS: regs.add(f"k{bind[place]}")
                else: regs.add(WHOLE.get(place, place))             # a register the row names outright; or `above128` (vzeroupper)
        WRITTEN[line] = regs
    return WRITTEN[line]


def expand(src, fn, numbered, inlines, notes=None):
    """A function's lines [(number, text)] as instructions: the uses of inline functions and the fors
    expanded, `$x`, `@label` and `#data` replaced. What is no instruction is left out of them and, where
    `notes` is a list, put there with the number of the instruction it stands before:
    ("place", number, the count's name, its lines) for `place b { ... }` (what holds there after b turns of
    the loop: the proof of the loop is written from it); ("entry", number, NAME) for `entry "NAME"` (the
    function is entered there too, under that name)."""
    out, uses = [], [0]

    def block(lines, start):
        depth, j = 1, start
        while depth:
            if j == len(lines): stop(src, lines[start - 1][0], "the `}` that ends this is missing")
            s = lines[j][1].split("//")[0].strip()
            depth += s.endswith("{"); depth -= s == "}"; j += 1
        return lines[start:j - 1], j

    def use(f, args, n, inside):
        if any(f is g for g, _, _ in inside): stop(src, n, f"the inline function {f.name} uses itself")
        if len(args) != len(f.params): stop(src, n, f"{f.name} takes {len(f.params)} registers, not {len(args)}")
        bind = {}
        for (p, cls), a in zip(f.params, args):
            if a not in CLASSES[cls]: stop(src, n, f"{f.name}: `{p}` is a register of the class {cls}, and `{a}` is not one")
            bind[p] = a
        for group in f.distinct:
            for a, b in itertools.combinations(group, 2):
                if WHOLE[bind[a]] == WHOLE[bind[b]]:
                    same = f"both are given {bind[a]}" if bind[a] == bind[b] else f"{bind[a]} and {bind[b]} are parts of one register"
                    stop(src, n, f"{f.name}: `{a}` and `{b}` must differ, and {same}")
        uses[0] += 1
        run(f.body, {}, {l: f".Lode_{fn}_{f.name}{uses[0]}_{l}" for l in f.labels}, inside + [(f, n, bind)])

    def kept(s, n, inside):
        """An instruction of an inline function changes only what `changes` lists: of that function, and of
        every inline function this use of it stands in."""
        if s.endswith(":") or s.startswith("."): return
        try: regs = sorted(written(s))
        except (ValueError, KeyError, IndexError) as e: stop(src, n, f"{inside[-1][0].name}, used at line {inside[-1][1]}: `{s}`: {e}")
        for f, at, bind in reversed(inside):
            for r in regs:
                if r not in {WHOLE[bind[p]] for p in f.changes}:
                    stop(src, n, f"{f.name}, used at line {at}: `{s}` changes {r}, which `changes` of {f.name} does not list")

    def run(lines, env, labels, inside):
        """`env`: what each `$x` of a for stands for. `labels`: the names in the object of the labels that
        are a use's own. `inside`: the uses of inline functions these lines stand in, the outermost first,
        each as (the inline function, the number of the use's line, {parameter: register})."""
        i = 0
        while i < len(lines):
            n, s = lines[i][0], lines[i][1].split("//")[0].strip(); i += 1
            if not s:
                continue
            m = re.fullmatch(r"for\s+(\w+)\s+in\s+(\d+)\.\.(\d+)\s*\{", s)
            if m:
                body, i = block(lines, i)
                for k in range(int(m.group(2)), int(m.group(3))): run(body, {**env, m.group(1): str(k)}, labels, inside)
                continue
            m = re.fullmatch(r"place\s+(\w+)\s*\{", s)
            if m:
                if env or inside: stop(src, n, f"fn {fn}: a place inside a for or an inline function")
                body, i = block(lines, i)
                if notes is not None: notes.append(("place", len(out), m.group(1), [l.split("//")[0].strip() for _, l in body if l.split("//")[0].strip()]))
                continue
            m = re.fullmatch(r'entry\s+"(\w+)"', s)
            if m:
                if env or inside: stop(src, n, f"fn {fn}: an entry inside a for or an inline function")
                if notes is not None: notes.append(("entry", len(out), m.group(1)))
                continue
            if re.fullmatch(r"def\s+\w+\s*\(.*\)\s*\{", s): stop(src, n, "`def` is not a form of Ode any more: write an `inline fn`, outside the function")
            for k, v in env.items():
                s = re.sub(r"\$" + k + r"\b", v, s)
            if inside and inside[-1][2]:
                bind = inside[-1][2]
                s = re.sub(r"(?<![@#$\w])(?:" + "|".join(map(re.escape, bind)) + r")\b", lambda g: bind[g.group(0)], s)
            m = re.fullmatch(r"(\w+)\((.*)\)", s)
            if m and m.group(1) in inlines:
                use(inlines[m.group(1)], [a.strip() for a in m.group(2).split(",")] if m.group(2).strip() else [], n, inside); continue
            if m: stop(src, n, f"`{m.group(1)}` is no inline function of this source")
            m = re.fullmatch(r"call\s+(\w+)", s)
            if m and m.group(1) not in REGISTERS: s = f"call CALL({m.group(1)})"          # a function, by the name a linker knows it by
            s = re.sub(r"@(\w+)", lambda g: labels.get(g.group(1), f".Lode_{fn}_{g.group(1)}"), s)
            s = re.sub(r"#([A-Za-z_]\w*)", lambda g: f".Lode_data_{g.group(1)}", s)     # `#name` is data; `#4` is a number
            s = re.sub(r"\s+", " ", s)
            if inside: kept(s, n, inside)
            out.append(s)

    run(numbered, {}, {}, [])
    return out


def found(src, name):
    """(the data, the symbol, the numbered lines, the source's inline functions) of the function NAME of a source."""
    _, data, inlines, fns = source(read_source(src), src)
    got = [(symbol, [(first + k, line) for k, line in enumerate(lines)]) for n, symbol, lines, first in fns if n == name]
    if len(got) != 1: sys.exit(f"{src}: no `fn {name}`")
    return data, got[0][0], got[0][1], inlines


def instructions(text, name, src="the source", notes=None):
    """The instructions of the function NAME of a source's text, as expand() gives them."""
    _, _, inlines, fns = source(text, src)
    got = [[(first + k, line) for k, line in enumerate(lines)] for n, _, lines, first in fns if n == name]
    if len(got) != 1: sys.exit(f"{src}: no `fn {name}`")
    return expand(src, name, got[0], inlines, notes)


def assembly(src, name, symbol=None):
    """The assembly of a function of the source, with the data it names: its lines, the uses of inline
    functions and the fors expanded, under its symbol (or `symbol`, for a test's copy). No instruction is
    added or changed. Its other entries (`entry "NAME"`) are names of their own; and where the source has a
    `place`, how many bytes into the function it is, as four bytes in a section `.ode.place` that is not
    loaded (the assembler knows the number; place_of() gives the rest of the place's proof)."""
    data, own, lines, inlines = found(src, name)
    symbol = symbol or own
    notes = []
    ins = expand(src, name, lines, inlines, notes)
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
    """Write a function's ELF object using the instruction table."""
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "core"))
    from asm import build_elf
    data, own, lines, inlines = found(src, name)
    notes = []
    expanded = expand(src, name, lines, inlines, notes)
    try:
        blob = build_elf(name, symbol or own, expanded, notes, data)
    except (ValueError, KeyError, IndexError) as e:
        raise SystemExit(f"odec: {src}: fn {name}: {e}") from None
    with open(obj, "wb") as f: f.write(blob)


def source_of(folder, name):
    """The source in `folder` that has `fn NAME`."""
    got = [os.path.join(folder, f) for f in sorted(os.listdir(folder)) if f.endswith(".ode") and re.search(rf"^fn\s+{name}\s+as\s", read_source(os.path.join(folder, f)), re.M)]
    if len(got) != 1: sys.exit(f"{folder}: {len(got)} sources have `fn {name}`")
    return got[0]


def place_of(src, name):
    """What a function's source says holds at its loop's place, as the proof kfn.py's verifier reads (without
    the place's number of bytes into the function, which build() writes in `.ode.place`); None if the source
    has no place. The lines of `place b { ... }`:
        keep rsp, rbp, r12            these registers hold what they held when the code first came back here
        keep zmm9                     a ZMM register, likewise
        keep [rsp + 0x800]            sixty-four bytes of the frame, likewise
        r13 = n - b                   a number that moves with the turns done (b) and a number among the arguments
        zmm0 .. zmm7 = h[b]           the words 0 .. 7 of the sequence's value after b turns, for lanes 0 to 15
        zmm8 .. zmm15 = h[b] lanes 16 the same, for the sixteen lanes from 16"""
    _, _, lines, inlines = found(src, name)
    notes = []
    expand(src, name, lines, inlines, notes)
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
        print(f"{len(names)} functions of {os.path.basename(a[0])}: objects in {a[2]}"); return
    if len(a) == 4 and a[0] == "--from": build(source_of(a[1], a[2]), a[2], a[3]); return
    if len(a) == 2: sys.stdout.write(assembly(a[0], a[1])); return
    if len(a) == 3: build(a[0], a[1], a[2]); return
    sys.exit(__doc__)


if __name__ == "__main__":
    main()
