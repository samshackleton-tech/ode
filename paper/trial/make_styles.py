"""Writes the page of styles from the trial's sources (src/) and results (results/): the same functions in
each notation, with the counts and verdicts read from the files, none typed.

    python3 make_styles.py OUT

The sources are compiled here to count their bytes and to quote what the compiler says of a mistake; the
verdicts are those test_styles.py wrote (`--verify`, `--arm`).
"""
import json, os, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SRC = os.path.join(HERE, "src")
sys.path[:0] = [HERE, os.path.join(ROOT, "lang")]
import ode2
import odec
import test_styles as t


def text(name):
    with open(os.path.join(SRC, name)) as f: return f.read()


def code_lines(source):
    """The lines of a source that hold something other than a comment."""
    return [line for line in source.splitlines() if line.strip() and not line.strip().startswith("//")]


def block(source, kind=""):
    return "```" + kind + "\n" + source.rstrip("\n") + "\n```\n"


def body(source):
    """A source without the comment lines at its top (the page says what they say)."""
    lines = source.splitlines()
    while lines and (lines[0].startswith("//") or not lines[0].strip()): lines.pop(0)
    return "\n".join(lines) + "\n"


def between(source, first, last, nth=1):
    """The lines of a source from the one that holds `first` to the `nth` one after it that is `last`."""
    lines = source.splitlines()
    start = next(i for i, line in enumerate(lines) if first in line)
    ends = [i for i, line in enumerate(lines) if i > start and line == last]
    return "\n".join(lines[start:ends[nth - 1] + 1]) + "\n"


def refuses(name, fn, old, new):
    """What is said of a source with one piece changed, which must be refused: the compiler's words for an
    x86-64 source, the prototype's for the AArch64 one."""
    return t.refusal(name, fn, old, new)[2]


def main(out):
    with open(os.path.join(HERE, "results", "verify.json")) as f: v = json.load(f)
    with open(os.path.join(HERE, "results", "arm.json")) as f: arm = json.load(f)
    with open(t.QUAD_RAW) as f: quad_raw = f.read()
    quad_new = text("quad32.ode")
    with tempfile.TemporaryDirectory(prefix="ode-styles-") as d:
        raw, inline = t.today("mix16_raw.ode", "mix16_3", d), t.today("mix16.ode", "mix16_3", d)
        scan, scan_named = t.today("all_zero.ode", "all_zero_early", d), t.today("all_zero_named.ode", "all_zero_early", d)
        places = t.places_today(text("all_zero.ode"), "all_zero_early", d)
        places_named = t.places_today(text("all_zero_named.ode"), "all_zero_early", d)
        quad, quad_written = t.today("quad32.ode", "quad32", d), t.today_of(quad_raw, "quad32", d)
    assert raw == inline and scan == scan_named and places == places_named and quad == quad_written
    mix, zero, quad_v = v["mix16_3"], v["all_zero"], v["quad32"]
    moved = v["all_zero with an instruction added before the loop, the place the tool finds"]
    stale = v["all_zero with an instruction added before the loop, that proof with the place at the count typed before"]
    slow = v["all_zero with an instruction added before the loop, the prover with the place file typed before"]
    assert mix["verifier"] == zero["verifier"] == quad_v["verifier"] == moved["verifier"] == "shown"
    assert mix["code bytes"] == len(t.code_of(raw)) and zero["code bytes"] == len(t.code_of(scan)) and quad_v["code bytes"] == len(t.code_of(quad))
    assert arm["as written"]["exit"] == 0 and all(c["exit"] != 0 for c in arm["changed"].values())
    rsp = sum(line.count("[rsp + ") for line in code_lines(quad_raw))
    # the stores that fill the table for the first call: those before the first call
    first_call = quad_raw.index("\n  call ")
    table = [int(line.split("[rsp + ")[1].split("]")[0]) for line in quad_raw[:first_call].splitlines() if line.startswith("  mov qword ptr [rsp + ")]
    assert table == list(range(0, 256, 8)), table
    assert slow["prover"].startswith("no answer within ") and slow["prover"].endswith(" seconds"), slow
    seconds = slow["prover"].split()[-2]
    assert sum(line.count("[rsp") for line in code_lines(quad_new)) == 0

    p = []
    say = p.append
    say("# One function, several notations\n")
    say("*This page is made by `paper/trial/make_styles.py` from the files in `paper/trial/src/` and the results in "
        "`paper/trial/results/`. Its counts and verdicts are read from them. Sections 1 to 3 show each function twice in "
        "the notation of the repository's compiler (`lang/odec.py`): with every instruction written out, and with the forms "
        "that the compiler expands. The forms came from the trial's prototype. They are the compiler's now, and what they were "
        "first compared with, a text macro and a file of typed counts of bytes, is gone (commit `082ba81` has this page as it "
        "was at the trial). Section 4 is still made with the prototype, `paper/trial/ode2.py`, a trial's tool: the compiler "
        "has no table of AArch64 instructions yet. The contracts are in today's specification "
        "language, so an output equation is written with `=` where the report proposes `==`.*\n")

    say("## 1. Three mixing steps\n")
    say("The function reads two arrays of sixteen words, `d` and `a`, mixes them three times and writes `d` back. "
        "One step is `(x ^ y) ror 16` in each word: into `d`, then into `a`, then into `d` again. Its contract:\n")
    say(block(body(text("mix16.spec"))))
    say("**Every instruction written out** (`mix16_raw.ode`):\n")
    say(block(body(text("mix16_raw.ode"))))
    say("**With an inline function** (`mix16.ode`). It says which class of register each operand is of, "
        "that the two must differ, and which one it changes:\n")
    say(block(body(text("mix16.ode"))))
    say(f"The two give one object file, byte for byte: {mix['instructions']} instructions, {mix['code bytes']} bytes of code. "
        f"The verifier says `{mix['verifier']}` of it; the proof file is {mix['proof bytes']} bytes and the statement {mix['statement bytes']}.\n")
    say("What the compiler says of four mistakes. Each refusal names the line of the mistake:\n")
    say("| The mistake | What the compiler says |\n|---|---|")
    for what, old, new in (
            ("one register for both operands", "  mix16(zmm1, zmm0)\n", "  mix16(zmm1, zmm1)\n"),
            ("a general register where a vector register belongs", "  mix16(zmm1, zmm0)\n", "  mix16(rax, zmm0)\n"),
            ("the inline function names a register that it was not given", "  vprord d, d, 16\n", "  vprord zmm2, d, 16\n"),
            ("the inline function changes a register that `changes` does not list", "  vprord d, d, 16\n", "  vprord a, d, 16\n")):
        say(f"| {what}: `{new.strip()}` | `` {refuses('mix16.ode', 'mix16_3', old, new)} `` |")
    say("\nWith the text macro that the compiler had before, the second of these was refused by the assembler, which named the "
        "function and not the line. The first and the third were taken, and the function then computed something else.\n")

    say("## 2. A scan with a loop\n")
    say("The function says whether every byte of an array is zero, and leaves at the first byte that is not. Its contract:\n")
    say(block(body(text("all_zero.spec"))))
    say("**Every instruction written out** (`all_zero.ode`). The loop's invariant stands at the loop, as `place { ... }`:\n")
    say(block(body(text("all_zero.ode"))))
    say("The prover needs the invariant with a count of bytes from the function's first byte to that instruction. "
        "The compiler works the count out (`odec.py all_zero.ode all_zero_early --places` prints this):\n")
    say(block(places))
    say("**With names for registers and `:=`** (`all_zero_named.ode`). `reg` gives a register a name for the rest of the "
        "function. `p := xs` is one instruction, `mov rdx, rdi`:\n")
    say(block(body(text("all_zero_named.ode"))))
    say(f"The two give one object file, {zero['instructions']} instructions and {zero['code bytes']} bytes of code, and the same place. "
        f"The verifier says `{zero['verifier']}`; the statement is {zero['statement bytes']} bytes and the proof {zero['proof bytes']}.\n")
    say(f"Then one instruction (`nop`) is added before the loop. The place moves with it, to `{moved['place']}`, and the function is "
        f"`{moved['verifier']}` again. Before, a person typed the count into a second file, and a count that is not moved goes wrong. "
        f"The same proof with the place at the count as it was before (`{stale['place']}`) is `{stale['verifier'].splitlines()[0]}`. "
        f"The prover, given the place at that count, had found no proof and had not stopped after {seconds} seconds: "
        "it does not say that the loop has no place.\n")

    say("## 3. A frame\n")
    say("`quad32` makes the parent of two parents with the 32-way kernel. Its frame holds a table of 32 addresses and two "
        "arrays of 32 results. This is how the table is filled for the first call.\n")
    say(f"**Every instruction written out** (`proof-core/examples/quad/quad32.ode`: {len(quad_raw.splitlines())} lines, {len(code_lines(quad_raw))} of them code). "
        f"Each store names its place in the frame as a number; `[rsp + N]` stands {rsp} times in the code. The first lines:\n")
    say(block(between(quad_raw, 'fn quad32 as "ode_quad32" {', "  mov qword ptr [rsp + 24], rax")))
    say(f"and {len(table) - 4} more pairs like the last, to `[rsp + {table[-1]}]`.\n")
    say(f"**With a frame** (`quad32.ode`: {len(quad_new.splitlines())} lines, {len(code_lines(quad_new))} of them code). The frame is declared once, "
        "and a store names a slot. `for i in 2..32` repeats its lines for each number from 2 to 31, with `$i` replaced by the number:\n")
    say(block(between(quad_new, 'fn quad32 as "ode_quad32" {', "  }", nth=2)))
    say(f"The two give one object file, the kept one, byte for byte ({quad_v['code bytes']} bytes of code). So the kept proofs stand: "
        f"the verifier says `{quad_v['verifier']}` with them, and `ode_quad32`'s own proof is {quad_v['proof bytes of ode_quad32']} bytes.\n")
    say("A store past the table's end would land in the first array of results. Written out, nothing says so. With the frame, the compiler says:\n")
    say(block(refuses("quad32.ode", "quad32", "table[1] := tmp", "table[32] := tmp")))
    say("`:=` moves as many bytes as both of its sides have, and never widens or cuts. A slot of the table has eight bytes and `eax` has four, "
        "so `table[0] := eax` is refused:\n")
    say(block(refuses("quad32.ode", "quad32", "table[0] := tmp", "table[0] := eax")))

    say("## 4. The same step on AArch64\n")
    say("This section is the prototype's. Four words to a register in place of sixteen. A rotation by 16 is one instruction there (`rev32` on halfwords); "
        "a rotation by 12 needs a third register, which the inline function names and requires to differ from the other two:\n")
    say(block(between(text("arm.ode2"), "inline fn mix16(", "}", nth=3)))
    say("A use that gives the scratch register and the destination the same register is refused:\n")
    say(block(refuses("arm.ode2", None, "mix12(v0, v1, v2)", "mix12(v0, v1, v0)")))
    say(f"These were run, not verified: there is no verifier for AArch64 yet. On an Apple M6 ({arm['machine']}) the functions of `arm.ode2` agree with "
        f"C that computes the same (`arm_check.c`), and {len(arm['changed'])} copies with one instruction changed each differ from it.\n")

    say("## What was measured\n")
    say("Each row is one function in one notation: the lines of its source that are code, the bytes of code in its object file, "
        "what the verifier printed, and the bytes of its proof file.\n")
    say("| Function | Notation | Lines of code | Bytes of code | The verifier | Proof bytes |\n|---|---|---|---|---|---|")
    for fn, name, src, r in (("mix16_3", "written out", text("mix16_raw.ode"), mix), ("mix16_3", "with an inline function", text("mix16.ode"), mix),
                             ("all_zero", "written out", text("all_zero.ode"), zero),
                             ("all_zero", "with names and `:=`", text("all_zero_named.ode"), zero)):
        say(f"| `{fn}` | {name} | {len(code_lines(src))} | {r['code bytes']} | {r['verifier']} | {r['proof bytes']} |")
    say(f"| `quad32` | written out | {len(code_lines(quad_raw))} | {quad_v['code bytes']} | {quad_v['verifier']} | {quad_v['proof bytes of ode_quad32']} |")
    say(f"| `quad32` | with a frame | {len(code_lines(quad_new))} | {quad_v['code bytes']} | {quad_v['verifier']} | {quad_v['proof bytes of ode_quad32']} |")
    say("\nWithin a function the notations give the same bytes, so the verdict and the proof are one. "
        "The verdicts are from an x86-64 Linux work machine with the repository's verifier; `paper/trial/test_styles.py` makes them again.\n")

    say("## What is not there yet\n")
    say("- An inline function has no contract yet: the verifier reads the instructions of each use, as if they were written out.\n"
        "- A slot of the frame is counted from the stack pointer as it is once the function has taken the frame's size from it. "
        "The compiler does not follow the stack pointer; the verifier judges the code.\n"
        "- A place names the registers that it speaks of itself (`name i = rcx`). The names that `reg` gives are not carried into it: "
        "a name in a place may also be a parameter of the contract, as `xs` and `n` are in section 2.\n"
        "- The compiler has no table of AArch64 instructions. The prototype, which section 4 is made with, judges `changes` from the "
        "first operand of each instruction as written. It is a trial's tool and is not in the suite.\n")
    with open(out, "w") as f: f.write("\n".join(p))
    print(f"{out}: {sum(len(x.split()) for x in p)} words")


if __name__ == "__main__":
    main(sys.argv[1])
