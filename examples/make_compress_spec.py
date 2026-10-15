#!/usr/bin/env pypy3
"""Write BLAKE3's compression function as an Ode specification.

    pypy3 examples/make_compress_spec.py > examples/blake3-compress.sexp

The output, not this script, is the specification of record; the tests
check it against the reference implementation (tests/test_blake3.py).
State words are named as C2SP names them: the chaining value cv0..cv7,
the IV words, counter-lo, counter-hi, block-len, flags; m0..m15 is the
block. Each G call gets steps tagged r<round><c|d><index>.
"""
import sys

IV = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A]
PERM = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
COLUMNS = [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15)]
DIAGONALS = [(0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]


def main():
    steps = [(f"iv{i}", str(IV[i])) for i in range(4)]
    state = ([f"cv{i}" for i in range(8)] + [f"iv{i}" for i in range(4)]
             + ["counter-lo", "counter-hi", "block-len", "flags"])
    msg = [f"m{i}" for i in range(16)]

    def g(a, b, c, d, x, y, tag):
        A, B, C, D = (state[i] for i in (a, b, c, d))
        steps.extend([
            (f"{tag}a", f"(add (add {A} {B}) {x})"),
            (f"{tag}d", f"(rotr (xor {D} {tag}a) 16)"),
            (f"{tag}c", f"(add {C} {tag}d)"),
            (f"{tag}b", f"(rotr (xor {B} {tag}c) 12)"),
            (f"{tag}A", f"(add (add {tag}a {tag}b) {y})"),
            (f"{tag}D", f"(rotr (xor {tag}d {tag}A) 8)"),
            (f"{tag}C", f"(add {tag}c {tag}D)"),
            (f"{tag}B", f"(rotr (xor {tag}b {tag}C) 7)")])
        state[a], state[b], state[c], state[d] = (
            f"{tag}A", f"{tag}B", f"{tag}C", f"{tag}D")

    for r in range(7):
        for j, (a, b, c, d) in enumerate(COLUMNS):
            g(a, b, c, d, msg[2 * j], msg[2 * j + 1], f"r{r}c{j}_")
        for j, (a, b, c, d) in enumerate(DIAGONALS):
            g(a, b, c, d, msg[8 + 2 * j], msg[9 + 2 * j], f"r{r}d{j}_")
        msg = [msg[PERM[i]] for i in range(16)]
    for i in range(8):
        steps.append((f"out{i}", f"(xor {state[i]} {state[i + 8]})"))
    for i in range(8):
        steps.append((f"out{8 + i}", f"(xor {state[8 + i]} cv{i})"))

    inputs = ([f"cv{i}" for i in range(8)] + [f"m{i}" for i in range(16)]
              + ["counter-lo", "counter-hi", "block-len", "flags"])
    out = ["; BLAKE3's compression function (C2SP BLAKE3, sections 2.2-2.3):",
           "; 7 rounds over the 16-word state. Written by",
           "; examples/make_compress_spec.py.",
           "(spec", "  (name blake3-compress)",
           f"  (inputs ({' '.join(inputs)}))", "  (steps ("]
    out += [f"    ({name} {e})" for name, e in steps]
    out += ["    ))", f"  (outputs ({' '.join(f'out{i}' for i in range(16))})))"]
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
