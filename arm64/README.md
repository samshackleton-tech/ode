# A first table of AArch64 instruction forms

A measurement, on the branch `experiment/arm-step1`. It is the first step of answer C of
[`../paper/ARM-PROPOSAL.md`](../paper/ARM-PROPOSAL.md): write a small table of AArch64 instructions in the
way Ode writes its table for x86-64, compare it with processors, and learn what it costs. Nothing here is
relied on by anybody yet, and nothing here names Ode's verifier or its contracts.

## What is here

| File | What it is |
|---|---|
| `arm64.tab` | The table: 25 instruction forms, one row a form. A row says how an assembler writes the form, how the decoded instruction is written, what the instruction does, and how its 32 bits are laid out. The head of the file says how to read it. |
| `word.py` | Writes an instance of a row as its instruction word, and reads four bytes back as an instance. A word is read only if the table writes that very word for the instance, so nothing is read that is not written. |
| `cross.py` | Runs every row on the processor of the machine it is started on, from random states, and compares what the processor leaves with what the row says. |
| `test_arm64.py` | The tests: on any machine, the words; on an AArch64 machine, the processor. |
| `results/` | What `cross.py --out` wrote on each machine. |

The language of a row's effect, and what each of its primitives means on numbers, are those of the table
for x86-64: `../core/table.py` and `../core/conc.py`. Neither file was changed for this table.

## What a row looks like

```
ldr64        | ldr D64, [B64, N]            | .ldr64 .D .B N       | D = mem64(B, N)
             = 11 111 0 01 01 nnnnnnnnnnnn BBBBB DDDDD ; N=n*8
```

The first line is the row: its name; the assembly of an instance, with `D` a register x0 to x30 and `B` a
base register that may also be `sp`; the decoded instruction; and the effect, here "D becomes the eight
bytes of memory at B + N". The second line is the instruction word, the highest bit first. A letter is a
field. `N=n*8` says that the displacement N is the field `n` times eight.

## How to run it

```
python3 word.py                     # the ways, a row at a time
python3 word.py f9400be0            # reads a word: ldr64: .ldr64 .x0 .sp 0x10
python3 cross.py --cases 200        # on an AArch64 machine with clang: every row against the processor
python3 test_arm64.py
```

## What `cross.py` does

For each row it makes random instances: registers, numbers and displacements chosen at random. Each
instance is run twice: once as clang assembles the row's assembly, and once as the word that `word.py`
writes. The two words must be the same. Each run starts from a random state: the registers x0 to x30, the
stack pointer, the four flags, the 128 bits of each of the 32 vector registers, and 1,024 bytes of memory
that base registers and the stack pointer point into. Afterwards every part of the state is compared with
what the row's effect says. A part that the row does not mention must be as it was; that includes the
flags, which no row of this table reads or writes.

One general register a case is left out of the comparison, a different one from case to case: it holds
the address of the case's state while the instruction runs. On macOS `x18` is left out as well, because
the system keeps it for itself. `bl` and `ret` are not run: they leave the code under test.

The tests give `cross.py` thirteen tables with one row changed (an effect, a displacement's unit, a field
of the word). Each must be found out, and is.

## What was measured

See `results/`. Each file is one run of `cross.py --cases 200`: the machine's processor, how many rows and
instances were run, and how many differ.

## What is not here yet

- The flags, and every instruction that reads or writes them (`subs`, `cmp`, `b.ne`, `cset`).
- Loads and stores that move their base register (`ldr w2, [x0], #4`), pairs (`stp`, `ldp`), and
  displacements below zero.
- The meaning of the rows in Lean, and a verifier that steps by this table.
- The proof that a row agrees with Google's `arm64-semantics`.
