# A first table of AArch64 instruction forms

A measurement, on the branch `experiment/arm-step1`. It is the first step of option C of
[`../paper/ARM-PROPOSAL.md`](../paper/ARM-PROPOSAL.md): write a small table of AArch64 instructions in the
way Ode writes its table for x86-64, compare it with processors, and learn what it costs. Nothing here is
relied on by anybody yet, and nothing in this folder names Ode's verifier or its contracts.

## What is here

The table below lists each file in this folder and what it does.

| File | What it does |
|---|---|
| `arm64.tab` | The table: 27 instruction forms, one row per form. A row says how an assembler writes the form, how the decoded instruction is written, what the instruction does, and how its 32 bits are laid out. The top of the file explains the format. |
| `word.py` | Writes an instance of a row as its 32-bit instruction word, and reads four bytes back as an instance. A word is read only if the table writes that exact word for the instance, so nothing is read that is not written. |
| `obj.py` | Reads a function's instructions from an AArch64 ELF object file using the table alone, including `bl` call targets from ELF relocations. Refuses any word that is not an instance of a row. |
| `cross.py` | Runs each runnable row on the processor of the machine it is started on, from random states, and compares what the processor leaves (and whether it faults) with what the row says. |
| `test_arm64.py` | The tests: on any machine, the instruction words and decoding; on an AArch64 machine with clang, comparison against the processor. |
| `results/` | What `cross.py --out` wrote on each processor tested. |

The effect language and its interpreter on numbers are shared with the x86-64 table: `../core/table.py`
and `../core/conc.py`. Three small additions were made to those two files for AArch64:

- `call TARGET link REGISTER` and `return REGISTER`, for calls and returns that keep the return address
  in a register (`x30`) rather than on the stack;
- `on16(sp)`, which returns the stack pointer when it is a multiple of 16 and raises a fault otherwise;
- keeping `.sp` out of the general base-register placeholder `B`, so loads and stores through the stack
  pointer have rows of their own (`ldr64_sp`, `str64_sp`).

## What a row looks like

```
ldr64        | ldr D64, [B64, N]            | .ldr64 .D .B N       | D = mem64(B, N)
             = 11 111 0 01 01 nnnnnnnnnnnn BBBBB DDDDD ; N=n*8
```

The first line is the row: its name; the assembly of an instance, with `D` and `B` general registers `x0`
to `x30`; the decoded instruction; and the effect, here "`D` becomes the eight bytes of memory at `B + N`".
The second line is the 32-bit instruction word, highest bit first. A letter is a bit field. `N=n*8` says
that the displacement `N` is the field `n` times eight.

When the base register is `sp` (register number 31 in the instruction word), AArch64 faults if `sp` is not
a multiple of 16. That form has its own row:

```
ldr64_sp     | ldr D64, [sp, N]             | .ldr64_sp .D N       | D = mem64(on16(sp), N)
             = 11 111 0 01 01 nnnnnnnnnnnn 11111 DDDDD ; N=n*8
```

## How to run it

```
python3 word.py                     # the encoding ways, one row at a time
python3 word.py f9400be0            # reads a word: ldr64_sp: .ldr64_sp .x0 0x10
python3 obj.py OBJECT SYMBOL        # lists a function's decoded instructions from an AArch64 object file
python3 cross.py --cases 200        # on an AArch64 machine with clang: every runnable row against the processor
python3 test_arm64.py
```

## What `cross.py` does

For each runnable row, `cross.py` picks random instances (registers, numbers, and displacements). Each
instance is run twice: once as clang assembles the row's assembly, and once as the 32-bit word that
`word.py` writes. The two words must be identical. Each run starts from a random state: the registers `x0`
to `x30`, the stack pointer, the four flags, the 128 bits of each of the 32 vector registers, and 1,024
bytes of memory that base registers and the stack pointer point into. In one case of four, the stack
pointer is not a multiple of 16.

After the instruction runs, every part of the state is compared with what the row's effect says. Where the
row says the processor faults (`on16(sp)` with a misaligned stack pointer), the processor must raise a
signal, and nowhere else may it. Any part of the state that the row does not mention must be unchanged;
that includes the flags, which no row of this table reads or writes.

One general register per case is left out of the comparison, a different one from case to case: it holds
the address of the case's state while the instruction runs. On macOS, `x18` is left out as well, because
the system reserves it. `bl` and `ret` are not run on the processor: they jump out of the test harness.

The tests give `cross.py` 16 tables with one row changed (a wrong effect, a wrong displacement unit, a
missing or extra alignment fault, or swapped register fields in the instruction word). Each change must be
caught, and is.

## What was measured

See `results/`. Each JSON file records one run of `cross.py --cases 200` on an AArch64 processor: which
processor ran it, how many rows and instances were run, how many instances differed from the processor,
and how many faulted as the rows say.

## What is not here yet

- The flags, and instructions that read or write them (`subs`, `cmp`, `b.ne`, `cset`).
- Loads and stores that update their base register (`ldr w2, [x0], #4`), register pairs (`stp`, `ldp`),
  and negative displacements.
- A Lean proof that rows of this table agree with Google's `arm64-semantics`.
