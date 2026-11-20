# Predicting the 16-way kernel's speed from uops.info: a first test (Nov 20, 2026)

Question: if per-processor performance data stood beside the instruction table, could the coder optimize
from the table and build and measure less often?

Test: the shipped 16-way AVX-512 kernel (`blake3_servil_avx512_p16` of `kcheck/b3hashr.o`, Ode `53d17e3`).
Predict its cycles for one 64-byte block (of sixteen lanes) from uops.info's table (file dated 2026-03-29),
then measure it.

## What was predicted

`extract.py` takes from uops.info, for each instruction form the kernel uses, on each processor family:
micro-ops, the ports they can use, the measured throughput, and the latency. `predict.py` walks the kernel's
path for one block (the instructions as the Ode table decodes them) and computes three lower bounds:
the longest dependency chain a block adds; micro-ops over the rename width; and the vector ports' load.
`sim.py` puts the micro-ops on ports one by one in program order (a crude scheduler).

## Results (cycles for one block; measured under the bench lock, one thread, medians of five)

| processor | measured | simple bound | measured / bound | crude scheduler | measured / scheduler |
|---|---|---|---|---|---|
| Zen 5 (Ryzen 7 9700X) | 390 | 288 | 1.35 | 227 to 286 | 1.36 to 1.72 |
| Zen 5 (EPYC 9255) | 390 | 288 | 1.35 | 227 to 286 | 1.36 to 1.72 |
| Ice Lake (Xeon Gold 6330) | 502 | 430 | 1.17 | 453 | 1.11 |
| Zen 4 (Threadripper PRO 7975WX; NOT under a bench lock) | 537 | 430 | 1.25 | 457 | 1.18 |

Instructions for one block: 985 by the walk of the path; 983.0 measured (plus about 95 for a call).

## What this shows

1. The data is easy to get and to join. Every instruction form of the kernel was found for every family.
   The join took minutes because the Ode table already names each instruction form.
2. The prediction is always too low, and the error differs by processor: the simple bound is low by 17% to
   35% (measured over bound: 1.17 to 1.35), the crude scheduler by 11% to 72%. The bound is a lower bound by
   construction, and the crude scheduler does not model the real one.
3. It ranks the processors correctly (Zen 5 fastest, then Ice Lake, then Zen 4).
4. One trap found: on Zen 4, uops.info lists a 512-bit operation as one micro-op on four ports, but the
   processor executes it in two halves. Counting micro-ops and ports alone predicts 216 cycles for both Zen 4
   and Zen 5. The measured-throughput column corrects this for Zen 4 (430). A table that is used for
   decisions must carry the measured throughput, not only micro-ops and ports.
5. Zen 5 is predicted worst. Something limits it to about 2.2 vector micro-ops a cycle in this kernel that
   the table does not show (the table suggests 2.7 to 4). Not found yet.

## What it does not show

Whether the table ranks two VARIANTS of one kernel correctly on one processor. That is the question that
matters for the coder, and it needs a second variant to test (for example the same kernel with its rounds
unrolled, or with another order of the message words' loads).

## Files, and how to run them

- `extract.py ARCH...` reads uops.info's `instructions.xml` in the working directory and writes `forms.json`
  there. The table is uops.info's and is not in this repository: it is at https://uops.info/xml.html.
  The numbers above are from `extract.py ZEN5 ZEN4 ICL` on the file dated 2026-03-29.
- `predict.py ARCH` (run where `forms.json` is) prints the three bounds and `PREDICTED cycles a block`.
- `sim.py ARCH [CAP]` (the same) is the crude scheduler; `CAP` limits the vector micro-ops started in a cycle
  (the table's "227 to 286" for Zen 5 is without a limit and with a limit of 3).
- `p16-cycles.sh DIR` is the measuring job: `DIR/ode` is a checkout of this repository; it writes
  `DIR/out/identity.txt` and `DIR/out/cycles.txt`. It counts cycles and instructions with the processor's
  counters, on one thread. A number is evidence only where nothing else runs on the machine.
- `results/`: what the job wrote on three machines, each run alone on its machine.
