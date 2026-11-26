# Performance and Memory Advice (`advice/`)

This folder holds Ode's advisory performance and memory-access estimator. It helps a coder compare instruction schedules, register layouts, loop alignment, and stack or buffer layouts before benchmarking on hardware.

Nothing in this folder is part of Bob's reliance set. The verifier (`proof-core/odeverify`) never imports or reads anything here, and the compiler (`lang/odec.py`) never changes the machine code based on these numbers. Every number printed here is advice for the coder, not a guarantee of hardware timing.

## Example

Run `lang/ode_tool.py advise` or `check --trace` on any x86-64 or AArch64 Ode file:

```sh
python3 lang/ode_tool.py check proof-core/examples/arm64/mix.ode proof-core/examples/arm64/mix.spec --trace --arch ampere1
python3 lang/ode_tool.py check proof-core/examples/arm64/mix.ode proof-core/examples/arm64/mix.spec --trace --arch ampere1 --align 7
```

With 64-byte-aligned buffers on AmpereOne, `arm_mix16_6` touches 5 cache lines with 0 cache-line splits. Shifting the buffers by 7 bytes (`--align 7`) shows 8 cache lines touched and 4 cache-line splits, naming the exact source lines (`mix.ode` lines 13, 14, and 18) where the vector loads and stores cross a 64-byte boundary.

## Two layers of output

Every report splits what is exact about the bytes and addresses from what is a rough cycle estimate.

### Layer 1: exact facts about code and memory addresses

1. **Code layout and loop alignment.** Decodes the object file through the same table (`core/x86.tab` or `arm64/arm64.tab`) that the verifier reads. Reports instruction count, byte length, instruction-cache lines touched, and each backward-edge loop's footprint. If aligning a loop top would save an instruction-cache line, it says so.
2. **Concrete memory-access trace.** Runs the compiled object file through the concrete machine interpreter (`core/conc.py`), following calls across functions, and records every byte read or written with its exact address, width, and Ode source line.
3. **Five exact memory hazards**, each pinned to the source line and frame field:
   - **Cache-line splits:** a load or store whose bytes cross a cache-line boundary (64 bytes on x86-64 and AmpereOne; 128 bytes on Apple M-series).
   - **Page crossings:** a load or store whose bytes cross a virtual memory page boundary (4 KiB on x86-64 and AmpereOne; 16 KiB on Apple M-series).
   - **Store-to-load forwarding (STLF) stalls:** a load that overlaps a recent store without matching its start and staying within its width (for example, two 8-byte stores followed by a 16-byte vector load). Clean exact-match forwards are counted separately.
   - **4K aliasing:** a load whose low 12 address bits overlap a recent store to a different 4 KiB page.
   - **L1D set-associativity conflicts:** counts how many distinct cache lines map to the same L1 data-cache set and flags when the depth exceeds the cache's way count.

### Layer 2: uiCA-style pipeline simulation, rough cycle bounds, and cache simulation

- **uiCA-style cycle-accurate loop simulator (`uica_sim.py`, `uops_ports.json`):** models front-end dispatch width, macro-op fusion (`cmp`/`test`/`add`/`sub`/`dec` + conditional branch), micro-fusion in the fused domain, rename-stage move and zero-idiom elimination, finite ROB and split vs. unified scheduler queues, and true out-of-order per-port reservation stations driven by `uops.info` port bitmasks (`ZEN5`, `ZEN4`, `ZEN3`, `ICL`, `EMR`, `ADL-P`).
- **Compute lower bound:** builds the register and static frame-slot dependency graph from each table row's reads and writes and takes the largest of critical-path latency, front-end issue width, and execution-unit throughput.
- **L1D cache simulation:** runs an exact LRU set-associative model over the concrete access trace under both warm-start (working set resident up to cache associativity) and cold-start assumptions.
- **Warm and cold totals:** adds dynamic compute lower bound, hazard penalties, and simulated L1 miss penalties. These totals are intended for comparing two variants of the same function (`ode_tool.py compare`), not for predicting exact wall-clock cycles.

## Target profiles in `arch.json`

The table below lists the five processor profiles in `advice/arch.json`. Each row gives the profile name, target architecture, cache-line size, page size, L1 data-cache geometry, and source of the instruction timings.

| Profile | Target | Cache line | Page | L1D cache | Instruction timings |
| --- | --- | --- | --- | --- | --- |
| `zen5` | `x86_64` | 64 B | 4 KiB | 48 KiB, 12-way | `uops.info` + hardware calibration |
| `zen4` | `x86_64` | 64 B | 4 KiB | 32 KiB, 8-way | `uops.info` (double-pumped 512-bit) |
| `icelake` | `x86_64` | 64 B | 4 KiB | 48 KiB, 12-way | `uops.info` + hardware calibration |
| `apple_m` | `arm64` | 128 B | 16 KiB | 128 KiB, 8-way | Architecture docs (calibration pending) |
| `ampere1` | `arm64` | 64 B | 4 KiB | 64 KiB, 4-way | Architecture docs + hardware calibration |

## Hardware calibration (`calibrate.py`, `results/`)

On 23 November 2026 we ran `advice/calibrate.py --run --rounds 11` (interleaved A/B rounds using Linux `perf_event_open` hardware CPU cycle counters on pinned cores) across four processors: an AMD Ryzen 7 9700X (Zen 5), an AMD Zen 5 24-core server processor, an Intel Xeon Gold 6330 (Ice Lake), and an Ampere-1a (AArch64). Full JSON logs live in `advice/results/`.

The table below compares each variant pair's measured slowdown (`B / A` in hardware CPU cycles per call) against the estimator's ranking. Each cell shows the measured median cycles for Variant A and Variant B, their ratio, and whether the estimator predicted the same ordering.

| Processor | Pair (A vs B) | Measured A (cyc) | Measured B (cyc) | Ratio B/A | Estimator rank |
| --- | --- | ---: | ---: | ---: | --- |
| Zen 5 desktop | `p16_align`: aligned vs +7 B (`wide/p16.ode`) | 1605.5 | 1666.7 | 1.04x | agreed |
| Zen 5 desktop | `alias_4k`: +0x10400 vs +0x10000 (64x) | 83.2 | 89.7 | 1.08x | agreed |
| Zen 5 desktop | `stlf_width`: 16 B vs 2x8 B->16 B (64x) | 779.2 | 990.3 | 1.27x | agreed |
| Zen 5 desktop | `l1d_set_conflict`: 8 vs 16 lines in set 0 | 115.9 | 186.9 | 1.61x | agreed |
| Zen 5 desktop | `adler_loop_align`: 2-line aligned vs 3-line | 877.4 | 1059.6 | 1.21x | loop hint (+20.8%) |
| Zen 5 server | `p16_align`: aligned vs +7 B (`wide/p16.ode`) | 1607.6 | 1680.2 | 1.05x | agreed |
| Zen 5 server | `alias_4k`: +0x10400 vs +0x10000 (64x) | 83.1 | 89.7 | 1.08x | agreed |
| Zen 5 server | `stlf_width`: 16 B vs 2x8 B->16 B (64x) | 713.1 | 905.1 | 1.27x | agreed |
| Zen 5 server | `l1d_set_conflict`: 8 vs 16 lines in set 0 | 115.9 | 186.8 | 1.61x | agreed |
| Zen 5 server | `adler_loop_align`: 2-line aligned vs 3-line | 838.5 | 1031.2 | 1.23x | loop hint (+23.0%) |
| Ice Lake | `p16_align`: aligned vs +7 B (`wide/p16.ode`) | 2042.8 | 2122.0 | 1.04x | agreed |
| Ice Lake | `alias_4k`: +0x10400 vs +0x10000 (64x) | 124.7 | 129.6 | 1.04x | agreed |
| Ice Lake | `stlf_width`: 16 B vs 2x8 B->16 B (64x) | 471.3 | 1158.4 | 2.46x | agreed |
| Ice Lake | `l1d_set_conflict`: 8 vs 16 lines in set 0 | 146.0 | 153.9 | 1.05x | agreed |
| Ice Lake | `adler_loop_align`: 2-line aligned vs 3-line | 1352.6 | 1494.4 | 1.10x | loop hint (+10.5%) |
| Ampere-1a | `arm_mix_align`: aligned vs +7 B (`mix.ode`) | 40.5 | 42.0 | 1.04x | agreed |
| Ampere-1a | `arm_stlf_width`: 16 B vs 2x8 B->16 B (16x) | 251.1 | 362.7 | 1.44x | agreed |
| Ampere-1a | `arm_l1d_conflict`: 4 vs 8 lines in set 0 | 33.8 | 41.0 | 1.21x | agreed |

Summary of what calibration showed:

- **Ranking:** all 15 hazard variant pairs agreed with hardware across all four processors. In addition, the static loop-alignment hint that `estimate.py` automatically reported on existing `kcheck/programs/adler32/adler32.ode` produced a real 20.8%–23.0% speedup on Zen 5 and 10.5% on Ice Lake when tested.
- **Two corrections made from the data:**
  1. The first version of `estimate.py` only tracked register dependencies and static `[sp + offset]` frame slots in its critical path, missing store-to-load chains through non-`sp` pointers (such as `add x2, sp, 0; st1 [x2]; ld1 [x2]` in `arm_stlf_width`). `analyze_memory` now tracks store-to-load dependency edges on exact concrete byte addresses from the trace.
  2. Summing raw L2 miss latency (10 cycles) or raw 4K-alias replay latency (10–12 cycles) per event overstated slowdowns because out-of-order memory-level parallelism and disambiguation predictors hide most of that latency. `arch.json` now uses amortized effective hazard penalties while Layer-1 hazard counts remain exact.

## Bare-metal PMU pipeline validation (`pmu_validate.py`, `uica_sim.py`)

On 26 November 2026 we ran `advice/pmu_validate.py --run` (25 loop kernels: 4 real Ode kernels, 9 targeted pipeline probes, and 12 reproducible randomized instruction mixes) under Linux `perf_event_open` hardware cycle counters on three bare-metal processors, comparing the older static lower bound, `llvm-mca`, and `uica_sim.py`. Full JSON data lives in `advice/results/pmu-*.json`.

The table below shows how many of the 25 kernels each estimator predicted within 10% and 15% of bare-metal measured cycles, along with median and mean absolute percentage error.

| Processor | Model | Within 10% | Within 15% | Median abs error | Mean abs error |
| --- | --- | ---: | ---: | ---: | ---: |
| AMD EPYC 9255 (Zen 5 server) | old `estimate.py` | 9/25 (36%) | 9/25 | 47.7% | 80.1% |
| AMD EPYC 9255 (Zen 5 server) | `llvm-mca -mcpu=znver5` | 8/25 (32%) | 13/25 | 14.5% | 28.8% |
| AMD EPYC 9255 (Zen 5 server) | **`uica_sim.py`** | **19/25 (76%)** | **22/25 (88%)** | **1.1%** | **6.3%** |
| AMD Ryzen 7 9700X (Zen 5 desktop) | old `estimate.py` | 9/25 (36%) | 9/25 | 47.7% | 80.1% |
| AMD Ryzen 7 9700X (Zen 5 desktop) | `llvm-mca -mcpu=znver5` | 8/25 (32%) | 13/25 | 14.5% | 28.8% |
| AMD Ryzen 7 9700X (Zen 5 desktop) | **`uica_sim.py`** | **19/25 (76%)** | **21/25 (84%)** | **5.3%** | **7.9%** |
| Intel Xeon Gold 6330 (Ice Lake) | old `estimate.py` | 7/25 (28%) | 8/25 | 31.1% | 61.7% |
| Intel Xeon Gold 6330 (Ice Lake) | `llvm-mca -mcpu=icelake-server` | 15/25 (60%) | 15/25 | 7.2% | 15.3% |
| Intel Xeon Gold 6330 (Ice Lake) | **`uica_sim.py`** | **19/25 (76%)** | **22/25 (88%)** | **8.1%** | **8.2%** |

Four concrete hardware findings from this PMU run directly improved `uica_sim.py`:

1. **Zen 5 512-bit latency bug in `uops.info` (solved the `p16` 390-cycle mystery):** `uops.info` listed 1-cycle latency for `VPXORD (ZMM)` and `VPRORD (ZMM)` on Zen 5, whereas bare-metal EPYC 9255 latency probes measured **2.000 cycles** for all three of `VPADDD`, `VPXORD`, and `VPRORD` on 512-bit ZMM registers (a single 14-instruction BLAKE3 G column measured `28.002` cycles, and 4 parallel columns `30.099` cycles). With this correction, `uica_sim.py` predicts the 985-instruction `p16` BLAKE3 kernel at **356 cyc vs. 390 measured (-8.7%)** on Zen 5 (down from -26.2%) and **461 cyc vs. 502 measured (-8.2%)** on Ice Lake (down from -14.3%).
2. **Zen 5 native 512-bit throughput and 4 load AGUs:** Bare-metal EPYC 9255 measured `4.01` cycles for 16 independent `VPADDD`/`VPXORD (ZMM)` (true 4.0/cycle across `FP0..3`, rather than `uops.info`'s `TP=0.37`) and `2.20` cycles for 8 independent loads (4 load AGUs, not 3).
3. **True out-of-order per-port cycle sets:** Tracking only a scalar next-free time per port prevented ready younger operations from filling earlier free cycles; switching to per-port occupied cycle sets jumped Ice Lake accuracy from 56% to 76% within 10%.
4. **Intel vs. AMD self-move elimination:** Hardware confirmed `mov rdx, rdx` is rename-eliminated on Zen 5 (`rand_00_scalar`: 3.02 cyc) but takes 1 ALU cycle on Ice Lake (`4.35` cyc).

## Explicit budgets

The coder can pass explicit upper bounds to `lang/ode_tool.py check` or `advise`: `--max-bytes`, `--max-icache-lines`, `--max-frame-bytes`, `--max-line-splits`, `--max-page-crossings`, `--max-stlf-partial`, and `--max-alias-4k`. Any exceeded budget causes exit code 2 after printing the full report.

## Tests

```sh
python3 advice/test_estimate.py
pypy3 advice/test_estimate.py
```

## Earlier study

- `uops-test/` (November 20, 2026): a first test of whether `uops.info`'s per-processor table predicts the cycles the 16-way BLAKE3 kernel takes per block. It ranks three processors correctly and is low by 17% to 35%. See also `DESIGN.md`, section 5.

*Ode stands for Ordered Data & Execution.*
