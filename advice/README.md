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

## Bare-metal PMU pipeline validation (`pmu_validate.py`, `pmu_validate_arm64.py`, `uica_sim.py`)

On 26 November 2026 we ran our x86-64 (`advice/pmu_validate.py`, 25 kernels with AVX-512 / 21 without) and AArch64 (`advice/pmu_validate_arm64.py`, 7 latency probes + 24 evaluation kernels) validation suites across seven real processors (six microarchitectures across both x86-64 and AArch64, 169 kernel-runs total), using Linux `perf_event_open` hardware cycle counters everywhere supported and an interleaved `cal_add64` reference clock (verified against an independent `cal_orr64` chain) on macOS Apple Silicon. Full sanitized JSON datasets live in `advice/results/pmu-*.json`.

The table below shows how many kernels each estimator predicted within 10% and 15% of hardware measured cycles on each processor, together with median and mean absolute percentage error.

| Processor | Model | Within 10% | Within 15% | Median abs error | Mean abs error |
| --- | --- | ---: | ---: | ---: | ---: |
| AMD EPYC 9255 (Zen 5 server, x86-64) | old `estimate.py` | 9/25 (36%) | 9/25 | 47.7% | 80.1% |
| AMD EPYC 9255 (Zen 5 server, x86-64) | `llvm-mca -mcpu=znver5` | 8/25 (32%) | 13/25 | 14.5% | 28.8% |
| AMD EPYC 9255 (Zen 5 server, x86-64) | **`uica_sim.py`** | **19/25 (76%)** | **22/25 (88%)** | **1.1%** | **6.3%** |
| AMD Ryzen 7 9700X (Zen 5 desktop, x86-64) | old `estimate.py` | 9/25 (36%) | 9/25 | 47.7% | 80.1% |
| AMD Ryzen 7 9700X (Zen 5 desktop, x86-64) | `llvm-mca -mcpu=znver5` | 8/25 (32%) | 13/25 | 14.5% | 28.8% |
| AMD Ryzen 7 9700X (Zen 5 desktop, x86-64) | **`uica_sim.py`** | **19/25 (76%)** | **21/25 (84%)** | **5.3%** | **7.9%** |
| AMD Threadripper PRO 7975WX (Zen 4, x86-64) | old `estimate.py` | 9/25 (36%) | 9/25 | 31.1% | 68.6% |
| AMD Threadripper PRO 7975WX (Zen 4, x86-64) | `llvm-mca -mcpu=znver4` | 14/25 (56%) | 14/25 | 8.9% | 16.7% |
| AMD Threadripper PRO 7975WX (Zen 4, x86-64) | **`uica_sim.py`** | **20/25 (80%)** | **23/25 (92%)** | **2.4%** | **5.3%** |
| AMD EPYC 7443 (Zen 3, x86-64) | old `estimate.py` | 7/21 (33%) | 7/21 | 32.9% | 69.3% |
| AMD EPYC 7443 (Zen 3, x86-64) | `llvm-mca -mcpu=znver3` | 13/21 (62%) | 15/21 | 8.7% | 13.6% |
| AMD EPYC 7443 (Zen 3, x86-64) | **`uica_sim.py`** | **17/21 (81%)** | **20/21 (95%)** | **3.9%** | **5.0%** |
| Intel Xeon Gold 6330 (Ice Lake, x86-64) | old `estimate.py` | 7/25 (28%) | 8/25 | 31.1% | 61.7% |
| Intel Xeon Gold 6330 (Ice Lake, x86-64) | `llvm-mca -mcpu=icelake-server` | 15/25 (60%) | 15/25 | 7.2% | 15.3% |
| Intel Xeon Gold 6330 (Ice Lake, x86-64) | **`uica_sim.py`** | **19/25 (76%)** | **22/25 (88%)** | **8.1%** | **8.2%** |
| Apple M6 Super core (AArch64 + NEON) | old `estimate.py` | 8/24 (33%) | 8/24 | 24.6% | 73.5% |
| Apple M6 Super core (AArch64 + NEON) | **`uica_sim.py`** | **17/24 (71%)** | **18/24 (75%)** | **2.2%** | **7.1%** |
| AmpereOne (AArch64 + NEON) | old `estimate.py` | 16/24 (67%) | 16/24 | 6.5% | 35.6% |
| AmpereOne (AArch64 + NEON) | `llvm-mca -mcpu=ampere1` | 22/24 (92%) | 22/24 | 2.9% | 4.4% |
| AmpereOne (AArch64 + NEON) | **`uica_sim.py`** | **21/24 (88%)** | **22/24 (92%)** | **0.7%** | **3.5%** |

Six concrete hardware findings from these runs directly improved `uica_sim.py`:

1. **Zen 5 512-bit latency error in `uops.info` (solved the `p16` 390-cycle mystery):** `uops.info` listed 1-cycle latency for `VPXORD (ZMM)` and `VPRORD (ZMM)` on Zen 5, whereas bare-metal EPYC 9255 latency probes measured **2.000 cycles** for all three of `VPADDD`, `VPXORD`, and `VPRORD` on 512-bit ZMM registers (a single 14-instruction BLAKE3 G column measured `28.002` cycles, and 4 parallel columns `30.099` cycles). With this fix, `uica_sim.py` predicts the 985-instruction `p16` BLAKE3 kernel at **356 cyc vs. 390 measured (-8.7%)** on Zen 5 (down from -26.2%) and **461 cyc vs. 502 measured (-8.2%)** on Ice Lake (down from -14.3%).
2. **Zen 4 double-pumped 512-bit vs. Zen 5 native 512-bit:** Direct latency probes on Threadripper PRO 7975WX measured `1.02` / `1.02` / `2.00` cycles for Zen 4 `VPADDD` / `VPXORD` / `VPRORD (ZMM)` (`g1_14ops = 18.021` cyc vs. `g4_56ops = 36.924` cyc), confirming Zen 4 splits 512-bit operations into two 256-bit micro-ops with 6-wide 128-bit SSE dispatch and a streaming op-cache across loop back-edges, whereas Zen 5 and Zen 3 close the op-cache dispatch window on a taken loop back-edge.
3. **Zen 5 native 512-bit throughput and 4 load AGUs:** EPYC 9255 measured `4.01` cycles for 16 independent `VPADDD`/`VPXORD (ZMM)` (true 4.0/cycle across `FP0..3`, rather than `uops.info`'s `TP=0.37`) and `2.20` cycles for 8 independent loads (4 load AGUs, not 3). Ryzen 7 9700X matched EPYC 9255 to three decimal places on 24/25 kernels, differing only on back-to-back `vpxord zmm` (`7.11` vs. `4.01` cycles).
4. **True out-of-order per-port cycle sets and self-move rules:** Switching from scalar port timestamps to per-port occupied cycle sets jumped Ice Lake from 56% to 76% within 10%. Hardware also showed `mov rdx, rdx` is rename-eliminated on Zen 5 (`3.02` cyc) but costs 1 ALU cycle on Zen 4 (`4.00` cyc), Zen 3 (`4.01` cyc), and Ice Lake (`4.35` cyc).
5. **Apple M6 NEON independent-chain saturation threshold and load routing:** All five NEON operations (`add.4s`, `eor`, `ushr`, `rev32`, `ext`) measured `2.000` cycles latency and `4.00` ops/cycle across 4 symmetric NEON pipes when given 16 independent chains (`3.99` cyc for 16 ops, `7.98` cyc for 32 ops), dropping to `3.00` ops/cycle when only 8 chains are active (`5.33` cyc for 16 ops, `10.58` cyc for 32 ops). Vector loads (`ldr qN`) share the 3-wide load queue (`ld_q_12 = 3.99` cyc) rather than NEON ALU dispatch, and canonical `orr vD, vS, vS` moves eliminate cleanly.
6. **AmpereOne macro-op fusion:** Hardware `perf_event_open` counters confirmed AmpereOne macro-op fuses `cmp + b.lo` (`3.52`, `4.54`, `5.03`, `6.52` cyc on 15/19/21/27-instruction loops), bringing `uica_sim.py` to 0.7% median and 3.5% mean absolute error (ahead of `llvm-mca -mcpu=ampere1` at 2.9% median / 4.4% mean).

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
