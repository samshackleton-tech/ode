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

### Layer 2: rough cycle bounds and cache simulation

- **Compute lower bound:** builds the register and static frame-slot dependency graph from each table row's reads and writes and takes the largest of critical-path latency, front-end issue width, and execution-unit throughput.
- **L1D cache simulation:** runs an exact LRU set-associative model over the concrete access trace under both warm-start (working set resident up to cache associativity) and cold-start assumptions.
- **Warm and cold totals:** adds dynamic compute lower bound, hazard penalties, and simulated L1 miss penalties. These totals are intended for comparing two variants of the same function (`ode_tool.py compare`), not for predicting exact wall-clock cycles.

## Target profiles in `arch.json`

The table below lists the five processor profiles in `advice/arch.json`. Each row gives the profile name, target architecture, cache-line size, page size, L1 data-cache geometry, and source of the instruction timings.

| Profile | Target | Cache line | Page | L1D cache | Instruction timings |
| --- | --- | --- | --- | --- | --- |
| `zen5` | `x86_64` | 64 B | 4 KiB | 48 KiB, 12-way | `uops.info` measurements |
| `zen4` | `x86_64` | 64 B | 4 KiB | 32 KiB, 8-way | `uops.info` (double-pumped 512-bit) |
| `icelake` | `x86_64` | 64 B | 4 KiB | 48 KiB, 12-way | `uops.info` measurements |
| `apple_m` | `arm64` | 128 B | 16 KiB | 128 KiB, 8-way | Architecture docs (calibration pending) |
| `ampere1` | `arm64` | 64 B | 4 KiB | 64 KiB, 4-way | Architecture docs (calibration pending) |

## Explicit budgets

The coder can pass explicit upper bounds to `lang/ode_tool.py check` or `advise`: `--max-bytes`, `--max-icache-lines`, `--max-frame-bytes`, `--max-line-splits`, `--max-page-crossings`, `--max-stlf-partial`, and `--max-alias-4k`. Any exceeded budget causes exit code 2 after printing the full report.

## Tests

```sh
python3 advice/test_estimate.py
pypy3 advice/test_estimate.py
```

## Earlier study

- `uops-test/` (November 20, 2026): a first test of whether `uops.info`'s per-processor table predicts the cycles the 16-way BLAKE3 kernel takes per block. It ranks three processors correctly and is low by 17% to 35%. See also `DESIGN.md`, section 5.
