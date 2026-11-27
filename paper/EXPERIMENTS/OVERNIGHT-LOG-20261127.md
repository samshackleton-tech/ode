# Iterative Cold-Room Improvement Log (2026-11-27)

This log records each round of the cold-room benchmark loop across the fixed 80-cell matrix: **5 models** (`google/gemini-4-neon`, `moonshotai/kimi-k3.1-pro`, `meta/muse-spark-open`, `z-ai/glm-5.3-prime`, `anthropic/claude-haiku-5.5`) × **8 tasks** (`ct_base64_decode`, `der_valid`, `ipv4_valid`, `ebpf`, `chacha20_4way`, `sha256_4way`, `blake3_compress1`, `blake3_compress_4way`) × **2 targets** (`x86_64`, `arm64`).

Every iteration fixes tool, compiler, prover, and verifier defects found in the previous round, simplifies High-Level Ode where models hit unnecessary friction, tightens local zero-cost tests so the same class of defect is caught before spending API calls, and re-runs the exact same 80 cells.

---

## Summary Table Across Iterations

| Iteration | Suite | Code Commit | Strict Pass | Native Pass | `verify2.py` (scalar) | Wall Clock | API Cost | Prover Median / p90 / Max |
|---|---|---|---:|---:|---:|---:|---:|---:|
| 1 | `hl-default-v1` | `8a4cdfa` | **28 / 80 (35.0%)** | 28 / 28 | 13 / 14 | 17.5 min | $35.76 | 0.87 s / 2.94 s / 19.24 s |
| 2 | `hl-default-v2` | *pending* | *pending* | *pending* | *pending* | *pending* | *pending* | *pending* |

---

## Iteration 1 — Baseline (`hl-default-v1`, commit `8a4cdfa`)

- **Pre-registration:** [`prereg-hl-default-v1.md`](prereg-hl-default-v1.md) (commit `ffa86871`).
- **Results:** [`results-hl-default-v1.md`](results-hl-default-v1.md), [`results-hl-default-v1.json`](results-hl-default-v1.json).
- **Headline:** **28 / 80 (35.0%)** strict passes; all 8 tasks were solved by at least one model (including `sha256_4way` on both architectures and pure High-Level Ode `ebpf` on `arm64`). Every passing binary passed native execution (`28 / 28`), emitted **0 silent spills** and **0 `stack var` allocations**, and used 712 total stack bytes across all 28 solutions.
- **By model:** `gemini-4-neon` 11/16 ($19.21, 17.5 min), `glm-5.3-prime` 5/16 ($7.10, 17.2 min, 12 truncations), `kimi-k3.1-pro` 5/16 ($5.24, 3.2 min), `muse-spark-open` 4/16 ($3.45, 3.5 min), `claude-haiku-5.5` 3/16 ($0.77, 6.7 min).

### Diagnosis 1: Why the Wall-Clock Tail Took 17.5 Minutes

Out of 21,668 total worker-seconds across the 80 cells, **96.5% (20,908 s)** was API wait and only **3.5% (760 s)** was local Ode compile/prove/audit time:

1. **Optimization rounds (`opt_rounds: 2`)** on `gemini-4-neon` added 3,090 s of API wait and $6.78 (including the two slowest individual turns at 237.9 s and 234.6 s), while only 1 of 22 post-pass optimization turns improved static cycles by more than 1.1%.
2. **High output-token cap (`max_tokens: 32000`)** let `glm-5.3-prime` spend 2,455 s on 12 truncated replies (up to 201 s per truncated turn).
3. **Round 8 (`max_rounds: 8`)** produced **0 / 28** passes (all 28 passes occurred in Rounds 1–7).

### Diagnosis 2: Ten Tool / Compiler / Prover / Verifier Defects Found

1. **Independent verifier tail-call spec order (`proof-core/verify2.py`):** On `ipv4_valid` (`muse-spark-open`, `arm64`), `verify2.py` evaluated callee `returns` before adding `(got_val, rv)` to `st["eqs"]`, shifting `callsOf` numbering relative to `Core.lean` whenever `t open k` ran at a tail call (`13/14` instead of `14/14`).
2. **Prover spec-chain & `t same` pruning (`proof-core/prove.py`):**
   - `t same` at `opened >= 1` discarded valid matches against `deg >= 2` anchor calls (such as a shared `join` + `for` invariant left-hand side) and wasted `O(N^2)` queries comparing pairs of already-resolved helper calls (`has_val == 1`).
   - When `t same` succeeded at `opened == 0`, the verifier incremented `o` to `1` and looped with `self.spec_max_open` still stuck at `1` from an earlier goal's `bud = 1` search, immediately aborting a fresh goal before trying deeper budgets.
   - `fast` mode capped `spec_budgets` at 12 (and `opened >= 14 and count >= 16`), cutting off 10-step unrolled loops that need 11 opens plus `fold2_ok`.
3. **`const_u32x4(num)` crash (`lang/ode_hl.py`):** Passing a numeric constant to `const_u32x4` raised `AttributeError: 'Num' object has no attribute 'name'` instead of lowering or raising a clean compiler error.
4. **Invalid `x86.tab` mnemonic for `unpackhi64` (`lang/ode_hl.py`):** `unpackhi64` emitted `vpunpckhqdq xmm`, which is not in `core/x86.tab` (the table provides `vshufps dst, a, b, 238` for the same lane permutation).
5. **Cross-target `shuf32` emission (`lang/ode_hl.py`):** `shuf32` emitted x86 `vpshufd` on `arm64`, crashing the AArch64 assembler instead of lowering portable NEON lane rotations/splats or raising a clear target diagnostic.
6. **Unaligned AArch64 immediate-offset loads/stores (`lang/ode_hl.py`):** `buf.u64(52)` and `src.u32x4(4)` emitted `ldr x, [base, 52]` and `ldr q, [base, 4]`, which violate AArch64's scaled immediate alignment (`8` / `16` bytes) instead of computing `add tmp, base, disp; ldr [tmp, 0]`.
7. **Naive `&&` splitting in `maintains` (`lang/ode_hl.py`):** Splitting `maintains` clauses on every `"&&"` broke `(if a <= x && x <= b then ... else ...)` inside invariants; `!=` in `maintains` also lacked a direct diagnostic.
8. **Uncaught `HLErr` on `inline fn -> ty`, wrong transitive `callee_stack`, and `ensures ret == ...` (`lang/ode_unified.py`):**
   - `parse_hl_inline` raised `HLErr` instead of `UnifiedErr` when given a return type on `inline fn`, leaking a Python traceback.
   - Transitive stack accounting used only the callee's lowered frame rather than `max(lowered, declared_stack)` and counted tail jumps (`jmp`/`b`) as non-tail calls.
   - Writing `ensures ret == ...` instead of `returns ...` produced a confusing downstream error instead of a parse-time diagnostic.
9. **Internal `__inl_*` variable noise and `blake3_compress1` skipped by concrete refuter (`lang/ode_tool.py`, `lang/refute_conc.py`):**
   - `vars:` error dumps exposed internal `__inl_N_*` temporary names from `inline fn` expansion.
   - `refute_conc.py` did not recognize `word`, `low word`, `counter`, or read-and-write (`in-out`) byte buffers, so buggy `blake3_compress1` solutions received no concrete counterexample.
10. **Experiment harness fence extraction and contract-hash mismatch diagnostics (`paper/EXPERIMENTS/run_suite.py`):**
    - A non-greedy regex in `extract_ode_source` left a stray ```` ```ode ```` line inside extracted source when replies contained earlier prose backticks.
    - Contract-hash mismatches were not classified as `contract_id_mismatch`, and models were not shown their compiled binary's canonical `.ocl` contract clauses to see which header clause differed.

### Why Earlier Local Tests Missed These Defects

Our existing unit and fuzz tests (`test_hl.py`, `test_hl_fuzz.py`) tested only a subset of intrinsics, focused mostly on scalar arithmetic and aligned offsets, did not assert that every entry of `ode_hl._INTRINSICS` assembles against both `x86.tab` and `arm64.tab`, did not run `verify2.py` on every scalar test, and did not check that `refute_conc.py` produces counterexamples on every task contract.

---

## Iteration 2 — TDD Matrix, 10 Bug Fixes, and Language Simplifications (`hl-default-v2`)

### 1. Three-Part Zero-Cost TDD Workflow Added First

- **Self-enforcing feature × target matrix (`lang/test_hl_matrix.py`, 8 test groups):** Automatically reads `ode_hl._INTRINSICS` (failing if any new intrinsic is added without a test entry), verifies every intrinsic on both `x86_64` and `arm64` against `x86.tab`/`arm64.tab`, checks that error hints never cite nonexistent intrinsics, verifies new vector operations, unaligned offsets, lexical `{ ... }` blocks, `refute_conc.py` on `blake3_compress1`, metamorphic tail-call + 4-step unroll dual-verification (`odeverify` + `verify2.py`), and `run_suite.py` fence extraction.
- **Expanded vector fuzzer & differential verifier tests:** Added `test_06_random_vector_exprs_and_intrinsics_both_arches` to `lang/test_hl_fuzz.py` (24 randomized 5-step `u32x4` vector programs across both targets checked against an exact lane oracle) and `test_18_tail_call_multi_open_spec_order` to `proof-core/test_verify2.py`.
- **Zero-cost local corpus replay:** Replayed all 80 saved `.ode` / `.last.ode` files from `hl-default-v1` locally in **21.3 s ($0.00)** before launching `hl-default-v2`:
  - **28 / 28** previously passing solutions still pass (0 regressions); all **14 / 14** scalar passes now pass `verify2.py`.
  - **2 / 52** previously failing solutions flip directly to `shown` with **zero model edits**: `chacha20_4way` (`claude-haiku-5.5`, `x86_64`, 1.3 s) and `ipv4_valid` (`kimi-k3.1-pro`, `x86_64`, 1.6 s).
  - **0** uncaught Python tracebacks across all 80 corpus files (down from 3).
  - `blake3_compress1` buggy solutions (`kimi-k3.1-pro`, `glm-5.3-prime`) now receive concrete word-level counterexamples (`refused with a proof`) in 0.3 s.

### 2. High-Level Ode Simplifications Added

- **Vector lane shifts:** `v >> k` and `v << k` (plus `shr32`/`shl32`) on `u32x4` lower directly to `vpsrld`/`vpslld` (`x86_64`) and `ushr.4s`/`shl.4s` (`arm64`).
- **Portable vector constructors:** `u32x4(w0, w1, w2, w3)` / `u32x4.of(...)` and `u32x4.splat(w)` work portably for both integer constants and runtime `word`/`u64` expressions on both `x86_64` and `arm64`, using `vmovq`/`fmov` + lane shuffles with zero extra scratch registers and full Lean verification (`u32x16(w)` / `u32x16.splat(w)` lower to `vpbroadcastd` on `x86_64`).
- **Portable `shuf32` on `arm64`:** Common lane rotations (`0x39`, `0x4E`, `0x93`, `0xE4`) and lane splats (`0x00`, `0x55`, `0xAA`, `0xFF`) lower directly to NEON `ext` / `zip1` / `zip2` / `orr`; unsupported masks emit a crisp error listing the supported masks and NEON alternatives.
- **Lexical `{ ... }` block scopes inside functions:** Standalone `{ ... }` blocks scope `let`/`var` names cleanly (releasing registers at block exit without name collisions).
- **Updated `docs/QUICKSTART.md`** concisely for the new portable vector constructors, vector shifts, portable `shuf32`, lexical `{ ... }` blocks, and accurate AArch64 NEON caller-saved register count (`v0..v7, v16..v29`).

### 3. Suite Settings for `hl-default-v2` (`paper/EXPERIMENTS/suites/hl-default-v2.json`)

- **Exact same 80 cells** (5 models × 8 tasks × 2 targets).
- **Tail-latency cuts:** `opt_rounds: 0`, `max_rounds: 7`, `max_tokens: 16384`, `max_usd: 50`.

*(Results for `hl-default-v2` will be appended as soon as the run completes.)*
