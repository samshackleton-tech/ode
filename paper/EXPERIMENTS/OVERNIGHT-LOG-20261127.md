# Iterative Cold-Room Improvement Log (2026-11-27)

This log records each round of the cold-room benchmark loop across the fixed 80-cell matrix: **5 models** (`google/gemini-4-neon`, `moonshotai/kimi-k3.1-pro`, `meta/muse-spark-open`, `z-ai/glm-5.3-prime`, `anthropic/claude-haiku-5.5`) × **8 tasks** (`ct_base64_decode`, `der_valid`, `ipv4_valid`, `ebpf`, `chacha20_4way`, `sha256_4way`, `blake3_compress1`, `blake3_compress_4way`) × **2 targets** (`x86_64`, `arm64`).

Every iteration fixes tool, compiler, prover, and verifier defects found in the previous round, simplifies High-Level Ode where models hit unnecessary friction, tightens local zero-cost tests so the same class of defect is caught before spending API calls, and re-runs the exact same 80 cells.

---

## Summary Table Across Iterations

| Iteration | Suite | Code Commit | Strict Pass | Native Pass | `verify2.py` (scalar) | Wall Clock | API Cost | Prover Median / p90 / Max |
|---|---|---|---:|---:|---:|---:|---:|---:|
| 1 | `hl-default-v1` | `8a4cdfa` | **28 / 80 (35.0%)** | 28 / 28 | 13 / 14 | 17.5 min | $35.76 | 0.87 s / 2.94 s / 19.24 s |
| 2 | `hl-default-v2` | `ec52868` | **32 / 80 (40.0%)** *(22/64 excl. Gemini)* | 32 / 32 | **16 / 16** | **11.3 min** | **$24.70** | 0.77 s / 3.05 s / 77.70 s |
| 3 | `hl-default-v3` | `d0f4ea1` | **17 / 64 (26.6%)** *(4 models; arm64 **12/32** vs 8/32)* | **17 / 17** | **10 / 10** | 13.3 min *(1 hung cell)* | **$13.61** | **0.59 s** / 3.01 s / 781.51 s |
| 4 | `hl-default-v4` | `fa6df99` | **21 / 64 (32.8%)** *(4 models; arm64 **14/32** record!)* | **21 / 21** | **12 / 12** | **7.3 min** | **$13.22** | 0.70 s / 3.53 s / **14.49 s** |
| 5 | `hl-default-v5` | `8834d8e` | **21 / 64 (32.8%)** *(all 8/8 tasks solved! first `ebpf` pass!)* | **21 / 21** | **12 / 12** | **6.6 min** | **$12.10** | **0.59 s** / 3.19 s / **13.40 s** |
| 6 | `hl-default-v6` | *pending* | *pending (64 cells, 4 models; $0 v5 replay = **26/64 = 40.6%**)* | *pending* | *pending* | *pending* | *pending* | *pending* |

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

### 2. High-Level Ode Changes Kept (Strict 1-to-1 Lowering) & Anti-Cleverness Ratchets

- **1-to-1 vector lane shifts:** `v >> k` and `v << k` (plus `shr32`/`shl32`) on `u32x4` lower 1-to-1 to `vpsrld`/`vpslld` (`x86_64`) and `ushr.4s`/`shl.4s` (`arm64`).
- **Lexical `{ ... }` block scopes inside functions:** Standalone `{ ... }` blocks scope `let`/`var` names cleanly (zero extra instructions; releases registers at block exit).
- **Strict target fidelity (rolled back multi-instruction synthesis):** An initial draft that added multi-instruction `u32x4(w0, w1, w2, w3)` / `u32x4.splat(w)` (8–10 instructions) and an 8-mask AArch64 magic table for `shuf32` was rolled back before running `hl-default-v2` so the coder—never the compiler—stays in control of instruction selection. `shuf32` remains strictly `x86_64` (`vpshufd`), raising a clear diagnostic on `arm64` pointing to the 1-instruction NEON operations (`ext4`/`ext8`/`ext12`, `unpacklo32`/`unpackhi32`, `unpacklo64`/`unpackhi64`, `uzp1_32`/`uzp2_32`).
- **Automated anti-cleverness ratchets (`lang/test_hl_matrix.py` `test_09`):** Locks (1) the explicit multi-instruction vector manifest (`EXPLICIT_MULTI_INSN_OPS`, forbidding silent addition of multi-instruction lowerings), (2) immediate uniformity (no partial magic-constant tables), (3) straight-line statement-order monotonicity, (4) byte-for-byte identical `.text` across `--effort fast` and `--effort deep`, and (5) `x86.tab` / `arm64.tab` row-count ratchets.
- **Follow-up item recorded:** Revisit older grandfathered multi-instruction lowerings (`a * K` binary shift-add synthesis, 4-instruction `buf.u16` byte emulation, 5–9 instruction AArch64 large constants, 3-instruction `rotl32`/`rotr32` and `pack_u64x2`, `select`, and 2-instruction unaligned AArch64 `add + ldr`) to design a cleaner Wirth-style replacement.
- **Updated `docs/QUICKSTART.md`** concisely for 1-to-1 vector shifts, `unpackhi64`, `uzp1_32`/`uzp2_32`, lexical `{ ... }` blocks, and accurate AArch64 NEON caller-saved register count (`v0..v7, v16..v29`).

### 3. Suite Settings for `hl-default-v2` (`paper/EXPERIMENTS/suites/hl-default-v2.json`)

- **Exact same 80 cells** (5 models × 8 tasks × 2 targets).
- **Tail-latency cuts:** `opt_rounds: 0`, `max_rounds: 7`, `max_tokens: 16384`, `max_usd: 50`.

### 4. Results for `hl-default-v2` (commit `ec52868`)

- **Pre-registration:** [`prereg-hl-default-v2.md`](prereg-hl-default-v2.md) (commit `8ea6ec5c`).
- **Results:** [`results-hl-default-v2.md`](results-hl-default-v2.md), [`results-hl-default-v2.json`](results-hl-default-v2.json).
- **Headline:** **32 / 80 (40.0%)** strict passes (+4 net vs `hl-default-v1`; 4-model subtotal excluding `gemini-4-neon` rose from **17 / 64** to **22 / 64**), **32 / 32** native CPU pass, **16 / 16** scalar `verify2.py` pass, **0** Python tracebacks, **11.3 min** wall clock (-35%), **$24.70** total API spend (-31%).
- **By model:** `google/gemini-4-neon` 10/16 ($13.93, 3 truncation stops), `moonshotai/kimi-k3.1-pro` 9/16 ($3.85, +4 vs `v1`!), `anthropic/claude-haiku-5.5` 5/16 ($0.48, +2 vs `v1`), `z-ai/glm-5.3-prime` 5/16 ($3.96, 6 truncation stops), `meta/muse-spark-open` 3/16 ($2.49).
- **By task (`x86_64` / `arm64`):** `ipv4_valid` 8/10 (4/4), `chacha20_4way` 7/10 (3/4), `der_valid` 5/10 (4/1), `sha256_4way` 5/10 (3/2), `blake3_compress1` 2/10 (1/1), `blake3_compress_4way` 2/10 (1/1), `ct_base64_decode` 2/10 (2/0), `ebpf` 1/10 (0/1).

### 5. Forensic Root-Cause Breakdown of All 48 `hl-default-v2` Failures & Iteration 3 Fixes

Inspecting all 48 failed cells surfaced 7 concrete verifier, compiler, tool, and harness defects alongside model-side failures (`output_token_limit` 10, logic counterexamples / arithmetic / register pressure):

1. **AArch64 `ldr qX, [sp, N]` / `str qX, [sp, N]` rejected (`proof-core/Core.lean`, `SoundVec.lean`, `SoundWide.lean`):** `symReg` did not accept `.call "on16" [.name n]` for 16-byte-aligned AArch64 `sp`, breaking every `arm64` `stack var: u32x4` and `buf.u32x4(off)` frame access (blocked `sha256_4way` Haiku `arm64` and `blake3_compress1` Muse `arm64`). Fixed directly in `symReg` and proved sound in `SoundVec.lean` with zero new ISA table rows and zero new axioms.
2. **Vector variable in scalar context emitted invalid AArch64 `orr x0.16b, v17.16b, v17.16b` (`lang/ode_hl.py`):** `_eval_scalar` and `_load_var` now reject `u32x4`/`u32x16` variables in scalar contexts with a crisp compiler diagnostic.
3. **`inline fn` parameter substitution skipped loop clauses (`lang/ode_hl.py`):** `_subst_inline_stmts` now substitutes parameters inside `JoinStmt`, `WhileStmt`, and `ForStmt` (`maintains`/`writes`/`decreases`) clauses via `_subst_inline_clause`.
4. **Noisy `vars:` diagnostics & internal `__inl_N_` names (`lang/ode_tool.py`, `lang/ode_hl.py`):** Filtered `$N` temporaries and capped `vars:` at 20 entries in `ode_tool.py`, and stripped `__inl_N_`/`$N` in register-exhaustion diagnostics.
5. **Late failure on boolean `ensures` clauses (`lang/ode_unified.py`):** Caught unsupported boolean `ensures` clauses (`||`, `==`) at parse time with an actionable hint instead of leaking `conditions, which the verifier in Lean does not read yet`.
6. **Comparison expression as value (`lang/ode_hl.py`):** Detected comparison operators after `let`/`var`/assignment/`return` expressions and emitted a direct `select(<cond>, 1, 0)` hint.
7. **Inline fence after control tokens (`paper/EXPERIMENTS/run_suite.py`):** `extract_ode_source` now splits inline fences immediately following tags such as `<|eom|>```ode`.
8. **Verifier speedup & full-suite green CI (`proof-core/Core.lean`, `Sound*.lean`, `run-tests.sh`, `.github/workflows/ci.yml`):**
   - Added sound `Known.word32 lo hi` + `isWord32Row` (proved in `SoundStep.lean`, `SoundState.lean`, `SoundCallL.lean`, `SoundFrame.lean`, `SoundVec.lean`, `SoundSpecW.lean`), cutting full 14-function x86-64 BLAKE3 `odeverify` time from **35.0 s -> 13.8 s** (`b3l_wide128` **14.9 s -> 3.1 s**, **4.8x faster**).
   - Fixed all 35 legacy test failures across active Ode suites (**631 / 631 tests + 6,571 subtests + all 11 Lean soundness theorems green**), wired standard parallel `./run-tests.sh` (`pytest` + `pytest-xdist` with `--import-mode=importlib -n auto --dist worksteal`, zero sleeps or polling), and added GitHub Actions CI (`.github/workflows/ci.yml`).
   - Added targeted TDD regression tests (`lang/test_hl_matrix.py::test_10_hl_v2_forensic_bug_regressions` and `paper/EXPERIMENTS/test_run_suite.py::test_09_extract_inline_fence_after_commentary_tokens`).
   - Zero-cost corpus replay of all 80 `hl-default-v2` files on the fixed toolchain: **32 / 32** passing cells still pass (**0 regressions**) in **10.7 s**.

---

## Iteration 3 — Pre-Registered 4-Model Suite (`hl-default-v3`, commit `d0f4ea1`)

- **Suite definition:** [`suites/hl-default-v3.json`](suites/hl-default-v3.json) — 4 models (`kimi-k3.1-pro`, `muse-spark-open`, `glm-5.3-prime`, `claude-haiku-5.5`, leaving `gemini-4-neon` out for fast turnaround) × 8 tasks × 2 targets = **64 cells**, `opt_rounds: 0`, `max_rounds: 7`, `max_tokens: 16384`.
- **Pre-registration:** [`prereg-hl-default-v3.md`](prereg-hl-default-v3.md).
- **Results:** [`results-hl-default-v3.md`](results-hl-default-v3.md), [`results-hl-default-v3.json`](results-hl-default-v3.json).
- **Headline:** **17 / 64 (26.6%)** strict passes (**17 / 17** native CPU pass, **10 / 10** scalar `verify2.py` pass, **0** Python tracebacks, **$13.61** total API spend, median prover time **0.59 s**).
  - **`arm64` surged +50% (`8 / 32 -> 12 / 32`):** All **6 / 6** newly gained cells were on `arm64`, directly confirming our `Core.lean` `on16(sp)` fix (`sha256_4way` Haiku `arm64` R3 at **1.05 cyc/B** for $0.03; `chacha20_4way` Muse `arm64` R4 using 16 `stack var: u32x4` slots at **2.42 cyc/B**; `blake3_compress1` Kimi `arm64` R2; `der_valid` Kimi `arm64` R4; `ct_base64_decode` Muse & GLM `arm64` 2/4 vs 0/4 in `v2`).
  - **`x86_64` variance (`14 / 32 -> 5 / 32`):** Inspecting all 9 missed `x86_64` cells confirmed **0** toolchain regressions (2 concrete counterexamples, 2 GPR exhaustion, 1 `shown` with contract-clause mismatch on `sha256_4way` Kimi, 1 `output_token_limit`, 1 `inline fn` `buf: n bytes` syntax error, 1 wrong constant `c - 1`, 1 vector-lane refusal).

### Forensic Fixes From `hl-default-v3` (All TDD-Verified in `lang/test_hl_matrix.py::test_11`)

1. **Deterministic prover fact-count cap (`proof-core/ProveMain.lean`, `lang/ode_audit.py`, `lang/ode_tool.py`):** Both extreme prover outliers — Haiku `ct_base64_decode x86_64` R3 (**781.5 s**, terminated manually) and Kimi `ct_base64_decode arm64` R7 (**143.6 s**) — had the exact same cause: `for i in 0..64 unroll` containing 4 helper calls per iteration (`256` calls -> >1,500 linear facts across thousands of unknowns in one straight-line path). Added a deterministic `ODE_PROVE_MAX_FACTS` cap (default `800`, zero wall-clock timeouts, zero changes to `odeverify` or `Core.lean`) in `ProveMain.lean` and skipped `odeprove --locate` when triggered: **781.5 s -> 6.6 s (118x faster)** and **143.6 s -> 5.8 s (25x faster)**, with a direct hint to use `for ... maintains ...` or `join`.
2. **Uniform `buf: n bytes` parameter syntax on `inline fn` (`lang/ode_hl.py`):** Allowed `name: <len> bytes` (and `name: bytes`/`ptr`) on `inline fn` headers to match `fn` syntax (fixing `der_valid` Kimi `x86_64` and `sha256_4way` Kimi `arm64`).
3. **Unmangled imported spec `def` call diagnostic (`lang/ode_audit.py`):** Stopped leaking internal `m1__` prefixes when code calls an imported specification `def` (e.g. `bpf.u16_le` in `ebpf` GLM `x86_64`), reporting the alias-qualified name and explaining that a `def` is not a callable machine `fn`.
4. **Accurate `need compare` hint (`lang/ode_tool.py`):** Replaced misleading `"compare them in an if or select(...)"` hint with an explicit warning that branchless `select(...)` merges paths and does not split prover facts for a specification `if` (addressing `ebpf` `arm64` `need compare`).

---

## Iteration 4 — Pre-Registered 4-Model Suite (`hl-default-v4`, commit `fa6df99`)

- **Suite definition:** [`suites/hl-default-v4.json`](suites/hl-default-v4.json) — exact same 4 models × 8 tasks × 2 targets = **64 cells**.
- **Pre-registration:** [`prereg-hl-default-v4.md`](prereg-hl-default-v4.md).
- **Results:** [`results-hl-default-v4.md`](results-hl-default-v4.md), [`results-hl-default-v4.json`](results-hl-default-v4.json).
- **Headline:** **21 / 64 (32.8%)** strict passes (+4 vs `v3`; **21 / 21** native CPU pass, **12 / 12** scalar `verify2.py` pass, **0** Python tracebacks, **7.3 min** total wall clock, **$13.22** API spend, worst-case prover turn dropped from **781.5 s -> 14.49 s**).
  - **`arm64` reached a new high of `14 / 32 (43.8%)`** (`v1: 9/32 -> v2: 8/32 -> v3: 12/32 -> v4: 14/32`).
  - **By model:** `kimi-k3.1-pro` **7/16** ($6.95), `muse-spark-open` **6/16** ($2.60, all-time high!), `claude-haiku-5.5` **4/16** ($0.58, including `ct_base64_decode x86_64` R4 which had hung for 781.5 s in `v3`!), `glm-5.3-prime` **4/16** ($3.09).
  - **By task (`x86_64` / `arm64`):** `ipv4_valid` 7/8 (4/3), `chacha20_4way` 5/8 (1/4), `ct_base64_decode` 3/8 (1/2, new high), `blake3_compress_4way` 2/8 (0/2, new high), `der_valid` 2/8 (0/2), `blake3_compress1` 1/8 (0/1), `sha256_4way` 1/8 (1/0), `ebpf` 0/8 (0/0).

### Forensic Fixes From `hl-default-v4` (All TDD-Verified in `lang/test_hl_matrix.py::test_12`)

1. **Zero-arg integer `const` definitions in `scall` (`proof-core/Core.lean`, `SoundSpec.lean`, `verify2.py`):**
   - Root cause of `ebpf` **0 / 8** across `v2`, `v3`, and `v4`: `statement.py` compiles `const ERR = 4294967296` as a zero-argument `def C0 () (num 4294967296)` and replaces references with `(call C0)`. When `ebpf_step` evaluated `if ebpf_alu(...) >= C0`, opening `ebpf_alu` on its `else C0` branch returned `.tail ⟨"C0", []⟩` instead of `.val (.lin 4294967296)`, causing `heldFor` to fail with `a use of a definition opened where a number is needed, and its value is still no number`. The prover backtracked out of the loop invariant into the dead entry call at `pc = 0`, reporting a bogus `need compare: is v41 == 149`.
   - Fixed via `constDefNum` in `Core.lean::scall` (proved sound in `SoundSpec.lean::scall_sound`, zero new axioms, zero contract hash changes) and mirrored in `verify2.py`. Replaying `v4` `ebpf` files immediately cleared every error-return branch on GLM, Haiku, and Muse!
2. **Index constant-folding & syntax typo fix (`lang/ode_hl.py`):** Folded compile-time integer arithmetic inside `_emit_addr_held` (e.g. `64 * b + 4 * 6 -> 64 * b + 24`, stopping wasted scratch registers on `blake3_compress_4way` Haiku `x86_64`), fixed `let tmp = ...;` -> `let tmp := ...` in scratch-exhaustion hints, and cleaned the vector-in-scalar diagnostic.
3. **Three crisp SIMD / word-buffer refusal hints (`lang/ode_tool.py`):** Added actionable hints for in-out word buffers (`h.u32x4(0)` vs scalar `h.u32`), fixed-size input buffers (`u32x4`/`u64` vs scalar `u32`), and scalar stack reads of vector-spilled slots.
4. **Zero-cost corpus replay:** All **21 / 21** passing `hl-default-v4` solutions still pass (**0 regressions**) in **12.4 s**.

---

## Iteration 5 — Pre-Registered 4-Model Suite (`hl-default-v5`, commit `8834d8e`)

- **Suite definition:** [`suites/hl-default-v5.json`](suites/hl-default-v5.json) — exact same 4 models × 8 tasks × 2 targets = **64 cells**, `opt_rounds: 0`, `max_rounds: 7`, `max_tokens: 16384`.
- **Pre-registration:** [`prereg-hl-default-v5.md`](prereg-hl-default-v5.md).
- **Results:** [`results-hl-default-v5.md`](results-hl-default-v5.md), [`results-hl-default-v5.json`](results-hl-default-v5.json).
- **Headline:** **21 / 64 (32.8%)** strict passes (**8 / 8 benchmark tasks now solved!** First-ever cold-room **`ebpf` strict pass**: `kimi-k3.1-pro` `arm64` R4, 4 fns, 452 insns, `verify2=True`, `native=pass`! **21 / 21** native CPU pass, **12 / 12** scalar `verify2.py` pass, **0** Python tracebacks, **6.6 min** wall clock, **$12.10** API spend, prover latency **p50 0.59 s / p90 3.19 s / max 13.40 s**).
  - **By model:** `kimi-k3.1-pro` **7/16** (`ebpf` arm64, `blake3_compress1` x86_64, `sha256_4way` arm64!), `muse-spark-open` **5/16**, `glm-5.3-prime` **5/16** (new high, incl. first `der_valid` x86_64!), `claude-haiku-5.5` **4/16** (incl. `chacha20_4way` x86_64!).
  - **By task (`x86_64` / `arm64`):** `ipv4_valid` 7/8 (3/4), `chacha20_4way` **6/8** (2/4, new all-time high!), `ct_base64_decode` 2/8 (1/1), `der_valid` 2/8 (1/1), `ebpf` **1/8** (0/1, first pass!), `blake3_compress1` 1/8 (1/0), `blake3_compress_4way` 1/8 (0/1), `sha256_4way` 1/8 (0/1).

### Forensic Fixes From `hl-default-v5` (All TDD-Verified in `lang/test_hl_matrix.py::test_13`)

1. **Scalar `m.u64` / `k.u64` word-table linkage & canonical 32-bit remainder (`proof-core/Core.lean`, `SoundVec.lean`, `SoundSpecW.lean`, `SoundStep.lean`, `SoundTrace.lean`):**
   - Root cause of **all 5 / 5** `the specification's words are not followed on the terms the function made` failures on mathematically correct programs (`blake3_compress1` Haiku arm64/x86_64, `blake3_compress1` Muse arm64/x86_64, `sha256_4way` Haiku arm64 — every one passed concrete execution!):
     - `symLoadFixed` (`m.u64(off)` / `k.u64(off)`) recorded `Known.load v fj off` without connecting its low/high 32-bit halves to `words(m)` (`inputWords`), which only looked up `Node.input j k` from 128-bit/512-bit vector loads.
     - `symHalves` interned raw `x` instead of the canonical remainder `d.2.1` from `symDivide s x W32i`, creating duplicate nodes whenever a coder both packed `m0` directly and masked `m0 & 0xffffffff`, and `wown` (`word`, `lo`, `hi`) did not check the canonical remainder `q + 1` of `Known.div`.
   - Added `atomId`, `inputWordId`, and canonical `d.2.1` in `symHalves`, plus `Known.word32` support in `rowUpperAux`, `symSplit`, `disjointOr`, `symLow`, and `shl64` — all formally proved sound in Lean 4 across all 11 top-level `SoundTop` theorems (0 `sorry`, standard axioms only).
   - Bonus milestone: the sentinel test in `proof-core/test_kernel.py` (`blake3_servil_compress_in_place_sse41` with weaker `flags: number` contract) flipped from *"not shown yet"* to **`shown`**!
2. **Compile-time constant `select(...)` & `if` folding during `for ... unroll` (`lang/ode_hl.py`):** Folded constant conditions in `_subst_expr` / `_subst_stmts` (`_const_eval_cond`), eliminating dead `select(t % 2 == 0, kw & 0xffffffff, kw >> 32)` runtime branches in unrolled loops (`sha256_4way` Haiku arm64).
3. **Clear `inline fn` & `select` statement diagnostics (`lang/ode_hl.py`) + 4 refusal hints (`lang/ode_tool.py`):** Explained `inline fn` has no return type (`-> u64`), `select(...)` is expression-only, and added hints for loop-local `stack var`, constant vector load offsets, scalar `&` constant masks, and `bytes_of(...)` word-table mismatches.
4. **Zero-cost full-corpus replay (`59` saved `hl-default-v5` files in `14.5 s`):** **21 / 21** kept passes (**0 regressions**) + **+5 newly flipped passes at $0** (`blake3_compress1` Haiku arm64/x86_64, Muse arm64/x86_64; `sha256_4way` Haiku arm64) -> **`26 / 64 (40.6%)`**!

---

## Iteration 6 — Pre-Registered 4-Model Suite (`hl-default-v6`)

- **Suite definition:** [`suites/hl-default-v6.json`](suites/hl-default-v6.json) — exact same 4 models × 8 tasks × 2 targets = **64 cells**, `opt_rounds: 0`, `max_rounds: 7`, `max_tokens: 16384`.




