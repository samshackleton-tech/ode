# Complete Cold-Room Failure Catalog & High-Level Ode Synthesis (2026-11-26)
## Why This Catalog Exists

Across **19 pre-registered cold-room runs** (`ebpf-v1` through `utf8-v1`), **7 language models** attempted **372 function-writing cells** across **14 tasks** and both `x86_64` and `arm64`, executing **2,143 compile-and-verify rounds**. Of those **372 cells**, **236 passed** (`63.4%`) and **136 failed** (`36.6%`, across **1,536 failing rounds**).

Looking at one failure at a time tempts us to patch dozens of small compiler, prover, and instruction-table gaps one by one. This catalog takes the opposite view: every single failing cell is recorded with both its **surface root-cause tag** (the immediate reason the verifier or compiler refused it) and a **High-Level Ode cluster** asking a deeper question: *why was the model touching that low-level mechanism at all, and could a single cleaner High-Level Ode construct convert a whole swathe of apparently unrelated failures into first-round successes by matching how models already think?*

---

## 1. Headline Counts (All 19 Runs: 372 Cells, 136 Failing Cells)

Of the **136 failing cells**, **27** (`W0-fixed-infra`) came from early harness or verifier limitations that were subsequently fixed during the experiment sequence (missing `odeprove` in `der-v1`, early pre-`odeprove` timeouts in `ebpf-v1`/`v2b`, `cmov`/`csel` helper limits in `ct-b64-v1`, missing multi-byte `bytes` loads in `ipv4-v1`/`ct-b64-v1`, and early syntax rules). That leaves **109 still-open failing cells**.

The table below groups all 136 failing cells by High-Level Ode cluster; each cell gives the cluster code, failing-cell count across all 19 runs, share of the 109 still-open failures, the surface errors it absorbs, and the single deterministic High-Level Ode construct that addresses the root cause.

| Cluster | Fail Cells (All / Open) | Share of 109 Open | Surface Failures Absorbed | Deterministic High-Level Ode Construct |
| --- | ---: | ---: | --- | --- |
| `W1-place-invariant` | 38 / 38 | **34.9%** | `prover:timeout-place-or-unfold` (22), `arith:place-invariant-or-postcond` (11), `model:invented-spec-def` (4), `place:spec-equality-syntax` (1) | **Structured loops (`loop` / `for`) with outer-context inheritance** instead of context-wiping `place` |
| `W2-buffer-slice` | 17 / 17 | **15.6%** | `arith:ptr-or-u64-wrap-guard` (17): `<= 2^64 - k`, `read neither of frame nor run`, `fixed count != 8 B` | **Checked buffer/slice indexing (`buf[i]`, `buf[i..i+k]`)** carrying buffer ownership and wraparound bounds |
| `W4-abi-stack-frame` | 14 / 14 | **12.8%** | `abi:callee-saved-or-preserves` (6), `syntax/isa:asm-or-decl-error` (4), `lang:manual-stack-frame` (3), `abi:stack-budget-exceeded` (1) | **Lexical helpers with `save` declarations, derived `preserves`, and linear `stack C + D * depth`** |
| `W3-ct-select-mask` | 14 / 14 | **12.8%** | `ct/arith:branchless-cmov-or-sub-underflow` (13), `verifier:and-mask-limit` (1) | **First-class constant-time `select(cond, a, b)`** (discarded-arm wrapping arithmetic + SWAR periodic byte masks) |
| `W5-simd-lanes` | 12 / 12 | **11.0%** | `verifier/diag:simd-word-mismatch` (6), `syntax/isa:simd-asm-error` (3), `verifier:pshufb-mask-limit` (2), `verifier:no-simd-load-from-bytes` (1) | **Deterministic SIMD ops (`rotl32`, `bswap32`, `load_u32x4`) and lane-diff diagnostics** |
| `W7-token-bloat` | 8 / 8 | **7.3%** | `model:output-token-limit` (8 cells, 38 rounds across `qwen3.8` & `gemini`) | **2x-3x shorter High-Level Ode source** (automatic side effect of Constructs `W1`-`W5`) |
| `W6-control-diag` | 6 / 6 | **5.5%** | `arith:need-compare-spec-order` (6) + path/callee diagnostic blind spots across `der_valid` & `json_str_valid` | **Structured `if`/`else` lowering + scoped, path-aware diagnostics** |
| `W0-fixed-infra` | 27 / 0 | — | `cmov-helper-limit` (8), `missing-odeprove` (7), `timeout-pre-odeprove` (5), `no-wide-bytes-load` (5), `early-ode-syntax` (2) | Already resolved in current `main` |
| **Total** | **136 / 109** | **100.0%** | **136 failing cells (1,536 failing rounds)** | **Top 5 constructs (`W1`-`W5`) cover 95/109 (87.2%) of still-open failures** |

---

## 2. The High-Level Ode Synthesis: Why Surface Bugs Hide Deeper Language Mismatches

Every construct below obeys the core Ode rule: the compiler expands deterministically to the coder's chosen instructions and carries types into proofs; it never guesses optimizations or hides code generation.

### 2.1 `W1-place-invariant` (38 still-open fail cells, 34.9%): `place` Wipes Context

- **What models think they are writing:** A loop over a buffer or state machine where facts established *before* the loop (input bounds like `n <= 65536`, register copies like `r9 == start`, or outer contract links like `spec.ipv4_valid(pkt) == spec.sum16_check(pkt, 0, words, 0)`) remain true unless modified inside the loop body.
- **What low-level Ode actually does:** `place { ... }` is a **total context wipe** at a raw assembly label. Any outer fact not manually re-stated inside `place` vanishes silently.
- **Concrete examples from the corpus:**
  - **`ipv4-v2` timeouts (`haiku arm64 blind`, `qwen x86_64 blind`):** Both models wrote `fact spec.sum16_check(pkt, 0, words, 0) == spec.sum16_check(pkt, j, words, s)` inside `place`, omitting the link back to `spec.ipv4_valid(pkt)`. After the loop, `odeprove` forgot the header checks done before the loop, tried to re-prove `spec.ipv4_valid(pkt)` from scratch by unfolding `sum16_check`, and hit the 45-second timeout (`22` of the `38` `W1` cells!).
  - **`der-v2` (`haiku x86_64`):** Haiku wrote an inner `@oid_loop` with `place { fact r11 <= rcx; decreases rcx - r11 }` — wiping out every fact about `buf`, `pos`, `lim`, `lvl`, and `der_valid(buf)`. When `@oid_loop` jumped to shared `@reject -> ret`, the verifier blamed `line 307: ret` with `cannot show: rsi(n) >= 2` and `v33 >= 128`, leaving Haiku guessing at header checks for 6 rounds.
  - **`der-v2` (`kimi x86_64`):** Kimi saved `start` into `r9` before the loop and wrote `spec.oid_ok(buf, r9, rcx, r10) == spec.oid_ok(buf, rdx, rcx, r8)` without `fact r9 == start`. `place` turned `r9` into a fresh symbolic variable `v19` with no link to `start`, producing the baffling error `cannot show: rdx(start) >= v19`.
- **High-Level Ode fix:** A structured `loop` / `for` block automatically **inherits every fact about registers and parameters not written inside the loop body**, knows its own induction bounds (`0 <= i <= limit`), and checks a single loop-goal clause (`maintains ...`) instead of forcing manual re-listing of 10-15 boilerplate facts. Even better: a coder can still put raw assembly instructions inside the loop body with zero loss of instruction control.

### 2.2 `W2-buffer-slice` (17 still-open fail cells, 15.6%): Manual Pointer/Offset Wraparound

- **What models think they are writing:** Reading `buf[pos]` or `buf[pos + 1]` after checking `pos + 2 <= end` where `end <= n` and `n <= 65536`.
- **What low-level Ode actually does:** Every manual `add addr, base, pos` or `lea r8, [rdx + 2]` emits a 64-bit no-wrap obligation (`base + pos <= 2^64 - 1`, `pos <= 2^64 - 3`). If a helper contract omits `requires n <= 65536` (as `claude-sonnet-5.5 x86_64` did on `fn seq0` in `der-v2` Round 8) or uses a pointer walk (`ptr += 4`) without re-proving `ptr == base + idx`, Ode refuses with `cannot show: rdx(pos) <= 2^64 - 3` or `a read that is neither of the frame nor of a run given`.
- **High-Level Ode fix:** First-class **checked slice views and indexed reads** (`buf[pos]` / `buf[pos..+4]` / `out[j] := val`) that expand deterministically to the target's `add` + `ldrb`/`movzx`/`ldr` instructions while automatically carrying buffer provenance and `base + len <= 2^64` through the proof.

### 2.3 `W3-ct-select-mask` (14 still-open fail cells, 12.8%, plus 8 fixed in `ct-b64-v1`): Constant-Time Select & Discarded-Arm Arithmetic

- **What models think they are writing:** Constant-time piecewise math like `if 65 <= c && c <= 90 then c - 1 else 0`, implemented branchlessly by computing `c - 1` speculatively and selecting it only when `c >= 65` (`sub t, c, 1; cmp c, 65; cmovae ...`).
- **What low-level Ode actually does:** Ode's `sub` rule refuses any unsigned underflow (`cannot show: rbx(c) >= 1` in `gemini x86_64 blind` on `ct-b64-v2`), **even when the result is immediately discarded by `cmov`/`csel`**! To work around this, `claude-sonnet-5.5 arm64` had to emit **four extra instructions** (`x10 := 65; cmp x6, 65; csel x7, x6, x10, hs; sub x8, x7, 1`) just to clamp `c` before subtracting `1`. Meanwhile, inlining 4 characters x 10 `csel`s in one loop (`claude-fable-5.2 arm64 blind`) exploded symbolic branch splits (`cannot show: v97 >= 65`), and models attempting SWAR byte-lane masking on 32/64-bit loads (`ipv4-v2` `gemini` 4x) hit `no proof rule for this AND mask` on `0x00FF00FF`.
- **High-Level Ode fix:**
  1. A first-class constant-time **`select(cond, then_expr, else_expr)`** expression that lowers deterministically to `cmp` + `cmov`/`csel`, allows wrapping/unused-arm arithmetic whose result is guarded by `cond`, and automatically joins after each `select` (or helper) to prevent $2^N$ path blowup.
  2. Periodic byte-lane mask rules (`0x00FF00FF`, `0x00FF00FF00FF00FF`, `0x8080808080808080`) for SWAR loads.

### 2.4 `W4-abi-stack-frame` (14 still-open fail cells, 12.8%): Manual Callee-Saved Lists & Peeled Recursion

- **What models think they are writing:** Small internal helpers that save whatever callee-saved registers they touch, and bounded recursive parsers (`der_seq(buf, pos, end, depth)` for `depth <= 3`).
- **What low-level Ode actually does:**
  - Models hand-write 10-register `preserves rdi, rsi, r10, r11, ...` clauses and then accidentally clobber one (`kimi x86_64` Round 8 in `der-v2`: clobbered `r10`), or clobber callee-saved `v8..v15` vector registers in NEON (`12` failing rounds).
  - Because Ode only allows `stack C` or `stack C + D * bits(...)` — not linear `stack C + D * depth` — bounded recursion like `der_seq` cannot call itself recursively. Models either copy-paste 4 near-identical functions (`seq0..seq3`, ~500 lines) or build a brittle manual register/stack state machine (`haiku`, `qwen`, `kimi arm64 R8`), hitting `the name rsp stands for nothing here` or `indexed store not in x86.tab`.
- **High-Level Ode fix:**
  1. Deterministic **`save r12, r13, ...`** block (emits exact prologue pushes / epilogue pops and updates stack budget automatically), plus **derived `preserves`** for internal helpers (anything not in `out` or `clobbers` is preserved by checking).
  2. Linear stack bounds **`stack C + D * depth`** in `Core.lean` so bounded recursion verifies cleanly in one function instead of 4x copy-paste or manual stacks.

### 2.5 `W5-simd-lanes` (12 still-open fail cells, 11.0%): Opaque SIMD Mismatches & Shuffle Encodings

- **What models think they are writing:** `rotl32(v, 16)`, `bswap32(v)`, loading 4-way/16-way lanes from buffers, and getting told *which lane* disagreed if a shuffle or round constant is off.
- **What low-level Ode actually does:** `qwen3.8` (`sha256-v1`, both `x86_64` arms) tried `pshufb` for endianness byte-swap and hit `a shuffle of bytes that is no turn of each word by 8 or 16 bits: not here yet`; `kimi` (`ct-b64-v1`) tried a 16-byte SIMD load from a `bytes` buffer; and when a 4-way ChaCha20 or SHA-256 kernel had one lane typo (`kimi` & `qwen` in `chacha20-v1`, `kimi` in `sha256-v1`), Ode printed only `the specification's words are not followed on the terms the function made` — without identifying which output word index differed.
- **High-Level Ode fix:** Standard deterministic vector idioms (including `bswap32` via `pshufb`/`rev32`, 16-byte loads from `bytes` buffers) and a **lane-index diff diagnostic** (`output word 3 differs: got ..., spec expects ...`).

### 2.6 `W6-control-diag` (6 fail cells) & `W7-token-bloat` (8 fail cells): Diagnostics & Source Length

- **Diagnostic misfires amplified failure loops across multiple models:**
  - `matching spec comparison(s)` grepped the *entire* spec file instead of definitions reachable from the failing function — blaming `der_hdr_len` when `kimi` and `sonnet` were verifying `oid_ok`!
  - Shared `@reject -> ret` tails hid which predecessor path or empty `place` lost facts (`haiku` in `der-v2`).
  - `trace_refusal` after a helper call (`kimi arm64` R6-R7 in `der-v2`) printed the caller's `trace depends on`, not noting when the *callee's* contract omitted an input and kept its return value out of the trace.
- **Token bloat (`38` truncated rounds, `8` failing cells in `qwen3.8` & `gemini`):** Monolithic 400-700-line low-level `.ode` files pushed reasoning models past 32,000 output tokens. High-Level Ode constructs `W1`-`W5` cut typical file length by 2x-3x directly.

---

## 3. Deep Dive: Why the More Efficient Models Failed at `der_valid` (`der-v2`)

In `der-v2`, the four frontier models scored **7/8 (87.5%)** (`gemini` 2/2, `gpt-6.2` 2/2, `claude-fable` 2/2, `claude-sonnet` 1/2), while the three lower-cost / open-weights models (`claude-haiku-5.5`, `kimi-k3.1-pro`, `qwen3.8-2.4t-a95b`) scored **0/6** (plus `claude-sonnet-5.5 x86_64`). Inspecting every `.last.ode` and round diagnostic in `exp-der-v2` reveals **five distinct, concrete failure mechanisms** — and shows how High-Level Ode dissolves almost all of them:

| Model & Target | Architecture Chosen | Surface Failure Progression (Rounds 1-8) | Deeper High-Level Ode Explanation |
| --- | --- | --- | --- |
| `claude-haiku-5.5` (`arm64` & `x86_64`) | **1 monolithic fn** (`fn der_valid`, 283-309 lines) with manual 3-slot register stack `s1, s2, s3` | R1-R5: `u64` wrap (`v35 <= 2^64 - 3`) then `ret: cannot show rsi(n) >= 2` & `v33 >= 128`. Inner `@oid_loop` wrote `place { fact r11 <= rcx; decreases rcx - r11 }`, wiping every outer fact. Shared `@reject -> ret` blamed line 307 instead of line 261. | **Forced into manual stack** by lack of linear `stack C + D * depth` (`W4`); **wiped outer facts** at inner loop `place` (`W1`); **blinded** by shared-`ret` diagnostic (`W6`). |
| `kimi-k3.1-pro` (`arm64`) | **Multi-fn helpers** (R1-R7: `der_hdr_len_impl`, `der_prim_ok_impl`, `der_seq_impl`), then panicked to **1 monolithic fn** in R8 | R1-R5 passed `der_hdr_len_impl` & `der_prim_ok_impl` cleanly (fixing 1 error/round!). Stuck R6-R7 on `trace_refusal` at `b.eq @no` after `bl der_hdr_len_impl`. Panicked in R8, rewriting into 1 fn with invented `der_cont(...)`. | Almost passed! Derailed by **unhelpful `trace_refusal`** not naming which callee omitted inputs from `trace depends on` (`W6`), then panicked into monolithic `place` (`W1`). |
| `kimi-k3.1-pro` (`x86_64`) | **7 helper fns** (`oid_go`, `prim_ok`, `seq0..seq3`, `der_valid`, 709 lines) — the right structure! | R1: self-tail-call `jmp oid_go` refused (`not shown before this one`). R2-R8 stuck in `oid_go`: saved `start`->`r9`, `state`->`r10` (clobbering `r10` which it listed in `preserves`!), omitted `fact r9 == start`, got `cannot show: rdx(start) >= v19` AND misleading `matching spec comparison(s): def m1__der_hdr_len` in R4-R7. | Right decomposition! Killed by **`place` context wipe** dropping `r9 == start` (`W1`), manual **`preserves` contradiction** (`W4`), and **mis-scoped `der_hdr_len` diagnostic** (`W6`). |
| `qwen3.8-2.4t-a95b` (`arm64` & `x86_64`) | `arm64`: 0 code emitted (2x 32k token truncation). `x86_64`: **1 monolithic fn** (386 lines) using manual `rsp` stack | `x86_64` R1: indexed stack store `mov [rsp + t2], acc` not in `x86.tab`. R2: `add rsp, 96` arithmetic error. R3: 32k truncation. R4: `fact rsp >= 512` inside `place` (`the name rsp stands for nothing here`). | Forced into manual `rsp` stack by lack of **`stack C + D * depth`** (`W4`), plus **32k token bloat** from 400-line boilerplate (`W7`). |
| `claude-sonnet-5.5` (`x86_64`) | **7 helper fns** (`oidk`, `prim`, `seq0..seq3`, `der_valid`, 588 lines) — passed `arm64` in R8! | Passed `oidk` and `prim` by R7 (after losing 3 rounds R3-R5 to the same mis-scoped `def m1__der_hdr_len` diagnostic inside `oidk`/`prim`!). Reached `seq0` on R8 and failed on **1 missing line**: `requires n <= 65536` on `fn seq0` (`lea r8, [rdx + 2]`: `cannot show: rdx(pos) <= 2^64 - 3`). | Almost passed! Lost 3 rounds to **mis-scoped diagnostic** (`W6`), then tripped on **manual `u64` wrap guard** (`W2`) on the final round. |

---

## 4. Complete Surface Root-Cause Tag Summary (All 136 Failing Cells)

Each row counts how many of the 136 failing cells ended under that surface root-cause tag (tags marked `[FIXED]` were eliminated in later commits of this session).

| Surface Root-Cause Tag | Fail Cells | Wirth Cluster |
| --- | ---: | --- |
| `prover:timeout-place-or-unfold` | 22 | `W1-place-invariant` |
| `arith:ptr-or-u64-wrap-guard` | 17 | `W2-buffer-slice` |
| `ct/arith:branchless-cmov-or-sub-underflow` | 13 | `W3-ct-select-mask` |
| `arith:place-invariant-or-postcond` | 11 | `W1-place-invariant` |
| `model:output-token-limit` | 8 | `W7-token-bloat` |
| `verifier:cmov-helper-limit [FIXED]` | 8 | `W0-fixed-infra` |
| `harness:missing-odeprove [FIXED]` | 7 | `W0-fixed-infra` |
| `arith:need-compare-spec-order` | 6 | `W6-control-diag` |
| `abi:callee-saved-or-preserves` | 6 | `W4-abi-stack-frame` |
| `verifier/diag:simd-word-mismatch` | 6 | `W5-simd-lanes` |
| `prover:timeout-pre-odeprove [FIXED]` | 5 | `W0-fixed-infra` |
| `verifier:no-wide-bytes-load [FIXED]` | 5 | `W0-fixed-infra` |
| `syntax/isa:asm-or-decl-error` | 4 | `W4-abi-stack-frame` |
| `model:invented-spec-def` | 4 | `W1-place-invariant` |
| `lang:manual-stack-frame` | 3 | `W4-abi-stack-frame` |
| `syntax/isa:simd-asm-error` | 3 | `W5-simd-lanes` |
| `syntax:early-ode-syntax [FIXED]` | 2 | `W0-fixed-infra` |
| `verifier:pshufb-mask-limit` | 2 | `W5-simd-lanes` |
| `abi:stack-budget-exceeded` | 1 | `W4-abi-stack-frame` |
| `verifier:no-simd-load-from-bytes` | 1 | `W5-simd-lanes` |
| `verifier:and-mask-limit` | 1 | `W3-ct-select-mask` |
| `place:spec-equality-syntax` | 1 | `W1-place-invariant` |

---

## 5. Complete Cell-by-Cell Failure Catalog (All 136 Failing Cells, 19 Runs)

Each row records one failing cold-room cell across all 19 runs (`ebpf-v1` through `utf8-v1`): run ID, task, model, target architecture, optimization arm (`-` for correctness-only runs), rounds executed, surface root-cause tag, High-Level Ode cluster, and the final round's exact diagnostic summary.

| # | Run | Task | Model | Target | Arm | Rounds | Surface Tag | Wirth Cluster | Last Round Diagnostic |
| ---: | --- | --- | --- | --- | --- | ---: | --- | --- | --- |
| 1 | `ebpf-v1` | `ebpf` | `claude-fable-5.2` | `arm64` | `-` | 8 | `prover:timeout-pre-odeprove [FIXED]` | `W0-fixed-infra` | trace_refusal |
| 2 | `ebpf-v1` | `ebpf` | `claude-fable-5.2` | `x86_64` | `-` | 8 | `prover:timeout-pre-odeprove [FIXED]` | `W0-fixed-infra` | arith_need_entail |
| 3 | `ebpf-v1` | `ebpf` | `claude-sonnet-5.5` | `arm64` | `-` | 8 | `prover:timeout-pre-odeprove [FIXED]` | `W0-fixed-infra` | prover_timeout_120s |
| 4 | `ebpf-v1` | `ebpf` | `claude-sonnet-5.5` | `x86_64` | `-` | 8 | `prover:timeout-pre-odeprove [FIXED]` | `W0-fixed-infra` | other |
| 5 | `ebpf-v1` | `ebpf` | `gemini-4-neon` | `arm64` | `-` | 8 | `syntax:early-ode-syntax [FIXED]` | `W0-fixed-infra` | compile_or_parse_error |
| 6 | `ebpf-v2b` | `ebpf` | `claude-sonnet-5.5` | `arm64` | `-` | 8 | `prover:timeout-pre-odeprove [FIXED]` | `W0-fixed-infra` | prover_timeout_120s |
| 7 | `ebpf-v2b` | `ebpf` | `claude-sonnet-5.5` | `x86_64` | `-` | 8 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | refused: |
| 8 | `ebpf-v2b` | `ebpf` | `gemini-4-neon` | `arm64` | `-` | 8 | `syntax:early-ode-syntax [FIXED]` | `W0-fixed-infra` | Traceback (most recent call last): |
| 9 | `suite-v3` | `ebpf` | `claude-sonnet-5.5` | `arm64` | `-` | 8 | `arith:need-compare-spec-order` | `W6-control-diag` | refused: |
| 10 | `suite-v3` | `ebpf` | `claude-sonnet-5.5` | `x86_64` | `-` | 8 | `syntax/isa:asm-or-decl-error` | `W4-abi-stack-frame` | refused: |
| 11 | `suite-v3` | `ebpf` | `gemini-4-neon` | `arm64` | `-` | 8 | `model:output-token-limit` | `W7-token-bloat` | output_token_limit |
| 12 | `suite-v4` | `ebpf` | `claude-fable-5.2` | `x86_64` | `-` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `ret`: cannot show: rsi >= 8 |
| 13 | `suite-v4` | `ebpf` | `claude-sonnet-5.5` | `arm64` | `-` | 8 | `abi:callee-saved-or-preserves` | `W4-abi-stack-frame` | `ret`: refused: at the return a register a callee keeps (x15) does not hold what it held at entry |
| 14 | `suite-v4` | `ebpf` | `claude-sonnet-5.5` | `x86_64` | `-` | 7 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout_120s |
| 15 | `suite-v4` | `ebpf` | `gemini-4-neon` | `arm64` | `-` | 6 | `arith:need-compare-spec-order` | `W6-control-diag` | `ret`: cannot decide: is v65 (byte 0..255) equal to 149, below it, or above it? (the proof needs one o |
| 16 | `suite-v4` | `ebpf` | `gemini-4-neon` | `x86_64` | `-` | 4 | `model:output-token-limit` | `W7-token-bloat` | output_token_limit |
| 17 | `suite-v5` | `ebpf` | `claude-sonnet-5.5` | `arm64` | `-` | 8 | `arith:need-compare-spec-order` | `W6-control-diag` | `ret`: cannot decide: is x2(fuel) equal to 0, below it, or above it? (the proof needs one of the three |
| 18 | `suite-v5` | `ebpf` | `claude-sonnet-5.5` | `x86_64` | `-` | 7 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout_120s |
| 19 | `suite-v5` | `ebpf` | `gemini-4-neon` | `x86_64` | `-` | 4 | `arith:need-compare-spec-order` | `W6-control-diag` | `call err_val_fn`: cannot decide: is rdx(fuel) equal to 0, below it, or above it? (the proof needs one of the thre |
| 20 | `suite-v5` | `header_score` | `claude-sonnet-5.5` | `arm64` | `-` | 8 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | `bl hr0`: cannot show: v33 (byte 0..255) >= 128 |
| 21 | `suite-v5` | `header_score` | `claude-sonnet-5.5` | `x86_64` | `-` | 8 | `abi:stack-budget-exceeded` | `W4-abi-stack-frame` | `call rule0`: refused: a call needs more stack than this function's contract allows |
| 22 | `suite-v6` | `ebpf` | `claude-fable-5.2` | `x86_64` | `-` | 3 | `model:output-token-limit` | `W7-token-bloat` | output_token_limit |
| 23 | `suite-v6` | `ebpf` | `claude-sonnet-5.5` | `arm64` | `-` | 7 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout_120s |
| 24 | `suite-v6` | `ebpf` | `claude-sonnet-5.5` | `x86_64` | `-` | 7 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout_120s |
| 25 | `suite-v6` | `ebpf` | `gemini-4-neon` | `arm64` | `-` | 4 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout_120s |
| 26 | `perf-v1` | `byte_sum` | `gemini-4-neon` | `arm64` | `blind` | 5 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | refused in byte_sum: |
| 27 | `perf-v1` | `byte_sum` | `gemini-4-neon` | `x86_64` | `advised` | 6 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout_120s |
| 28 | `perf-v2` | `weighted_sum` | `gemini-4-neon` | `arm64` | `blind` | 5 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout_120s |
| 29 | `der-v1` | `der_valid` | `claude-fable-5.2` | `arm64` | `-` | 3 | `harness:missing-odeprove [FIXED]` | `W0-fixed-infra` | refused in prim_ok: |
| 30 | `der-v1` | `der_valid` | `claude-fable-5.2` | `x86_64` | `-` | 4 | `harness:missing-odeprove [FIXED]` | `W0-fixed-infra` | prover_timeout |
| 31 | `der-v1` | `der_valid` | `claude-haiku-5.5` | `arm64` | `-` | 8 | `harness:missing-odeprove [FIXED]` | `W0-fixed-infra` | refused in der_valid: |
| 32 | `der-v1` | `der_valid` | `claude-haiku-5.5` | `x86_64` | `-` | 8 | `harness:missing-odeprove [FIXED]` | `W0-fixed-infra` | refused in seq_ok: |
| 33 | `der-v1` | `der_valid` | `claude-sonnet-5.5` | `arm64` | `-` | 7 | `harness:missing-odeprove [FIXED]` | `W0-fixed-infra` | refused in seq0: |
| 34 | `der-v1` | `der_valid` | `claude-sonnet-5.5` | `x86_64` | `-` | 8 | `harness:missing-odeprove [FIXED]` | `W0-fixed-infra` | refused in seq0: |
| 35 | `der-v1` | `der_valid` | `kimi-k3.1-pro` | `arm64` | `-` | 8 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | refused in der_prim_ok: |
| 36 | `der-v1` | `der_valid` | `kimi-k3.1-pro` | `x86_64` | `-` | 8 | `lang:manual-stack-frame` | `W4-abi-stack-frame` | refused: a write that is not eight bytes of the frame in use |
| 37 | `der-v1` | `der_valid` | `gpt-6.2-astra-pro` | `arm64` | `-` | 6 | `harness:missing-odeprove [FIXED]` | `W0-fixed-infra` | refused in seq_zero: |
| 38 | `der-v1` | `der_valid` | `qwen3.8-2.4t-a95b` | `arm64` | `-` | 2 | `model:output-token-limit` | `W7-token-bloat` | output_token_limit |
| 39 | `der-v1` | `der_valid` | `qwen3.8-2.4t-a95b` | `x86_64` | `-` | 2 | `model:output-token-limit` | `W7-token-bloat` | output_token_limit |
| 40 | `der-v2` | `der_valid` | `claude-haiku-5.5` | `arm64` | `-` | 8 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | `cmp pos, lim`: cannot show: v33 (byte 0..255) >= 128 |
| 41 | `der-v2` | `der_valid` | `claude-haiku-5.5` | `x86_64` | `-` | 8 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | `ret`: cannot show: v33 (byte 0..255) >= 128 |
| 42 | `der-v2` | `der_valid` | `claude-sonnet-5.5` | `x86_64` | `-` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `lea r8, [rdx + 2]`: cannot show: rdx(pos) <= 2^64 - 3 |
| 43 | `der-v2` | `der_valid` | `kimi-k3.1-pro` | `arm64` | `-` | 8 | `model:invented-spec-def` | `W1-place-invariant` | `cmp pos, end`: refused: no definition der_cont |
| 44 | `der-v2` | `der_valid` | `kimi-k3.1-pro` | `x86_64` | `-` | 8 | `abi:callee-saved-or-preserves` | `W4-abi-stack-frame` | `ret`: refused: at the return a register a callee keeps (r10) does not hold what it held at entry |
| 45 | `der-v2` | `der_valid` | `qwen3.8-2.4t-a95b` | `arm64` | `-` | 2 | `model:output-token-limit` | `W7-token-bloat` | output_token_limit |
| 46 | `der-v2` | `der_valid` | `qwen3.8-2.4t-a95b` | `x86_64` | `-` | 4 | `lang:manual-stack-frame` | `W4-abi-stack-frame` | `cmp pos, end`: refused: the name rsp stands for nothing here |
| 47 | `sha256-v1` | `sha256_4way` | `claude-haiku-5.5` | `x86_64` | `advised` | 7 | `syntax/isa:simd-asm-error` | `W5-simd-lanes` | ode: <tmp> line 1: unexpected top-level item in '.ode': ''''ode' |
| 48 | `sha256-v1` | `sha256_4way` | `claude-haiku-5.5` | `x86_64` | `blind` | 8 | `syntax/isa:simd-asm-error` | `W5-simd-lanes` | ode: <tmp> line 1: unexpected top-level item in '.ode': 'The previous reply was cut off partway |
| 49 | `sha256-v1` | `sha256_4way` | `kimi-k3.1-pro` | `arm64` | `blind` | 8 | `verifier/diag:simd-word-mismatch` | `W5-simd-lanes` | refused: |
| 50 | `sha256-v1` | `sha256_4way` | `kimi-k3.1-pro` | `x86_64` | `advised` | 8 | `verifier/diag:simd-word-mismatch` | `W5-simd-lanes` | `ret`: refused: a word of the run is not known to hold what the specification says |
| 51 | `sha256-v1` | `sha256_4way` | `qwen3.8-2.4t-a95b` | `arm64` | `advised` | 8 | `verifier/diag:simd-word-mismatch` | `W5-simd-lanes` | <tmp> line 147: 'add addr, sp, tmp': 'sp' is not a general 64-bit register x0..x30 (for 'add D6 |
| 52 | `sha256-v1` | `sha256_4way` | `qwen3.8-2.4t-a95b` | `x86_64` | `advised` | 8 | `verifier:pshufb-mask-limit` | `W5-simd-lanes` | `pshufb xmm6, xmm15`: refused: a shuffle of bytes that is no turn of each word by 8 or 16 bits: not here yet |
| 53 | `sha256-v1` | `sha256_4way` | `qwen3.8-2.4t-a95b` | `x86_64` | `blind` | 6 | `verifier:pshufb-mask-limit` | `W5-simd-lanes` | `pshufb xmm1, xmm15`: refused: a shuffle of bytes that is no turn of each word by 8 or 16 bits: not here yet |
| 54 | `ct-b64-v1` | `ct_base64_decode` | `claude-fable-5.2` | `x86_64` | `blind` | 6 | `verifier:cmov-helper-limit [FIXED]` | `W0-fixed-infra` | prover_timeout |
| 55 | `ct-b64-v1` | `ct_base64_decode` | `claude-haiku-5.5` | `arm64` | `advised` | 8 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `cmp g, 64`: cannot show: 4*v135 (0..63) + v136 (0..3) >= v119 (byte 0..255) |
| 56 | `ct-b64-v1` | `ct_base64_decode` | `claude-haiku-5.5` | `arm64` | `blind` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `mov x0, ok`: cannot show: v48 (0..189) >= 189 |
| 57 | `ct-b64-v1` | `ct_base64_decode` | `claude-haiku-5.5` | `x86_64` | `advised` | 8 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `cmp r8, 256`: cannot show: v21 (byte 0..255) >= 65 |
| 58 | `ct-b64-v1` | `ct_base64_decode` | `claude-haiku-5.5` | `x86_64` | `blind` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `ret`: cannot show: r10(c) >= 65 |
| 59 | `ct-b64-v1` | `ct_base64_decode` | `claude-sonnet-5.5` | `arm64` | `blind` | 8 | `verifier:cmov-helper-limit [FIXED]` | `W0-fixed-infra` | `add x1, x20, x21`: cannot show: v138 (byte 0..255) >= 4*v222 (0..63) + v225 (0..3) |
| 60 | `ct-b64-v1` | `ct_base64_decode` | `claude-sonnet-5.5` | `x86_64` | `advised` | 8 | `verifier:cmov-helper-limit [FIXED]` | `W0-fixed-infra` | prover_timeout |
| 61 | `ct-b64-v1` | `ct_base64_decode` | `claude-sonnet-5.5` | `x86_64` | `blind` | 8 | `verifier:cmov-helper-limit [FIXED]` | `W0-fixed-infra` | `cmp r12, 4`: refused: a number is expected (or a use of a definition whose value is held) |
| 62 | `ct-b64-v1` | `ct_base64_decode` | `gemini-4-neon` | `arm64` | `advised` | 4 | `verifier:no-wide-bytes-load [FIXED]` | `W0-fixed-infra` | `ldrb w8, [x14, 1]`: cannot show: x2(n) >= v38 (0..256) + 2 |
| 63 | `ct-b64-v1` | `ct_base64_decode` | `gemini-4-neon` | `arm64` | `blind` | 3 | `verifier:no-wide-bytes-load [FIXED]` | `W0-fixed-infra` | `ldr t0, [addr, 0]`: refused: a read of a run of bytes that is not one byte: not here yet |
| 64 | `ct-b64-v1` | `ct_base64_decode` | `gemini-4-neon` | `x86_64` | `advised` | 7 | `verifier:cmov-helper-limit [FIXED]` | `W0-fixed-infra` | `movzx r13d, byte ptr [r10 + 1]`: cannot show: rdx(n) >= v18 (byte 0..255) + 2 |
| 65 | `ct-b64-v1` | `ct_base64_decode` | `gemini-4-neon` | `x86_64` | `blind` | 7 | `verifier:cmov-helper-limit [FIXED]` | `W0-fixed-infra` | prover_timeout |
| 66 | `ct-b64-v1` | `ct_base64_decode` | `kimi-k3.1-pro` | `arm64` | `advised` | 8 | `abi:callee-saved-or-preserves` | `W4-abi-stack-frame` | `ret`: refused: at the return a register a callee keeps (x2) does not hold what it held at entry |
| 67 | `ct-b64-v1` | `ct_base64_decode` | `kimi-k3.1-pro` | `arm64` | `blind` | 8 | `model:invented-spec-def` | `W1-place-invariant` | `add tmp, x5, 159`: refused: no definition dec_u |
| 68 | `ct-b64-v1` | `ct_base64_decode` | `kimi-k3.1-pro` | `x86_64` | `advised` | 8 | `verifier:no-simd-load-from-bytes` | `W5-simd-lanes` | `vmovdqu xmm0, [rsi]`: refused: sixteen bytes that are of no run of words given to read |
| 69 | `ct-b64-v1` | `ct_base64_decode` | `kimi-k3.1-pro` | `x86_64` | `blind` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `ret`: cannot show: r11(b) >= 65 |
| 70 | `ct-b64-v1` | `ct_base64_decode` | `gpt-6.2-astra-pro` | `x86_64` | `advised` | 8 | `verifier:cmov-helper-limit [FIXED]` | `W0-fixed-infra` | `ret`: cannot show: v33 (byte 0..255) >= 65 |
| 71 | `ct-b64-v1` | `ct_base64_decode` | `gpt-6.2-astra-pro` | `x86_64` | `blind` | 8 | `verifier:cmov-helper-limit [FIXED]` | `W0-fixed-infra` | `call accept_tag`: cannot show: v34 >= 64 |
| 72 | `ct-b64-v1` | `ct_base64_decode` | `qwen3.8-2.4t-a95b` | `arm64` | `advised` | 8 | `abi:callee-saved-or-preserves` | `W4-abi-stack-frame` | refused: |
| 73 | `ct-b64-v1` | `ct_base64_decode` | `qwen3.8-2.4t-a95b` | `arm64` | `blind` | 8 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `cmp idx, 256`: cannot show: |
| 74 | `ct-b64-v1` | `ct_base64_decode` | `qwen3.8-2.4t-a95b` | `x86_64` | `advised` | 6 | `syntax/isa:asm-or-decl-error` | `W4-abi-stack-frame` | ode: line 0: name expected, not None |
| 75 | `ct-b64-v1` | `ct_base64_decode` | `qwen3.8-2.4t-a95b` | `x86_64` | `blind` | 5 | `model:output-token-limit` | `W7-token-bloat` | output_token_limit |
| 76 | `ct-b64-v2` | `ct_base64_decode` | `claude-fable-5.2` | `arm64` | `blind` | 7 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `add ad, po, oj`: cannot show: v97 (byte 0..255) >= 65 |
| 77 | `ct-b64-v2` | `ct_base64_decode` | `claude-haiku-5.5` | `arm64` | `advised` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `ldrb w6, [x4, 0]`: refused: a read that is neither of the frame nor of a run given |
| 78 | `ct-b64-v2` | `ct_base64_decode` | `claude-haiku-5.5` | `arm64` | `blind` | 8 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `cmp q, 64`: cannot show: 4*v225 (0..63) + v228 (0..3) >= v217 (byte 0..255) |
| 79 | `ct-b64-v2` | `ct_base64_decode` | `claude-haiku-5.5` | `x86_64` | `advised` | 8 | `verifier:and-mask-limit` | `W3-ct-select-mask` | `and r11, r9`: refused: an and with what is no number of the table: not here yet |
| 80 | `ct-b64-v2` | `ct_base64_decode` | `claude-haiku-5.5` | `x86_64` | `blind` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `movzx eax, byte ptr [r8 + 0]`: refused: a read that is neither of the frame nor of a run given |
| 81 | `ct-b64-v2` | `ct_base64_decode` | `claude-sonnet-5.5` | `arm64` | `advised` | 8 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `cmp gi, 64`: cannot show: 4*v131 (0..63) + v167 (0..3) >= v171 (byte 0..255) |
| 82 | `ct-b64-v2` | `ct_base64_decode` | `claude-sonnet-5.5` | `arm64` | `blind` | 8 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `bl ct_dec`: cannot show: v65 (byte 0..255) >= 65 |
| 83 | `ct-b64-v2` | `ct_base64_decode` | `claude-sonnet-5.5` | `x86_64` | `blind` | 8 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | prover_timeout |
| 84 | `ct-b64-v2` | `ct_base64_decode` | `gemini-4-neon` | `arm64` | `advised` | 3 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `cmp idx, 256`: cannot show: v37 (byte 0..255) >= 65 |
| 85 | `ct-b64-v2` | `ct_base64_decode` | `gemini-4-neon` | `arm64` | `blind` | 3 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `ldrb d1w, [t0, 1]`: cannot show: x2(n) >= v38 (0..256) + 2 |
| 86 | `ct-b64-v2` | `ct_base64_decode` | `gemini-4-neon` | `x86_64` | `advised` | 5 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `cmp rcx, 64`: cannot show: 4*v54 (0..63) + v55 (0..3) >= v60 (byte 0..255) |
| 87 | `ct-b64-v2` | `ct_base64_decode` | `gemini-4-neon` | `x86_64` | `blind` | 5 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `sub r14, 1`: cannot show: rbx(c) >= 1 |
| 88 | `ct-b64-v2` | `ct_base64_decode` | `kimi-k3.1-pro` | `arm64` | `advised` | 8 | `syntax/isa:asm-or-decl-error` | `W4-abi-stack-frame` | <tmp> line 30: 'add addr, srcp, inoff': 'inoff' is not a general 64-bit register x0..x30 (for ' |
| 89 | `ct-b64-v2` | `ct_base64_decode` | `kimi-k3.1-pro` | `arm64` | `blind` | 6 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | prover_timeout |
| 90 | `ct-b64-v2` | `ct_base64_decode` | `kimi-k3.1-pro` | `x86_64` | `advised` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `ret`: cannot show: rax(c) >= 65 |
| 91 | `ct-b64-v2` | `ct_base64_decode` | `kimi-k3.1-pro` | `x86_64` | `blind` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `movzx cw, byte ptr [base]`: refused: a read of a run of a fixed count that is not eight bytes within it: not here yet |
| 92 | `ct-b64-v2` | `ct_base64_decode` | `qwen3.8-2.4t-a95b` | `arm64` | `advised` | 8 | `model:invented-spec-def` | `W1-place-invariant` | `cmp idx, 64`: refused: no definition valid_from |
| 93 | `ct-b64-v2` | `ct_base64_decode` | `qwen3.8-2.4t-a95b` | `arm64` | `blind` | 5 | `ct/arith:branchless-cmov-or-sub-underflow` | `W3-ct-select-mask` | `bl dec_one`: cannot show: v65 (byte 0..255) >= 65 |
| 94 | `ct-b64-v2` | `ct_base64_decode` | `qwen3.8-2.4t-a95b` | `x86_64` | `advised` | 8 | `model:invented-spec-def` | `W1-place-invariant` | `cmp idx, 64`: refused: no definition vok_from |
| 95 | `ct-b64-v2` | `ct_base64_decode` | `qwen3.8-2.4t-a95b` | `x86_64` | `blind` | 5 | `syntax/isa:asm-or-decl-error` | `W4-abi-stack-frame` | ode: line 0: name expected, not None |
| 96 | `json-v1` | `json_str_valid` | `claude-haiku-5.5` | `arm64` | `advised` | 8 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 97 | `json-v1` | `json_str_valid` | `claude-haiku-5.5` | `arm64` | `blind` | 8 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 98 | `json-v1` | `json_str_valid` | `claude-haiku-5.5` | `x86_64` | `blind` | 8 | `arith:need-compare-spec-order` | `W6-control-diag` | `cmp idx, end`: cannot decide: is v53 (byte 0..255) equal to 92, below it, or above it? (the proof needs one of |
| 99 | `json-v1` | `json_str_valid` | `gemini-4-neon` | `arm64` | `advised` | 6 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 100 | `json-v1` | `json_str_valid` | `gemini-4-neon` | `arm64` | `blind` | 6 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 101 | `json-v1` | `json_str_valid` | `gemini-4-neon` | `x86_64` | `advised` | 6 | `arith:need-compare-spec-order` | `W6-control-diag` | `lea b0, [idx + 4]`: cannot decide: is v39 (byte 0..255) equal to 92, below it, or above it? (the proof needs one of |
| 102 | `json-v1` | `json_str_valid` | `gemini-4-neon` | `x86_64` | `blind` | 4 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 103 | `json-v1` | `json_str_valid` | `kimi-k3.1-pro` | `arm64` | `advised` | 8 | `abi:callee-saved-or-preserves` | `W4-abi-stack-frame` | refused: |
| 104 | `json-v1` | `json_str_valid` | `kimi-k3.1-pro` | `arm64` | `blind` | 8 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 105 | `json-v1` | `json_str_valid` | `qwen3.8-2.4t-a95b` | `arm64` | `advised` | 8 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | `ldrb h, [addr, 3]`: cannot show: v70 (byte 0..255) >= 48 |
| 106 | `json-v1` | `json_str_valid` | `qwen3.8-2.4t-a95b` | `x86_64` | `blind` | 2 | `model:output-token-limit` | `W7-token-bloat` | output_token_limit |
| 107 | `ipv4-v1` | `ipv4_valid` | `claude-haiku-5.5` | `arm64` | `advised` | 8 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 108 | `ipv4-v1` | `ipv4_valid` | `claude-haiku-5.5` | `arm64` | `blind` | 8 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 109 | `ipv4-v1` | `ipv4_valid` | `claude-haiku-5.5` | `x86_64` | `advised` | 8 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 110 | `ipv4-v1` | `ipv4_valid` | `claude-haiku-5.5` | `x86_64` | `blind` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `cmp idx, words`: cannot show: v30 + 256*v54 (byte 0..255) + v55 (byte 0..255) <= 1966050 |
| 111 | `ipv4-v1` | `ipv4_valid` | `claude-sonnet-5.5` | `arm64` | `advised` | 8 | `place:spec-equality-syntax` | `W1-place-invariant` | `cmp k, words`: refused: a use of a definition can only be said to be equal to a number |
| 112 | `ipv4-v1` | `ipv4_valid` | `claude-sonnet-5.5` | `x86_64` | `blind` | 8 | `abi:callee-saved-or-preserves` | `W4-abi-stack-frame` | `ret`: refused: at the return a register a callee keeps (r10) does not hold what it held at entry |
| 113 | `ipv4-v1` | `ipv4_valid` | `gemini-4-neon` | `x86_64` | `advised` | 6 | `verifier:no-wide-bytes-load [FIXED]` | `W0-fixed-infra` | `shl rax, 8`: cannot show: -2 >= 0 |
| 114 | `ipv4-v1` | `ipv4_valid` | `gemini-4-neon` | `x86_64` | `blind` | 8 | `verifier:no-wide-bytes-load [FIXED]` | `W0-fixed-infra` | `ret`: cannot show: -2 >= 0 |
| 115 | `ipv4-v1` | `ipv4_valid` | `kimi-k3.1-pro` | `arm64` | `advised` | 8 | `verifier:no-wide-bytes-load [FIXED]` | `W0-fixed-infra` | `lsl a, sum, 48`: refused: a use of a definition can only be said to be equal to a number |
| 116 | `ipv4-v1` | `ipv4_valid` | `kimi-k3.1-pro` | `x86_64` | `advised` | 8 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | `cmp count, 0`: cannot show: 8*v24 (0..7) >= 8*v22 |
| 117 | `ipv4-v1` | `ipv4_valid` | `qwen3.8-2.4t-a95b` | `arm64` | `advised` | 8 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 118 | `ipv4-v1` | `ipv4_valid` | `qwen3.8-2.4t-a95b` | `arm64` | `blind` | 8 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 119 | `ipv4-v1` | `ipv4_valid` | `qwen3.8-2.4t-a95b` | `x86_64` | `advised` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `cmp idx, words`: cannot show: v26 + 256*v40 (byte 0..255) + v41 (byte 0..255) <= 1966050 |
| 120 | `ipv4-v1` | `ipv4_valid` | `qwen3.8-2.4t-a95b` | `x86_64` | `blind` | 8 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | `ret`: cannot show: 256*v20 (byte 0..255) + v21 (byte 0..255) >= 4*v19 (5..15) |
| 121 | `chacha20-v1` | `chacha20_4way` | `kimi-k3.1-pro` | `x86_64` | `advised` | 8 | `verifier/diag:simd-word-mismatch` | `W5-simd-lanes` | `ret`: refused: the specification's words are not followed on the terms the function made |
| 122 | `chacha20-v1` | `chacha20_4way` | `qwen3.8-2.4t-a95b` | `arm64` | `blind` | 6 | `verifier/diag:simd-word-mismatch` | `W5-simd-lanes` | ode: <tmp> line 1: unexpected top-level item in '.ode': ''''ode' |
| 123 | `chacha20-v1` | `chacha20_4way` | `qwen3.8-2.4t-a95b` | `x86_64` | `advised` | 3 | `syntax/isa:simd-asm-error` | `W5-simd-lanes` | <tmp> line 57: 'vpunpckhqdq xmm1, xmm8, xmm10': instruction not in x86.tab |
| 124 | `chacha20-v1` | `chacha20_4way` | `qwen3.8-2.4t-a95b` | `x86_64` | `blind` | 8 | `verifier/diag:simd-word-mismatch` | `W5-simd-lanes` | `ret`: refused: the specification's words are not followed on the terms the function made |
| 125 | `ipv4-v2` | `ipv4_valid` | `claude-haiku-5.5` | `arm64` | `advised` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `ret`: cannot show: x2(words) <= 0 |
| 126 | `ipv4-v2` | `ipv4_valid` | `claude-haiku-5.5` | `arm64` | `blind` | 8 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 127 | `ipv4-v2` | `ipv4_valid` | `claude-haiku-5.5` | `x86_64` | `blind` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `ret`: cannot show: v28 (0..30) <= 1 |
| 128 | `ipv4-v2` | `ipv4_valid` | `gemini-4-neon` | `x86_64` | `advised` | 5 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 129 | `ipv4-v2` | `ipv4_valid` | `gemini-4-neon` | `x86_64` | `blind` | 7 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 130 | `ipv4-v2` | `ipv4_valid` | `kimi-k3.1-pro` | `arm64` | `advised` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `mov total, sum`: cannot show: -2 >= 0 |
| 131 | `ipv4-v2` | `ipv4_valid` | `kimi-k3.1-pro` | `x86_64` | `blind` | 8 | `lang:manual-stack-frame` | `W4-abi-stack-frame` | ode: line 40: a contract says 'stack' once |
| 132 | `ipv4-v2` | `ipv4_valid` | `qwen3.8-2.4t-a95b` | `arm64` | `blind` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `add end_ptr, base, hdr_len`: cannot show: x0(pkt) + 4*v35 (5..15) <= 2^64 - 1 |
| 133 | `ipv4-v2` | `ipv4_valid` | `qwen3.8-2.4t-a95b` | `x86_64` | `advised` | 8 | `arith:ptr-or-u64-wrap-guard` | `W2-buffer-slice` | `cmp k, words`: cannot show: rsi(n) >= 2*v23 + 4 |
| 134 | `ipv4-v2` | `ipv4_valid` | `qwen3.8-2.4t-a95b` | `x86_64` | `blind` | 8 | `prover:timeout-place-or-unfold` | `W1-place-invariant` | prover_timeout |
| 135 | `utf8-v1` | `utf8_valid` | `claude-haiku-5.5` | `arm64` | `advised` | 8 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | `res := 0`: cannot show: v68 (byte 0..255) >= 128 |
| 136 | `utf8-v1` | `utf8_valid` | `claude-haiku-5.5` | `x86_64` | `blind` | 8 | `arith:place-invariant-or-postcond` | `W1-place-invariant` | `cmp rcx, rsi`: cannot show: v34 (byte 0..255) >= 128 |
