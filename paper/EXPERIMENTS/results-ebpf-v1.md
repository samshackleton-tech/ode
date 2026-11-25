# Results Report: Multi-Model Cold-Room eBPF Experiment (`prereg-ebpf-v1`)

- **Pre-registration commit (frozen before any task API call):** `60a7726c2f801ff54ea325784c36b5c5e29f20a1` ([`prereg-ebpf-v1.md`](prereg-ebpf-v1.md))
- **Execution window:** `2026-11-25 17:20 UTC` to `17:39 UTC` (19 minutes total wall clock across 8 concurrent cold-room cells)
- **Deviations from pre-registration:** **None.** Zero files, prompts, timeouts, or tools were modified during the experiment. All 8 cells are reported verbatim.

---

## 1. Primary Outcome Table (All 8 Cells)

Binary primary outcome: **`PASS`** iff within at most 8 rounds the model's `.ode` file passes `ode pack` and `ode audit --expect-contract d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa` (`VERDICT: shown`, `100%` `.text` coverage, `0 hooks`).

| Model | Target | Outcome | Rounds | Cost (USD) | API (s) | Tool (s) | Fns | Insns | `.text` (B) | `.proof` (B) | Audit (s) | Native CPU test |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| `openai/gpt-6.2-astra-pro` | `x86_64` | **PASS** | 5 / 8 | $1.89 | 222.8 | 130.5 | 7 | 187 | 680 | 54,349 | 0.111 | 5/5 exact (x86-64 Linux) |
| `openai/gpt-6.2-astra-pro` | `arm64` | **PASS** | 8 / 8 | $2.85 | 330.9 | 263.1 | 6 | 177 | 740 | 78,552 | 0.158 | 5/5 exact (Apple M6) |
| `google/gemini-4-neon` | `x86_64` | **PASS** | 7 / 8 | $1.30 | 572.5 | 20.8 | 6 | 219 | 813 | 162,075 | 0.159 | 5/5 exact (x86-64 Linux) |
| `google/gemini-4-neon` | `arm64` | FAIL | 8 / 8 | $1.64 | 756.0 | 121.4 | — | — | — | — | — | — |
| `anthropic/claude-fable-5.2` | `x86_64` | FAIL* | 8 / 8 | $4.56 | 627.9 | 244.8 | — | — | — | — | — | — |
| `anthropic/claude-fable-5.2` | `arm64` | FAIL | 8 / 8 | $4.35 | 705.7 | 241.0 | — | — | — | — | — | — |
| `anthropic/claude-sonnet-5.5` | `x86_64` | FAIL | 8 / 8 | $0.85 | 290.2 | 575.0 | — | — | — | — | — | — |
| `anthropic/claude-sonnet-5.5` | `arm64` | FAIL | 8 / 8 | $0.74 | 256.5 | 846.9 | — | — | — | — | — | — |

- **Overall strict pass rate:** **3 / 8 cells (`37.5%`)**, spanning **two model families** (`openai/gpt-6.2-astra-pro` on both architectures; `google/gemini-4-neon` on `x86_64`) and **both target architectures** (`x86_64` and `arm64`).
- **Total API spend across all 8 cells (60 rounds):** **$18.17**.
- **Compactness of passing machine code:** Both `openai/gpt-6.2-astra-pro` artifacts were **smaller than our hand-written reference** (`proof-core/examples/ebpf/ebpf_unified.ode`, 209 x86-64 / 192 arm64 instructions): **187 instructions (680 B)** on x86-64 and **177 instructions (740 B)** on AArch64.
- **Native hardware execution:** All three passing artifacts ran natively on real hardware (x86-64 Linux workhorse and Apple M6) against the 5-vector RFC 9669 test suite (`sum(1..10)=55`, out-of-fuel `4294967296`, `fib(10)=55`, `fib(15)=610`, invalid opcode `4294967296`) and produced `55 4294967296 55 610 4294967296`.
- **Independent second verifier (`proof-core/verify2.py`):** All three passing bundles use multi-function custom-calling helpers (`argregs` / `call`), which `verify2.py` currently rejects as outside its implemented scope (`refused: unsupported statement line in verify2: argregs ...`). Extending `verify2.py` to multi-function custom-calling proofs is a concrete follow-up.
- **\*Note on `anthropic/claude-fable-5.2` (`x86_64`, Round 8):** Scored **`FAIL`** under the pre-registered criterion, because `ode pack` failed. However, in Round 8 its 6-function x86-64 implementation actually **passed `ode check` (`shown` in `4.18 s`)** before exposing a real alpha-capture bug in `lang/ode_audit.py` (`_map_places_text`), detailed in Section 3 below.

---

## 2. Failure-Mode Taxonomy (All 60 Rounds)

Every round across all 8 cells is accounted for below (total = 60 rounds):

| Outcome / Failure Category | Rounds | Share | Root cause |
|---|---:|---:|---|
| `prover_timeout_120s` | 18 | 30.0% | Monolithic single-loop VMs without custom-calling helpers (especially `sonnet-5.5`: 11 of its 16 rounds). |
| `calling_syntax_error` | 16 | 26.7% | Models followed `docs/QUICKSTART.md` prose `calling { in ...; out ...; preserves ... }` with semicolons (`;`) or omitted `=`, hitting cryptic parser errors (`not a word of the language: ';'` or `= expected, not 'rax'`). |
| `prover_no_proof_found` | 13 | 21.7% | Normal iterative proof debugging (loop `place` bounds, branch conditions, register preservation). |
| `unified_parse_error` | 6 | 10.0% | Top-level syntax issues (e.g., stray prose or malformed `for` header) on early rounds. |
| `PASS` (`ode audit` = `shown`) | 3 | 5.0% | Complete verified, packed, audited ELF64 `.o` + `.proof`. |
| `empty_reply` | 2 | 3.3% | Reasoning + completion tokens exhausted the 16,000-token cap (`fable-5.2` arm64 R2; `gemini-4-neon` x86-64 R1). |
| `check_pass_pack_fail` | 1 | 1.7% | `fable-5.2` x86-64 R8 passed `ode check` in 4.18 s, then hit a real `_map_places_text` alpha-capture bug in `ode pack`. |
| `counterexample_refuted` | 1 | 1.7% | `gemini-4-neon` x86-64 R6 caught by concrete counterexample (`op=7, lhs=7, rhs=7 -> expected 14, actual 4294967296`), fixed in R7 -> `PASS`. |
| `isa_table_error` (`no row in *.tab`) | **0** | **0.0%** | **Zero instruction-table errors across all 60 rounds** after adding `ja`/`jbe`, `b.hi`/`b.ls` and providing full `.tab` files. |

---

## 3. Four Concrete Findings for Ode Language, Tooling, and Docs

This experiment surfaced four actionable engineering defects directly from cold-room evidence—none of which were visible from author-written tests alone:

1. **Real alpha-capture bug in `lang/ode_audit.py` (`_map_places_text`):**
   `claude-fable-5.2` (`x86_64`, R8) named its loop `place` variables `name a0 = rax`, `name a1 = rcx`, `name a2 = r9`, `name a3 = r10`. Because `ode check` leaves contract argument names (`prog, n, fuel, arg1`) unrenamed, `ode check` proved all 6 functions `shown` in `4.18 s`. When `ode pack` canonicalized `(prog, n, fuel, arg1) -> (a0, a1, a2, a3)`, `_map_places_text` renamed `prog -> a0` inside `place` without first alpha-renaming colliding local `place` variable names (`a0..a3`), silently capturing `prog` with `r0`! **Fix:** alpha-rename any local `place` `name` that collides with a canonical name (`a0..`, `f0..`, `C0..`) before applying the glossary substitution in `_map_places_text`.

2. **26.7% of all rounds (16/60) were burned on `calling { ... }` syntax friction:**
   Every single flagship model (`gpt-6.2-astra-pro`, `claude-fable-5.2`, `gemini-4-neon`) lost 2–3 rounds guessing `calling` syntax because `docs/QUICKSTART.md` Section 5 summarized it in prose with semicolons (`calling { in ...; out ...; preserves ... }`) without showing an inline code snippet of `for x86_64 calling { in a = r10, b = r11 \n out = r9 \n preserves ... }`. **Fix (Wirth rule — fix BOTH parser AND docs):** accept optional `;` separators and optional `out REG` (as well as `out = REG`) in `calling` blocks, emit a clear syntax hint on malformed `calling` headers, and include a full worked `calling` code block in `docs/QUICKSTART.md`.

3. **Factoring helpers vs. monolithic loops is the decisive proof-speed factor:**
   Every passing artifact (`astra62-x86` 7 fns, `astra62-arm64` 6 fns, `gemini4-x86` 6 fns) and `fable52-x86` R8 (6 fns, `4.18 s`) factored the VM into 5–6 `calling` helpers matching the sub-definitions of `ebpf_spec.ode`. Every cell that stayed monolithic (`sonnet-5.5` on both targets, plus early rounds of `astra62`/`fable52`) hit repeated 120 s prover timeouts (18/60 rounds). **Takeaway:** both the prover (automatic path merging / helper outlining) and `docs/QUICKSTART.md` should make helper decomposition explicit, and `ode check` should warn on prover timeouts when a large loop mixes many branches without helper boundaries.

4. **Concrete counterexample feedback (`refused with a proof`) works in one round:**
   When `gemini-4-neon` (`x86_64`, R6) had a real bug in its ALU helper, `ode check` printed the exact failing input (`op=7, lhs=7, rhs=7 -> expected 14, actual 4294967296`), and the model corrected it and passed `ode audit` on the very next round (R7). Conversely, `isa_table_error` dropped to **0/60** once `ja`/`jbe`, `b.hi`/`b.ls`, and untruncated `.tab` tables were supplied.
