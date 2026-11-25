# Pre-Registration Statement: Multi-Model Cold-Room eBPF Experiment (`prereg-ebpf-v1`)

- **Pre-registered UTC timestamp:** `2026-11-25 17:19 UTC`
- **Status at commit:** **Zero experimental task calls made.** Only a single `"Reply with the single word OK."` API schema check was run beforehand against the four model endpoints to verify request compatibility.
- **Pinned Ode repository baseline commit:** `cb5450aa5ea193092d541b632d7c1c235b4b815a`

---

## 1. Research Question

Given only Ode's concise documentation (`docs/QUICKSTART.md`), the target processor instruction table (`core/x86.tab` or `arm64/arm64.tab`), an unmodified RFC 9669 eBPF subset specification (`ebpf_spec.ode`), and live compiler/prover/verifier feedback (`ode check`, `ode pack`, `ode audit`), can frontier language models from multiple families independently write native x86-64 and AArch64 machine code that passes full `ode audit` against a locked canonical contract?

A secondary goal is qualitative diagnosis: recording every compiler, invariant, instruction-table, or prover obstacle encountered across models and architectures so we can eliminate real language and diagnostic friction in future Ode iterations.

---

## 2. Locked Inputs (64-Hex BLAKE3 Digests)

All inputs below are frozen before any run starts and passed **untruncated** to every model:

| Artifact | Path | BLAKE3-256 (64 hex chars) |
|---|---|---|
| Specification | `proof-core/examples/ebpf/ebpf_spec.ode` | `b13cc432c3cb48a1c88bea3b2a91eb9ca389a38b74a5d1ca971d3ec88b870b87` |
| Coder quickstart | `docs/QUICKSTART.md` | `603cfb9c2dc8177906dd766fe8055e6162f1e3740280570f0202c914bc6e4bea` |
| x86-64 ISA table (96 rows) | `core/x86.tab` | `e9ff8cc0b3467375e7935569b469474e04cdd91a15bfb02556a7a959e4d38d73` |
| AArch64 ISA table (56 rows) | `arm64/arm64.tab` | `adaa95953e3526fa7e2ffcadf55b4aaebfd3417b2e9cba26f6a433d2c1c521c6` |
| Experiment runner | `paper/EXPERIMENTS/ebpf_v1_runner.py` | `9a21b4c8821a6907de1f3c6f3e7e7945cb0173f65b500caeef538e3dcfdddd5d` |

*(No reference implementation—including `proof-core/examples/ebpf/ebpf_unified.ode`—is shown or accessible to any model.)*

### Locked Exported Contract & Expected Canonical Identifier

Every candidate file imports `ebpf_spec.ode` unchanged via `use bpf = "ebpf_spec.ode"` and implements:

```ode
fn ebpf_run(prog: n bytes, n: number, fuel: number, arg1: number)
    requires n < 18446744073709551615
    requires arg1 < 4294967296
    returns bpf.ebpf_run(prog, fuel, arg1)
    trace depends on prog, n, fuel, arg1
    stack 128
```

- **Expected 52-character lowercase base-32 BLAKE3 contract ID (identical on x86-64 and AArch64):**  
  `d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa`
- **Expected exported ELF symbol:**  
  `ode_d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa`

---

## 3. Experimental Design & Fixed Parameters

### Panel: 4 Models × 2 Targets = 8 Independent Cold-Room Cells

| Model ID (OpenRouter) | Family / Role | Targets |
|---|---|---|
| `anthropic/claude-fable-5.2` | Anthropic flagship | `arm64`, `x86_64` |
| `openai/gpt-6.2-astra-pro` | OpenAI flagship | `arm64`, `x86_64` |
| `google/gemini-4-neon` | Google flagship | `arm64`, `x86_64` |
| `anthropic/claude-sonnet-5.5` | Exploratory pilot baseline | `arm64`, `x86_64` |

Each cell runs in complete isolation (fresh temporary directory containing only a copy of `ebpf_spec.ode`; zero shared conversation state across cells).

### Fixed Hyperparameters

- **Maximum rounds per cell:** `8`
- **Sampling temperature:** `0.2`
- **Completion + reasoning token cap:** `16,000`
- **Reasoning effort:** `medium`
- **API request timeout:** `220 s` per round
- **Local tool timeout (`ode check` / `ode pack` / `ode audit`):** `120 s` per command
- **History retention:** initial prompt + latest 3 rounds verbatim
- **Runner modification rule:** `ebpf_v1_runner.py`, `docs/QUICKSTART.md`, `ebpf_spec.ode`, the instruction tables, the compiler, and the verifier will **not** be altered between cells or mid-run. Any infrastructure failure (API timeout, HTTP 5xx) will be recorded verbatim as a failed/errored round, never silently dropped or cherry-picked.

---

## 4. Outcome Definitions

### Primary Outcome (Binary, per cell)

A cell is scored **`PASS`** if and only if, within at most 8 rounds:
1. `ode pack` compiles, proves, and packs the model's `.ode` file into an ELF64 object file (`.o`) and separate `.proof` file (exit 0), **and**
2. `ode audit FILE.o --proof FILE.proof --expect-contract d7b6z5hr3w25whmsn56nvv3qcsq5ugtcxifauztdznaekaiiahfa` exits 0 and prints `VERDICT: shown` with `100% of executable code` covered and `0 hooks`.

Otherwise, the cell is scored **`FAIL`**.

### Secondary Metrics (Reported for All 8 Cells)

- Rounds to `PASS` (1–8, or `FAIL`)
- Total API cost (USD) and wall-clock time (API seconds and tool seconds)
- Emitted function count, machine instruction count, `.text` size (bytes), `.proof` size (bytes), and `ode audit` wall time (seconds)
- Independent cross-verification of passing artifacts with `proof-core/verify2.py` (pass/fail/scope note)
- Taxonomy of per-round failure modes across all 8 cells (syntax/parse error, table instruction error, concrete counterexample `refused with a proof`, prover `no proof found`, tool timeout, API error)

---

## 5. Publication Commitment

All 8 cells—passes, failures, costs, round counts, and categorized error logs—will be published in full in a companion results report (`paper/EXPERIMENTS/results-ebpf-v1.md`) referencing this pre-registration commit hash.
