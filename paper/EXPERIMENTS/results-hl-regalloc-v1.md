# Results: Pre-Registered Cold-Room Suite `hl-regalloc-v1` (in progress: 214/216 cells finished)

- **Pre-registration commit:** `1d5a5b6d82e76f49aa7cff1d6de5b96d50a28059`
- **Updated (UTC):** `2026-11-27T04:37:09Z`
- **Strict pass rate:** **148/214** finished cells (216 scheduled)
- **Independent second verifier (`verify2.py`):** **80/148** passing cells dual-verified
- **Real-silicon native harness:** **148/148** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 1157 rounds, **$198.13** USD

## Arm-by-Arm Controlled A/B Comparison

Each row summarizes all cells assigned to one experimental arm: pass rate, rounds and time to pass, API cost, and efficiency of verified code.

| Arm | Passes | Mean rounds (pass) | Mean tool s | Mean total s | Cost (USD) | Mean insns | Mean `cyc/B` | Mean saved regs | Mean stack B | Spills / `stack var` | `TRY_HARDER` |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `legacy` | **51/72** | 2.67 | 13.76 | 340.9 | $66.06 | 494.1 | 2.148 | 1.20 | 27.3 | 3 / 0 | 0 |
| `ode_reg` | **46/70** | 2.41 | 24.10 | 340.2 | $65.45 | 454.4 | 2.300 | 0.37 | 19.3 | 0 / 0 | 0 |
| `ode_reg_ask` | **51/72** | 2.94 | 8.15 | 330.1 | $66.63 | 597.5 | 2.304 | 0.41 | 29.5 | 0 / 5 | 0/2 |

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `arm64` | `legacy` | PASS (R1, best R2) | 3 | 5.78 -> **5.16** | 64 B | $1.95 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg` | PASS (R1, best R2) | 3 | 6.11 -> **5.17** | 64 B | $1.33 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg_ask` | PASS (R1, best R2) | 3 | 5.17 -> **5.15** | 64 B | $2.05 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `x86_64` | `legacy` | PASS (R3, best R3) | 5 | 4.19 -> **4.19** | 64 B | $2.23 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg` | PASS (R2, best R2) | 4 | 4.19 -> **4.19** | 64 B | $1.75 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg_ask` | PASS (R7, best R8) | 8 | 4.79 -> **4.18** | 64 B | $3.85 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `legacy` | FAIL (other) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg` | FAIL (other) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg_ask` | FAIL (other) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `legacy` | FAIL (other) | 8 | — | — | $0.06 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg` | FAIL (other) | 8 | — | — | $0.08 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg_ask` | FAIL (other) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `arm64` | `legacy` | PASS (R2, best R3) | 4 | 6.06 -> **5.42** | 64 B | $0.32 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg` | PASS (R8, best R8) | 8 | 6.14 -> **6.14** | 64 B | $1.19 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg_ask` | FAIL (other) | 8 | — | — | $1.05 | — | not_run |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `x86_64` | `legacy` | FAIL (other) | 8 | — | — | $0.70 | — | not_run |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg` | FAIL (other) | 8 | — | — | $0.87 | — | not_run |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg_ask` | PASS (R6, best R7) | 8 | 4.98 -> **4.35** | 64 B | $0.74 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `arm64` | `legacy` | PASS (R1, best R3) | 3 | 5.47 -> **5.11** | 64 B | $1.01 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `arm64` | `ode_reg` | PASS (R1, best R3) | 3 | 5.47 -> **5.10** | 64 B | $1.00 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `arm64` | `ode_reg_ask` | PASS (R1, best R3) | 3 | 5.47 -> **5.11** | 64 B | $0.92 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `x86_64` | `legacy` | PASS (R3, best R5) | 5 | 4.34 -> **4.18** | 64 B | $1.11 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `x86_64` | `ode_reg` | PASS (R3, best R5) | 5 | 4.34 -> **4.34** | 64 B | $1.02 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `x86_64` | `ode_reg_ask` | PASS (R3, best R5) | 5 | 4.34 -> **4.18** | 64 B | $1.25 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `arm64` | `legacy` | PASS (R2, best R4) | 4 | 6.11 -> **5.16** | 64 B | $1.24 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg` | PASS (R1, best R3) | 3 | 6.11 -> **5.13** | 64 B | $0.85 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg_ask` | PASS (R1, best R3) | 3 | 6.11 -> **5.11** | 64 B | $0.86 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `x86_64` | `legacy` | PASS (R2, best R4) | 4 | 4.80 -> **4.15** | 64 B | $1.24 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg` | PASS (R2, best R4) | 4 | 4.80 -> **4.17** | 64 B | $0.97 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg_ask` | PASS (R2, best R4) | 4 | 4.80 -> **4.18** | 64 B | $0.97 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `legacy` | FAIL (other) | 8 | — | — | $0.76 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg` | FAIL (isa_table_error) | 8 | — | — | $0.56 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg_ask` | FAIL (other) | 8 | — | — | $0.68 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `legacy` | FAIL (other) | 8 | — | — | $0.47 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg` | FAIL (other) | 8 | — | — | $0.71 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg_ask` | FAIL (compile_or_parse_error) | 8 | — | — | $0.55 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `arm64` | `legacy` | FAIL (compile_or_parse_error) | 8 | — | — | $7.71 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg` | FAIL (compile_or_parse_error) | 8 | — | — | $7.86 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg_ask` | PASS (R8, best R8) | 8 | 1.94 -> **1.94** | 256 B | $6.79 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `legacy` | PASS (R3, best R4) | 5 | 1.63 -> **1.26** | 256 B | $3.76 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg` | PASS (R5, best R7) | 7 | 1.41 -> **1.23** | 256 B | $6.12 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg_ask` | PASS (R5, best R7) | 7 | 1.62 -> **1.24** | 256 B | $5.78 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `legacy` | FAIL (other) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg` | FAIL (other) | 8 | — | — | $0.08 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg_ask` | FAIL (compile_or_parse_error) | 8 | — | — | $0.09 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `legacy` | FAIL (other) | 8 | — | — | $0.06 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg` | FAIL (other) | 8 | — | — | $0.08 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg_ask` | FAIL (other) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `legacy` | FAIL (compile_or_parse_error) | 8 | — | — | $1.03 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg` | FAIL (other) | 8 | — | — | $1.02 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg_ask` | FAIL (compile_or_parse_error) | 8 | — | — | $0.98 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `legacy` | PASS (R5, best R6) | 7 | 1.70 -> **1.52** | 256 B | $1.28 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg` | FAIL (other) | 8 | — | — | $1.43 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg_ask` | PASS (R6, best R8) | 8 | 1.62 -> **1.42** | 256 B | $1.26 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `arm64` | `legacy` | FAIL (other) | 8 | — | — | $3.34 | — | not_run |
| `blake3_compress_4way` | `google/gemini-4-neon` | `arm64` | `ode_reg` | FAIL (other) | 8 | — | — | $1.82 | — | not_run |
| `blake3_compress_4way` | `google/gemini-4-neon` | `arm64` | `ode_reg_ask` | PASS (R4, best R4) | 6 | 3.46 -> **3.46** | 256 B | $2.44 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `x86_64` | `legacy` | PASS (R2, best R2) | 4 | 1.59 -> **1.59** | 256 B | $1.67 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `x86_64` | `ode_reg` | PASS (R3, best R3) | 5 | 1.44 -> **1.44** | 256 B | $1.64 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `x86_64` | `ode_reg_ask` | PASS (R3, best R5) | 5 | 1.61 -> **1.43** | 256 B | $1.53 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `legacy` | PASS (R6, best R8) | 8 | 5.37 -> **3.31** | 256 B | $2.77 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg` | PASS (R4, best R6) | 6 | 5.45 -> **3.31** | 256 B | $1.94 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg_ask` | PASS (R4, best R6) | 6 | 5.38 -> **3.30** | 256 B | $2.15 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `legacy` | PASS (R2, best R4) | 4 | 1.61 -> **1.23** | 256 B | $1.54 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg` | PASS (R2, best R4) | 4 | 1.71 -> **1.25** | 256 B | $1.41 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg_ask` | PASS (R3, best R5) | 5 | 1.61 -> **1.23** | 256 B | $1.76 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `legacy` | FAIL (output_token_limit) | 8 | — | — | $1.17 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg_ask` | FAIL (output_token_limit) | 8 | — | — | $1.14 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `legacy` | FAIL (other) | 8 | — | — | $0.79 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg` | FAIL (compile_or_parse_error) | 8 | — | — | $1.16 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg_ask` | FAIL (other) | 8 | — | — | $0.77 | — | not_run |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `legacy` | PASS (R1, best R2) | 3 | 2.41 -> **2.33** | 256 B | $1.50 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg` | PASS (R1, best R1) | 3 | 2.40 -> **2.40** | 256 B | $1.21 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg_ask` | PASS (R1, best R2) | 3 | 2.41 -> **2.33** | 256 B | $1.42 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `legacy` | PASS (R1, best R2) | 3 | 1.71 -> **1.70** | 256 B | $1.73 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg` | PASS (R1, best R3) | 3 | 1.71 -> **1.70** | 256 B | $2.40 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg_ask` | PASS (R2, best R3) | 4 | 2.04 -> **1.71** | 256 B | $1.90 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `legacy` | PASS (R5, best R5) | 7 | 2.41 -> **2.41** | 256 B | $0.04 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg` | PASS (R1, best R3) | 3 | 2.50 -> **2.41** | 256 B | $0.02 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg_ask` | PASS (R1, best R1) | 3 | 2.41 -> **2.41** | 256 B | $0.02 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `legacy` | FAIL (other) | 8 | — | — | $0.04 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg` | FAIL (other) | 8 | — | — | $0.03 | — | not_run |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg_ask` | FAIL (other) | 8 | — | — | $0.03 | — | not_run |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `legacy` | PASS (R1, best R1) | 3 | 2.41 -> **2.41** | 256 B | $0.21 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg` | PASS (R1, best R3) | 3 | 2.52 -> **2.41** | 256 B | $0.22 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg_ask` | PASS (R1, best R1) | 3 | 2.41 -> **2.41** | 256 B | $0.21 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `legacy` | PASS (R1, best R1) | 3 | 3.58 -> **3.58** | 256 B | $0.26 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg` | PASS (R1, best R2) | 3 | 3.61 -> **2.05** | 256 B | $0.28 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg_ask` | PASS (R1, best R2) | 3 | 3.58 -> **1.94** | 256 B | $0.28 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `legacy` | PASS (R1, best R1) | 3 | 2.41 -> **2.41** | 256 B | $0.65 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `ode_reg` | PASS (R1, best R2) | 3 | 2.41 -> **2.41** | 256 B | $0.61 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `ode_reg_ask` | PASS (R1, best R3) | 3 | 2.41 -> **2.40** | 256 B | $0.64 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `legacy` | PASS (R1, best R3) | 3 | 1.72 -> **1.70** | 256 B | $1.08 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `ode_reg` | PASS (R1, best R1) | 3 | 2.04 -> **2.04** | 256 B | $0.78 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `ode_reg_ask` | PASS (R1, best R1) | 3 | 1.80 -> **1.80** | 256 B | $1.00 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `legacy` | PASS (R1, best R3) | 3 | 2.41 -> **2.33** | 256 B | $1.09 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg` | PASS (R1, best R2) | 3 | 2.41 -> **2.33** | 256 B | $0.96 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg_ask` | PASS (R1, best R3) | 3 | 2.41 -> **2.33** | 256 B | $1.08 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `legacy` | PASS (R1, best R3) | 3 | 1.72 -> **1.70** | 256 B | $1.01 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg` | PASS (R1, best R3) | 3 | 1.72 -> **1.70** | 256 B | $1.09 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg_ask` | PASS (R1, best R1) | 3 | 1.72 -> **1.72** | 256 B | $0.99 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `legacy` | PASS (R3, best R4) | 5 | 7.58 -> **2.50** | 256 B | $0.27 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg` | FAIL (compile_or_parse_error) | 8 | — | — | $0.66 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg_ask` | PASS (R6, best R7) | 8 | 2.41 -> **2.41** | 256 B | $0.48 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `legacy` | FAIL (other) | 8 | — | — | $1.17 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg` | FAIL (other) | 8 | — | — | $0.42 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg_ask` | FAIL (compile_or_parse_error) | 8 | — | — | $0.57 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `legacy` | PASS (R3, best R3) | 5 | 2.17 -> **2.17** | 4 B | $1.64 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg` | PASS (R1, best R2) | 3 | 2.33 -> **2.08** | 4 B | $1.43 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg_ask` | PASS (R1, best R1) | 3 | 2.33 -> **2.33** | 4 B | $1.00 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `legacy` | PASS (R2, best R3) | 4 | 0.60 -> **0.55** | 20 B | $1.38 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg` | PASS (R2, best R3) | 4 | 2.75 -> **2.50** | 4 B | $1.36 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg_ask` | PASS (R1, best R1) | 3 | 3.00 -> **3.00** | 4 B | $0.92 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `legacy` | FAIL (compile_or_parse_error) | 8 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg` | FAIL (other) | 8 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg_ask` | FAIL (other) | 8 | — | — | $0.04 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `legacy` | FAIL (arith_need_entail) | 8 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg_ask` | FAIL (arith_need_entail) | 8 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `legacy` | PASS (R2, best R2) | 4 | 2.33 -> **2.33** | 4 B | $0.21 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg` | PASS (R6, best R6) | 8 | 2.38 -> **2.38** | 4 B | $0.51 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg_ask` | PASS (R2, best R3) | 4 | 2.38 -> **1.23** | 8 B | $0.22 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `legacy` | PASS (R1, best R1) | 3 | 0.60 -> **0.60** | 20 B | $0.20 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg` | FAIL (arith_need_entail) | 8 | — | — | $0.59 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg_ask` | PASS (R2, best R2) | 4 | 2.75 -> **2.75** | 4 B | $0.27 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `legacy` | PASS (R8, best R8) | 8 | 1.96 -> **1.96** | 4 B | $1.08 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `ode_reg` | PASS (R7, best R7) | 8 | 1.96 -> **1.96** | 4 B | $1.83 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `ode_reg_ask` | FAIL (other) | 8 | — | — | $1.31 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `legacy` | PASS (R6, best R6) | 8 | 0.50 -> **0.50** | 20 B | $1.48 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `ode_reg` | PASS (R7, best R7) | 8 | 2.25 -> **2.25** | 4 B | $1.42 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `ode_reg_ask` | FAIL (spec_need_open) | 8 | — | — | $1.25 | — | not_run |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `legacy` | PASS (R3, best R5) | 5 | 2.33 -> **1.96** | 4 B | $0.71 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg` | PASS (R1, best R1) | 3 | 2.04 -> **2.04** | 4 B | $0.53 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg_ask` | PASS (R2, best R2) | 4 | 2.04 -> **2.04** | 4 B | $0.44 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `legacy` | PASS (R1, best R1) | 3 | 2.75 -> **2.75** | 4 B | $0.47 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg` | PASS (R1, best R3) | 3 | 2.75 -> **2.25** | 4 B | $0.50 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg_ask` | PASS (R2, best R2) | 4 | 2.50 -> **2.50** | 4 B | $0.48 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `legacy` | FAIL (arith_need_entail) | 8 | — | — | $0.24 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg` | PASS (R5, best R6) | 7 | 2.29 -> **2.00** | 4 B | $0.24 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg_ask` | FAIL (arith_need_entail) | 8 | — | — | $0.30 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `legacy` | PASS (R6, best R6) | 8 | 2.75 -> **2.75** | 4 B | $0.48 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg` | PASS (R5, best R5) | 7 | 2.75 -> **2.75** | 4 B | $0.48 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg_ask` | PASS (R5, best R5) | 7 | 2.75 -> **2.75** | 4 B | $0.28 | shown | NATIVE_PASS 333/333 |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `legacy` | PASS (R1, best R1) | 1 | — | — | $0.43 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg` | PASS (R2, best R2) | 2 | — | — | $0.83 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg_ask` | PASS (R1, best R1) | 1 | — | — | $0.39 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `legacy` | PASS (R3, best R3) | 3 | — | — | $1.30 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg` | PASS (R1, best R1) | 1 | — | — | $0.47 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg_ask` | PASS (R6, best R6) | 6 | — | — | $2.92 | refused | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `legacy` | FAIL (other) | 8 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg` | FAIL (compile_or_parse_error) | 8 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg_ask` | PASS (R7, best R7) | 7 | — | — | $0.05 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `legacy` | PASS (R8, best R8) | 8 | — | — | $0.05 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg` | FAIL (arith_need_entail) | 8 | — | — | $0.06 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg_ask` | FAIL (arith_need_compare) | 8 | — | — | $0.05 | — | not_run |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `legacy` | PASS (R1, best R1) | 1 | — | — | $0.07 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg` | PASS (R2, best R2) | 2 | — | — | $0.19 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg_ask` | PASS (R1, best R1) | 1 | — | — | $0.09 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `legacy` | PASS (R4, best R4) | 4 | — | — | $0.35 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg` | PASS (R1, best R1) | 1 | — | — | $0.11 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg_ask` | PASS (R1, best R1) | 1 | — | — | $0.10 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `legacy` | PASS (R4, best R4) | 4 | — | — | $0.52 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `ode_reg` | PASS (R5, best R5) | 5 | — | — | $0.53 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `ode_reg_ask` | PASS (R5, best R5) | 5 | — | — | $0.54 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `legacy` | PASS (R5, best R5) | 5 | — | — | $0.68 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `ode_reg` | PASS (R2, best R2) | 2 | — | — | $0.32 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `ode_reg_ask` | PASS (R2, best R2) | 2 | — | — | $0.32 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `legacy` | PASS (R3, best R3) | 3 | — | — | $0.77 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg` | PASS (R4, best R4) | 4 | — | — | $0.86 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg_ask` | PASS (R4, best R4) | 4 | — | — | $0.59 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `legacy` | PASS (R3, best R3) | 3 | — | — | $0.90 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg` | FAIL (arith_need_entail) | 8 | — | — | $2.39 | — | not_run |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg_ask` | PASS (R6, best R6) | 6 | — | — | $1.05 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `legacy` | FAIL (arith_need_entail) | 8 | — | — | $0.42 | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg` | FAIL (arith_need_compare) | 8 | — | — | $0.44 | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg_ask` | PASS (R5, best R5) | 5 | — | — | $0.15 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `legacy` | FAIL (other) | 8 | — | — | $0.32 | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg` | FAIL (other) | 8 | — | — | $0.30 | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg_ask` | FAIL (arith_need_entail) | 8 | — | — | $0.22 | — | not_run |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `legacy` | PASS (R1, best R2) | 3 | 1.00 -> **0.62** | 4 B | $0.90 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg` | PASS (R1, best R3) | 3 | 0.83 -> **0.54** | 4 B | $0.87 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `ode_reg_ask` | PASS (R1, best R1) | 3 | 0.83 -> **0.83** | 2 B | $0.91 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `legacy` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 4 B | $1.28 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg` | PASS (R2, best R4) | 4 | 1.00 -> **0.75** | 4 B | $1.32 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `ode_reg_ask` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $1.27 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `legacy` | PASS (R2, best R2) | 4 | 0.92 -> **0.92** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg` | PASS (R1, best R3) | 3 | 1.00 -> **0.83** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ode_reg_ask` | PASS (R7, best R7) | 8 | 0.92 -> **0.92** | 2 B | $0.02 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `legacy` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg` | PASS (R3, best R3) | 5 | 1.00 -> **1.00** | 2 B | $0.02 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ode_reg_ask` | PASS (R1, best R1) | 3 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `legacy` | PASS (R1, best R3) | 3 | 0.92 -> **0.75** | 4 B | $0.15 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg` | PASS (R1, best R1) | 3 | 0.92 -> **0.92** | 2 B | $0.16 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `ode_reg_ask` | PASS (R1, best R2) | 3 | 0.92 -> **0.62** | 4 B | $0.15 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `legacy` | PASS (R1, best R1) | 3 | 1.00 -> **1.00** | 2 B | $0.19 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg` | PASS (R1, best R1) | 3 | 1.00 -> **1.00** | 2 B | $0.19 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ode_reg_ask` | PASS (R1, best R1) | 3 | 1.00 -> **1.00** | 2 B | $0.18 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `legacy` | PASS (R6, best R6) | 8 | 0.50 -> **0.50** | 4 B | $1.43 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `ode_reg` | FAIL (arith_need_entail) | 8 | — | — | $1.14 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `ode_reg_ask` | FAIL (other) | 8 | — | — | $1.76 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `legacy` | FAIL (arith_need_entail) | 8 | — | — | $1.31 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `ode_reg` | FAIL (spec_need_open) | 8 | — | — | $1.43 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `ode_reg_ask` | FAIL (spec_need_open) | 8 | — | — | $1.14 | — | not_run |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `legacy` | PASS (R1, best R1) | 3 | 0.54 -> **0.54** | 4 B | $0.56 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg` | PASS (R1, best R3) | 3 | 0.62 -> **0.54** | 4 B | $0.32 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `ode_reg_ask` | PASS (R3, best R5) | 5 | 0.83 -> **0.62** | 4 B | $0.48 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `legacy` | PASS (R4, best R4) | 6 | 1.00 -> **1.00** | 2 B | $0.72 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg` | PASS (R4, best R4) | 6 | 1.00 -> **1.00** | 2 B | $0.62 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ode_reg_ask` | PASS (R7, best R7) | 7 | — | — | $0.99 | refused | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `legacy` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.14 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.14 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ode_reg_ask` | PASS (R2, best R2) | 4 | 0.83 -> **0.83** | 2 B | $0.13 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `legacy` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.13 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.11 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ode_reg_ask` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.15 | shown | NATIVE_PASS 607/607 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `other` | 333 |
| `compile_or_parse_error` | 252 |
| `arith_need_entail` | 182 |
| `spec_need_open` | 30 |
| `arith_need_compare` | 17 |
| `output_token_limit` | 17 |
| `place_error` | 6 |
| `trace_refusal` | 5 |
| `isa_table_error` | 4 |
| `calling_syntax_error` | 2 |
