# Results: Pre-Registered Cold-Room Suite `hl-ab-v1`

- **Pre-registration commit:** `b4f3200e051362056e8be5ade849a10826b6e61f`
- **Finished (UTC):** `2026-11-27T02:05:58Z`
- **Strict pass rate:** **208/288** finished cells
- **Independent second verifier (`verify2.py`):** **111/208** passing cells dual-verified
- **Real-silicon native harness:** **208/208** passing cells executed and passed on matching hardware
- **Total rounds / API spend:** 1556 rounds, **$286.61** USD

## Arm-by-Arm Controlled A/B Comparison

Each row summarizes all cells assigned to one experimental arm: pass rate, rounds and time to pass, API cost, and efficiency of verified code.

| Arm | Passes | Mean rounds (pass) | Mean tool s | Mean total s | Cost (USD) | Mean insns | Mean `cyc/B` | Mean stack B | Total spills |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `ask_both` | **46/72** | 2.39 | 8.65 | 342.2 | $74.63 | 499.3 | 2.398 | 18.1 | 0 |
| `auto` | **56/72** | 2.86 | 14.97 | 317.4 | $73.45 | 528.4 | 2.301 | 18.6 | 4 |
| `fast_fail` | **54/72** | 3.22 | 8.27 | 339.3 | $75.63 | 562.5 | 2.253 | 10.6 | 0 |
| `no_spill` | **52/72** | 2.79 | 14.80 | 317.4 | $62.90 | 547.2 | 2.270 | 25.6 | 0 |

## Cell-by-Cell Outcomes

Each row reports one cold-room cell: verdict, rounds used, API cost, compiled code size, `verify2.py` status, and real-silicon test result.

| Task | Model | Target | Arm | Verdict | Rounds | Initial -> Best `cyc/B` | Unroll (B/it) | Cost (USD) | `verify2.py` | Native CPU |
| --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `arm64` | `ask_both` | FAIL (output_token_limit) | 6 | — | — | $6.00 | — | not_run |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `arm64` | `auto` | PASS (R4, best R5) | 6 | 5.78 -> **5.17** | 64 B | $3.64 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `arm64` | `fast_fail` | FAIL (compile_or_parse_error) | 8 | — | — | $7.41 | — | not_run |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `arm64` | `no_spill` | PASS (R1, best R2) | 3 | 6.11 -> **5.17** | 64 B | $1.59 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `x86_64` | `ask_both` | PASS (R7, best R8) | 8 | 4.80 -> **4.19** | 64 B | $3.85 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `x86_64` | `auto` | PASS (R2, best R4) | 4 | 4.80 -> **4.19** | 64 B | $1.71 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `x86_64` | `fast_fail` | PASS (R4, best R6) | 6 | 4.79 -> **4.18** | 64 B | $2.27 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-fable-5.2` | `x86_64` | `no_spill` | PASS (R2, best R3) | 4 | 4.19 -> **4.19** | 64 B | $1.82 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `ask_both` | FAIL (compile_or_parse_error) | 8 | — | — | $0.06 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `auto` | FAIL (other) | 8 | — | — | $0.05 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `fast_fail` | FAIL (other) | 8 | — | — | $0.08 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `arm64` | `no_spill` | FAIL (other) | 8 | — | — | $0.06 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `ask_both` | FAIL (compile_or_parse_error) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `auto` | FAIL (other) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `fast_fail` | FAIL (compile_or_parse_error) | 8 | — | — | $0.08 | — | not_run |
| `blake3_compress1` | `anthropic/claude-haiku-5.5` | `x86_64` | `no_spill` | FAIL (compile_or_parse_error) | 8 | — | — | $0.06 | — | not_run |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `arm64` | `ask_both` | PASS (R2, best R3) | 4 | 6.10 -> **5.47** | 64 B | $0.34 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `arm64` | `auto` | PASS (R2, best R2) | 2 | — | — | $0.17 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `arm64` | `fast_fail` | PASS (R5, best R6) | 7 | 6.11 -> **5.47** | 64 B | $0.69 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `arm64` | `no_spill` | PASS (R4, best R4) | 4 | — | — | $0.37 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ask_both` | PASS (R6, best R6) | 8 | 4.80 -> **4.80** | 64 B | $0.77 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `x86_64` | `auto` | PASS (R3, best R4) | 5 | 5.14 -> **5.14** | 64 B | $0.49 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `x86_64` | `fast_fail` | PASS (R7, best R7) | 8 | 4.98 -> **4.98** | 64 B | $1.02 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `anthropic/claude-sonnet-5.5` | `x86_64` | `no_spill` | PASS (R4, best R5) | 6 | 4.98 -> **4.36** | 64 B | $0.57 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `arm64` | `ask_both` | PASS (R1, best R3) | 3 | 5.47 -> **5.12** | 64 B | $0.96 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `arm64` | `auto` | PASS (R1, best R3) | 3 | 5.47 -> **5.16** | 64 B | $0.91 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `arm64` | `fast_fail` | PASS (R1, best R3) | 3 | 5.43 -> **5.10** | 64 B | $0.93 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `arm64` | `no_spill` | PASS (R1, best R3) | 3 | 5.47 -> **5.09** | 64 B | $0.90 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `x86_64` | `ask_both` | PASS (R3, best R5) | 5 | 4.34 -> **4.13** | 64 B | $1.26 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `x86_64` | `auto` | PASS (R3, best R5) | 5 | 4.34 -> **4.18** | 64 B | $1.27 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `x86_64` | `fast_fail` | PASS (R3, best R5) | 5 | 4.34 -> **4.16** | 64 B | $1.15 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `google/gemini-4-neon` | `x86_64` | `no_spill` | PASS (R3, best R5) | 5 | 4.34 -> **4.31** | 64 B | $1.04 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `arm64` | `ask_both` | PASS (R1, best R3) | 3 | 5.78 -> **5.17** | 64 B | $0.83 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `arm64` | `auto` | PASS (R1, best R3) | 3 | 5.78 -> **5.11** | 64 B | $0.89 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `arm64` | `fast_fail` | PASS (R1, best R3) | 3 | 6.11 -> **5.12** | 64 B | $0.92 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `arm64` | `no_spill` | PASS (R1, best R3) | 3 | 6.11 -> **5.11** | 64 B | $0.89 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ask_both` | PASS (R3, best R5) | 5 | 4.81 -> **4.17** | 64 B | $1.19 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `x86_64` | `auto` | PASS (R2, best R4) | 4 | 4.80 -> **4.14** | 64 B | $1.21 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `x86_64` | `fast_fail` | PASS (R2, best R4) | 4 | 4.81 -> **4.17** | 64 B | $0.96 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `openai/gpt-6.2-astra-pro` | `x86_64` | `no_spill` | PASS (R2, best R4) | 4 | 4.80 -> **4.17** | 64 B | $1.06 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ask_both` | FAIL (other) | 8 | — | — | $0.79 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `auto` | PASS (R5, best R5) | 5 | — | — | $0.82 | — | NATIVE_PASS 201/201 |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `fast_fail` | FAIL (output_token_limit) | 8 | — | — | $0.47 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `no_spill` | FAIL (other) | 8 | — | — | $0.90 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ask_both` | FAIL (compile_or_parse_error) | 8 | — | — | $0.42 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `auto` | FAIL (other) | 8 | — | — | $0.54 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `fast_fail` | FAIL (compile_or_parse_error) | 8 | — | — | $0.68 | — | not_run |
| `blake3_compress1` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `no_spill` | FAIL (compile_or_parse_error) | 8 | — | — | $0.57 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `arm64` | `ask_both` | FAIL (other) | 8 | — | — | $9.50 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `arm64` | `auto` | FAIL (other) | 8 | — | — | $8.61 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `arm64` | `fast_fail` | PASS (R6, best R8) | 8 | 1.95 -> **1.74** | 256 B | $5.80 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `arm64` | `no_spill` | FAIL (other) | 8 | — | — | $7.46 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `ask_both` | PASS (R3, best R4) | 5 | 1.42 -> **1.25** | 256 B | $3.41 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `auto` | PASS (R4, best R6) | 6 | 1.42 -> **1.24** | 256 B | $3.90 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `fast_fail` | PASS (R6, best R8) | 8 | 1.42 -> **1.24** | 256 B | $6.33 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `no_spill` | PASS (R2, best R4) | 4 | 1.62 -> **1.24** | 256 B | $2.92 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ask_both` | FAIL (other) | 8 | — | — | $0.10 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `auto` | FAIL (other) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `fast_fail` | FAIL (compile_or_parse_error) | 8 | — | — | $0.06 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `no_spill` | FAIL (other) | 8 | — | — | $0.21 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ask_both` | FAIL (other) | 8 | — | — | $0.12 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `auto` | FAIL (other) | 8 | — | — | $0.05 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `fast_fail` | FAIL (other) | 8 | — | — | $0.07 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `no_spill` | FAIL (other) | 8 | — | — | $0.10 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `ask_both` | FAIL (other) | 8 | — | — | $1.33 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `auto` | FAIL (compile_or_parse_error) | 8 | — | — | $1.09 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `fast_fail` | FAIL (compile_or_parse_error) | 8 | — | — | $1.33 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `no_spill` | FAIL (other) | 8 | — | — | $1.07 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ask_both` | FAIL (compile_or_parse_error) | 8 | — | — | $1.22 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `auto` | FAIL (other) | 8 | — | — | $1.32 | — | not_run |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `fast_fail` | PASS (R6, best R6) | 8 | 4.48 -> **4.48** | 256 B | $0.97 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `no_spill` | PASS (R7, best R7) | 8 | 1.65 -> **1.65** | 256 B | $1.81 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `arm64` | `ask_both` | PASS (R6, best R6) | 8 | 3.49 -> **3.49** | 256 B | $2.45 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `arm64` | `auto` | PASS (R6, best R6) | 8 | 3.47 -> **3.47** | 256 B | $2.63 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `arm64` | `fast_fail` | PASS (R7, best R7) | 8 | 3.47 -> **3.47** | 256 B | $2.52 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `arm64` | `no_spill` | PASS (R8, best R8) | 8 | 3.48 -> **3.48** | 256 B | $2.75 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `x86_64` | `ask_both` | PASS (R4, best R5) | 6 | 1.61 -> **1.41** | 256 B | $2.30 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `x86_64` | `auto` | PASS (R3, best R5) | 5 | 1.63 -> **1.20** | 256 B | $1.97 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `x86_64` | `fast_fail` | PASS (R4, best R4) | 6 | 1.61 -> **1.61** | 256 B | $1.93 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `google/gemini-4-neon` | `x86_64` | `no_spill` | PASS (R3, best R5) | 5 | 1.73 -> **1.42** | 256 B | $1.61 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `ask_both` | FAIL (other) | 8 | — | — | $2.56 | — | not_run |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `auto` | PASS (R6, best R8) | 8 | 5.37 -> **3.30** | 256 B | $3.13 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `fast_fail` | PASS (R6, best R8) | 8 | 5.37 -> **3.30** | 256 B | $2.84 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `no_spill` | PASS (R7, best R8) | 8 | 5.38 -> **3.47** | 256 B | $2.61 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ask_both` | PASS (R3, best R5) | 5 | 1.74 -> **1.33** | 256 B | $1.65 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `auto` | PASS (R4, best R6) | 6 | 1.63 -> **1.22** | 256 B | $4.08 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `fast_fail` | PASS (R6, best R8) | 8 | 1.70 -> **1.39** | 256 B | $4.79 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `no_spill` | PASS (R4, best R6) | 6 | 1.61 -> **1.23** | 256 B | $2.10 | — | NATIVE_PASS 121/121 |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ask_both` | FAIL (compile_or_parse_error) | 8 | — | — | $0.60 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `auto` | FAIL (other) | 8 | — | — | $0.62 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `fast_fail` | FAIL (other) | 8 | — | — | $0.44 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `no_spill` | FAIL (compile_or_parse_error) | 8 | — | — | $0.75 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ask_both` | FAIL (compile_or_parse_error) | 8 | — | — | $0.93 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `auto` | FAIL (compile_or_parse_error) | 8 | — | — | $0.79 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `fast_fail` | FAIL (compile_or_parse_error) | 8 | — | — | $1.11 | — | not_run |
| `blake3_compress_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `no_spill` | FAIL (compile_or_parse_error) | 8 | — | — | $0.69 | — | not_run |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `ask_both` | PASS (R1, best R1) | 3 | 2.41 -> **2.41** | 256 B | $1.17 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `auto` | PASS (R1, best R2) | 3 | 2.48 -> **2.41** | 256 B | $1.23 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `fast_fail` | PASS (R1, best R2) | 3 | 2.48 -> **2.34** | 256 B | $1.25 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `arm64` | `no_spill` | PASS (R1, best R2) | 3 | 2.48 -> **2.34** | 256 B | $1.14 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `ask_both` | PASS (R1, best R2) | 3 | 1.71 -> **1.70** | 256 B | $1.69 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `auto` | PASS (R1, best R1) | 3 | 1.72 -> **1.72** | 256 B | $1.79 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `fast_fail` | PASS (R1, best R2) | 3 | 1.72 -> **1.70** | 256 B | $1.75 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-fable-5.2` | `x86_64` | `no_spill` | PASS (R1, best R3) | 3 | 2.04 -> **1.70** | 256 B | $1.63 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `ask_both` | PASS (R2, best R3) | 4 | 2.41 -> **2.41** | 256 B | $0.02 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `auto` | PASS (R1, best R1) | 3 | 2.41 -> **2.41** | 256 B | $0.02 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `fast_fail` | PASS (R7, best R7) | 8 | 2.41 -> **2.41** | 256 B | $0.05 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `arm64` | `no_spill` | PASS (R6, best R7) | 8 | 2.42 -> **2.41** | 256 B | $0.05 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `ask_both` | PASS (R1, best R2) | 3 | 5.89 -> **3.61** | 256 B | $0.02 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `auto` | PASS (R2, best R2) | 4 | 3.62 -> **3.62** | 256 B | $0.03 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `fast_fail` | PASS (R1, best R2) | 3 | 5.89 -> **3.61** | 256 B | $0.02 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-haiku-5.5` | `x86_64` | `no_spill` | FAIL (other) | 8 | — | — | $0.04 | — | not_run |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `ask_both` | PASS (R1, best R1) | 3 | 2.41 -> **2.41** | 256 B | $0.21 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `auto` | PASS (R3, best R3) | 5 | 2.41 -> **2.41** | 256 B | $0.37 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `fast_fail` | PASS (R1, best R3) | 3 | 2.48 -> **2.41** | 256 B | $0.22 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `arm64` | `no_spill` | PASS (R1, best R2) | 3 | 2.52 -> **2.41** | 256 B | $0.23 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ask_both` | PASS (R1, best R1) | 3 | 3.58 -> **3.58** | 256 B | $0.23 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `auto` | PASS (R1, best R2) | 3 | 5.89 -> **3.58** | 256 B | $0.24 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `fast_fail` | PASS (R1, best R1) | 3 | 3.58 -> **3.58** | 256 B | $0.27 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `anthropic/claude-sonnet-5.5` | `x86_64` | `no_spill` | PASS (R1, best R2) | 3 | 3.58 -> **2.04** | 256 B | $0.29 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `ask_both` | PASS (R1, best R1) | 3 | 2.41 -> **2.41** | 256 B | $0.57 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `auto` | PASS (R2, best R2) | 4 | 2.41 -> **2.41** | 256 B | $0.69 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `fast_fail` | PASS (R2, best R3) | 4 | 2.41 -> **2.41** | 256 B | $0.70 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `arm64` | `no_spill` | PASS (R1, best R3) | 3 | 2.41 -> **2.41** | 256 B | $0.57 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `ask_both` | PASS (R1, best R3) | 3 | 1.70 -> **1.70** | 256 B | $1.14 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `auto` | PASS (R1, best R1) | 3 | 1.72 -> **1.72** | 256 B | $1.09 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `fast_fail` | PASS (R2, best R4) | 4 | 1.72 -> **1.70** | 256 B | $1.12 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `google/gemini-4-neon` | `x86_64` | `no_spill` | PASS (R1, best R3) | 3 | 2.04 -> **1.70** | 256 B | $0.96 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `ask_both` | PASS (R1, best R2) | 3 | 2.41 -> **2.33** | 256 B | $1.06 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `auto` | PASS (R1, best R3) | 3 | 2.41 -> **2.33** | 256 B | $0.96 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `fast_fail` | PASS (R1, best R2) | 3 | 2.41 -> **2.33** | 256 B | $1.05 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `arm64` | `no_spill` | PASS (R1, best R3) | 3 | 2.41 -> **2.33** | 256 B | $1.05 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ask_both` | PASS (R1, best R3) | 3 | 1.72 -> **1.72** | 256 B | $0.91 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `auto` | PASS (R1, best R2) | 3 | 1.72 -> **1.70** | 256 B | $1.20 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `fast_fail` | PASS (R1, best R3) | 3 | 1.72 -> **1.70** | 256 B | $0.91 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `openai/gpt-6.2-astra-pro` | `x86_64` | `no_spill` | PASS (R1, best R1) | 3 | 1.72 -> **1.72** | 256 B | $1.08 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ask_both` | FAIL (other) | 8 | — | — | $0.46 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `auto` | PASS (R4, best R5) | 6 | 2.41 -> **2.41** | 256 B | $0.37 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `fast_fail` | FAIL (other) | 8 | — | — | $0.41 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `no_spill` | PASS (R4, best R6) | 6 | 7.58 -> **2.48** | 256 B | $0.28 | — | NATIVE_PASS 98/98 |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ask_both` | FAIL (other) | 8 | — | — | $0.57 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `auto` | FAIL (other) | 8 | — | — | $0.47 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `fast_fail` | FAIL (other) | 8 | — | — | $0.66 | — | not_run |
| `chacha20_4way` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `no_spill` | PASS (R4, best R6) | 6 | 2.66 -> **2.00** | 256 B | $0.44 | — | NATIVE_PASS 98/98 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `ask_both` | PASS (R2, best R3) | 4 | 2.00 -> **2.00** | 4 B | $1.47 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `auto` | PASS (R1, best R1) | 3 | 2.04 -> **2.04** | 4 B | $1.03 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `fast_fail` | PASS (R1, best R1) | 3 | 2.08 -> **2.08** | 4 B | $0.97 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `arm64` | `no_spill` | PASS (R1, best R1) | 3 | 2.12 -> **2.12** | 4 B | $0.94 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `ask_both` | PASS (R1, best R1) | 3 | 2.50 -> **2.50** | 4 B | $1.12 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `auto` | PASS (R2, best R4) | 4 | 2.75 -> **2.50** | 4 B | $1.27 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `fast_fail` | PASS (R1, best R1) | 3 | 0.50 -> **0.50** | 20 B | $1.03 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-fable-5.2` | `x86_64` | `no_spill` | PASS (R2, best R2) | 4 | 2.25 -> **2.25** | 4 B | $1.24 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `ask_both` | FAIL (arith_need_entail) | 8 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `auto` | FAIL (arith_need_entail) | 8 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `fast_fail` | FAIL (arith_need_entail) | 8 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `arm64` | `no_spill` | FAIL (other) | 8 | — | — | $0.03 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `ask_both` | FAIL (other) | 8 | — | — | $0.04 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `auto` | PASS (R2, best R2) | 4 | 2.75 -> **2.75** | 4 B | $0.02 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `fast_fail` | PASS (R5, best R6) | 7 | 2.75 -> **0.39** | 28 B | $0.03 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-haiku-5.5` | `x86_64` | `no_spill` | FAIL (other) | 8 | — | — | $0.04 | — | not_run |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `ask_both` | PASS (R2, best R2) | 4 | 2.33 -> **2.33** | 4 B | $0.21 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `auto` | PASS (R4, best R4) | 6 | 2.29 -> **2.29** | 4 B | $0.35 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `fast_fail` | PASS (R3, best R3) | 5 | 2.04 -> **2.04** | 4 B | $0.28 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `arm64` | `no_spill` | PASS (R1, best R1) | 3 | 2.29 -> **2.29** | 4 B | $0.15 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ask_both` | PASS (R3, best R3) | 5 | 2.75 -> **2.75** | 4 B | $0.33 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `auto` | PASS (R3, best R3) | 5 | 2.75 -> **2.75** | 4 B | $0.34 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `fast_fail` | PASS (R2, best R2) | 4 | 2.75 -> **2.75** | 4 B | $0.26 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `anthropic/claude-sonnet-5.5` | `x86_64` | `no_spill` | PASS (R4, best R5) | 6 | 2.75 -> **2.50** | 4 B | $0.40 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `ask_both` | FAIL (arith_need_entail) | 8 | — | — | $1.41 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `auto` | FAIL (arith_need_entail) | 8 | — | — | $1.34 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `fast_fail` | PASS (R6, best R6) | 8 | 1.96 -> **1.96** | 4 B | $1.67 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `google/gemini-4-neon` | `arm64` | `no_spill` | PASS (R7, best R7) | 8 | 1.96 -> **1.96** | 4 B | $1.44 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `ask_both` | FAIL (other) | 8 | — | — | $1.32 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `auto` | PASS (R8, best R8) | 8 | 0.50 -> **0.50** | 20 B | $1.31 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `fast_fail` | FAIL (arith_need_entail) | 8 | — | — | $1.64 | — | not_run |
| `ct_base64_decode` | `google/gemini-4-neon` | `x86_64` | `no_spill` | FAIL (arith_need_entail) | 8 | — | — | $1.14 | — | not_run |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `ask_both` | PASS (R2, best R4) | 4 | 2.08 -> **2.08** | 4 B | $0.57 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `auto` | PASS (R3, best R3) | 5 | 1.96 -> **1.96** | 4 B | $0.54 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `fast_fail` | PASS (R2, best R2) | 4 | 2.00 -> **2.00** | 4 B | $0.50 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `arm64` | `no_spill` | PASS (R1, best R1) | 3 | 2.04 -> **2.04** | 4 B | $0.47 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ask_both` | PASS (R2, best R2) | 4 | 2.50 -> **2.50** | 4 B | $0.70 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `auto` | PASS (R1, best R3) | 3 | 2.50 -> **2.25** | 4 B | $0.39 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `fast_fail` | PASS (R2, best R2) | 4 | 2.50 -> **2.50** | 4 B | $0.51 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `openai/gpt-6.2-astra-pro` | `x86_64` | `no_spill` | PASS (R1, best R3) | 3 | 2.50 -> **2.25** | 4 B | $0.56 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ask_both` | PASS (R4, best R4) | 6 | 2.67 -> **2.67** | 4 B | $0.20 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `auto` | PASS (R4, best R4) | 6 | 2.12 -> **2.12** | 4 B | $0.24 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `fast_fail` | PASS (R3, best R3) | 5 | 2.33 -> **2.33** | 4 B | $0.13 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `no_spill` | FAIL (calling_syntax_error) | 8 | — | — | $0.20 | — | not_run |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ask_both` | PASS (R3, best R3) | 5 | 2.75 -> **2.75** | 4 B | $0.15 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `auto` | PASS (R3, best R3) | 5 | 3.00 -> **3.00** | 4 B | $0.20 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `fast_fail` | PASS (R6, best R7) | 8 | 1.00 -> **1.00** | 12 B | $0.27 | shown | NATIVE_PASS 333/333 |
| `ct_base64_decode` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `no_spill` | PASS (R2, best R2) | 4 | 3.00 -> **3.00** | 4 B | $0.13 | shown | NATIVE_PASS 333/333 |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `ask_both` | PASS (R2, best R2) | 2 | — | — | $0.80 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `auto` | PASS (R8, best R8) | 8 | — | — | $6.34 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `fast_fail` | PASS (R2, best R2) | 2 | — | — | $0.74 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `arm64` | `no_spill` | PASS (R2, best R2) | 2 | — | — | $0.82 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `ask_both` | FAIL (arith_need_entail) | 8 | — | — | $5.89 | — | not_run |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `auto` | PASS (R2, best R2) | 2 | — | — | $0.80 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `fast_fail` | PASS (R6, best R6) | 6 | — | — | $3.41 | refused | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `no_spill` | PASS (R3, best R3) | 3 | — | — | $1.57 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ask_both` | FAIL (arith_need_entail) | 8 | — | — | $0.05 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `auto` | FAIL (arith_need_compare) | 8 | — | — | $0.04 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `fast_fail` | FAIL (arith_need_compare) | 8 | — | — | $0.05 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `no_spill` | FAIL (arith_need_entail) | 8 | — | — | $0.05 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ask_both` | FAIL (arith_need_entail) | 8 | — | — | $0.05 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `auto` | FAIL (arith_need_entail) | 8 | — | — | $0.05 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `fast_fail` | FAIL (other) | 8 | — | — | $0.05 | — | not_run |
| `der_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `no_spill` | FAIL (arith_need_compare) | 8 | — | — | $0.06 | — | not_run |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `ask_both` | PASS (R4, best R4) | 4 | — | — | $0.42 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `auto` | PASS (R2, best R2) | 2 | — | — | $0.18 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `fast_fail` | PASS (R1, best R1) | 1 | — | — | $0.08 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `no_spill` | PASS (R2, best R2) | 2 | — | — | $0.20 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ask_both` | PASS (R1, best R1) | 1 | — | — | $0.10 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `auto` | PASS (R2, best R2) | 2 | — | — | $0.20 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `fast_fail` | PASS (R2, best R2) | 2 | — | — | $0.20 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `no_spill` | PASS (R1, best R1) | 1 | — | — | $0.12 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `ask_both` | PASS (R4, best R4) | 4 | — | — | $0.53 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `auto` | PASS (R3, best R3) | 3 | — | — | $0.40 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `fast_fail` | PASS (R7, best R7) | 7 | — | — | $1.30 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `arm64` | `no_spill` | PASS (R3, best R3) | 3 | — | — | $0.42 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `ask_both` | PASS (R5, best R5) | 5 | — | — | $0.48 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `auto` | PASS (R4, best R4) | 4 | — | — | $0.49 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `fast_fail` | PASS (R5, best R5) | 5 | — | — | $0.61 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `google/gemini-4-neon` | `x86_64` | `no_spill` | PASS (R5, best R5) | 5 | — | — | $0.71 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `ask_both` | PASS (R1, best R1) | 1 | — | — | $0.16 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `auto` | PASS (R5, best R5) | 5 | — | — | $1.20 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `fast_fail` | PASS (R3, best R3) | 3 | — | — | $0.58 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `no_spill` | PASS (R4, best R4) | 4 | — | — | $0.84 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ask_both` | PASS (R3, best R3) | 3 | — | — | $0.60 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `auto` | PASS (R3, best R3) | 3 | — | — | $1.03 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `fast_fail` | PASS (R4, best R4) | 4 | — | — | $0.86 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `no_spill` | FAIL (arith_need_entail) | 8 | — | — | $2.22 | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ask_both` | FAIL (compile_or_parse_error) | 8 | — | — | $0.33 | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `auto` | PASS (R4, best R4) | 4 | — | — | $0.15 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `fast_fail` | PASS (R6, best R6) | 6 | — | — | $0.28 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `no_spill` | FAIL (arith_need_entail) | 8 | — | — | $0.37 | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ask_both` | FAIL (arith_need_entail) | 8 | — | — | $0.32 | — | not_run |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `auto` | PASS (R5, best R5) | 5 | — | — | $0.21 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `fast_fail` | PASS (R3, best R3) | 5 | 0.49 -> **0.49** | 439 B | $0.36 | shown | NATIVE_PASS 257/257 |
| `der_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `no_spill` | PASS (R8, best R8) | 8 | — | — | $0.31 | shown | NATIVE_PASS 257/257 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `ask_both` | PASS (R1, best R1) | 3 | 0.83 -> **0.83** | 2 B | $0.99 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `auto` | PASS (R1, best R3) | 3 | 0.83 -> **0.54** | 4 B | $0.84 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `fast_fail` | PASS (R1, best R1) | 3 | 0.83 -> **0.83** | 2 B | $0.94 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `arm64` | `no_spill` | PASS (R1, best R3) | 3 | 0.83 -> **0.67** | 4 B | $0.88 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `ask_both` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $1.21 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `auto` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $1.46 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `fast_fail` | PASS (R2, best R3) | 4 | 1.00 -> **0.75** | 4 B | $1.34 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-fable-5.2` | `x86_64` | `no_spill` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $1.38 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `ask_both` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `auto` | PASS (R3, best R3) | 5 | 0.92 -> **0.92** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `fast_fail` | PASS (R3, best R4) | 5 | 0.92 -> **0.75** | 4 B | $0.02 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `arm64` | `no_spill` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `ask_both` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `auto` | PASS (R5, best R5) | 7 | 1.00 -> **1.00** | 2 B | $0.03 | refused | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `fast_fail` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-haiku-5.5` | `x86_64` | `no_spill` | PASS (R1, best R1) | 3 | 1.00 -> **1.00** | 2 B | $0.01 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `ask_both` | PASS (R1, best R3) | 3 | 0.92 -> **0.75** | 4 B | $0.15 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `auto` | PASS (R1, best R3) | 3 | 0.92 -> **0.42** | 8 B | $0.15 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `fast_fail` | PASS (R1, best R2) | 3 | 0.92 -> **0.83** | 2 B | $0.14 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `arm64` | `no_spill` | PASS (R1, best R3) | 3 | 0.83 -> **0.79** | 4 B | $0.15 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `ask_both` | PASS (R1, best R3) | 3 | 1.00 -> **1.00** | 2 B | $0.18 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `auto` | PASS (R2, best R4) | 4 | 1.50 -> **1.00** | 4 B | $0.24 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `fast_fail` | PASS (R1, best R1) | 3 | 1.00 -> **1.00** | 2 B | $0.18 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `anthropic/claude-sonnet-5.5` | `x86_64` | `no_spill` | PASS (R1, best R2) | 3 | 1.00 -> **1.00** | 2 B | $0.18 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `ask_both` | FAIL (arith_need_entail) | 8 | — | — | $1.47 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `auto` | PASS (R6, best R8) | 8 | 0.50 -> **0.46** | 8 B | $1.46 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `fast_fail` | FAIL (other) | 8 | — | — | $1.42 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `arm64` | `no_spill` | PASS (R6, best R6) | 8 | 0.50 -> **0.50** | 4 B | $1.32 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `ask_both` | FAIL (spec_need_open) | 8 | — | — | $1.05 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `auto` | FAIL (other) | 8 | — | — | $1.14 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `fast_fail` | FAIL (other) | 8 | — | — | $1.03 | — | not_run |
| `ipv4_valid` | `google/gemini-4-neon` | `x86_64` | `no_spill` | FAIL (spec_need_open) | 8 | — | — | $1.16 | — | not_run |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `ask_both` | PASS (R3, best R5) | 5 | 0.83 -> **0.54** | 4 B | $0.57 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `auto` | PASS (R1, best R3) | 3 | 0.62 -> **0.54** | 4 B | $0.51 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `fast_fail` | PASS (R3, best R3) | 5 | 0.83 -> **0.83** | 2 B | $0.47 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `arm64` | `no_spill` | PASS (R1, best R3) | 3 | 0.62 -> **0.54** | 4 B | $0.33 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `ask_both` | PASS (R5, best R5) | 7 | 1.00 -> **1.00** | 2 B | $0.67 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `auto` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.66 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `fast_fail` | PASS (R5, best R6) | 7 | 1.00 -> **0.75** | 4 B | $0.76 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `openai/gpt-6.2-astra-pro` | `x86_64` | `no_spill` | PASS (R8, best R8) | 8 | — | — | $1.07 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `ask_both` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.14 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `auto` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.15 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `fast_fail` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.11 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `arm64` | `no_spill` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.16 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `ask_both` | PASS (R2, best R4) | 4 | 1.00 -> **1.00** | 2 B | $0.13 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `auto` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.13 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `fast_fail` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.10 | shown | NATIVE_PASS 607/607 |
| `ipv4_valid` | `qwen/qwen3.8-2.4t-a95b` | `x86_64` | `no_spill` | PASS (R2, best R2) | 4 | 1.00 -> **1.00** | 2 B | $0.15 | shown | NATIVE_PASS 607/607 |

## Failing Round Breakdown

Each row counts failing rounds across all cells by root-cause category.

| Failure category | Failing rounds |
| --- | --- |
| `other` | 396 |
| `compile_or_parse_error` | 391 |
| `arith_need_entail` | 244 |
| `spec_need_open` | 38 |
| `arith_need_compare` | 25 |
| `trace_refusal` | 8 |
| `calling_syntax_error` | 7 |
| `output_token_limit` | 7 |
| `place_error` | 5 |
| `isa_table_error` | 4 |
