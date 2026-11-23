# Proposal: verifying recursive functions and the final four functions of BLAKE3

*Status (23 November 2026): written proposal, awaiting approval before any implementation in `proof-core/`.*

## 1. What is left to reach 100% of single-threaded BLAKE3

The single-threaded Ode BLAKE3 hash (`kcheck/b3hashr.o`) consists of 14 functions and 3,761 x86-64 instructions. As of commit `9c32c8c4`, the Lean 4 verifier (`proof-core`, `odeverify`) verifies 10 of those 14 functions, covering 3,098 of the 3,761 instructions (82.4%).

The table below lists all 14 functions in `kcheck/b3hashr.o`. Each row gives the function's symbol name, how many instructions it contains, whether `odeverify` verifies it today, and what is missing for the four functions that remain.

| Function | Instructions | Verified in Lean 4 today? | What is needed to verify it |
|---|---:|---|---|
| `b3l_pad` | 39 | Yes | — |
| `b3l_chunk_node` | 81 | Yes | — |
| `b3l_node_out` | 18 | Yes | — |
| `b3l_wide32` | 259 | Yes | — |
| `b3l_wide128` | 670 | Yes | — |
| `blake3_servil_compress_in_place_avx512` | 76 | Yes | — |
| `blake3_servil_compress_in_place_sse41` | 94 | Yes | — |
| `blake3_servil_avx512_k32` | 702 | Yes | — |
| `blake3_servil_avx512_p32` | 699 | Yes | — |
| `blake3_servil_avx512_p16` | 460 | Yes | — |
| `b3l_take` | 133 | No | Self-recursion (`decreases`), `bits(...)` stack budget, `cvs` array precondition, two-variable linear precondition |
| `b3l_part32` | 76 | No | Passing a stack array of 32 chaining values to `b3l_take`, two-variable linear precondition |
| `b3l_subtree` | 189 | No | Self-recursion (`decreases`), `bits(...)` stack budget, two-variable linear precondition |
| `b3l_hashr` | 265 | No | `bits(...)` stack budget, passing stack `kf` and `cvs` to `b3l_take` and `b3l_subtree` |
| **Total (14 functions)** | **3,761** | **10 of 14 (3,098 = 82.4%)** | **4 remaining (663 = 17.6%)** |

Notice that all four remaining functions are already verified by the Python prototype in `kcheck/`, and their contracts are already written in `kcheck/blake3.spec` and `kcheck/proofs/inner.spec`. None of them requires any new x86-64 instructions or any change to the processor model (`Machine.lean`) or the trace model (`Trace.lean`). Even the doubling loop that finds where a BLAKE3 tree splits (`left_chunks`) is already verified in `proof-core` (`proof-core/test_doubling.py`).

What is missing in `proof-core` is four small contract and verification rules. This proposal describes each one with a concrete example, explains why it is needed, evaluates simpler alternatives, and asks for a decision before changing `proof-core/`.

---

## 2. A concrete example: how `b3l_subtree` and `b3l_take` work

In BLAKE3 (`kcheck/blake3.spec`), a message longer than one 1,024-byte chunk is split into two parts:

- The left part has `k` full chunks, where `k` is the largest power of two such that `1024 * k < len(bytes)`.
- The right part has the remaining `len(bytes) - 1024 * k` bytes.

The specification defines the chaining value of any slice of bytes recursively:

```
def left_chunks(bytes) { the greatest power of two k with 1024 * k < len(bytes) }

def children(key, flags, t, bytes) {
    let k = left_chunks(bytes)
    subtree(key, flags, t, bytes[0 .. 1024 * k])
      ++ subtree(key, flags, t + k, bytes[1024 * k .. len(bytes)])
}

def subtree(key, flags, t, bytes) {
    if len(bytes) <= 1024 then node_value(chunk_node(key, t, flags, bytes), 0)
    else compress(key, children(key, flags, t, bytes), counter(0), 64, flags | PARENT)
}
```

Take a concrete message of 3,073 bytes (three full 1,024-byte chunks plus 1 extra byte):

1. `left_chunks` is `2`, because `1024 * 2 = 2048 < 3073`, while the next power of two gives `1024 * 4 = 4096 >= 3073`.
2. The left part has `2048` bytes (chunks `t` and `t + 1`).
3. The right part has `3073 - 2048 = 1025` bytes (chunks `t + 2` and `t + 3`).
4. Both parts are strictly shorter than `3073` bytes (`2048 < 3073` and `1025 < 3073`), so recursing on each part always terminates.

The compiled function `b3l_subtree` follows this exact definition. Its contract in `kcheck/proofs/inner.spec` is:

```
contract b3l_subtree(out: cv, input: len bytes, len: number, kf: keyed, t: number, plat: any) {
    requires no_overlap(out, input, kf)
    requires len >= 1
    requires 1024 * t + len <= 18446744073709551615
    ensures out = subtree(kf.key, kf.flags, t, input)
    trace depends on len, t, plat
    decreases len
    stack 16896 + 384 * bits((len - 1) / 1024)
    needs sse41
    needs avx512 if plat == 5
}
```

For medium messages between 2 and 32 chunks (`1025 <= len <= 32768`), `b3l_part32` (and the top-level entry point `b3l_hashr`) first calls the 32-lane AVX-512 chunk kernel `blake3_servil_avx512_k32` once to compute the chaining values of all full chunks into a 1,024-byte stack buffer `cvs`. It then hands `cvs` to `b3l_take`, which walks the same binary tree recursively and reads precomputed full-chunk values directly out of `cvs` instead of compressing them again:

```
contract b3l_take(out: cv, input: len bytes, len: number, kf: keyed, t: number, cvs: cvs) {
    requires no_overlap(out, input, kf, cvs)
    requires len >= 1
    requires 1024 * t + len <= 18446744073709551615
    requires cvs[i] == node_value(chunk_node(kf.key, t + i, kf.flags, input[1024 * i .. 1024 * i + 1024]), 0)
        for i in 0..len / 1024
    ensures out = subtree(kf.key, kf.flags, t, input)
    trace depends on len, t
    decreases len
    stack 640 + 384 * bits((len - 1) / 1024)
    needs sse41
    needs avx512
}
```

Finally, `b3l_hashr` (`kcheck/blake3.spec`) is the entry point that an auditor reads:

```
contract b3l_hashr(out: 32 bytes, input: len bytes, len: number, key: 32 bytes, flags: byte, plat: any) {
    requires no_overlap(out, input, key)
    ensures out = bytes_of(hash_words(words(key), flags, input))
    trace depends on len, flags, plat
    stack 18688 + 384 * bits(len / 1024)
    needs sse41
    needs avx512 if plat == 5
}
```

Every rule proposed below comes directly from a line in those three contracts.

---

## 3. The four proposed additions to `proof-core`

### Addition 1: Direct self-recursion with a `decreases` line

**What the rule is today.** Today `proof-core` verifies a list of functions from bottom to top (`verdictFrom` in `proof-core/Core.lean`). Each function may call only functions listed earlier in the file. A function cannot call itself.

**What is proposed.** A contract may carry an optional `decreases E` line, where `E` is a whole-number expression over the function's arguments (for both `b3l_take` and `b3l_subtree`, `E` is simply `len`).

- When verifying a function whose contract includes `decreases E`, the verifier adds the function's own contract to its table of callable functions while checking its body.
- At every call to itself, in addition to checking all ordinary call preconditions, the verifier checks two inequalities using its existing linear arithmetic rule:
  1. `0 <= E_callee` (the measure at the recursive call is not negative), and
  2. `E_callee < E_caller` (the measure at the recursive call is strictly smaller than at entry).
- A function without a `decreases` line still cannot call itself. Mutual recursion (function A calling function B which calls function A) is not added.

**Why the soundness proof stays small.** In `proof-core/SoundTop.lean`, `verdictFrom_sound` and `verdictFrom_trace_sound` currently step through the list of functions one by one. For a function with `decreases E`, that single step uses strong mathematical induction (`Nat.strongRecOn`) on the natural number `E`: assuming the function meets its contract and its two-run trace promise for all entry states with strictly smaller `E`, `verifyOne_sound` and `verifyOne_trace_sound` establish both properties at `E`. Because `E` is a natural number that drops strictly on every recursive call, infinite recursion is impossible, so the plain-machine termination theorem (`EndsP`) holds with no new Lean axioms.

**Note on `trace depends on` with recursion.** At a recursive call, two runs that agree on the caller's `trace depends on` values must follow the same branch into the call and pass the same `trace depends on` values to the callee. Because `len` is listed in `trace depends on` for both `b3l_take` and `b3l_subtree`, the two runs enter the recursive call with equal `len` (hence the same induction step `E`), so the strong-induction hypothesis applies directly to both `Meets` and `TraceOk`.

---

### Addition 2: Stack budgets of the form `base + step * bits(expr)`

**What the rule is today.** Today a contract's stack budget (`Contract.stack` in `proof-core/Contract.lean`) is a single fixed constant number of bytes, such as `stack 8192`.

**Why a fixed constant cannot verify a recursive function.** Suppose a recursive function `f` uses 336 bytes of stack frame before calling itself, and its contract declares a fixed constant `stack S`. At the recursive call, the verifier must check:

```
caller_frame_used + callee_stack_budget <= caller_stack_budget
```

With a constant `S`, that inequality becomes `336 + S <= S`, which is always false! A recursive function cannot fit its own constant stack budget inside itself unless the budget decreases with recursion depth.

**What is proposed.** Allow a contract's `stack` line to be either:
- a fixed constant `N` (unchanged from today), or
- `base + step * bits(expr)`, where `base` and `step` are fixed non-negative constants, `expr` is a linear quotient over entry arguments (such as `(len - 1) / 1024` or `len / 1024`), and `bits(n)` is the number of binary digits of a non-negative integer `n`:
  - `bits(0) = 0`,
  - for `n >= 1`, `bits(n) = floor(log2(n)) + 1` (the smallest `d` with `n < 2^d`).

**Why checking `bits(...)` stays simple on BLAKE3's code.** Let `c = (len - 1) / 1024` for a message with `len > 1024`, so `c >= 1`. In `b3l_take` and `b3l_subtree`, the doubling loop finds the unique power of two `k = 2^m` such that `2^m <= c < 2^(m+1)`. On that path:

- For the caller: `2^m <= c < 2^(m+1)`, so `bits(c) = m + 1`.
- For the left recursive call (`len_left = 1024 * 2^m`): `(len_left - 1) / 1024 = 2^m - 1 < 2^m`, so `bits((len_left - 1) / 1024) = m = bits(c) - 1`.
- For the right recursive call (`len_right = len - 1024 * 2^m`): since `len - 1 < 1024 * 2^(m+1)`, we have `len_right - 1 < 1024 * 2^m`, so `(len_right - 1) / 1024 < 2^m`, and therefore `bits((len_right - 1) / 1024) <= m = bits(c) - 1`.

Both recursive calls drop `bits(...)` by at least 1! Because `proof-core` already splits the doubling loop into its 54 concrete paths (`m = 0, 1, ..., 53`, as proved in `proof-core/test_doubling.py`), on path `m` the caller's budget is the concrete number `base + step * (m + 1)` and each recursive call needs at most `base + step * m`. Checking that the caller's frame (336 bytes) fits inside the difference `step = 384` bytes reduces to ordinary integer arithmetic.

For `b3l_hashr`, which accepts `len == 0` as well as `len >= 1`, the contract writes `stack 18688 + 384 * bits(len / 1024)`. When `len >= 1`, `(len - 1) / 1024 <= len / 1024`, so by monotonicity of `bits` (`a <= b -> bits(a) <= bits(b)`), `bits((len - 1) / 1024) <= bits(len / 1024)`, and the call from `b3l_hashr` to `b3l_subtree` or `b3l_take` checks cleanly.

No general logarithm solver is needed in the verifier. Only two elementary rules about `bits` enter `Core.lean` and `SoundLin.lean`:
1. Bounds from a power of two: `0 <= x < 2^d -> bits(x) <= d`, and `2^d <= x -> d + 1 <= bits(x)` (for `d <= 64`).
2. Monotonicity: `0 <= x <= y -> bits(x) <= bits(y)`.

---

### Addition 3: A read-only array of precomputed values (`requires cvs[i] == ... for i in 0..count`)

**What the rule is today.** Today a contract can describe:
- a read-only run of bytes of variable length (`input: len bytes`),
- a read-only run of bytes of fixed length (`kf: keyed`, 40 bytes),
- a table of fixed-count pointers (`ptrs: 32 inputs`), and
- an output buffer written by the function (`out: cv`, 32 bytes).

It cannot express a read-only array whose length depends on `len` and whose `i`-th 32-byte entry is already promised by the caller to equal a specification expression `E(i)` — which is exactly what `b3l_take`'s `cvs` argument is:

```
requires cvs[i] == node_value(chunk_node(kf.key, t + i, kf.flags, input[1024 * i .. 1024 * i + 1024]), 0)
    for i in 0..len / 1024
```

**What is proposed.** Add a read-only value-array argument kind to `Contract.lean`: an argument `A` pointing to `count` consecutive 32-byte entries (`32 * count` bytes in memory, non-overlapping with every output buffer and the stack frame), together with a specification template `E(i)` that gives the value of entry `i` for every `0 <= i < count`.

The verifier uses such an array in three exact places (matching `b3l_part32`, `b3l_hashr`, and `b3l_take`):

1. **Creating it at a call (`b3l_part32` or `b3l_hashr` calling `b3l_take`).** The caller has a stack buffer `cvs` filled by `blake3_servil_avx512_k32`. Since commit `9c32c8c4`, `Core.lean` already tracks the 8-word symbolic value of every 32-byte slot written into the caller's stack frame (`frameCellWords`). At the call, the verifier checks that `32 * count` lies within the stack buffer and that each slot `i` in `0..count` holds the 8 words of `E(i)`.
2. **Slicing it across recursive calls (`b3l_take` calling `b3l_take`).**
   - For the left call (`cvs`, length `1024 * k`, counter `t`): slots `0..k` of the caller's `cvs` satisfy `E(i)` directly because `k <= len / 1024`.
   - For the right call (`cvs + 32 * k`, length `len - 1024 * k`, counter `t + k`): slot `j` of the shifted pointer is slot `k + j` of the caller's `cvs`, and substituting `i = k + j` in `E(i)` yields `t + (k + j) = (t + k) + j` and `input[1024 * (k + j) ..] = (input[1024 * k ..])[1024 * j ..]`.
3. **Reading an entry at a leaf (`b3l_take` when `len == 1024`).** When `b3l_take` loads 32 bytes from `cvs + 0` (via two 16-byte `movups` loads) and copies them to `out`, the verifier checks `0 < len / 1024` (which holds when `len == 1024`, since `1024 / 1024 = 1`) and returns the symbolic 8 words of `E(0)`, which match `subtree(kf.key, kf.flags, t, input)` when `len == 1024`.

---

### Addition 4: Multi-variable linear entry preconditions (`requires 1024 * t + len <= 2^64 - 1`)

**What the rule is today.** Today `Contract.lean` has two single-variable numeric precondition lists: `bounds` (`x < b`) and `atLeast` (`k <= x`). Those cannot state a relation between two arguments, such as:

```
requires 1024 * t + len <= 18446744073709551615
```

which appears in `b3l_take`, `b3l_part32`, and `b3l_subtree` to guarantee that chunk counters `t + i` stay within 64 bits across the subtree.

**What is proposed.** Add a list of linear inequalities over entry arguments (`c + a_1 * r_1 + ... + a_k * r_k >= 0`) to `Contract.pre`. (Over time, this single field can also replace both `bounds` and `atLeast`, shrinking `Contract.lean`.)

- At function entry, each linear precondition is added directly to the verifier's linear-fact list `s.facts`.
- At a call site, each linear precondition of the callee is checked by substituting the caller's symbolic rows for the callee's argument registers and running the existing `entails` check.
- In `SoundState.lean` and `SoundCall.lean`, the soundness proof is identical in shape to the existing proofs for `bounds` and `atLeast`.

---

## 4. What does not change

To keep the verifier small and Bob's reading list short, the following are deliberately kept out of this proposal:

- **No change to the processor model (`Machine.lean`) or instruction tables (`core/x86.tab`, `arm64/arm64.tab`).** Every instruction in `b3l_take`, `b3l_part32`, `b3l_subtree`, and `b3l_hashr` is already in `core/x86.tab`.
- **No change to the trace semantics (`Trace.lean`).** `Ode.verify_all_trace` and `Ode.verify_all_result` keep their exact statements on `traceAgree` and `EndsP`.
- **No mutual recursion between compiled functions.** Only direct self-recursion with a `decreases` line is added.
- **No change to the top-level contract of `b3l_hashr` in `kcheck/blake3.spec`.** An auditor reads the same 8-line contract (6 clauses) that is already written there.
- **No new Lean axioms and no `maxHeartbeats` overrides.** All theorems in `SoundTop.lean` continue to depend only on `[propext, Classical.choice, Quot.sound]`.

---

## 5. Alternatives considered and tradeoffs

### Alternative A: Replace recursion in BLAKE3 with an explicit loop and a stack array

Instead of adding self-recursion to the verifier, `b3l_subtree` and `b3l_take` could be rewritten as an iterative loop maintaining an explicit 54-entry stack of chaining values (the way the Rust crate does).

- **Upside:** The verifier would not need `decreases` on contracts or `bits(...)` stack budgets.
- **Downside:** Proving an iterative stack-based tree merger equivalent to BLAKE3's recursive specification `subtree` requires a substantial loop invariant relating the partial stack of chaining values to the binary decomposition of the chunk count (hundreds of lines of inductive tree lemmas, as seen in the earlier November proof of `CvStack::merge`). By contrast, the recursive `b3l_subtree` matches the specification `subtree` line for line in 189 instructions, and direct self-recursion is also generally useful for other divide-and-conquer programs in Ode.
- **Recommendation:** Keep the recursive implementation and add direct self-recursion to `proof-core`.

### Alternative B: Use a fixed constant stack bound instead of `bits(...)`

Could `b3l_hashr`, `b3l_subtree`, and `b3l_take` simply declare a fixed constant stack limit large enough for any 64-bit input (such as `stack 40960`)?

- **Why this does not work for recursive contracts:** As shown in section 3 (Addition 2), a recursive function with constant stack budget `S` and non-zero frame size `F` cannot satisfy `F + S <= S` at its recursive call. The stack budget of a recursive function *must* depend on a decreasing quantity (here `bits((len - 1) / 1024)`). Using `bits(...)` also gives callers a much tighter guarantee for small inputs (for a 1 KiB message, `b3l_hashr` uses at most 18,688 bytes rather than 40 KiB).
- **Recommendation:** Add `base + step * bits(expr)` stack budgets.

### Alternative C: Inline `b3l_take` into `b3l_part32` instead of adding `cvs` preconditions

Could we avoid Addition 3 (`requires cvs[i] == ...`) by avoiding `b3l_take` altogether?

- **Why this does not eliminate the issue cleanly:** `b3l_part32` handles any input between 2 and 32 chunks (`1025 <= len <= 32768`), which has 31 different tree shapes depending on `len`. Both `b3l_part32` and `b3l_hashr` call `b3l_take` to fold the 2..32 precomputed chunk chaining values from `k32` into the exact BLAKE3 binary tree. Without `cvs`, either `b3l_part32` would have to unroll 31 separate tree shapes (blowing up code size) or re-compress chunks one by one (losing the 32-way AVX-512 speedup on 2 KiB..32 KiB inputs).
- **Recommendation:** Add the read-only `cvs` value-array precondition so `b3l_take` stays compact and fast.

---

## 6. Planned stages and verification checks (after approval)

If approved, implementation will proceed in three small, separately verified commits:

1. **Stage 1 — Self-recursion, `bits(...)` stack budgets, and linear entry preconditions:**
   - Extend `Contract.lean`, `Core.lean`, `Reader.lean`, `SoundState.lean`, `SoundCall.lean`, `SoundTop.lean`, and `statement.py` / `prove.py`.
   - Test on a small standalone recursive example first (with positive and negative controls: missing `decreases`, non-decreasing recursive call, insufficient `step` in `bits(...)` stack budget, and violated linear precondition).
   - Verify `test_sound.py` (standard axioms only, zero `sorry`, zero `maxHeartbeats`) and re-measure the 14-job verification basket in `paper/REVIEW.md`.
2. **Stage 2 — Read-only `cvs` array precondition + `b3l_take` and `b3l_part32`:**
   - Add `cvs` precondition support and soundness proofs (`SoundCallW.lean`, `SoundSpecW.lean`).
   - Verify shipped `b3l_take` (133 instructions) and `b3l_part32` (76 instructions) from `kcheck/b3hashr.o` in Lean 4, with negative controls (wrong slice offset, missing chunk entry, wrong counter shift).
   - Coverage reaches 12 of 14 functions (3,307 of 3,761 instructions = 87.9%).
3. **Stage 3 — `b3l_subtree` and `b3l_hashr` (100% of single-threaded BLAKE3 in Lean 4):**
   - Verify shipped `b3l_subtree` (189 instructions) and `b3l_hashr` (265 instructions) from `kcheck/b3hashr.o` in Lean 4, with negative controls and end-to-end check against the 105 official BLAKE3 test vectors.
   - Coverage reaches **14 of 14 functions (3,761 of 3,761 instructions = 100%)**.
   - Update `paper/ODE.md`, `paper/REVIEW.md`, and add the four new functions to the verification basket.

---

## 7. Decisions requested

No code for these four additions has been written in `proof-core/` yet. Please confirm yes or no on each:

1. **Direct self-recursion with `decreases E`** (strong induction in `SoundTop.lean`; no mutual recursion between compiled functions).
2. **Stack budgets of the form `base + step * bits(expr)`** (fixed `stack N` kept as the `step = 0` case).
3. **Read-only value-array preconditions `requires A[i] == E(i) for i in 0..count`** (for `cvs` in `b3l_take`).
4. **Multi-variable linear entry preconditions** (`requires 1024 * t + len <= 2^64 - 1`, generalizing `bounds` and `atLeast`).
