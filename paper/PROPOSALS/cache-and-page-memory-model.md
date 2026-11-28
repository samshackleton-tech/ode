# Proposal: Cache-Line- and Page-Oriented Memory Model (Phases 1–3)

## 1. Motivation: Hardware Memory Reality vs. Arbitrary Width Traps

Real x86-64 and AArch64 processors do not organize memory around arbitrary access-width categories. They organize memory around two orthogonal dimensions:

1. **Coherence, locality, and protection boundaries (cache lines and virtual memory pages):**
   - **Cache lines (`64 B` on x86-64 / Neoverse, `128 B` on Apple Silicon)** are the unit of coherence, ownership, spatial locality, and prefetching. Two cores writing different fields inside the same cache line suffer false sharing; an access crossing a cache-line boundary pays a split-line penalty; a streaming output that writes full cache lines benefits from write-only / non-temporal intent (avoiding Read-For-Ownership traffic).
   - **Virtual memory pages (`4 KiB` on x86-64 / Linux, `16 KiB` on Apple Silicon, `2 MiB` hugepages)** are the unit of mapping, permission enforcement, guard pages, and TLB coverage.
   - **Dynamic access patterns** — active stream count, stride, store-to-load forwarding across widths, and working-set footprint in cache lines and pages — determine real-world throughput far more than single-instruction latency.
2. **Register transfer widths (`1, 2, 4, 8, 16, 64 B`):**
   - Given a readable or writable region, the processor loads and stores at whatever register width fits within bounds.

Currently, `proof-core/Core.lean` conflates these two dimensions across five ad-hoc buffer paths (`regions`, `fixeds`, `inouts`, `outs`, `frame` vs. `frameW`):

- Fixed-size read-only buffers (`fixeds`) allow `8 B` (`Known.load`) and `16 B`/`64 B` (`Node.input`), but refuse `4 B` scalar loads (`buf.u32(off)`).
- In-out word buffers (`inouts`) allow `16 B`/`64 B` vector loads before the first write, but refuse `4 B` and `8 B` scalar loads (`h.u32(off)`, `h.u64(off)`) and refuse reads after partial writes even though `s.wroteW` already tracks every written word.
- The stack frame allows `8 B` scalar writes followed by `16 B` vector reads (`framePairRows`, which is actually a 15+ cycle store-to-load forwarding stall on real CPUs!), while refusing `16 B` vector writes followed by `4 B`/`8 B` scalar reads (`frameW`), and refusing `4 B` scalar stores (`out.u32(off) := x`, `stack.u32(off) := x`).

Across the 69 failing programs from cold-room suites `hl-default-v10` and `hl-default-v11`, **5 failures** hit these exact asymmetries directly:
- 3× `buf.u32(off)` on fixed-size input word buffers (`blake3_compress_4way`, `sha256_4way`),
- 1× `h.u64(off)` on an in-out word buffer (`blake3_compress1`),
- 1× `hb.u64(off)` reading stack slots written by `hb.u32x4(0) := ...` (`blake3_compress1`).

---

## 2. Core Principle: Separate Region Roles & Geometry from Access Width

Every memory region in Ode has four orthogonal properties:

| Property | Meaning | Hardware Correspondence |
| --- | --- | --- |
| **Extent `(base, len)`** | Fixed byte count `K` or runtime length `n` | Bounds & guard-page safety |
| **Alignment `align A`** | Power-of-two base alignment (`1, 16, 64, 128, 4096, 16384`) | Cache-line / page boundaries, non-temporal & aligned SIMD |
| **Access / sharing role** | `read` (shared), `inout` (exclusive RW), `write` (exclusive write-only) | MESI/MOESI cache states (`S`, `E/M`, streaming / no-RFO) |
| **Value view** | Uniform across `1/2/4/8/16/64 B` via one `Row ↔ Tab` bridge | Machine register transfers with zero arbitrary width traps |

Crucially, separating **role** from **width** preserves the hardware-meaningful guarantees:
- A pure `write` output region remains unreadable before a word or byte is written to it, preserving exclusive streaming / no-RFO intent and preventing reads of stale memory.
- A `read` region remains read-only and freely shareable across threads.
- An `inout` region is exclusive read-write and disjoint from every other buffer, readable and writable at any supported width both before and after partial writes.
- A hardware microarchitectural hazard such as narrow-store → wide-load store-forwarding stall belongs in **`ode advise`**, not as an arbitrary soundness refusal (and conversely, functional soundness permits any width-consistent access while `ode advise` flags real forwarding or split-line penalties).

---

## 3. Three-Phase Rollout

### Phase 1 — Uniform Word Access Widths & Bidirectional `Row ↔ Tab` Bridge (Immediate)

#### 3.1 One New `Known` Constructor: `Known.termVal`

Today `Core.lean` bridges `Row → Tab` (`wAtom`: turns any linear `Row` into `Node.atom (Lin.word r)`), but has no dual bridge `Tab → Row`. Phase 1 adds one constructor to `Known`:

```lean
| termVal (v id : Nat)   -- ρ v = (den (inpOf ctx s0) ρ T id : Int)  (with 0 ≤ ρ v < 2^32)
```

- **Acyclic soundness:** when `valOfTerm s id` allocates a fresh scalar variable `v := s.nvars`, `id < s.terms.length` only references variables `< s.nvars` (`WordsWF.atoms`). Extending `ρ` with `ρ v := den (inpOf ctx s0) ρ s.terms id` via `Carried.fresh` is strictly acyclic and immediately yields `0 ≤ ρ v < 2^32` (recorded via `Known.word32 v (v + 1)` plus linear range facts `0 ≤ v ≤ 2^32 - 1`).
- **Canonical reuse:** if `s.tab.arr[id]? = some (.atom r)` with `isWord32Row s r`, `valOfTerm` returns `r` directly without allocating a variable; if `Known.termVal v id` already exists in `s.known`, `valOfTerm` reuses `Lin.var v` so repeated loads of the same word denote the exact same variable.
- **Lossless round-trip (`Tab → Row → Tab`):**
  - `atomId` checks `knownVarTerm v s.known` when `r = Lin.var v` (after `Lin.word`), resolving `Lin.var v` straight back to `id` with zero duplicate `Node.atom`.
  - `wAtomKnown s.known r t` resolves single `termVal` variables (and linear combinations of `termVal` variables mod $2^{32}$) directly into existing `Tab` IDs / `Node.add` nodes, so scalar 32-bit arithmetic on loaded words and SIMD 32-bit arithmetic produce identical `Tab` terms.

#### 3.2 Unified Word-Backed Loads (`symLoadWords` + `valOfTerm`)

1. **Read-after-write on `outs` / `inouts` in `symLoadWords`:** when `addr` hits `outs[w]` at constant 4-byte-aligned offset `c` within bounds, if `w ∈ s.intact` and `w` is an `inout`, intern `Node.input j (c/4 + i)` as before; otherwise look up each word `(w, c/4 + i)` in `s.wroteW` (succeeding if all `width` words are known in `s.wroteW` — covering both `inout` after partial writes and `write` buffers after those words have been written!).
2. **Scalar `mem32` and `mem64` loads via `symLoadWords`:**
   - Keep the existing `s.frame.lookup c` fast path for 8-byte scalar stack slots.
   - Keep `Known.load` strictly for 8-byte pointer-table loads (`tableAt` entries such as `blocks: 16 pointers`, where `findLane` expects a single 64-bit address variable) and `mbounds`-constrained 8-byte fixed entries (preserving all existing AVX-512 and counter proofs intact).
   - For all other 4-byte (`size = 4`) or 8-byte (`size = 8`) loads hitting `fixeds`, `inouts`/`wroteW`, `frameW`, or `valArrays`: delegate directly to `symLoadWords ctx s addr (size / 4)` and convert the resulting 1 or 2 word IDs via `valOfTerm`:
     - `size = 4` → `[id0]` → `Lin.var v0`.
     - `size = 8` → `[id0, id1]` → `Lin.add (Lin.var v0) (Lin.scale W32i (Lin.var v1))`.
   - Returning `v0 + 2^32 * v1` gives cross-width coherence automatically: `(x & 0xFFFFFFFF)` evaluates to `v0`, `(x >> 32)` evaluates to `v1` with zero `Known.div`, and a subsequent `buf.u32(off + 4)` returns the exact same `v1`.
3. **Symmetric 4-byte scalar stores (`symStore4`):**
   - To `outs[w]` at 4-byte-aligned constant offset `c` (when no byte-wise `s.wrote` exists on `w`): `s.touch ctx w`, convert `x` to 1 word term via `wAtomKnown`, and `rememberStore ... w (c / 4) [lo.1]`.
   - To stack `frame` at 4-byte-aligned `c` (`sp ≤ c`, `c + 4 ≤ 0`, `-(stack) ≤ c`): write `(c, lo.1)` into `s.frameW` and clear any overlapping 8-byte `s.frame` entry.
   - Wire `buf.u32(off) := expr` in `lang/ode_hl.py` (1-to-1 `mov dword ptr [addr], r32` / `str w, [addr]`, zero new ISA rows).
4. **Trace safety (`Trace.lean` & `publicLoad`):**
   - `Trace.lean` is already parametric over `memSize`/`memWidth`.
   - `publicLoad` already permits non-hidden `fixeds` at any `size` within bounds, and conservatively marks reads from `outs` and `frameW` (`publicLoad = false`), matching vector spill handling.
5. **Store-to-load forwarding hazard diagnostic in `ode advise`:**
   - Scan decoded loops for overlapping stack-slot stores and loads where the load is strictly wider than the store (e.g., `8 B` store followed by `16 B` load to an overlapping `[rsp+o]` / `[sp+o]` address) and emit an explicit microarchitectural stall warning.

#### 3.3 Extensibility Payoff from Phase 1

- **Vector-to-scalar lane extraction** (`movd`/`pextrd` on x86-64, `umov w, v.s[k]` on AArch64) becomes a 2-line call (`symLane` → `valOfTerm`) whenever needed — directly helpful for hybrid scalar/SIMD kernels (BLAKE3 finalization, ChaCha20 tail, Brotli/LZ4).
- **Zero new proof-file tags and zero new ISA table rows:** completely deterministic for Bob's verifier.
- **Meter 2 impact:** ~+55–188 lines in `proof-core/Core.lean` (~3% of 5,910 lines), with Lean soundness lemmas reusing the already-proved `symLoadWords_sound` and `Carried.fresh`. All 11 top-level theorems in `proof-core/test_sound.py` remain verbatim with zero omitted proof steps and standard axioms only.

---

### Phase 2 — Cache-Line & Page Alignment, Coherence Disjointness, and Streaming Ops (Next)

1. **First-class region alignment (`align A`, `A ∈ {16, 64, 128, 4096, 16384}`):**
   - Allowed on buffer parameters in contracts (`buf: n bytes align 64`) and local stack arrays (`buf scratch[64] align 64`).
   - Represented in `Core.lean` as a single modular entry fact `base % A == 0` (checked by callers on call boundaries, preserved under `base + k * A` offsets).
   - Enables machine-checked aligned SIMD loads/stores, proves zero cache-line splits for aligned accesses, and justifies page-bounded SIMD over-reads (reads staying strictly inside `[base & ~(P-1), (base & ~(P-1)) + P)` without crossing a page boundary into a guard page).
2. **Cache-line disjointness (`line_disjoint`):**
   - Optional contract separation strengthening byte-disjointness to cache-line-disjointness (`floor(a / L) ≠ floor(b / L)` for `L = 64` or `128`), guaranteeing zero false sharing between concurrently accessed exclusive regions.
3. **Explicit 1-to-1 hardware cache & streaming instructions (`.tab` rows):**
   - Software prefetch (`prefetcht0` / `prefetchnta` on x86-64, `prfm pldl1keep` / `prfm pldl1strm` on AArch64): functional effect `nothing`, checked strictly by `Trace.lean` so prefetch addresses never depend on values kept out of the trace.
   - Non-temporal streaming stores (`movntdq` / `vmovntdq` on x86-64, `stnp` on AArch64): reuse `symStoreWords` on aligned `write` regions, letting the coder bypass cache allocation explicitly on large streaming outputs.
4. **Locality metrics in `ode advise`:**
   - Report per-loop active memory stream count, stride classification (unit/cache-line/strided/indirect), cache-line alignment & split warnings, and estimated cache-line (L1D/L2) and VM-page (TLB) working-set footprints.

---

### Phase 3 — Verified Sub-Region Partitioning & Arena / Page Management (Future)

1. **Disjoint sub-region splitting & borrowing:**
   - Partition a page- or cache-line-aligned arena (`arena: n bytes align 4096`) into disjoint aligned sub-regions (`[0 .. k)`, `[k .. n)`) whose non-overlap and alignment follow by linear/modular arithmetic.
2. **Target applications:**
   - Multi-threaded BLAKE3 subtree arenas (per-worker cache-line-disjoint scratch + output lines, zero false sharing),
   - Brotli / zstd / LZ4 sliding windows and ring buffers with explicit L1D/L2 cache-line budgeting,
   - Verified slab, bump, and page-pool memory managers where every allocation carries machine-checked bounds, alignment, and coherence isolation.

---

## 4. Verification & Reliance Impact

- **Bob's reliance set does not grow:** no compiler component enters the reliance set; Phase 1 adds zero new proof-file advice tags and keeps all 11 theorems in `proof-core/test_sound.py` intact.
- **Validation plan for Phase 1:**
  1. Lean 4 build (`lake build`) + `proof-core/test_sound.py -n0` (11/11 theorems, zero omitted proof steps, standard axioms only).
  2. Full Python / unit / fuzz / matrix test suites + new dual-arch regressions covering fixed `.u32`, in-out `.u32`/`.u64` (before and after writes), `frameW` → scalar `.u32`/`.u64`, `out.u32` / `stack.u32` stores, and `ode advise` store-forwarding hazard detection.
  3. **`$0` replay of all 69 failing `.last.ode` programs from `hl-default-v10` + `hl-default-v11`** to confirm direct progress/flips on the 5 `mem_model_nonuniformity` cells before spending any API budget.
