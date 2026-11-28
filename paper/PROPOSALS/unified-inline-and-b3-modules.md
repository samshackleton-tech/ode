# Proposal: Unified `[inline] fn`, Stricter Call-Site `check`, and Content-Addressed Modules

## 1. Motivation

Two tensions meet whenever a coder writes portable High-Level Ode across `x86_64` and `arm64`:

1. **No universal 1-to-1 instruction set spans both ISAs.** Operations such as 32-bit lane rotation (`rotr32`), `xar` fused XOR-rotate on ARMv8.2-SHA3, `vprord` on AVX-512, 16-bit little-endian loads (`buf.u16`), 64-bit pair packing (`pack_u64x2`), and constant multiplication (`a * 25`) lower to different instruction sequences on each target. Traditional compilers bury this difference inside clever compiler heuristics. Ode forbids silent compiler cleverness: the coder owns every emitted instruction.
2. **Modular verification vs. call overhead.** Factoring branchy logic (such as Base64 character decoding or eBPF ALU dispatch) into a compiled `fn` keeps symbolic path counts linear, at the cost of `call`/`ret` overhead in hot loops. Inlining the same logic removes call overhead, at the cost of exponential symbolic path splitting unless a `join` merge point cuts the paths.

This proposal resolves both tensions with **one** function grammar, **one** non-generalizing verifier check primitive, and **one** content-addressed module-loading rule — eliminating both hard-coded standard libraries and hidden multi-instruction synthesis (`EXPLICIT_MULTI_INSN_OPS`) from the compiler.

---

## 2. Unified `[inline] fn` and Per-Target Bodies

`fn`, `inline fn`, and `for <target>` collapse into a single declaration:

```ebnf
fn_decl    ::= ["inline"] "fn" ident "(" params ")" ["->" type] contract_clauses fn_body
fn_body    ::= block
             | ("for" target [":" variant] block)+
param      ::= ["var" | "const"] ident ":" type
```

### Examples

A target-specialized, expression-returning `inline fn` with a compile-time `const` immediate:

```ode
inline fn rotr32(v: u32x4, const k: u64) -> u32x4
    for x86_64:avx512 { return vprord(v, k) }
    for x86_64        { return (v >> k) | (v << (32 - k)) }
    for arm64         { return sli32(v >> k, v, 32 - k) }
```

A contracted `inline fn` whose contract gives zero-call modular verification and standalone auditability:

```ode
inline fn b64_dec(c: u8) -> u64
    requires c <= 255
    returns spec.b64_dec(c)
{
    var d: u64 := 0
    d := select(65 <= c && c <= 90, c - 1, d)
    d := select(97 <= c && c <= 122, c - 7, d)
    d := select(48 <= c && c <= 57, c + 68, d)
    d := select(c == 43, 126, d)
    d := select(c == 47, 127, d)
    return d
}
```

### Rules

1. **`fn` vs. `inline fn`:**
   - **`fn`** compiles to its own machine-code symbol (`ode_<52>`), requires a `.ocl` contract, and is invoked via `call`/`bl`. `var` and `const` parameter modifiers are not permitted on compiled `fn`.
   - **`inline fn`** expands hygienically at every call site with zero `call`/`ret` instructions and must be non-recursive. Contracts are optional.
   - Toggling a non-`const`, non-`var` contracted function between `fn` and `inline fn` is a one-word change (`inline`), preserving both contract semantics and proof modularity.
2. **Target resolution (`fn_body`):** Identical for `fn` and `inline fn`: exact `arch:variant`, then base `arch`, then portable `{ ... }`. Keeping `for <target>` strictly at `fn_body` ensures every target divergence has an explicit name and typed interface and avoids ambiguity with `for` loops.
3. **`const` parameters:** Arguments to `const` parameters must fold to compile-time integers (`Num`, `const` definitions, `for ... unroll` induction variables, or arithmetic on them). During expansion, `const` parameters substitute as `Num` and fold through the existing compile-time arithmetic and branch-elimination passes (`_const_eval_int`, `_const_eval_cond`), allowing compile-time specialization (`if k == 16 { ... }`, `for bit in 0..64 unroll { ... }`) in plain `.ode` source.
4. **Call-by-value evaluation:** Non-`const`, non-`var` arguments that are compound expressions are evaluated once into a temporary before expansion; `let y := f(...)` and `y := f(...)` assign `return expr` directly into `y` with no extra move.
5. **Per-target explicit stack placement:** In an otherwise shared portable body, `stack(x86_64) var v: u32x4 := ...` (or `stack(arm64)`) places `v` on the stack only on the named architecture, keeping zero silent spilling and zero penalty on architectures with more registers.

---

## 3. Stricter Call-Site `requires` Checking and Auto-`join`

### Verifier Addition (`proof-core/Core.lean`, `SoundTop.lean`, `verify2.py`)

Add one minimal non-generalizing assertion item at a PC:

```text
check +0xNN {
    fact <spec_fact>
    ...
}
```

- **Semantics in `Core.lean` (~10 lines):** When execution reaches `c.pc`, `Core.lean` runs the existing `establish` function on each fact in `c.facts` (proving it from the current symbolic state and appending it to `s.facts`/`s.spec`) **without** generalizing registers (`Sym.general`), clearing `wrote`, or resetting flags (`zf`, `cf`).
- **Soundness (`SoundTop.lean`, ~10 lines):** Follows directly from the existing `establish_sound` theorem, because checking an extra fact leaves the concrete machine state intact.
- **Mirror (`proof-core/verify2.py`, ~8 lines):** Runs the existing `_establish_fact` helper at `c.pc`.

### Compiler Expansion of Contracted `inline fn`

When expanding a call to an `inline fn` that declares a contract:

1. **Entry (`requires`):** Emit `check` at the call site for every `requires` clause (with formal parameters substituted by the actual arguments). A caller that violates `requires` is refused immediately at the call line, giving strict mechanical symmetry with compiled `fn`.
2. **Body:** Emit the expanded 1-to-1 instructions inline.
3. **Exit (`returns` / `ensures`):** When the expanded body is scalar and contains branches or `select`, emit a `join` `place` carrying the substituted postcondition (`dst == returns_expr`, `ensures` facts) plus any active enclosing loop `writes` clause (so `Sym.general` preserves the enclosing loop's write invariant). Straight-line vector bodies emit no `join`, letting the word-DAG flow straight through.
4. **Standalone audit (`ode audit` / `ode check`):** Contracted `inline fn`s without `const` or `var` parameters are also verified standalone across every `for <target>` arm using the standard `fn` verification path. `const`-parameterized `inline fn`s are verified at every concrete instantiation (and via dedicated library test files covering canonical parameter values).

---

## 4. Single Module-Loading Mechanism: Content-Addressed BLAKE3-256

To mirror Ode's nameless content-addressed contracts (`ode_<52>`, `<52>.ocl`) and avoid any privileged `"std"` directory or ambient path search, `use` has **one** uniform form:

```ode
use vec = "7k2q..."   // exact 52-char lowercase RFC 4648 base-32 BLAKE3-256 of the module's bytes
use bpf = "a9x4..."
```

### Rules

1. **Identifier:** The sole module identifier is the 52-char lowercase RFC 4648 base-32 BLAKE3-256 digest (`[a-z2-7]{52}`) of the module file's exact UTF-8 bytes. Any auditor can compute or verify a module hash with `b3sum` alone, with zero Ode parser in the hash definition.
2. **Lookup (pure capability, zero hard-coded `"std"`):**
   - `ode` searches the importing file's own directory plus any explicit `--store DIR` directories supplied by the caller.
   - In each directory, `ode` checks `<dir>/<52>.ode` first (O(1)), then indexes `*.ode` files in `<dir>` by their BLAKE3-256 digest (allowing human-readable filenames such as `lib/vec.ode` or `ebpf_spec.ode` on disk while remaining immune to renames or moves).
   - Every loaded file is checked against its requested digest (`b3_52(bytes) == <52>`) before parsing.
   - If a requested digest is not found, `ode` prints the available `<filename> = <52>` entries from the searched directories so updating a changed module is immediate.
3. **CLI helper:** `ode hash <file.ode>...` prints `<52>  <file.ode>` for any module file.
4. **Reachability pruning:** Compiled `fn`s in imported modules are included in `.o` and `.proof` only if reachable from the requested entry function(s); unused library `fn`s and `inline fn`s add zero code size or proof work.
5. **TOOWTDI migration:** Existing relative-path `use alias = "file.ode"` statements across the repository (`proof-core/examples/`, `paper/EXPERIMENTS/tasks/`, tests, docs) are migrated to 52-char hashes, and the superseded path-based loader is deleted.

---

## 5. Retiring Group B (`EXPLICIT_MULTI_INSN_OPS`)

Once Phases 1–3 land, ordinary content-addressed `.ode` modules in `lib/` (passed via `--store lib`, with no special status in the compiler) replace the grandfathered multi-instruction lowerings in `lang/ode_hl.py`:

| Current compiler synthesis | Replacement in ordinary `.ode` modules (`lib/`) |
|---|---|
| `rotr32` / `rotl32` (2–3 insns) | `lib/vec.ode`: `inline fn rotr32(v: u32x4, const k: u64) -> u32x4` + `rotl32` + `xor_rotr32` |
| `pack_u64x2` (3 insns) | `lib/vec.ode`: `inline fn pack_u64x2(lo: u64, hi: u64) -> u32x4` |
| `u32x4(c0, c1, c2, c3)` | `lib/vec.ode`: `inline fn const_u32x4(const a, const b, const c, const d) -> u32x4` (or 1-insn `data` load) |
| `buf.u16(i)` (4-insn byte emulation) | `lib/bytes.ode`: `inline fn load_u16_le(buf, i) -> u64` (or 1-insn hardware `ldrh`/`movzx` row) |
| `a * K` (binary shift-add synthesis) | `lib/int.ode`: `inline fn mul_const(x: u64, const k: u64) -> u64` (`for bit in 0..64 unroll`) |

Every line in the compiler lowers strictly 1-to-1 to the target ISA table (`x86.tab` / `arm64.tab`), and Bob's verifier relies on nothing outside `Core.lean` (or `verify2.py`).

---

## 6. Implementation Order (Each Step Independently Tested & Green)

1. **Phase 1 — Verifier `check` primitive:** Add non-generalizing `check` to `proof-core/Core.lean`, `Reader.lean`, `SoundTop.lean` (all 11 theorems proved, standard axioms only), `verify2.py`, and `prove.py` + unit tests.
2. **Phase 2 — Unified `[inline] fn` + `const` params + `stack(arch)` + stricter `check` / auto-`join`:** Implement in `lang/ode_unified.py` and `lang/ode_hl.py`, plus standalone audit of contracted non-`const` `inline fn`s and TDD regressions in `lang/test_hl_matrix.py`.
3. **Phase 3 — Pure content-addressed `use alias = "<52>"` + `--store DIR` + `ode hash` + reachability pruning:** Implement in `lang/ode_unified.py` and `lang/ode_tool.py`, migrate all existing `use` sites and benchmark harnesses, delete relative-path `use`.
4. **Phase 4 — Reusable `lib/{vec,bytes,int}.ode` modules & Group B retirement:** Write and verify `lib/*.ode`, migrate callers, and shrink `EXPLICIT_MULTI_INSN_OPS` in `lang/ode_hl.py` + `lang/test_hl_matrix.py::test_09`.
