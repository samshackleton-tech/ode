# Standalone Lean 4 Specification-Agreement Proofs (`lean2ode/agree`)

This standalone Lean 4 package lives outside Bob's verifier (`proof-core/`). Just as
`arm64/agree/` proves that Ode's AArch64 instruction table agrees with Google DeepMind's
`arm64-semantics`, `lean2ode/agree/` proves that `Contract.evalSpec` (Ode's exact specification
evaluator in `proof-core/Contract.lean`) evaluating the OdeSpecL definitions emitted by `lean2ode`
agrees **for all inputs** with the original upstream Lean 4 specifications.

## Theorems Proved in `SpecAgree.lean`

Each row below names one agreement theorem in `SpecAgree.lean`, the upstream Lean 4 specification
it covers, and the quantified domain over which agreement with `Contract.evalSpec` is proved. All
eight theorems compile with zero `sorry`, zero `bv_decide`, and only the standard Lean 4 axioms
`[propext, Classical.choice, Quot.sound]`.

| Theorem | Upstream Lean 4 Function | Quantified Domain |
|---|---|---|
| `SpecAgree.agree_der_tagOk` | `X509.tagOk` (`keithadler/lean-x509`) | All `t : Nat` (infinite) |
| `SpecAgree.agree_der_constructed` | `X509.constructed` (`keithadler/lean-x509`) | All `t : Nat` (infinite) |
| `SpecAgree.agree_der_beF` | `X509.beF` (`keithadler/lean-x509`, recursive) | All `f, n : Nat` by induction on `f` (infinite) |
| `SpecAgree.agree_der_be` | `X509.be` (`keithadler/lean-x509`) | All `n : Nat` (infinite) |
| `SpecAgree.agree_der_encodeLen` | `X509.encodeLen` (`keithadler/lean-x509`) | All `n : Nat` (infinite) |
| `SpecAgree.agree_blake3_rotr` | `BLAKE3.rotr` (`c2sp/BLAKE3`) | All `x : UInt32` (`2^32` words) and `k < 32` |
| `SpecAgree.agree_b64_val` | RFC 4648 `b64Val` | All `b : UInt8` (`256` bytes) |
| `SpecAgree.agree_b64_letter` | RFC 4648 `b64Letter` | All `v : Nat` (infinite) |

## How Zero Skew Is Enforced

`test_spec_agree.py` runs `lean2ode` live on the reference Lean 4 source, lowers the resulting
OdeSpecL text through `proof-core/statement.py` (`statement.definitions`), and asserts that the
exact `.statement` S-expressions match the `Contract.Def` ASTs proved in `SpecAgree.lean`.

## Running

```sh
cd lean2ode/agree
lake build
./.lake/build/bin/spec-agree-check
python3 test_spec_agree.py
```
