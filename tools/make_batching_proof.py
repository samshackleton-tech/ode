#!/usr/bin/env pypy3
"""Emit the loop-batching goal and proof. No kernel import: a producer.

Run from the repository root: pypy3 tools/make_batching_proof.py.
The generated goal is for the owner to read and pin; the proof can come
from anyone. Each proof step carries its rule, never its own conclusion.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from ode.canon import canonical_bytes, hash_of, parse


def artifacts(theory):
    goal = parse(f"""(goal 2 #{hash_of(theory).hex()}
      ((n Nat) (s State) (m Blocks) (i Nat))
      (eq (chain (double n) s m i) (pairs n s m i)))""")
    one = "(compress s (block-at m i))"
    two = f"(compress {one} (block-at m (succ i)))"
    base = """((unfold double (zero))
      (refl s) (refl m) (refl i)
      (cong chain 0 1 2 3)
      (unfold chain (zero) s m i)
      (trans 4 5)
      (unfold pairs (zero) s m i)
      (sym 7)
      (trans 6 8))"""
    step = f"""((unfold double (succ k))
      (refl s) (refl m) (refl i)
      (cong chain 0 1 2 3)
      (unfold chain (succ (succ (double k))) s m i)
      (trans 4 5)
      (unfold chain (succ (double k)) {one} m (succ i))
      (trans 6 7)
      (ih {two} m (succ (succ i)))
      (trans 8 9)
      (unfold pairs (succ k) s m i)
      (sym 11)
      (trans 10 12))"""
    proof = parse(f"(proof 2 #{hash_of(goal).hex()} () (induct n k {base} {step}))")
    return goal, proof


def main():
    directory = ROOT / "examples" / "proofs"
    theory = parse((directory / "batching.theory.sexp").read_bytes())
    goal, proof = artifacts(theory)
    for name, value in (("goal", goal), ("proof", proof)):
        (directory / f"batching.{name}.sexp").write_bytes(canonical_bytes(value))
    print(f"goal #{hash_of(goal).hex()}")


if __name__ == "__main__":
    main()
