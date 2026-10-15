; Addition on mathematical natural numbers. These are defining equations,
; not algebraic axioms. The kernel checks counter-decreasing recursion.
(theory 2 () ()
  ((add ((a Nat) (b Nat)) Nat
     b
     (k (succ (add k b))))))
