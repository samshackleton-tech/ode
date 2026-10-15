; Addition on mathematical natural numbers, defined by structural recursion.
(theory 3 () ()
  ((add ((a Nat) (b Nat)) Nat
     ((zero () b)
      (succ (k) (succ (add k b)))))))
