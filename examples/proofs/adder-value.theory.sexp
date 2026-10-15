; A Boolean full-adder column preserves the natural-number value.
; sum-bit + 2*carry-bit = a+b+carry-in, with bit values zero or one.
(theory 3
  (
    (Bit ((bit0 ()) (bit1 ())))
  )
  ()
  (
    (not-bit ((a Bit)) Bit ((bit0 () (bit1)) (bit1 () (bit0))))
    (xor-bit ((a Bit) (b Bit)) Bit ((bit0 () b) (bit1 () (not-bit b))))
    (and-bit ((a Bit) (b Bit)) Bit ((bit0 () (bit0)) (bit1 () b)))
    (or-bit ((a Bit) (b Bit)) Bit ((bit0 () b) (bit1 () (bit1))))
    (carry-bit ((a Bit) (b Bit) (c Bit)) Bit ((bit0 () (and-bit b c)) (bit1 () (or-bit b c))))
    (add ((a Nat) (b Nat)) Nat ((zero () b) (succ (k) (succ (add k b)))))
    (bit-value ((a Bit)) Nat ((bit0 () (zero)) (bit1 () (succ (zero)))))
  ))
