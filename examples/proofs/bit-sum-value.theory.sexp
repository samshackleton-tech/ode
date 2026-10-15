; Paired input bits have equal widths by construction; the output keeps final carry.
; Least significant bit first; bits-value is a mathematical natural number.
(theory 3
  (
    (Bit ((bit0 ()) (bit1 ())))
    (Bits ((empty ()) (bit (Bit Bits))))
    (Columns ((no-columns ()) (column (Bit Bit Columns))))
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
    (left-bits ((columns Columns)) Bits ((no-columns () (empty)) (column (a b tail) (bit a (left-bits tail)))))
    (right-bits ((columns Columns)) Bits ((no-columns () (empty)) (column (a b tail) (bit b (right-bits tail)))))
    (add-columns ((columns Columns) (c Bit)) Bits ((no-columns () (bit c (empty))) (column (a b tail) (bit (xor-bit (xor-bit a b) c) (add-columns tail (carry-bit a b c))))))
    (bits-value ((bits Bits)) Nat ((empty () (zero)) (bit (a tail) (add (bit-value a) (add (bits-value tail) (bits-value tail))))))
  ))
