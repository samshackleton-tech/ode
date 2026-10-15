; Finite bit strings. No word-operation axioms: the operations below are
; total functions defined by exhaustive constructor cases.
;
; xor-bits takes the width of its first argument. If the second argument
; is shorter it is zero-extended; extra bits are ignored. On equal-width
; inputs this is ordinary bitwise XOR, including on 32-bit words.
(theory 3
  ((Bit ((bit0 ()) (bit1 ())))
   (Bits ((empty ()) (bit (Bit Bits)))))
  ()
  ((not-bit ((a Bit)) Bit
     ((bit0 () (bit1))
      (bit1 () (bit0))))
   (xor-bit ((a Bit) (b Bit)) Bit
     ((bit0 () b)
      (bit1 () (not-bit b))))
   (head ((xs Bits)) Bit
     ((empty () (bit0))
      (bit (h t) h)))
   (tail ((xs Bits)) Bits
     ((empty () (empty))
      (bit (h t) t)))
   (zeros ((xs Bits)) Bits
     ((empty () (empty))
      (bit (h t) (bit (bit0) (zeros t)))))
   (xor-bits ((xs Bits) (ys Bits)) Bits
     ((empty () (empty))
      (bit (h t) (bit (xor-bit h (head ys)) (xor-bits t (tail ys))))))
   (width ((xs Bits)) Nat
     ((empty () (zero))
      (bit (h t) (succ (width t)))))))
