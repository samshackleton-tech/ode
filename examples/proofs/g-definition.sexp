; BLAKE3 G as two half-round equations over State(a,b,c,d,x,y).
; Word32 addition is modulo 2^32; ror-N rotates right by N bits.
; The message words x and y are preserved. No register instructions occur here.
(
  (g-first ((s State)) State
    ((state (a b c d x y)
      (state
        (add32 (add32 a b) x)
        (ror-12 (xor32 b
          (add32 c (ror-16 (xor32 d (add32 (add32 a b) x))))))
        (add32 c (ror-16 (xor32 d (add32 (add32 a b) x))))
        (ror-16 (xor32 d (add32 (add32 a b) x)))
        x y))))
  (g-second ((s State)) State
    ((state (a b c d x y)
      (state
        (add32 (add32 a b) y)
        (ror-7 (xor32 b
          (add32 c (ror-8 (xor32 d (add32 (add32 a b) y))))))
        (add32 c (ror-8 (xor32 d (add32 (add32 a b) y))))
        (ror-8 (xor32 d (add32 (add32 a b) y)))
        x y))))
  (g ((s State)) State
    ((state (a b c d x y)
      (g-second (g-first (state a b c d x y))))))
)
