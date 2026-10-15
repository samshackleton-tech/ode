; BLAKE3's G mixing function (C2SP BLAKE3, section 2.2), as an Ode word
; specification: the specification of record for this slice.
; G(a, b, c, d, x, y) updates four state words with two message words.
(wspec
  (name blake3-g)
  (inputs (a b c d x y))
  (steps
    ((a1 (add (add a b) x))
     (d1 (rotr (xor d a1) 16))
     (c1 (add c d1))
     (b1 (rotr (xor b c1) 12))
     (a2 (add (add a1 b1) y))
     (d2 (rotr (xor d1 a2) 8))
     (c2 (add c1 d2))
     (b2 (rotr (xor b1 c2) 7))))
  (outputs (a2 b2 c2 d2)))
