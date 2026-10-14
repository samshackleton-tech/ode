; mix(x, k) = rotl3((x XOR k) + 60) -- the worked example (SPEC s14 at toy scale).
; Written freely here; `build` canonicalizes it and names it by its hash.
(spec
  (name mix)
  (inputs 2)
  (body (rotl (add (xor (var 0) (var 1)) (const 60)) 3)))
