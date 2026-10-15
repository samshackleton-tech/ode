; A single chain versus two consecutive batches of arbitrary sizes.
; compress and block-at are arbitrary total functions, as in batching.
(theory 2
  (State Block Blocks)
  ((compress (State Block) State)
   (block-at (Blocks Nat) Block))
  ((add ((n Nat) (k Nat)) Nat
     k
     (p (succ (add p k))))
   (chain ((n Nat) (s State) (m Blocks) (i Nat)) State
     s
     (p (chain p (compress s (block-at m i)) m (succ i))))))
