; A chain of compression steps, or two steps per loop iteration.
; State, Blocks, and Block are arbitrary nonempty sets. compress and
; block-at are arbitrary total functions. Block may include flags,
; counter, and block length: the theorem assumes no cryptographic law.
(theory 1
  (State Block Blocks)
  ((compress (State Block) State)
   (block-at (Blocks Nat) Block))
  ((double ((n Nat)) Nat
     (zero)
     (k (succ (succ (double k)))))

   (chain ((n Nat) (s State) (m Blocks) (i Nat)) State
     s
     (k (chain k (compress s (block-at m i)) m (succ i))))

   (pairs ((n Nat) (s State) (m Blocks) (i Nat)) State
     s
     (k (pairs k
               (compress (compress s (block-at m i)) (block-at m (succ i)))
               m (succ (succ i)))))))
