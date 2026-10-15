; BLAKE3 (C2SP BLAKE3, sections 2.4-2.6): the 32-byte hash of a message
; of any length. The specification of record: one definition, for every
; length.
;
; len is the message length in bytes; m is the message as little-endian
; words, zero-padded to whole 64-byte blocks (at least one). The result h
; is the hash as 8 words. compress is BLAKE3's compression function, named
; by its hash; a readable copy is examples/blake3-compress.sexp.
;
; A *node* is a compression not yet run: 28 words, in the compression's
; input order -- chaining value (8), block (16), counter low and high,
; block length, flags. The root is the last node, run with ROOT added.
(spec
  (name blake3)
  (inputs ((len nat) (m words)))
  (uses ((compress #8ab0f1624cd1178d89715392b2c37efb28080b8c1f72e31f138b3c3770a81b6b)))
  (funs
    ((iv () (list 1779033703 3144134277 1013904242 2773480762
                  1359893119 2600822924 528734635 1541459225))
     (cv (node) (slice (compress node) 0 8))
     ; Chunk c's last node; every earlier block of the chunk chained in.
     (chunk ((c nat))
       (let ((start (n* c 1024))
             (blocks (nmax 1 (ndiv (n+ (nmin 1024 (n- len start)) 63) 64))))
         (chain c start blocks 0 (iv))))
     (chain ((c nat) (start nat) (blocks nat) (b nat) cv)
       (let ((off (n+ start (n* 64 b)))
             (node (concat cv (slice m (ndiv off 4) 16)
                           (list (word c) (word (ndiv c 4294967296))
                                 (word (nmin 64 (n- len off)))
                                 (word (n+ (if (n= b 0) 1 0)
                                           (if (n= b (n- blocks 1)) 2 0)))))))
         (if (n= b (n- blocks 1))
             node
             (chain c start blocks (n+ b 1) (cv node)))))
     ; The node over chunks lo .. lo+n-1: the left subtree takes the
     ; largest power of two of them that leaves at least one for the right.
     (tree ((lo nat) (n nat))
       (if (n= n 1)
           (chunk lo)
           (let ((k (split 1 n)))
             (concat (iv) (cv (tree lo k)) (cv (tree (n+ lo k) (n- n k)))
                     (list 0 0 64 4)))))
     (split ((k nat) (n nat)) (if (n< (n* 2 k) n) (split (n* 2 k) n) k))))
  (steps
    ((chunks (nmax 1 (ndiv (n+ len 1023) 1024)))
     (ok (require (n= (count m) (n* 16 (nmax 1 (ndiv (n+ len 63) 64)))) 1))
     (root (tree 0 chunks))
     (h (slice (compress (concat (slice root 0 27) (list (add (at root 27) 8))))
               0 8))))
  (outputs (h)))
