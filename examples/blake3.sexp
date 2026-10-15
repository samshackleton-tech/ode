; BLAKE3 (C2SP BLAKE3, sections 2.4-2.6): the 32-byte hash of a message
; of any length. The specification of record: one definition, for every
; length.
;
; len is the message length in bytes; m is the message as little-endian
; words, zero-padded to whole 64-byte blocks (at least one). The result h
; is the hash as 8 words. compress is BLAKE3's compression function, and
; full-chunk the chaining value of one full 1024-byte chunk, both named by
; hash; readable copies are examples/blake3-compress.sexp and
; examples/blake3-chunk.sexp.
;
; A *node* is a compression not yet run: 28 words, in the compression's
; input order -- chaining value (8), block (16), counter low and high,
; block length, flags. The root is the last node, run with ROOT added.
(spec
  (name blake3)
  (inputs ((len nat) (m words)))
  (uses ((full-chunk #f1186a4716d66e11ed5d890df9679b21d4a7f50c4f135545fe634bca28a3b343)
         (compress #6d5c8554f810e8ea78a642238b861ef958fcd5c306e7afbf7cd97d58f5fc8cab)))
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
             (concat (iv) (subtree-cv lo k) (subtree-cv (n+ lo k) (n- n k))
                     (list 0 0 64 4)))))
     ; A subtree's chaining value; a full chunk's comes from full-chunk.
     (subtree-cv ((lo nat) (n nat))
       (if (n= n 1)
           (if (n< (n* (n+ lo 1) 1024) (n+ len 1))
               (full-chunk (word lo) (word (ndiv lo 4294967296)) (slice m (n* lo 256) 256))
               (cv (chunk lo)))
           (cv (tree lo n))))
     (split ((k nat) (n nat)) (if (n< (n* 2 k) n) (split (n* 2 k) n) k))))
  (steps
    ((chunks (nmax 1 (ndiv (n+ len 1023) 1024)))
     (ok (require (n= (count m) (n* 16 (nmax 1 (ndiv (n+ len 63) 64)))) 1))
     (root (tree 0 chunks))
     (h (slice (compress (concat (slice root 0 27) (list (add (at root 27) 8))))
               0 8))))
  (outputs (h)))
