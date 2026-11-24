import SpecAgree

#print axioms SpecAgree.agree_der_tagOk
#print axioms SpecAgree.agree_der_constructed
#print axioms SpecAgree.agree_der_beF
#print axioms SpecAgree.agree_der_be
#print axioms SpecAgree.agree_der_encodeLen
#print axioms SpecAgree.agree_blake3_rotr
#print axioms SpecAgree.agree_b64_val
#print axioms SpecAgree.agree_b64_letter

def main : IO Unit := do
  IO.println "spec-agree: 8 theorems checked (X509 tagOk/constructed/beF/be/encodeLen, BLAKE3 rotr, RFC4648 b64Val/b64Letter)"
