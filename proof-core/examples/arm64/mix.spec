// The mixing step of the trial (paper/trial/src/mix16.spec), for three functions for AArch64 (mix.s).
// Three mixing steps on sixteen words: d, then a, then d again. Each step is `(x ^ y) ror 16`, a word at a time.
def xor_ror16(d, a) { (d ^ a) >>> 16 }
def mix16_step(d, a) { [xor_ror16(d[i], a[i]) for i in 0..16] }
def mix16_chain_3(d, a) {
  let d1 = mix16_step(d, a)
  let a2 = mix16_step(a, d1)
  let d3 = mix16_step(d1, a2)
  d3
}

contract arm_mix16_3(out: block, d: block, a: block) {
    requires disjoint(out, d, a, 1)
    ensures out = mix16_chain_3(d, a)
    stack 0
}

contract arm_mix16_again(out: block, d: block, a: block) {
    requires disjoint(out, d, a, 1)
    ensures out = mix16_chain_3(d, a)
    stack 16
}

contract arm_mix16_6(out: block, d: block, a: block) {
    requires disjoint(out, d, a, 1)
    ensures out = mix16_chain_3(mix16_chain_3(d, a), a)
    stack 96
}
