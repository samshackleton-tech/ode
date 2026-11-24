// Stage 1 Verifier-in-Ode (`arm64/word.py`): given an encoded 32-bit AArch64 instruction
// word (low 32 bits of `w`), extract Rd = w % 32 and return 1 iff Rd < 31 (general register x0..x30).
def rd_valid(w) {
    if w % 32 < 31 then 1 else 0
}

contract ode_v_arm64_rd_valid(w: number) {
    returns rd_valid(w)
    trace depends on w
    stack 0
}
