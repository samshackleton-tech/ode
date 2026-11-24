// Copy n bytes (n <= 32) from src into a 32-byte block out, zero-padding the tail.
// Constant-time in the data bytes: trace depends on n only.
def pad32(src) { [if i < len(src) then src[i] else 0 for i in 0..32] }

contract ode_lz4_pad_lit32(out: 32 bytes, src: n bytes, n: number) {
    requires no_overlap(out, src)
    requires n <= 32
    ensures out = pad32(src)
    trace depends on n
    stack 0
}
