// Strict RFC 4648 two-character ASCII hexadecimal byte decoder (0-9, a-f, A-F).
// Returns decoded byte 0..255 on valid hex pair (hi, lo), or 256 if either byte is not hex.
def hex_nib(b) {
    if b >= 48 && b <= 57 then b - 48
    else if b >= 97 && b <= 102 then b - 87
    else if b >= 65 && b <= 70 then b - 55
    else 16
}

def hex_pair(hi, lo) {
    if hex_nib(hi) == 16 || hex_nib(lo) == 16 then 256
    else hex_nib(hi) * 16 + hex_nib(lo)
}

contract ode_hex_decode_byte(hi: number, lo: number) {
    requires hi < 256
    requires lo < 256
    returns hex_pair(hi, lo)
    trace depends on hi, lo
    stack 0
}
