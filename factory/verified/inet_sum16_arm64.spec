// RFC 1071 Internet checksum 16-bit one's-complement sum over `pairs` big-endian 16-bit words
// (len == 2 * pairs bytes, e.g. IPv4/TCP/UDP headers): s[0] = 0, each word w adds into s
// with end-around carry folding (s + w >= 65536 -> s + w - 65535), keeping s < 65536.
def fold16(x) {
    if x >= 65536 then x - 65535 else x
}

sequence inet16(bytes) {
    s[0] = 0
    s[i + 1] = fold16(s[i] + 256 * bytes[2 * i] + bytes[2 * i + 1])
}

contract ode_inet_sum16(input: len bytes, len: number, pairs: number) {
    requires len == 2 * pairs
    returns inet16(input)[pairs]
    trace depends on input, len, pairs
    stack 0
}
