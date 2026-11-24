// LZ4 block format extended length reader (from kcheck/programs/lz4/lz4.spec):
// While buf[at] == 255, add 255 to `acc`; when buf[at] < 255, add buf[at] and return total (>= 15).
// Returns 0 if the buffer ends before a byte < 255 (valid lengths are always >= 15).
def lz4_len_from(buf, at, acc) {
    if at >= len(buf) then 0
    else if buf[at] == 255 then lz4_len_from(buf, at + 1, acc + 255)
    else acc + buf[at]
}

contract ode_lz4_ext_len(buf: n bytes, n: number) {
    requires n <= 65536
    returns lz4_len_from(buf, 0, 15)
    trace depends on buf, n
    stack 0
}
