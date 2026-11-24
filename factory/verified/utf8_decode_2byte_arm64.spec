// Strict RFC 3629 UTF-8 1-byte and 2-byte scalar decoder.
// Accepts ASCII (0x00..0x7F -> 0..127) and canonical 2-byte sequences (0xC2..0xDF, 0x80..0xBF -> 128..2047).
// Rejects truncation, overlong 0xC0/0xC1 encodings (CVE-2008-2938), invalid continuations,
// and 3+/4-byte lead octets, returning 4294967295 (0xFFFFFFFF).
def utf8_cp2(a) {
    if len(a) == 0 then 4294967295
    else if a[0] < 128 then a[0]
    else if a[0] >= 194 && a[0] <= 223 then
        if len(a) >= 2 && a[1] >= 128 && a[1] <= 191 then
            (a[0] - 192) * 64 + (a[1] - 128)
        else 4294967295
    else 4294967295
}

contract ode_utf8_decode_2byte(input: n bytes, n: number) {
    returns utf8_cp2(input)
    trace depends on input, n
    stack 0
}
