// RFC 4648 Section 4 Base64 alphabet encoder: 0..25 -> A-Z, 26..51 -> a-z,
// 52..61 -> 0-9, 62 -> '+' (43), 63 -> '/' (47).
def b64_letter(v) {
    if v < 26 then 65 + v
    else if v < 52 then 71 + v
    else if v < 62 then v - 4
    else if v == 62 then 43
    else 47
}

contract ode_b64_encode_char(v: number) {
    requires v < 64
    returns b64_letter(v)
    trace depends on v
    stack 0
}
