// Strict canonical RFC 4648 Section 3.5 & 4 Base64 4-byte quad validator.
// Enforces alphabet membership, valid '=' / '==' placement, and canonical zero
// trailing padding bits (rejects e.g. "Zh==" and "Zm9="). Returns 1 if valid, 0 otherwise.
def b64_val(b) {
    if b >= 65 && b <= 90 then b - 65
    else if b >= 97 && b <= 122 then b - 71
    else if b >= 48 && b <= 57 then b + 4
    else if b == 43 then 62
    else if b == 47 then 63
    else 255
}

def b64_quad_ok(v0, v1, c2, v2, c3, v3) {
    if v0 == 255 || v1 == 255 then 0
    else if c2 == 61 then
        if c3 == 61 && v1 % 16 == 0 then 1 else 0
    else if c3 == 61 then
        if v2 != 255 && v2 % 4 == 0 then 1 else 0
    else if v2 != 255 && v3 != 255 then 1
    else 0
}

def b64_valid_quad(c0, c1, c2, c3) {
    b64_quad_ok(b64_val(c0), b64_val(c1), c2, b64_val(c2), c3, b64_val(c3))
}

contract ode_b64_char_val(b: number) {
    requires b < 256
    returns b64_val(b)
    trace depends on b
    stack 0
}

contract ode_b64_valid_quad(c0: number, c1: number, c2: number, c3: number) {
    requires c0 < 256
    requires c1 < 256
    requires c2 < 256
    requires c3 < 256
    returns b64_valid_quad(c0, c1, c2, c3)
    trace depends on c0, c1, c2, c3
    stack 64
}
