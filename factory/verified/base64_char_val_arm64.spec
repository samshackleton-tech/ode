// RFC 4648 Section 4 Base64 alphabet decoder: A-Z -> 0..25, a-z -> 26..51,
// 0-9 -> 52..61, '+' (43) -> 62, '/' (47) -> 63; any other byte -> 255.
def b64_val(b) {
    if b >= 65 && b <= 90 then b - 65
    else if b >= 97 && b <= 122 then b - 71
    else if b >= 48 && b <= 57 then b + 4
    else if b == 43 then 62
    else if b == 47 then 63
    else 255
}

contract ode_b64_char_val(b: number) {
    requires b < 256
    returns b64_val(b)
    trace depends on b
    stack 0
}
