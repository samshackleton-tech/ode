// UTF-8 fast-path ASCII validator: returns 1 iff every byte in input[0..n] is < 128.
def ascii_from(a, at) {
    if at == len(a) then 1
    else if a[at] >= 128 then 0
    else ascii_from(a, at + 1)
}

contract ode_utf8_is_ascii(input: n bytes, n: number) {
    returns ascii_from(input, 0)
    trace depends on input, n
    stack 0
}
