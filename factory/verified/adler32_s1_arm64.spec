// RFC 1950 Adler-32 s1 sequence: s[0] = 1, s[i+1] = (s[i] + input[i]) % 65521.
sequence s1(bytes) { s[0] = 1   s[i + 1] = (s[i] + bytes[i]) % 65521 }

contract ode_adler32_s1(input: n bytes, n: number) {
    returns s1(input)[n]
    trace depends on input, n
    stack 0
}
