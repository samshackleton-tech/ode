// Canonical ASN.1 / DER SEQUENCE element walker: walks consecutive canonical DER TLVs
// spanning buf[0..n] with zero trailing garbage bytes.
// Returns 1 if buf[0..n] is a valid concatenation of canonical DER TLVs, 0 otherwise.
def der_seq_l1(buf, at) {
    if at + 3 > len(buf) then 0
    else if buf[at + 2] >= 128 && at + 3 + buf[at + 2] <= len(buf) then der_seq_from(buf, at + 3 + buf[at + 2])
    else 0
}

def der_seq_l2(buf, at) {
    if at + 4 > len(buf) then 0
    else if buf[at + 2] >= 1 && at + 4 + 256 * buf[at + 2] + buf[at + 3] <= len(buf) then der_seq_from(buf, at + 4 + 256 * buf[at + 2] + buf[at + 3])
    else 0
}

def der_seq_from(buf, at) {
    if at == len(buf) then 1
    else if at + 2 > len(buf) then 0
    else if buf[at] % 32 == 31 then 0
    else if buf[at + 1] < 128 then
        if at + 2 + buf[at + 1] <= len(buf) then der_seq_from(buf, at + 2 + buf[at + 1]) else 0
    else if buf[at + 1] == 129 then der_seq_l1(buf, at)
    else if buf[at + 1] == 130 then der_seq_l2(buf, at)
    else 0
}

contract ode_der_walk_seq(buf: n bytes, n: number) {
    returns der_seq_from(buf, 0)
    trace depends on buf, n
    stack 32
}
