// Canonical ASN.1 / DER TLV parser (ITU-T X.690 Section 10.1).
// Enforces single-byte tag (tag % 32 != 31), rejects indefinite length (0x80),
// rejects non-minimal long forms (0x81 with len < 128; 0x82 with high byte 0),
// rejects lengths > 65535 (0x83+), and enforces header + length <= len(buf).
// Returns total TLV byte size (header + content) if valid, or 0 if malformed/truncated.
def der_tlv_l1(buf, at) {
    if at + 3 > len(buf) then 0
    else if buf[at + 2] >= 128 && at + 3 + buf[at + 2] <= len(buf) then 3 + buf[at + 2]
    else 0
}

def der_tlv_l2(buf, at) {
    if at + 4 > len(buf) then 0
    else if buf[at + 2] >= 1 && at + 4 + 256 * buf[at + 2] + buf[at + 3] <= len(buf) then 4 + 256 * buf[at + 2] + buf[at + 3]
    else 0
}

def der_tlv_size(buf, at) {
    if at + 2 > len(buf) then 0
    else if buf[at] % 32 == 31 then 0
    else if buf[at + 1] < 128 then
        if at + 2 + buf[at + 1] <= len(buf) then 2 + buf[at + 1] else 0
    else if buf[at + 1] == 129 then der_tlv_l1(buf, at)
    else if buf[at + 1] == 130 then der_tlv_l2(buf, at)
    else 0
}

contract ode_der_tlv_len(buf: n bytes, n: number) {
    returns der_tlv_size(buf, 0)
    trace depends on buf, n
    stack 0
}
