// Canonical unsigned 32-bit LEB128 / Protobuf / WebAssembly varint decoder.
// Rejects empty/truncated input, non-canonical trailing 0x00 bytes on multi-byte encodings,
// and >32-bit overflow (5th byte >= 16), returning 4294967296 (2^32) as sentinel.
def varint32(a) {
    if len(a) == 0 then 4294967296
    else if a[0] < 128 then a[0]
    else if len(a) == 1 then 4294967296
    else if a[1] < 128 then
        if a[1] == 0 then 4294967296 else (a[0] - 128) + 128 * a[1]
    else if len(a) == 2 then 4294967296
    else if a[2] < 128 then
        if a[2] == 0 then 4294967296 else (a[0] - 128) + 128 * (a[1] - 128) + 16384 * a[2]
    else if len(a) == 3 then 4294967296
    else if a[3] < 128 then
        if a[3] == 0 then 4294967296 else (a[0] - 128) + 128 * (a[1] - 128) + 16384 * (a[2] - 128) + 2097152 * a[3]
    else if len(a) == 4 then 4294967296
    else if a[4] < 16 then
        if a[4] == 0 then 4294967296 else (a[0] - 128) + 128 * (a[1] - 128) + 16384 * (a[2] - 128) + 2097152 * (a[3] - 128) + 268435456 * a[4]
    else 4294967296
}

contract ode_varint_decode_u32(input: n bytes, n: number) {
    returns varint32(input)
    trace depends on input, n
    stack 0
}
