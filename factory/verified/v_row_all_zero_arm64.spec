// Stage 1 Verifier-in-Ode (`Arithmetic.refutes`): returns 1 iff every coefficient
// byte in row[0..n] is zero.
def row_zero_from(a, at) {
    if at == len(a) then 1
    else if a[at] != 0 then 0
    else row_zero_from(a, at + 1)
}

contract ode_v_row_all_zero(row: n bytes, n: number) {
    returns row_zero_from(row, 0)
    trace depends on row, n
    stack 0
}
