// Whether every byte of a run is zero.
def all_zero_from(xs, at) {
    if at == len(xs) then 1
    else if xs[at] != 0 then 0
    else all_zero_from(xs, at + 1)
}

def all_zero(xs) { all_zero_from(xs, 0) }

contract ode_all_zero(xs: n bytes, n: number) {
    returns all_zero(xs)
    trace depends on xs, n
    stack 0
}
