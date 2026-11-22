// 1 where two arrays hold the same bytes, 0 where some byte differs.
def same_from(a, b, at) {
    if at == len(a) then 1
    else if a[at] != b[at] then 0
    else same_from(a, b, at + 1)
}

def same(a, b) { same_from(a, b, 0) }

contract ode_equal_early(a: n bytes, b: n bytes, n: number) {
    returns same(a, b)
    trace depends on a, b, n
    stack 0
}
