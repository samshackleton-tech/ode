// Whether two runs of n bytes are the same. And the public contracts of the two functions: ode_equal, and
// ode_common, which it calls.

// How many bytes two runs have alike at their start (as in ../../../kcheck/programs/common/common.spec).
def alike(a, b, at) { if at == len(a) then at else if a[at] != b[at] then at else alike(a, b, at + 1) }

def common(a, b) { alike(a, b, 0) }

// 1 where every byte is alike, 0 where some byte differs.
def equal(a, b) { if common(a, b) == len(a) then 1 else 0 }

// =========================================================================================================
// The public contracts (what a contract means: LANGUAGE.md, part 2). Nothing is written, so the runs may overlap.
contract ode_common(a: n bytes, b: n bytes, n: number) {
    returns common(a, b)
    trace depends on a, b, n
    stack 40
}

contract ode_equal(a: n bytes, b: n bytes, n: number) {
    returns equal(a, b)
    trace depends on a, b, n
    stack 56
}
