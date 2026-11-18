// The low byte of one number and the low half of another, added.
def low(a, b) { a % 256 + b % 4294967296 }

// =========================================================================================================
// The public contract (what a contract means: LANGUAGE.md, part 2).
contract ode_low(a: number, b: number) {
    returns low(a, b)
    stack 0
}
