// Parts of a number.

// The low byte of one number and the low half of another, added.
def low(a, b) { a % 256 + b % 4294967296 }

// A number's quotient by eight, rounded down.
def eighth(a) { a / 8 }

// =========================================================================================================
// The public contracts (what a contract means: LANGUAGE.md, part 2).
contract ode_low(a: number, b: number) {
    returns low(a, b)
    stack 0
}

contract ode_eighth(a: number) {
    returns eighth(a)
    stack 0
}
