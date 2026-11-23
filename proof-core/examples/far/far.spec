// The number 2^63 added and taken away; and 8 taken away by an addition.

// =========================================================================================================
// The public contracts (what a contract means: LANGUAGE.md, part 2). Each function runs the same instructions
// whatever x is, and touches no memory but its return address, so its trace depends on nothing.
contract ode_far(x: number) {
    requires x <= 9223372036854775807
    returns x + 9223372036854775808
    stack 0
}

contract ode_near(x: number) {
    requires x >= 9223372036854775808
    returns x - 9223372036854775808
    stack 0
}

contract ode_less(x: number) {
    requires x >= 8
    returns x - 8
    stack 0
}
