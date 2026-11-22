// The number 2^63 added and taken away; and 8 taken away by an addition.

// =========================================================================================================
// The public contracts (what a contract means: LANGUAGE.md, part 2). Each function runs the same instructions
// whatever x is, and touches no memory but its return address. The contracts say `trace depends on x` all the
// same, for the number returned: the verifier in Lean takes the number a function returns as one that its
// caller's trace may depend on, so it must be made of nothing that is hidden.
contract ode_far(x: number) {
    requires x <= 9223372036854775807
    returns x + 9223372036854775808
    trace depends on x
    stack 0
}

contract ode_near(x: number) {
    requires x >= 9223372036854775808
    returns x - 9223372036854775808
    trace depends on x
    stack 0
}

contract ode_less(x: number) {
    requires x >= 8
    returns x - 8
    trace depends on x
    stack 0
}
