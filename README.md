Ode: a short poem of praise

## The toy implementation, and how to check it yourself

`ode/` is an initial, toy-scale implementation of `SPEC.md`: an executable
specification, a compiler to a straight-line byte machine (ODE8), a
deterministic emitter, a small independent checker that proves the emitted
bytes compute the specification on *every* input (by exhaustion over the
whole domain), and an assurance map generated from the checker record.
Nothing is trusted between the specification and the checker.

Verify the worked example end to end (Python 3, no dependencies):

```sh
pypy3 -m unittest discover -s tests     # 11 tests, incl. mutants the checker must reject
pypy3 -m ode build examples/mix.json examples/build
pypy3 -m ode check examples/build       # ACCEPT, 65536 cases
pypy3 -m ode run   examples/build 60 165   # 174
pypy3 -m ode assure examples/build      # writes and prints examples/build/assurance.md
```

Hand-check the run: the specification (`examples/mix.json`) is
`mix(x, k) = rotl3((x XOR k) + 60)`, so `mix(60, 165)`: `60 XOR 165 = 153`,
`153 + 60 = 213`, `rotl3(213) = 174`. Then flip any byte of the binary in a
copy of `examples/build/` and run `check` again: it rejects, and the test
suite shows it also rejects a mutant whose hashes were honestly recomputed.
