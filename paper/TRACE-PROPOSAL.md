# What a trace may depend on: naming values

*A proposal. Nothing in it is built. It replaces the "Proposed return rule" of `ODE.md` section 3 as that page stood in revision 4, which is withdrawn. It changes the formal model, so it waits for a decision. Each statement's basis is given at the end.*

## The proposal in three sentences

1. `trace depends on` may name expressions over the function's arguments, not only arguments: `trace depends on n, same(want, tag)`.
2. A function may let a number decide a jump, or use it in an address, only where that number is made of what its own clause names. Any other number it may compute with, store and return.
3. A returned number carries no permission and no restriction of its own. After a call the caller knows of it what the called function's `returns` says, and asks the question of sentence 2 about that expression.

## Two functions that compare

```
// 1 where the two runs hold the same bytes, 0 where they differ.
def same(a, b) { ... }

contract equal(a: n bytes, b: n bytes, n: number) {       // stops at the first byte that differs
    returns same(a, b)
    trace depends on a, b, n
}

contract equal_ct(a: n bytes, b: n bytes, n: number) {    // reads every byte, whatever the bytes are
    returns same(a, b)
    trace depends on n
}
```

Both return the same number. They differ in what a run of them shows: `equal` jumps on bytes, `equal_ct` folds the differences into one number and jumps on none.

Today the second contract cannot be shown. The verifier asks that a returned number be made of nothing the clause leaves out. `ode_far` returns `x + 2^63` and runs the same instructions whatever `x` is; with its `trace depends on x` taken away it is refused at the return. So today a function must name an input only because it returns something made of it.

## Three callers

Each is given a tag it expects (`want`) and a tag that arrived (`tag`), 32 bytes each, and calls one of the two functions. Only the lines that matter are written.

```
fn check {                        fn pick {                         fn keep {
    call equal_ct                     call equal_ct                     call equal_ct
    test rax, rax                     mov rax, [rbx + rax*8]            mov [rbx], al
    jz @bad                           ...                               ...
    ...                           }                                 }
}
```

`check` jumps on the answer. `pick` uses the answer in an address. `keep` stores the answer where its caller asked and does nothing else with it.

The least each caller's clause can say, under this proposal:

| The caller | calling `equal` | calling `equal_ct` |
|---|---|---|
| `check`: jumps on the answer | `want, tag` | `same(want, tag)` |
| `pick`: the answer in an address | `want, tag` | `same(want, tag)` |
| `keep`: stores the answer | `want, tag` | nothing |

The left column is what `equal` costs every caller: its own trace shows the bytes, so each caller's does. The right column is what the callers do themselves. A tag check has to act on the answer, so its trace depends on the answer, and its contract says so in those words. It does not depend on the bytes, and its contract no longer has to say that it does.

The cases, with the verdict the verifier is to give:

| | The function | Its clause | What it does | Verdict |
|---|---|---|---|---|
| 1 | `equal_ct` | `n` | returns the answer | shown: it jumps on no byte, and returning asks no permission |
| 2 | `check`, calling `equal_ct` | `same(want, tag)` | jumps on the answer | shown: by `equal_ct`'s `returns` the answer is `same(want, tag)`, which the clause names |
| 3 | `check`, calling `equal_ct` | nothing | jumps on the answer | refused at the jump: the flag is made of `same(want, tag)`, which the clause does not name |
| 4 | `pick`, calling `equal_ct` | nothing | the answer in an address | refused at the load, for the same reason |
| 5 | `pick`, calling `equal_ct` | `same(want, tag)` | the answer in an address | shown: a load at one of two addresses shows no more than a jump does |
| 6 | `keep`, calling `equal_ct` | nothing | stores the answer | shown |
| 7 | `check`, calling `equal` | `same(want, tag)` | jumps on the answer | refused at the call: `equal`'s trace depends on the bytes of `a` and `b`, and they are not made of `same(want, tag)` |
| 8 | `check`, calling `equal` | `want, tag` | jumps on the answer | shown, as today |
| 9 | `sign`: `y := ode_far(x)`, then a jump on `y` | nothing | jumps on `y` | refused at the jump: `y` is `x + 2^63`, and `x` is not named |
| 10 | the same | `x` | jumps on `y` | shown: `y` is made of `x` |

## What the clause means

Take two runs of the function, each from a state that meets `requires`. Let the two states agree on where things lie (the addresses the function is given, the stack, the loaded program), on every argument the clause names (for a run of bytes: on its bytes), and on the value of every expression the clause names. Then the two runs execute the same instructions at the same addresses and touch the same memory.

The two states may differ in everything else: the bytes of a run the clause does not name, a number it does not name, whatever the caller left in a register that carries no argument.

Three things follow from that sentence.

- Naming an expression does not name its arguments. Under `trace depends on same(want, tag)` no byte of `want` may decide a jump. Two runs with different tags that both fail look the same.
- A named expression is taken at entry. If the function also writes one of the runs, the clause still speaks of the bytes it was given.
- The clause is the one place that says what may show. A person who reads the contract reads the clause and the definitions its expressions use, and nothing in the code or the proof file can add to it.

As before, this is about which instructions run and which addresses they touch. It is not about elapsed time, speculative execution or what else a processor lets be observed.

## Where the verifier looks

**"Made of what the clause names."** An expression is so if it is a constant; an address the function is given; an argument the clause names; a byte of a run the clause names, at a place that is itself so; an expression the clause names, or one the proof shows equal to it; or an operation, or a use of a definition, on operands that are all so.

- **At a jump or an address**, as today: the flag or the register must be known to be made of what the clause names.
- **By value**, new: where the verifier has shown that a register holds the value of an expression E, and E is made of what the clause names, the register counts as made of what the clause names from there on. After a call, E is the called function's `returns` with the call's arguments put in. Elsewhere the proof file names the register and E, and the verifier shows the equality as it shows any other.
- **At a call**: for each thing the called function's clause names, with the call's arguments put in, the verifier must show it is made of what the caller's clause names. Today it asks this of arguments only.
- **At the return**: nothing about the number returned. Today's check there goes.

The second item is what the trial's two forms of one function need. Suppose `check` uses `equal_ct` inline: the same instructions, no call. The answer is then computed in `check`'s own code from bytes the clause does not name, and only a step that says "this register holds `same(want, tag)`" lets the jump through. Without that step the inline use would be refused where the call is shown.

## Why a returned number needs no rule of its own

Bytes that a function writes for its caller already have none. A function whose clause names only `n` may write a digest of the message. Its contract promises nothing about marks on those bytes, and the caller's verifier takes them as possibly made of anything. A returned number is eight more such bytes in a register. The present rule treats it differently, and `ode_far` shows the cost.

It also removes a thing that would otherwise travel in contracts. With a mark on returned numbers, every contract would have to say whether its result is marked, and a caller's result made of it would be marked in turn. Here no mark crosses a call. The value crosses, in `returns`, and each function is judged by its own clause.

## What changes

- **The language.** The clause takes expressions of the specification language. Today the reader refuses one ("name expected, not '('").
- **A contract.** It keeps the list of arguments the clause leaves out and gains the list of expressions the clause names. What it promises about marks at the return loses the line about the returned number.
- **The formal model.** Marks stay on places: registers, flags, bytes. The model's machine gets one kind of step that changes marks only. At a listed instruction it compares a register with the value, at entry, of a listed expression made of what the clause names; if they are equal the register's mark is cleared, and if not the machine stops, as it stops today where something marked decides a jump. At a call it compares in the same way each expression the called function's clause names. The list is the proof file's. The theorem about two runs gains one hypothesis, that the two entry states agree on the named expressions. Its conclusion stays about the plain machine, with no marks and no list in it. The argument: a specification expression has at most one value (`Value.unique`), so two runs that agree on the named expressions agree on every expression made of them, and so on the register.
- **The verifier.** The step by value; the wider question at a call; no check of the returned number; messages that say what a flag or an address is made of and that the clause does not name it.
- **The prover.** Where a jump is refused for a mark, it looks for an expression the register is known to hold and writes the item. After a call that is the `returns` expression.

Size, as an estimate: about a thousand lines of Lean and Python, most of them in the two files that prove the trace theorem (2,337 lines today). The fourteen jobs of the basket should keep their verdicts. One of them jumps on a number that a called function returned (`ode_equal`), and that number is made of arguments its clause names. That is a reading of the contracts and of the code, to be confirmed by running them.

## What this does not do

- It does not make `equal`'s contract finer. `equal`'s trace depends only on `n` and on where the first difference lies, and the rule would allow a clause that says so. Showing it needs a fact about the definition (below the first difference the bytes are alike) that is shown by induction. Whether today's verifier can show that is not known.
- A caller can use a returned number in the trace only where the called function's contract gives it by `returns E`. A result described only by relations in `ensures` is not known to be made of anything.
- Two expressions written differently are different until the proof shows them equal: `same(tag, want)` is not `same(want, tag)` by itself.
- Bytes in memory are not cleared by value in the first version, only registers. A value stored and loaded again keeps the standing it had when stored.
- A clause for an entry point that Rust or C calls is a separate question and stays open.

## Other ways considered

- **A mark on the returned number, yes or no.** Too coarse: `check` must be able to jump on `equal_ct`'s answer, and `pick` without the clause must not.
- **A mark for each input the result is made of.** Still wrong for `check`: the answer is made of `want` and `tag`, and `check` should not have to name them.
- **A word in the code that releases a number** (`reveal rax`). It would put the permission in the code, which a reader of the contract does not read. Here the permission is in the clause and the code only uses it.
- **No marks at all: the verifier follows two runs at once.** It would replace the trace proofs whole. The step by value gets the same verdicts on these examples with the present machinery.

## What is asked

1. The three sentences at the top, and the meaning.
2. The step by value at any instruction, not only after a call. The narrower form is a smaller change to the model, and it would refuse an inline use where it shows the call.
3. Whether the theorem about two runs should then state the agreement of the two entry states directly, with no mark in its statement. It is a restatement, and it shortens what a reader of that theorem reads.

## The tests, written before the rule is built

The ten cases above, each with its verdict and, for a refusal, the instruction and the reason. And these, which must be refused:

- `equal_ct`'s contract over code that jumps on a byte;
- `check` with `trace depends on same(want, tag)` whose code jumps on `want[0]`;
- a proof item that says a register holds `same(want, tag)` where it holds something else;
- a proof item for an expression that is not made of what the clause names;
- `check` calling `equal_ct` with the runs in the other order, with no step that shows the two expressions equal;
- the function of case 2 with the callee's `returns` taken away.

Each form is tried as a call and as an inline use, and on both processors once the second has a verifier.

## Basis

**Measured.** Three small programs in `paper/trial/trace/`, run on November 22 on an x86-64 work machine with the repository's verifier; `today.txt` there holds what they printed. `ode_far` without its `trace depends on x`, with the kept proof: refused, at the return. `ode_equal`, which calls `ode_common` and jumps on the number returned: shown as kept; with the runs, or the count, or the whole line left out of its clause it is refused with the kept proof, at the call (case 8 and case 7 in today's terms). The reader, given `trace depends on n, common(a, b)`: "name expected, not '('".

**Read in the code.** A contract's list of what the clause leaves out, and what it promises about marks at entry and at the return (`Contract.lean`, `quietAt`, `quietAfter`). The marks and the theorem about two runs (`Machine.lean`, `Trace.lean`, `SoundTop.lean`: `verify_all_trace`, whose conclusion is about the plain machine). What the verifier takes as not marked after a call, and what it asks at one (`Core.lean`: `afterCallQ`, `callQuiet`, `quietAtCall`). The contracts of the basket's fourteen jobs, for what they return. That a specification expression has at most one value (`SoundSpec.lean`: `Value.unique`).

**Judgment.** The size. That the step by value is sound: the argument is given above and is not yet a proof. That the basket keeps its verdicts.

**Not known.** Whether `equal`'s finer clause can be shown today. Whether a named expression must be shown to have a value under `requires`, or whether "the two runs agree on it" may include "neither has one".
