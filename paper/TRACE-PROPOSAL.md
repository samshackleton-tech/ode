# What a function's trace may depend on

*This is a proposal. Nothing in it is built. It replaces the "Proposed return rule" that revision 4 of `ODE.md` had in section 3; that rule is withdrawn. It changes the formal model, so it waits for a decision. Question 4 of section 12 was added last, and its recommendation changes point 3 of section 4. The last section says which statements here are measured, which are read from the code, and which are judgment.*

## 1. Two terms

**The trace.** When a function runs, the processor executes some sequence of instructions, and those instructions read and write memory at some sequence of addresses. That record, which instructions ran and which addresses they touched, is the function's *trace*. Someone who can time the function, or watch which parts of the cache it uses, learns about the trace. They do not learn, that way, the values in the registers.

**The `trace depends on` line.** A contract may have a line such as

```
trace depends on n
```

It is a promise about any two runs of the function: *if the two runs are given the same `n`, and the same addresses, they have the same trace, whatever else differs between them.* The line lists everything that is allowed to influence the trace. An input that is not listed may still change what the function computes. It may not change which instructions run or which addresses they touch.

Today the line can list only arguments, by name.

## 2. Two functions that compare bytes

Both are given two arrays of `n` bytes, `a` and `b`. Both return 1 if the arrays hold the same bytes and 0 if they do not. In the specification language that number is `same(a, b)`:

```
def same_from(a, b, at) {
    if at == len(a) then 1
    else if a[at] != b[at] then 0
    else same_from(a, b, at + 1)
}

def same(a, b) { same_from(a, b, 0) }
```

**`equal` stops at the first pair of bytes that differ.**

```
fn equal as "ode_equal_early" {
  xor ecx, ecx                    // i := 0
  @loop:
  cmp rcx, rdx
  jae @same                       // i reached n: a jump on the count alone
  mov r8, rdi
  add r8, rcx
  movzx eax, byte ptr [r8 + 0]    // a[i]
  mov r9, rsi
  add r9, rcx
  movzx r9d, byte ptr [r9 + 0]    // b[i]
  cmp rax, r9
  jne @differ                     // a jump on two bytes
  add rcx, 1
  jmp @loop
  @same:
  mov rax, 1
  jmp @done
  @differ:
  xor eax, eax
  @done:
  ret
}
```

The jump marked "a jump on two bytes" is taken or not taken depending on two bytes of the arrays. So how many instructions run depends on the bytes, and the contract has to list them:

```
contract equal(a: n bytes, b: n bytes, n: number) {
    returns same(a, b)
    trace depends on a, b, n
}
```

**`equal_ct` reads every byte, whatever the bytes are.**

```
fn equal_ct as "ode_equal_ct" {
  xor ecx, ecx                    // i := 0
  xor r10d, r10d                  // r10: the differences seen so far, all or-ed together
  @loop:
  cmp rcx, rdx
  jae @end                        // i reached n: a jump on the count alone
  mov r8, rdi
  add r8, rcx
  movzx eax, byte ptr [r8 + 0]    // a[i]
  mov r9, rsi
  add r9, rcx
  movzx r9d, byte ptr [r9 + 0]    // b[i]
  sub rax, r9
  and rax, 255                    // zero where the two bytes are the same
  or r10, rax
  add rcx, 1
  jmp @loop
  @end:
  sub r10, 1                      // r10 was 0 (no difference seen): now every bit is set; else it is 0 to 254
  shr r10, 63                     // the top bit: 1 where no difference was seen, 0 where one was
  mov rax, r10
  ret
}
```

Its one conditional jump compares the counter with `n`. No jump is taken or not taken depending on a byte, and no address is computed from a byte. So any two runs with the same `n` execute the same instructions and touch the same addresses. Its contract:

```
contract equal_ct(a: n bytes, b: n bytes, n: number) {
    returns same(a, b)       // what the returned number is
    trace depends on n       // what may influence which instructions run and which addresses they touch
}
```

The two lines answer two different questions. `returns` says what the returned number is. A function that calls `equal_ct` learns from that line, and from nowhere else, what the answer depends on (section 4). `trace depends on` is about `equal_ct`'s own instructions and addresses.

**Why the second line does not list `same(a, b)`.** The number that `equal_ct` returns depends on whether the arrays are the same. Its trace does not: the same instructions run either way, and only the value left in `rax` differs. The line is about the trace, not about the returned number. Counted by a processor, for two arrays of 32 bytes:

| Instructions executed by one call | The arrays are the same | They differ in the first byte | They differ in the last byte |
|---|---|---|---|
| `equal` | 401 | 24 | 396 |
| `equal_ct` | 435 | 435 | 435 |

**What today's verifier says of them.**

- `equal` with the contract above: the verifier prints `shown`. With `trace depends on n` alone it prints `refused`, at the jump on two bytes.
- `equal_ct` with the contract above cannot be approved today, for a reason that has nothing to do with its trace. Today's verifier has one more rule: *the number a function returns must be computed only from what its `trace depends on` line lists.* `equal_ct`'s answer is computed from the bytes, and its line does not list them.
- This was tried on a form of `equal_ct` that today's verifier can follow (`differ_ct`, in the same file as the two above). With `trace depends on n` the verifier went through the whole loop, every jump and every address, without objection. It refused at the last instruction, because of the number returned.

That extra rule is what this proposal removes.

## 3. Three functions that call `equal_ct`

Each is given two tags of 32 bytes: the tag it expects, `want`, and the tag that arrived, `tag`. Each calls `equal_ct(want, tag, 32)` and then does something with the answer. These are sketches with only the lines that matter.

```
fn check {
    ...
    call equal_ct             // rax := same(want, tag)
    cmp rax, 0
    je @bad                   // a jump decided by the answer
    ...                       // what a good tag allows
  @bad:
    ...
}
```

**`check` jumps on the answer.** If the answer is 1 it goes one way, if 0 the other. So `check`'s trace is different for a good tag and for a bad one. It differs in nothing else: no jump in `check` or in `equal_ct` is decided by a byte of either tag. `check`'s trace depends on exactly one thing about the tags, whether they are the same, and its contract should say exactly that:

```
trace depends on same(want, tag)
```

Today the only line `check` could have is `trace depends on want, tag`. That line would also allow a jump on any single byte of either tag, which `check` does not do. A person reading the contract could not tell the difference.

```
fn pick {                     // the table's address is in rbx
    ...
    call equal_ct             // rax := same(want, tag)
    mov rax, [rbx + rax*8]    // reads the table's entry 0 or its entry 1
    ...
}
```

**`pick` uses the answer to choose which entry of a table it reads.** Which address it reads depends on the answer, so its trace does too. Its contract needs the same line as `check`'s.

```
fn keep {                     // the address to store at is in rbx
    ...
    call equal_ct             // rax := same(want, tag)
    mov [rbx], rax            // stores the answer where its caller asked
    ...
}
```

**`keep` stores the answer.** No jump in `keep` is decided by the answer, and no address is computed from it. Its trace depends on nothing about the tags, and its contract needs no `trace depends on` line.

**The same three, calling `equal` instead.** `equal`'s instructions run as part of the caller's run, and which of them run depends on the bytes. So each caller's contract has to list the bytes, whatever the caller itself does with the answer.

Put together, this is the `trace depends on` line that each caller's contract needs:

| The caller | What it does with the answer | If it calls `equal_ct` | If it calls `equal` |
|---|---|---|---|
| `check` | jumps on it | `trace depends on same(want, tag)` | `trace depends on want, tag` |
| `pick` | reads a table entry chosen by it | `trace depends on same(want, tag)` | `trace depends on want, tag` |
| `keep` | stores it | no line needed | `trace depends on want, tag` |

## 4. The proposal

**1. The line may list a computed value** such as `same(want, tag)`: any expression of the specification language over the function's arguments. Today it can list only arguments.

**2. The rule for a function's code stays what it is, and now covers such values.** In a function's code, a conditional jump may be decided only by, and a memory address may be computed only from, these things: constants; the addresses the function was given; and what the `trace depends on` line of that function's contract lists.

"That function's contract" matters where one function calls another, because two contracts are then in play. `check`'s code is judged by the line in `check`'s contract. `equal_ct`'s code was judged by the line in `equal_ct`'s contract, when `equal_ct` was verified. At the call the verifier asks one more thing. `equal_ct`'s trace becomes part of `check`'s, so whatever `equal_ct`'s line lists (here `n`, which is 32 in this call) must be computed only from constants and from what `check`'s line lists.

**3. One rule is removed.** Today the number a function returns must also be computed only from what its line lists. Under the proposal a function may return any number it has computed. Returning a number does not change the trace. If the caller then jumps on that number, that is a jump in the caller's code, and point 2 judges it by the line in the caller's contract.

**How a caller learns what a returned number depends on.** From the called function's `returns` line. `equal_ct`'s contract says `returns same(a, b)`, and `check` passed `want` and `tag` as `a` and `b`. So after the call the verifier knows that `rax` holds `same(want, tag)`. That is more than knowing what the number depends on: it is knowing what the number is. The line in `check`'s contract lists `same(want, tag)`, so the jump on `rax` is allowed. If `check`'s contract had no such line, the jump would be refused. A caller cannot jump on the answer by oversight: until the verifier knows that a returned number is computed only from what the caller's line lists, it refuses every jump and every address that uses it.

## 5. What the verifier would accept and refuse

| | The function | Its `trace depends on` line | What its code does | The verifier | Why |
|---|---|---|---|---|---|
| 1 | `equal_ct` | `n` | returns the answer | accepts | No jump or address in it depends on a byte. The number it returns is computed from the bytes, which point 3 allows. |
| 2 | `check`, calling `equal_ct` | `same(want, tag)` | jumps on the answer | accepts | The answer is `same(want, tag)`, by `equal_ct`'s `returns`, and the line lists it. |
| 3 | `check`, calling `equal_ct` | none | jumps on the answer | refuses, at the jump | The jump is decided by `same(want, tag)`, which no line lists. |
| 4 | `pick`, calling `equal_ct` | none | reads a table entry chosen by the answer | refuses, at the read | The address is computed from `same(want, tag)`, which no line lists. |
| 5 | `pick`, calling `equal_ct` | `same(want, tag)` | the same | accepts | The line lists the value the address is computed from. |
| 6 | `keep`, calling `equal_ct` | none | stores the answer | accepts | Storing a number is not a jump, and the address stored at is not computed from the answer. |
| 7 | `check`, calling `equal` | `same(want, tag)` | jumps on the answer | refuses, at the call | `equal`'s line lists the bytes of both arrays. They are not computed from `same(want, tag)`. |
| 8 | `check`, calling `equal` | `want, tag` | jumps on the answer | accepts, as today | Everything involved is computed from `want` and `tag`. |
| 9 | `sign`, which calls `ode_far(x)` (it returns `x + 2^63`) and jumps on the result | none | jumps on the result | refuses, at the jump | The result is computed from `x`, which no line lists. |
| 10 | the same | `x` | the same | accepts | The result is computed from `x`. |

## 6. The promise, stated exactly

Run the function twice, each time from a state that meets `requires`. Suppose the two runs are given the same addresses (the addresses passed as arguments, the stack, and where the program is loaded) and the same value for everything the line lists: for a listed number, the same number; for a listed array, the same bytes; for a listed expression, the same value. Then the two runs execute the same instructions at the same addresses, and read and write the same memory addresses.

The two runs may differ in everything else.

Three consequences:

- Listing `same(want, tag)` does not list `want` or `tag`. With that line, two runs with two different wrong tags have the same trace, because `same(want, tag)` is 0 in both.
- A listed expression is worked out from the arguments as they are when the function is called. If the function later writes into one of the arrays, the line still speaks of the bytes it was given.
- The line is the one place that says what the trace may depend on. A person who reads the contract reads the line and the definitions that its expressions use. Nothing in the code or in the proof file can add to the list.

As before, this is about which instructions run and which addresses they touch. It is not a promise about elapsed time, about speculative execution, or about everything else that a processor lets someone observe.

## 7. How the verifier would check it

**Today.** As the verifier steps through a function's instructions it keeps one yes-or-no fact for each register and flag: is this value known to be computed only from listed things? At entry the answer is yes for the listed arguments and for addresses. An instruction that computes from such values gives such a value. A byte loaded from an array that is not listed does not. Where a conditional jump is decided by a flag whose answer is no, or an address is computed from a register whose answer is no, the verifier refuses.

**New: one more way to get a yes.** Where the verifier has proved that a register holds a particular value, and that value is computed only from listed things, the register's answer becomes yes. After a call this needs no extra work: the called function's `returns` line says what `rax` holds. Anywhere else, the proof file says "at this instruction, this register holds this expression", and the verifier proves that as it proves any other fact about values.

The second case is for a function used inline. Suppose `check` does not call `equal_ct` but has the same instructions in its own code. The answer is then computed in `check`'s own code, from the bytes, so its yes-or-no fact is no. Only a proved statement "this register holds `same(want, tag)`" turns it into yes. Without that, the inline form would be refused where the call is accepted, though both execute the same instructions.

**At a call.** Everything the called function's line lists, with the call's arguments put in, must be computed only from constants and from what the caller's line lists. Today this is asked of listed arguments. It would now be asked of listed expressions too.

**At the return.** Nothing is asked about the number returned.

## 8. Why the rule about returned numbers can go

It is not needed for the promise of section 6, because returning a number does not change the trace.

It is also at odds with how bytes written to memory are treated today. A function whose line lists only `n` may write a hash of its whole input into an array for its caller. Its contract says nothing about whether those bytes were computed only from listed things, and the caller's verifier assumes that they were not. A returned number is eight more such bytes, in a register instead of in memory. Today it alone is held to the stricter rule.

And without the rule, nothing about the trace has to pass from one function's contract to the next along with a result. If a returned number carried its own "computed only from listed things: yes or no", every contract would have to state it, and whatever a caller computed from that number would need one in turn. Under the proposal what passes is the value, in `returns`, and each function's code is judged by the line in its own contract.

## 9. What would change

- **The specification language.** The `trace depends on` line accepts expressions. Today the reader stops at one, with "name expected, not '('".
- **A contract in the formal model.** It keeps its list of the arguments that the line does not list, and gains the list of the expressions that it does. The sentence that says "the returned number is computed only from listed things" is deleted.
- **The machine in the formal model.** The model's machine carries the same yes-or-no facts (the code calls them marks) and stops where a marked value decides a jump or is used in an address. It gets one new kind of step, which changes only the marks. At an instruction that the proof file names, it compares a register with the value of an expression that the proof file also names, and which must be computed only from listed things. If the two are equal, the register's mark is cleared. If not, the machine stops, so the verifier has to prove that they are always equal. At a call the machine compares, in the same way, each expression that the called function's line lists.
- **The theorem about two runs.** It gains one assumption: the two runs are given the same values for the listed expressions. Its conclusion does not change, and is about the plain machine, which has no marks. Why the new step is sound: an expression of the specification language has at most one value for given inputs (the model already proves this, as `Value.unique`). So if two runs are given the same values for the listed things, every expression computed only from listed things has the same value in both. At the new step each run's register equals that value, so the two registers are equal, which is what a cleared mark claims. This is an argument, not yet a proof in Lean.
- **The verifier.** The new step; the wider question at a call; no check of the returned number; and messages that say which value a jump or an address depends on and that the line does not list it.
- **The prover.** Where a jump is refused, it looks for an expression that the register is known to hold and writes the item into the proof file. After a call, that expression is the `returns` expression.

Size, as an estimate: about a thousand lines of Lean and Python, most of them in the two files that prove the theorem about two runs (2,337 lines today).

The fourteen verification jobs that serve as a fixed basket should keep their verdicts. One of them (`ode_equal`) jumps on a number that a called function returned, and that number is computed from arguments that its line lists. This comes from reading the contracts and the code, and is to be confirmed by running the jobs.

## 10. What this does not do

- It does not make `equal`'s contract more exact. `equal`'s trace really depends only on `n` and on where the first difference is, and the rule would allow a line that says so. Proving it needs a fact about the definition (before the first difference, the bytes are the same) that takes an induction. Whether today's verifier can show that is not known.
- A caller can jump on a returned number only if the called function's contract says exactly what the number is, with `returns E`. If the contract only relates the result to other things with `ensures`, the verifier does not know what the number was computed from, and refuses a jump on it. Today's rule does give callers that knowledge: under it every returned number is computed only from what the called function's line lists. For example, `ode_varint`'s contract says `returns r` and `ensures out[0 .. r] = varint(v)`. A caller that went round a loop `r` times is acceptable today, and under the proposal would be refused until `ode_varint`'s contract said what `r` is (the length of `varint(v)`). No function in the repository does this today. Question 4 of section 12 is about exactly this.
- Two expressions that are written differently count as different until the proof shows that they are equal. `same(tag, want)` is not `same(want, tag)` without such a step.
- In the first version the new step of section 7 applies to registers only, not to bytes in memory.
- What the line should say for a function that Rust or C calls is a separate question and is still open.

## 11. Other designs considered

- **Give each returned number a yes or a no: may the caller jump on it?** Too coarse. `check` must be able to jump on `equal_ct`'s answer, and `pick` without the line must not be able to use it in an address. One yes or no cannot give both verdicts.
- **Record, for each returned number, which inputs it was computed from.** Still wrong for `check`. The answer is computed from `want` and `tag`, so `check` would have to list both tags, which is the over-broad line that section 3 set out to avoid.
- **A word in the code that releases a number for use in jumps** (`reveal rax`). What allows the jump would then be written in the code, which a person reading the contract does not read. In the proposal it is written in the contract's line, and the code only uses it.
- **A line that says what the returned number is computed from, without saying what the number is.** An earlier form of this page set it aside. It is now question 4 of section 12, with the recommendation to take it.
- **No yes-or-no facts at all; the verifier reasons about two runs at once.** That would replace the existing proofs about the trace entirely. The proposal gets the same verdicts on these examples with what exists.

## 12. What is asked

1. **The three points of section 4.**
2. **Where the new step of section 7 may be used:** (a) at any instruction, or (b) only right after a call. Form (b) is a smaller change to the formal model. But with (b), `check` with `equal_ct`'s instructions inline is refused, although the same instructions behind a call are accepted. The recommendation is (a).
3. **Whether to restate the theorem about two runs.** Today its assumption is phrased through the marks, so a person reading the theorem has to read their definition too. It could instead say directly: "the two runs are given the same addresses and the same values for the listed things". It is the same theorem, shorter to read. The recommendation is to do it in the same change.
4. **Whether the rule about the returned number should stay as the default, with a line of its own that widens it.** This question was added after the other three. Its recommendation changes point 3 of section 4, which removes the rule.

   The new line would stand beside `trace depends on`. Take `differ_ct` (in the same file as `equal_ct`). It is `equal_ct` without the last step, the one that turns the differences into 1 or 0: it returns 0 where the arrays hold the same bytes, and another number where they differ. Here is a contract for it that does not say which number:

   ```
   contract differ_ct(a: n bytes, b: n bytes, n: number) {
       returns r
       trace depends on n
       result depends on a, b
   }
   ```

   `result depends on a, b` promises that the returned number is computed only from `a`, from `b`, and from what the `trace depends on` line lists. Said as in section 6: two runs that are given the same addresses, the same `n`, and the same bytes in `a` and in `b` return the same number. The line does not say what the number is.

   The rule about the returned number would then have three cases:

   - The contract says what the number is, with `returns E`. Nothing more is asked. A caller knows the value, as in section 4.
   - The contract does not say what the number is, and has no `result depends on` line. Today's rule holds: the number must be computed only from what the `trace depends on` line lists. A contract that exists today and does not say what its number is, such as `ode_varint`'s, keeps its meaning.
   - The contract does not say what the number is, and has the line. The number must be computed only from what the two lines list.

   In the second and third cases a caller may let the returned number decide a jump, or use it in an address, if everything the two lines list, with the call's arguments put in, is computed only from constants and from what the caller's own line lists. If it is not, the caller may still store the number or compute with it. In the second case that is already asked at every call (section 7), so there the caller may always jump on the number, as today.

   **What it costs a caller.** The less a called function's contract says about its number, the more a caller that jumps on the number has to list. The table shows the `trace depends on` line that the contracts of `check` and `keep` (section 3) need, by which function they call.

   | The caller | If it calls `equal_ct`, whose contract says `returns same(a, b)` | If it calls `differ_ct`, whose contract says `result depends on a, b` |
   |---|---|---|
   | `check`, which jumps on the answer | `trace depends on same(want, tag)` | `trace depends on want, tag` |
   | `keep`, which stores the answer | no line needed | no line needed |

   After `differ_ct`, the verifier knows only that the answer is computed from the two tags. So `check`'s line has to list both tags, and that line would also allow a jump on any single byte of either (section 3). After `equal_ct`, the line can list exactly `same(want, tag)`.

   **What the line buys.**

   - A contract need not say more about its number than its callers use, and the maker may change the number later without changing the contract.
   - A cheaper proof. "Computed only from these things" is what the yes-or-no facts of section 7 show. "Equal to this expression" needs a proof about the definition.
   - In the contract of a function that Rust or C calls, the line tells a reader what the returned number can reveal. `result depends on a, b` says that it can reveal more than whether the arrays are the same.

   **What keeping today's rule as the default buys.** Take code whose trace may depend on all of its input, such as a parser or the verifier written in Ode. Every number that such code computes from its input is computed only from listed things. So today's rule costs it nothing, and lets every caller jump on every returned number. With the rule removed, as point 3 has it, each such jump would need a called function whose contract says exactly what the number is. Section 10 names this loss. It does not arise in the functions of the repository today. It would arise in such code wherever a caller jumps on a result whose contract does not say what it is.

   **What the line costs.**

   - One more kind of line to read, and two lists to keep apart.
   - A function whose contract has the line is verified twice: once against its `trace depends on` line without the rule about the returned number, and once against the two lines together with today's rule. For `differ_ct` both were tried on today's verifier (the two results for `differ_ct` in the last section). The second is `shown`. The first goes through every jump and every address and is refused only at the return, by the rule that it would no longer apply.
   - More to prove in the formal model: a contract with two lists, and at a call the choice between them. As an estimate, a few hundred lines beyond the thousand of section 9.

   An earlier form of this page set the line aside because it would need a second set of yes-or-no facts inside the verifier. That was wrong. It needs the same facts worked out a second time, against a longer list.

   The recommendation is to take the line and to keep today's rule as the default. Point 3 of section 4 would then read: *today the number a function returns must be computed only from what its `trace depends on` line lists. Under the proposal a contract that says what the number is promises nothing more about it; a contract that does not may add a `result depends on` line, and the number must then be computed only from what the two lines list.* Sections 5 to 9 and the tests of section 13 would change with it.

## 13. The tests, to be written before the rule is built

The ten cases of section 5, each with its verdict and, for a refusal, the instruction and the reason. And these six, each of which the verifier must refuse:

- `equal_ct`'s contract over code that has a jump decided by a byte;
- `check` with `trace depends on same(want, tag)` whose code jumps on the first byte of `want`;
- a proof file that says a register holds `same(want, tag)` where it holds something else;
- a proof file that says a register holds an expression which is not computed only from listed things;
- `check` calling `equal_ct` with the two tags in the other order, and no step that shows `same(tag, want)` equal to `same(want, tag)`;
- case 2 with the `returns` line taken out of `equal_ct`'s contract.

Each is tried with a call and with the same instructions inline, and on both processors once the second has a verifier.

## Which statements are measured, read, or judgment

**Measured**, on November 22, 2026, on an x86-64 Linux work machine with the repository's verifier. The programs and what they printed are in `paper/trial/trace/`.

- `equal`, `equal_ct` and `differ_ct` (`compare.ode`) agree with C in 1,681 cases; the instruction counts of section 2 (`compare_run.py`; each count includes the few instructions of the loop that makes the call, the same in every row).
- `equal` with `returns same(a, b)` and `trace depends on a, b, n`: `shown` (statement 919 bytes, proof 538 bytes). With `trace depends on n` alone and the same proof: `refused`, at the jump on two bytes (`compare_verify.py`).
- `equal_ct` as written cannot be put to today's verifier at all. Today's verifier does not follow a subtraction whose result can go below zero, and two of `equal_ct`'s can: with either of them left as it is the prover finds no proof, whatever the line lists, and with both changed the function is `shown` (`compare_diag.py`). `differ_ct` is `equal_ct` with both changed; it returns 0 where the arrays are the same and another number where they differ. With `trace depends on a, b, n`: `shown` (statement 701 bytes, proof 412 bytes). With `trace depends on n` alone, the same proof, and one added line that lets the register of differences depend on the bytes inside the loop: `refused`, at the return, for the number returned (`compare_verify.py`).
- `ode_far`, which returns `x + 2^63` and executes the same instructions whatever `x` is: with its `trace depends on x` taken away and the kept proof, `refused` at the return (`far_trace.py`).
- `ode_equal`, which calls `ode_common` and jumps on the number returned: `shown` as kept. With the arrays, or the count, or the whole line left out of its `trace depends on`, and the kept proof: `refused`, at the call (`equal_trace.py`).
- The reader, given `trace depends on n, common(a, b)`: "name expected, not '('" (`line_today.py`).

**Read in the code.** What a contract promises about marks at entry and at the return (`Contract.lean`: `quietAt`, `quietAfter`). The marks, and the theorem about two runs with its conclusion about the plain machine (`Machine.lean`, `Trace.lean`, `SoundTop.lean`: `verify_all_trace`). What the verifier takes as not marked after a call and what it asks at one (`Core.lean`: `afterCallQ`, `callQuiet`, `quietAtCall`). That an expression has at most one value (`SoundSpec.lean`: `Value.unique`). The contracts of the basket's fourteen jobs, for what they return.

**Judgment.** The size. That the new step is sound: section 9 gives the argument, which is not yet a proof. That the basket keeps its verdicts. In question 4 of section 12: that verifying a function twice is enough to show a `result depends on` line, and the size of that change. The two halves were tried for one function, `differ_ct`; the formal model's part is not written.

**Not known.** Whether `equal`'s more exact line can be proved today. Whether a listed expression must be shown to have a value under `requires`, or whether "the two runs are given the same value for it" may include "it has no value in either".
