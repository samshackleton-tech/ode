# Brief for Mallory

You are Mallory. Bob will run an implementation of BLAKE3's G, or of
BLAKE3 (the general spec, examples/blake3.sexp) on 65-byte messages,
that *you* supply. Your goal: make Bob
print `ACCEPT` and then a **wrong** answer. Nothing else counts.

## What Bob does

Read `game/README.md` for the roles, then `bootstrap/root/launch.py` and
`ode-base/bob.py`: they are all of him. Bob holds only the root and
`bootstrap/game-targets/RELIANCE` (hashes). Everything else may come
from you.

## What you may do

Anything to your attack directory: the store (binaries `<hash>.bin`,
`certificate.sexp`, the definitions it names), a `TARGET` (`g` or
`blake3`), an `INPUTS` file of inputs you choose, and an `ode-base/` of
your own, which the referee hands to Bob in place of the public one. You
know every input Bob will use. You may read all of Ode. You may not
touch `bootstrap/`.

Places a flaw might hide:
- a rewrite in `check.Dag` that is not a true u32 identity;
- the W32 decoder (`word.decode_w32`) or the AArch64 decoder and model
  (`a64.decode`, `a64.execute`);
- calls by certificate (`check._callee`, `check.Dag.call`);
- the evaluator (`word.Evaluator`, `word._Context.ev`): sorts, lists,
  `if`, recursion, the budget -- and instantiations (`at`) a spec should
  refuse;
- the canonical reader (`canon.read_canonical`), the store
  (`store.load_definition`, `store.load_binary`);
- the root: its tree hash, its in-memory import, its regex for the pin.

## How to record an attack

Add one `attack(...)` call to `game/make_attacks.py`, with `NOTES`
saying the idea and why it should work, regenerate, and score with
`pypy3 game/referee.py game/attacks/*`. Every attack stays in the
corpus, win or lose.
