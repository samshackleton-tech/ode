# Names and identities in Ode

The requirements below are decided (Sam Shackleton, November 16, 2026). The proposal that follows them
is a direction she found good so far and has yet to decide. The last section says what the tools do today.

## The problem, on one example

A maker sends Bob the file `odeframe.o`. Bob's verifier prints the contract, which reads (shortened):

    contract ode_unframe(out, cap, input, n) { ... len(unframe(input)) ... }

and `unframe` is defined using `lz4(...)` and `adler32(...)`.

Every word there was chosen by the maker: `ode_unframe`, `unframe`, `lz4`, `adler32`, the file's name, the
comments. An attacking maker chooses them to reassure. The definition she calls `adler32` may be something
else. That is phishing: Bob reads a word the attacker chose and takes it to mean what he means by it.

So, from Bob's side: **every name someone else provides is a possible ploy; only a name Bob assigned
himself is a hint he can lean on.** Of each binding of a name ask two questions. How does Bob know it
binds to the right thing? Is there a way of naming that makes knowing it cheaper?

## Requirements

Hard:

- **Nothing a supply-chain attacker can use to make Bob overlook a backdoor.** Minimize the attacker's
  freedom to choose what is presented to Bob.
- **It scales with players who coordinate only partly**: auditors comparing notes; makers whose
  wished-for names collide ("The-Best-Database-Ever"); a contested fork; developers using one another's
  work with little coordination.
- **It holds in a hostile setting**: evil players look like good ones, and keys are stolen or bought. Of
  every sending and every use of a name, ask how good players use it and how evil players use it.
- **Every name says which namespace it is read in.**

Set aside on purpose: ergonomics, comfort, what people wish to be called, names for the unaided eye and
hand, names that are easy to remember.

## Six ways a name crosses from one namespace to another

| | the way | verdict |
|---|---|---|
| 1 | no importing: names are private | useful, and too little alone |
| 2 | one global namespace | bad |
| 3 | detect collisions and look-alikes | bad as a foundation |
| 4 | names defined by content | good wherever the name can follow the thing and is never rebound |
| 5 | linked local namespaces: name the namespace too (`alice.adler32`) | good: `alice` was already a name in this namespace, so `alice.adler32` adds no new problem |
| 6 | unique names that can be rebound (`n_1`, `n_2`) | useful as places for a reader's own words |

## Decided

- **BLAKE3 for every hash, whole.** Sixteen digits resist no adversary. Hashes are compared by the tool
  and never by eye.
- **The glossary.** The author writes names as before. A tool replaces each chosen name by a counted
  letter or number, in order of first use from the contract, and puts "letter means the author's name" in
  a glossary beside the text. **Only the form with names replaced is ever hashed.** A glossary belongs to
  whoever wrote it and is about a hash; several glossaries for one thing is normal.
- **File names and a contract's name follow the same rules** as names inside a specification
  (`b3hashr.o`, `b3l_hashr`). Convention and preference are no grounds for an exception.
- **A comment that points to an outside document gives that document's BLAKE3 hash.**
- **Two modes of the verifier.** Bob's prints nothing the maker chose that he has no use for (the names of
  the functions inside, a refusal's inner terms). Carol the maintainer's mode prints them.
- **Where a contract could ask less of the caller at the price of being harder to read, the simpler
  contract for Bob wins.**

## The proposal: a hash is a thing's name; a word is somebody's

1. **What is hashed.** To know what the contract `ode_unframe` promises, Bob must read the definition of
   `unframe`, then the definitions it uses, down to the language's own words such as `len`. The contract
   with all of those is the *full contract*: everything Bob must read to know what is promised.
2. **The maker's words are taken out before hashing.** Names of definitions and parameters, and comments,
   do not change what is promised. The tool drops the comments and replaces each name by a number counted
   from the contract in order of first appearance. The maker's

        def unframe(bytes) {
            fails SHORT if len(bytes) < 4
            let body = lz4(bytes[0 .. len(bytes) - 4])
            fails SUM if adler32(body) != be32(bytes[len(bytes) - 4 .. len(bytes)])
            body
        }

   becomes

        D2(a) {
            fails 3 if len(a) < 4
            let b = D3(a[0 .. len(a) - 4])
            fails 4 if D4(b) != D5(a[len(a) - 4 .. len(a)])
            b
        }

   The hash of the full contract written this way is the contract's name. The same promise has the same
   hash whatever the maker called things; a different promise has a different hash however it is dressed.
   Because counting starts from the contract, definitions that use one another need no special treatment.
3. **The maker's words travel beside it** as her glossary: D2 is "unframe", D3 is "lz4". A suggestion.
4. **Bob keeps his own list.** When he has read something and is satisfied, he gives its hash his own
   word. From then on his tool shows that word, and shows "new to you" for a hash he has no word for,
   whatever the maker calls it. An attacker cannot make a different thing appear under Bob's word.
5. **Other people's words** reach Bob through his own word for the person: "alice says: compared with
   RFC 1950, equal", where `alice` is Bob's word for that auditor. Someone he has no word for is "a
   stranger". A stolen key can change only its owner's list; it changes no hash and no verification.
6. **Code** is named by its position in a file, and the file by its hash. The verifier's result reads:
   "the bytes at position 0 of this file meet the contract (yours: ...)". **A contract contains no hash of
   code**: a rebuild would change the contract's name and lose Bob's word for it.
7. **The language's own words** (`len`, `bytes_of`, `requires`) are fixed by the language page. A full
   contract begins with the hash of that page.

Against the requirements: the attacker chooses only content, which is what Bob's reading and the verifier
examine. Nobody shares a namespace, so there is nothing to fight over. Auditors who never met reach the
same hash and can lay their lists side by side. Still exposed: a contract new to Bob must be read, by him
or by someone he chose; and the tool that replaces names and hashes is code he relies on.

Ode 0.1 had two pieces of this worth carrying over. Its *pet names* are the lists of steps 4 and 5. Its
*separated domains* hash each kind of thing (a specification, a proof, code) in a BLAKE3 key-derivation
context of its own, with a revision number for its meaning, so the same bytes read as two kinds have two
names, and `b3sum --derive-key` can still recompute each.

## What the tools do today

- BLAKE3 digests of files and specifications are printed whole; the hash is worked out by the
  specification `blake3.spec` itself, so no second implementation of BLAKE3 is relied on.
- A name is declared once; the language's own fourteen words cannot be redefined; a proof may declare no
  name the reader's text writes; a name with a look-alike letter or an invisible character is refused.
- Every name a file gives a linker must be verified, and a file is read in one shape. (A file with two
  functions of one name, the verified one local and another global, was once accepted; a C program linked
  with it ran the other.)
- Nothing a maker wrote reaches Bob's terminal as control characters. Bob's mode leaves out inner names;
  `--maintain` prints them.

What Bob still meets, counted on the BLAKE3 example: every readable name particular to the program is the
maker's (the file's name, the contract's name, six argument names, the names of sixteen definitions, and
81 lines of comments in a specification of 185). The one identifier that says "this is the contract you
read before" is a digest of the file as typed, which a changed space changes. Five definitions and three
constants of `blake3.spec` are used by no contract.

Unbuilt: the form with names replaced and its hash; glossaries; Bob's own list and "new to you"; file and
contract names under the same rules; comments citing documents by hash; the language page's hash at the
head of a full contract; separated domains.
