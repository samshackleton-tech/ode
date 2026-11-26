import Std.Data.HashMap
import Arithmetic
import Contract
/-!
# The verifier: a function's instructions run on symbols, by the table, with a proof

`verify` goes through every path of a function from its entry, doing each instruction's effect as the
table says it (`symInstr`), and holds at each point of a path what is in `Sym`. It searches for nothing.
Where something has to be known that it cannot see at once, the proof says it, in the order the verifier
comes to need it:

  * that some whole numbers satisfy an inequality: a proof of arithmetic (`Arithmetic.refutes`);
  * which of two numbers is the greater, or that they are equal (`lt`, `eq`, `gt`), then the proofs;
  * that a way a jump can go is taken by no input (`dead`, then the proof), or is to be gone (`live`);
  * which use of a definition to open (`open N`) on the way to a fact of the specification;
  * at a shift to the left, whether the number shifted is shown to be small enough that no bit is lost
    (`exact`, then the proof) or only its low part is doubled (`wrap`).

A loop is taken once, from a place the proof names: what holds there (`Place`), and a number that is less
at each coming back and never below zero.

Where the proof has run out, the answer is `need …` and what is needed (so a prover can be written as: ask,
answer, ask again). Any other answer but yes is `refused: …`.

It is written to be reasoned about: plain recursion, no loops, one small monad.
-/
namespace Ode
open Arithmetic (Row Step)

/-! ## Sums of unknowns with whole multiples (rows without their `≥ 0`) -/
namespace Lin

def strip : List Int → List Int
  | [] => []
  | c :: cs =>
    match strip cs with
    | [] => if c == 0 then [] else [c]
    | d :: ds => c :: d :: ds

def const (k : Int) : Row := ⟨[], k⟩
def var (x : Nat) : Row := ⟨List.replicate x 0 ++ [1], 0⟩
def add (a b : Row) : Row := ⟨strip (Arithmetic.sum a.coeff b.coeff), a.constant + b.constant⟩
def scale (n : Int) (a : Row) : Row := ⟨strip (Arithmetic.scale n a.coeff), n * a.constant⟩
def sub (a b : Row) : Row := add a (scale (-1) b)
def isConst (a : Row) : Option Int := if a.coeff.isEmpty then some a.constant else none
def coeffOf (a : Row) (x : Nat) : Int := a.coeff.getD x 0

/-- Whether two lists of multiples are the same but for zeros at their ends: the difference of the two
rows is then a number alone. (Asked without making the difference.) -/
def sameCoeff : List Int → List Int → Bool
  | [], ys => Arithmetic.allZero ys
  | x :: xs, [] => Arithmetic.allZero (x :: xs)
  | x :: xs, y :: ys => x == y && sameCoeff xs ys

/-- The same list of numbers, one by one. -/
def sameList : List Int → List Int → Bool
  | [], [] => true
  | x :: xs, y :: ys => x == y && sameList xs ys
  | _, _ => false

/-- The same row: what `==` says of two rows, asked number by number (which is faster). -/
def same (a b : Row) : Bool := a.constant == b.constant && sameList a.coeff b.coeff

/-- Is the second list `c` times the first, number by number, but for zeros at their ends? -/
def timesCoeff (c : Int) : List Int → List Int → Bool
  | [], ys => Arithmetic.allZero ys
  | x :: xs, [] => c * x == 0 && timesCoeff c xs []
  | x :: xs, y :: ys => y == c * x && timesCoeff c xs ys

/-- `g` less `c` times `f`, where that is a number alone. (What `isConst (sub g (scale c f))` gives, asked
without making the rows.) -/
def lessTimes (g : Row) (c : Int) (f : Row) : Option Int :=
  if timesCoeff c f.coeff g.coeff then some (g.constant - c * f.constant) else none

end Lin

/-- Is the row one of the facts? -/
def among (facts : List Row) (g : Row) : Bool := facts.any fun f => Lin.same f g

/-! ## The proof, and asking it -/

inductive Item where
  | tag (name : String) (n : Nat)
  | proof (starts : List Nat) (steps : List Step)   -- of arithmetic: the rows it starts from, by their numbers among those the verifier holds
  | proofRows (starts : List Row) (steps : List Step) -- of arithmetic: the rows it starts from, given explicitly (independent of fact order)
  | know (g : Row)                                  -- a row for the verifier to show from the facts, and then to keep among them
  | clear (pc : Nat) (reg : Nat) (e : SExpr)        -- at `pc`, prove register `reg` equals `e` (allowed by `traceClean`) and clear its mark
  deriving Inhabited

/-- The proof's lines as the verifier takes them: by their numbers, and the number of the next one. (By
number, so that a prover's program can hand a line over when the verifier first comes to it.) -/
structure Items where
  line : Nat → Option Item
  next : Nat := 0

def Items.ofList (l : List Item) : Items :=
  let a := l.toArray
  { line := fun n => a[n]? }

/-- A step of the verifier: it takes what it needs from the front of the proof, and gives an answer and the
rest of the proof, or stops with the reason. -/
def V (α : Type) := Items → Except String (α × Items)

namespace V
def pure (a : α) : V α := fun items => .ok (a, items)
def bind (x : V α) (f : α → V β) : V β := fun items =>
  match x items with
  | .ok (a, rest) => f a rest
  | .error why => .error why
instance : Monad V where
  pure := V.pure
  bind := V.bind
end V

def refuse (why : String) : V α := fun _ => .error ("refused: " ++ why)

def showRow (r : Row) : String := " ".intercalate (toString r.constant :: r.coeff.map toString)

def need (what : String) (facts goals : List Row) : V α := fun _ =>
  .error ("need " ++ what ++ "\n" ++ String.join (facts.map fun f => "f " ++ showRow f ++ "\n")
    ++ String.join (goals.map fun g => "g " ++ showRow g ++ "\n"))

def pop : V (Option Item) := fun items =>
  match items.line items.next with
  | none => .ok (none, items)
  | some i => .ok (some i, { items with next := items.next + 1 })

def finished : V Bool := fun items => .ok ((items.line items.next).isNone, items)

def each (f : α → V Unit) : List α → V Unit
  | [] => pure ()
  | a :: rest => do f a; each f rest

def fold (f : β → α → V β) : β → List α → V β
  | b, [] => pure b
  | b, a :: rest => do let b ← f b a; fold f b rest

/-- `-g - 1 ≥ 0`: that `g ≥ 0` does not hold. -/
def negation (g : Row) : Row := Lin.sub (Lin.const (-1)) g

/-- Seen at once: a number not below zero, or a fact plus such a number. -/
def plain (facts : List Row) (g : Row) : Bool :=
  match Lin.isConst g with
  | some k => decide (0 ≤ k)
  -- (the two constants are compared first: that is one step, and comparing the multiples is one for every unknown)
  | none => facts.any fun f => decide (f.constant ≤ g.constant) && Lin.sameCoeff g.coeff f.coeff

/-- Seen at once to equal a constant `k`: either `r` is already a constant row, or `facts`
contains a lower bound `f` with the same variable coefficients (`ev r ≥ k`) and `plain` sees
the matching upper bound `k - r ≥ 0`. Lets loop-hoisted mask/shift registers work seamlessly. -/
def constOf (facts : List Row) (r : Row) : Option Int :=
  match Lin.isConst r with
  | some k => some k
  | none =>
    facts.findSome? fun f =>
      if Lin.sameCoeff r.coeff f.coeff then
        let k := r.constant - f.constant
        if plain facts (Lin.sub (Lin.const k) r) then some k else none
      else none

/-- The rows a proof of arithmetic starts from: those of the rows given that it names by their numbers. -/
def pick (given : List Row) (numbers : List Nat) : List Row := numbers.filterMap fun k => given[k]?

/-- `g ≥ 0` follows from the facts. `what`: the word by which a proof that has no step for it is asked for
one. -/
def entailAs (what : String) (facts : List Row) (g : Row) : V Unit :=
  if plain facts g then pure () else do
    match ← pop with
    | some (.proof starts steps) =>
      if Arithmetic.refutes (negation g :: facts) (pick (negation g :: facts) starts) steps then pure ()
      else refuse "a proof of arithmetic does not show what is to be shown"
    | some (.proofRows starts steps) =>
      if Arithmetic.refutes (negation g :: facts) starts steps then pure ()
      else refuse "a proof of arithmetic does not show what is to be shown"
    | some _ => refuse "a proof of arithmetic is expected"
    | none => need what facts [g]

/-- `g ≥ 0` follows from the facts. -/
def entail (facts : List Row) (g : Row) : V Unit := entailAs "entail" facts g

inductive Cmp where
  | lt | eq | gt

def Cmp.isLt : Cmp → Bool
  | .lt => true
  | _ => false
def Cmp.isEq : Cmp → Bool
  | .eq => true
  | _ => false
def Cmp.isGt : Cmp → Bool
  | .gt => true
  | _ => false

/-- Which of the two is the greater, by the facts. -/
def compare (facts : List Row) (a b : Row) : V Cmp :=
  match Lin.isConst (Lin.sub a b) with
  | some k => pure (if k < 0 then .lt else if k == 0 then .eq else .gt)
  | none => do
    match ← pop with
    | some (.tag name _) =>
      if name == "eq" then do entail facts (Lin.sub a b); entail facts (Lin.sub b a); pure .eq
      else if name == "lt" then do entail facts (Lin.sub (Lin.sub b a) (Lin.const 1)); pure .lt
      else if name == "gt" then do entail facts (Lin.sub (Lin.sub a b) (Lin.const 1)); pure .gt
      else refuse "lt, eq or gt is expected"
    | some _ => refuse "lt, eq or gt is expected"
    | none => need "compare" facts [Lin.sub a b]

/-- Whether `a` is below `b`, by the facts: the proof says which, `lt` (below) or `ge` (not below). -/
def isBelow (facts : List Row) (a b : Row) : V Bool :=
  match Lin.isConst (Lin.sub a b) with
  | some k => pure (decide (k < 0))
  | none => do
    match ← pop with
    | some (.tag name _) =>
      if name == "lt" then do entail facts (Lin.sub (Lin.sub b a) (Lin.const 1)); pure true
      else if name == "ge" then do entail facts (Lin.sub a b); pure false
      else refuse "lt or ge is expected"
    | some _ => refuse "lt or ge is expected"
    | none => need "below" facts [Lin.sub a b]

/-- At a shift to the left: is the number shown to stay below `m`, so that no doubling is lost? Seen at once;
or the proof says which: `exact`, and a proof of arithmetic follows, or `wrap`. -/
def staysBelow (facts : List Row) (x : Row) (m : Int) : V Bool :=
  if plain facts (Lin.sub (Lin.const (m - 1)) x) then pure true
  else do
    match ← pop with
    | some (.tag name _) =>
      if name == "exact" then do entail facts (Lin.sub (Lin.const (m - 1)) x); pure true
      else if name == "wrap" then pure false
      else refuse "exact or wrap is expected"
    | some _ => refuse "exact or wrap is expected"
    | none => need "shift" facts [Lin.sub (Lin.const (m - 1)) x]

/-! ## What is held at a point of a path -/

inductive Flag where
  | unknown
  | equal (a b : Row)      -- set exactly when a = b
  | below (a b : Row)      -- set exactly when a < b
  deriving Inhabited

/-- A value of the specification, on symbols. -/
inductive SVal where
  | lin (r : Row)
  | region (k : Nat)
  | bool (b : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- A use of a definition. -/
structure SCall where
  f : String
  args : List SVal
  deriving DecidableEq, Repr, Inhabited

inductive SFact where
  | same (a b : SCall)          -- the two have the same value, or neither has one
  | value (c : SCall) (v : Row) -- the use has this value
  | neq (r : Row)               -- this linear expression is not zero (`ev ρ r ≠ 0`)
  deriving DecidableEq, Repr, Inhabited

/-! ## Words

A word is 32 bits. What a vector register holds is not followed as arithmetic on unknowns (a sum that wraps
is no row): each word is a term, and the terms are kept in a table, a term being named by its number
there. Two words are known to be the same where their numbers are; a term made again gets the number it has
(where the table's advice finds it: see `Tab`). A sum is kept as the list of what is summed, in order of
number: `(a + m) + b` and `(a + b) + m` are one term. -/

def W32i : Int := 4294967296

inductive Node where
  | atom (r : Row)              -- a number the verifier holds as a row: as a word, its remainder by 2^32
  | input (run k : Nat)         -- word `k` of a run of words given to read, as it was at entry
  | add (xs : List (Nat × Nat)) -- linear combination of terms (sorted unique ids, nonzero coeffs mod 2^32), wrapping
  | xor (a b : Nat)
  | band (a b : Nat)
  | rotr (a n : Nat)            -- the term turned right by `n` bits
  | shl (a n : Nat)             -- the term shifted left by `n` bits, what passes 32 bits dropped
  | shr (a n : Nat)             -- the term shifted right by `n` bits
  | ult (a b : Nat)             -- 1 where the term `a` is below the term `b`, else 0 (a bit of a mask register)
  | sel (m a b : Nat)           -- the term `a` where the term `m` is not zero, else the term `b`
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- The terms a term is made of, by their numbers. -/
def Node.parts : Node → List Nat
  | .atom _ => []
  | .input _ _ => []
  | .add xs => xs.map Prod.fst
  | .xor a b => [a, b]
  | .band a b => [a, b]
  | .rotr a _ => [a]
  | .shl a _ => [a]
  | .shr a _ => [a]
  | .ult a b => [a, b]
  | .sel m a b => [m, a, b]

/-- The table of words. `arr`: the terms, each named by its number there. `idx`: where a term may be found,
so that one is looked up at once. The second is advice, and nothing that is shown rests on it: `intern` takes
a number from it only where that term stands at that number, and puts the term at the end otherwise. -/
structure Tab where
  arr : Array Node := #[]
  idx : Std.HashMap Node Nat := ∅
  deriving Inhabited

/-- The table's terms in order: what the reasoning speaks of. (The verifier's own steps read `arr`.) -/
def Tab.list (t : Tab) : List Node := t.arr.toList

/-- Where a term is in the table, looked up at once: the number the table's index gives, taken only where
that term stands at that number. (So what is found is right whatever the index holds; a term the index
does not have is not found.) -/
def Tab.find (t : Tab) (n : Node) : Option Nat :=
  match t.idx[n]? with
  | some i => if t.arr[i]? = some n then some i else none
  | none => none

/-- The number of a term in the table; a term that is not found there is put at the end. (Marked so that a
proof opens it only by asking to: what is reasoned of it is `intern_list` in SoundWord.lean.) -/
@[irreducible] def intern (n : Node) (t : Tab) : Nat × Tab :=
  match t.idx[n]? with
  | some i =>
    if t.arr[i]? = some n then (i, t)
    else (t.arr.size, { arr := t.arr.push n, idx := t.idx.insert n t.arr.size })
  | none => (t.arr.size, { arr := t.arr.push n, idx := t.idx.insert n t.arr.size })

def mergeAdd : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], ys => ys
  | xs, [] => xs
  | (a, ca) :: xs, (b, cb) :: ys =>
    if a < b then (a, ca) :: mergeAdd xs ((b, cb) :: ys)
    else if b < a then (b, cb) :: mergeAdd ((a, ca) :: xs) ys
    else
      let c := (ca + cb) % W32
      if c = 0 then mergeAdd xs ys else (a, c) :: mergeAdd xs ys

/-- A row with each of its numbers reduced to the remainder by 2^32: as a word it is the same word. -/
def Lin.word (r : Row) : Row := ⟨Lin.strip (r.coeff.map (· % W32i)), r.constant % W32i⟩

/-- The row of the quotients by 2^32: `r` is `Lin.word r` and 2^32 times this. -/
def Lin.high (r : Row) : Row := ⟨Lin.strip (r.coeff.map (· / W32i)), r.constant / W32i⟩

/-- The row has, as it is written, a part that is a multiple of 2^32: a low word and something above it. -/
def Lin.hasHigh (r : Row) : Bool := r.coeff.any fun c => c != 0 && c % W32i == 0

def wAtom (r : Row) (t : Tab) : Nat × Tab := intern (.atom (Lin.word r)) t

/-- What a term is a sum of: itself (with coeff 1), or the terms it sums. -/
def addends (t : Tab) (a : Nat) : List (Nat × Nat) :=
  match t.arr[a]? with
  | some (.add xs) => xs
  | _ => [(a, 1)]

def wAdd (a b : Nat) (t : Tab) : Nat × Tab :=
  intern (.add (mergeAdd (addends t a) (addends t b))) t

def wXor (a b : Nat) (t : Tab) : Nat × Tab := intern (.xor (min a b) (max a b)) t

def wAnd (a b : Nat) (t : Tab) : Nat × Tab := intern (.band (min a b) (max a b)) t

def wRotr (a n : Nat) (t : Tab) : Nat × Tab := intern (.rotr a n) t

def wShl (a n : Nat) (t : Tab) : Nat × Tab := intern (.shl a n) t

def wShr (a n : Nat) (t : Tab) : Nat × Tab := intern (.shr a n) t

/-- Is the one term below the other: 1 or 0. A term is not below itself. -/
def wUlt (a b : Nat) (t : Tab) : Nat × Tab := if a = b then wAtom (Lin.const 0) t else intern (.ult a b) t

/-- The term `a` where the term `m` is not zero, else the term `b`. Where `m` is the number 0 it is `b`. -/
def wSel (m a b : Nat) (t : Tab) : Nat × Tab :=
  if t.arr[m]? = some (.atom (Lin.word (Lin.const 0))) then (b, t) else intern (.sel m a b) t

/-- A term and a number of the table summed, wrapping. With the number 0 it is the term; where the term is
the word of a row, it is the word of that row and the number. -/
def wAddConst (a k : Nat) (t : Tab) : Nat × Tab :=
  if k = 0 then (a, t)
  else match t.arr[a]? with
    | some (.atom r) => wAtom (Lin.add r (Lin.const k)) t
    | _ => wAdd a (wAtom (Lin.const k) t).1 (wAtom (Lin.const k) t).2

/-- The or of two terms that is a turn: one is a term shifted left by `32 - n` bits, the other the same term
shifted right by `n`. (The term turned, and by how much.) -/
def orTurn (T : List Node) (a b : Nat) : Option (Nat × Nat) :=
  match T[a]?, T[b]? with
  | some (.shl x k), some (.shr y n) => if x = y ∧ k + n = 32 ∧ 0 < n ∧ 0 < k then some (x, n) else none
  | some (.shr y n), some (.shl x k) => if x = y ∧ k + n = 32 ∧ 0 < n ∧ 0 < k then some (x, n) else none
  | _, _ => none

def orTurns (T : List Node) : List (Nat × Nat) → Option (List (Nat × Nat))
  | [] => some []
  | (a, b) :: more =>
    match orTurn T a b, orTurns T more with
    | some t, some ts => some (t :: ts)
    | _, _ => none

/-- The numbers that terms are, where each is a number of the table. -/
def constWords (T : List Node) : List Nat → Option (List Int)
  | [] => some []
  | a :: more =>
    match T[a]?, constWords T more with
    | some (.atom r), some ks => (Lin.isConst r).map fun k => k :: ks
    | _, _ => none

/-- A shuffle of bytes by these four words is a turn of each word to the right by so many bits: the two
shuffles a rotation by 8 and by 16 bits is written as. -/
def shuffleTurn (ks : List Int) : Option Nat :=
  if ks = [0x00030201, 0x04070605, 0x080B0A09, 0x0C0F0E0D] then some 8
  else if ks = [0x01000302, 0x05040706, 0x09080B0A, 0x0D0C0F0E] then some 16
  else none

/-! ## Numbers that are no rows

A row is a sum of multiples of unknowns. Some numbers the verifier follows are none: eight bytes of memory
as one number, two numbers' bits put together, the words a definition gives of what it is used with. Each
is held as an unknown (or as terms of the table) of which it is known what it is. -/

/-- A thing a definition is used with, as the verifier holds it: a number, the counter of a number, a list
of words by their terms, the blocks an address of a table points to, or what another use of a definition
gives, that use being known by a number of its own. -/
inductive Key where
  | num (r : Row)
  | counter (r : Row)
  | words (ids : List Nat)
  | lane (j c l : Nat)            -- the blocks that the address at place `c` of the table `j` points to (as many as register `l` held at entry)
  | span (r : Nat) (off len : Row)    -- `len` bytes from place `off` on of the run of bytes at the address register `r` held at entry, as they were at entry
  | use (h : Nat)                 -- what the use of a definition that has the number `h` gives (`Known.use`)
  deriving DecidableEq, Repr, Inhabited

/-- A field of a serialized record layout in memory (`statement.py`'s `record_words`):
`words`: `n` 32-bit words; `bytes`: `n` bytes (`n % 4 = 0`); `u64`: 8 bytes (2 words) holding an unsigned
integer strictly below `bound` (`bound ≤ 2^64`). -/
inductive RecField where
  | words (name : String) (n : Nat)
  | bytes (name : String) (n : Nat)
  | u64 (name : String) (bound : Nat)
  deriving DecidableEq, Repr, Inhabited

def RecField.name : RecField → String
  | .words x _ => x
  | .bytes x _ => x
  | .u64 x _ => x

def RecField.nwords : RecField → Nat
  | .words _ n => n
  | .bytes _ n => n / 4
  | .u64 _ _ => 2

/-- What is known beyond the facts. -/
inductive Known where
  | load (v j c : Nat)            -- the unknown `v` is the eight bytes at place `c` of the run `j` (of a fixed count, given to read) as they were at entry: one number, the lowest byte first
  | or (v : Nat) (x y : Row)      -- the unknown `v` is `x | y`: the bits of both
  | held (f : String) (keys : List Key) (ids : List Nat)    -- the definition `f`, used with these things, is the list of the words of these terms
  | heldB (f : String) (keys : List Key) (ids : List Nat)   -- the definition `f`, used with these things, is the list of the bytes of the words of these terms, four a word, the lowest first
  | div (x : Row) (m : Int) (q : Nat)   -- the unknown `q` is `x` divided by `m` (a number above zero) rounded down, and the unknown after it is the remainder
  | block (j c : Nat) (off : Row) (vs : List Nat)   -- the sixteen unknowns `vs` are the sixteen words at byte `off` of the blocks that the address at place `c` of the table `j` points to, as they were at entry
  | use (f : String) (keys : List Key) (h : Nat)    -- the definition `f`, used with these things, gives something; `h` is that use's own number (an unknown's number, which no row speaks of)
  | record (h : Nat) (fields : List RecField) (ids : List Nat) -- the value decoded from `h` is a record with exact `fields`, whose serialized 32-bit words are `ids`
  deriving DecidableEq, Repr, Inhabited

/-- What is known NOT to be marked (not to depend on values kept out of the trace): general registers, the two flags, and
cells of the frame (eight bytes each, by how far they are from where the stack pointer was at entry).
Of anything not named here nothing is known: it may be marked. `lowq`: the general registers whose lowest
byte is known not to be marked, whatever the rest of the register is. -/
structure SMarks where
  regq : List Nat := []
  zq : Bool := false
  cq : Bool := false
  fq : List Int := []
  lowq : List Nat := []
  deriving Inhabited

/-- What a loop has written so far, as a place says it: each place `j` of the run `w` (a run given to
write, by its number), from the place `lo` on, holds thing `j` of the list that the definition `f` gives of
the things `args`. The definition is a list made thing by thing, `[e for x in 0..hi]`: the places go up
to `hi`. -/
structure RangeF where
  w : Nat
  lo : Row
  f : String
  args : List SVal
  fromStart : Bool := false
  deriving Inhabited

structure Sym where
  reg : Nat → Row                 -- the sixteen registers
  zf : Flag
  cf : Flag
  frame : List (Int × Row)        -- eight bytes at so many bytes from where the stack pointer was at entry
  facts : List Row                -- each `≥ 0`
  bytes : List (Nat × Nat × Row)  -- (unknown, run, place): the unknown is the byte at that place of that run
  spec : List SFact
  nvars : Nat                     -- unknowns in use: 0 to 15 are the registers at entry
  wrote : List (Nat × Row × Row)  -- (run given to write, place, byte): what that place of that run now holds
  tab : Tab := {}                 -- the table of words
  vec : List (Nat × List Nat) := []   -- (vector register, known low lanes as term numbers); the first entry for each register counts
  intact : List Nat := []         -- the runs given to write that nothing has been written to yet (by their numbers): they hold what they held at entry
  vecIntact : List Nat := []      -- the callee-saved vector registers still holding their entry values
  wroteW : List (Nat × Nat × Nat) := []   -- (run given to write, which word of it, the term): that word of that run now holds that term
  frameW : List (Int × Nat) := [] -- (entry-relative offset, term id): 4 bytes of the frame holding that 32-bit word term
  spill : List (Row × List Nat) := []  -- the aligned vector spills still known: each one's entry-relative offset and lane terms
  known : List Known := []        -- what is known of numbers that are no rows
  q : SMarks := {}                -- what is known not to be marked
  range : Option RangeF := none   -- what a place says a loop has written so far, where one says so
  stackAt : Option (Row × List (Int × Row) × List (Row × List Nat)) := none   -- the stack pointer, the frame's cells and the spills as they were when `settle` last showed the stack's facts: advice, and nothing rests on it
  deriving Inhabited

/-- Number of terms in the table in O(1) (equal to `t.list.length` by `Array.length_toList`). -/
abbrev Tab.size (t : Tab) : Nat := t.arr.size

/-- The terms of the table of words, in order. -/
abbrev Sym.terms (s : Sym) : List Node := s.tab.list

/-- What a place says of vector registers: for each lane `x` from 0 to 15, the words in that lane of the
registers `regs`, in their order, are the list of words the definition `f` gives of the things `args` (in
which `x` is the lane's number). -/
structure PlaceLanes where
  regs : List Nat
  x : String
  f : String
  args : SExpr
  deriving Inhabited

/-- What a place says of a cell of the frame that a vector was stored to: of the sixty-four bytes that lie
`off` bytes above the stack pointer, word `x` (from 0 to 15) is the word `e` (in which `x` is the word's
number). -/
structure PlaceCell where
  off : Nat
  x : String
  e : SExpr
  deriving Inhabited

structure Place where
  pc : Nat
  names : List (String × Nat)     -- a name for what a register holds there
  keep : List Nat                 -- registers that hold there what they held when the path first came there
  facts : List SExpr
  decreases : SExpr
  lanes : List PlaceLanes := []   -- what the vector registers hold there
  cells : List PlaceCell := []    -- what cells of the frame hold there
  marked : List Nat := []         -- registers that may depend on values kept out of the trace on a later coming there (they need not on the first)
  markedResult : List Nat := []   -- the same, for the `result depends on` pass (empty by default)
  wrote : Option (String × SExpr × String × SExpr × Bool) := none
                                  -- (run, bound, f, args, fromStart): suffix [bound..hi) or prefix [0..bound) of `run` holds `f(args)`
  isJoin : Bool := false          -- true for an acyclic mid-function join place (no `decreases`, shared across sibling paths)
  deriving Inhabited

/-- What a prover's helper may say where a proof that is still being written has run out: the rows it
would try to show next, before an `ensures` of a run of words and before a call. The verifier's program
gives none. Nothing is concluded from these rows: they are only printed (`popKnow`). -/
structure Advice where
  ensures : Sym → EnsureW → List Row := fun _ _ => []
  call : Sym → Contract → List Row := fun _ _ => []
  sameByte : Sym → Nat → Row → Bool := fun _ _ _ => false
  deriving Inhabited

structure Ctx where
  code : List (Nat × Instr)
  contract : Contract
  defs : List Def
  places : List Place := []                     -- the maker's: where the paths of loops are cut
  callees : List (String × Contract) := []      -- the functions this one calls, each with its contract
  selfName : Option String := none              -- this function's name when direct self-recursion is allowed
  advice : Advice := {}                         -- a prover's helper's; the verifier's program leaves it empty
  pieces : List Piece := []                     -- the read-only data of the program's object files, by number
  piece : Option Nat := none                    -- the file this function is of, where it takes an address in
                                                -- that file's read-only data
  resultPass : Bool := false                    -- true during the second pass for `result depends on`
  runsCallees : List String := []               -- callees verified under `Runs` (for functions using `cmov`/`csel`)
  deriving Inhabited

/-- Does this function contain any conditional select (`cmov*` / `csel`) instruction? -/
def hasSelect (code : List (Nat × Instr)) : Bool :=
  code.any fun p =>
    match p.2.effect with
    | [.set (.name _) (.call "select" [.name _, _, _])] => true
    | _ => false

/-- Does this function contain any call or tail-call instruction? -/
def hasCallOrTail (code : List (Nat × Instr)) : Bool :=
  code.any fun p => (callTarget p.2).isSome || (tailTarget p.2).isSome

/-- The bytes of the read-only data of the function's own file, where the function takes an address there. -/
def Ctx.data (ctx : Ctx) : List Nat :=
  match ctx.piece with
  | some k =>
    match ctx.pieces[k]? with
    | some pc => pc.bytes
    | none => []
  | none => []

def symEnvIn (c : Contract) : List (String × Kind) → List Nat → Nat → List (String × SVal)
  | (n, .number) :: args, r :: regs, k => (n, .lin (Lin.var r)) :: symEnvIn c args regs k
  | (n, .bytes len) :: args, _ :: regs, k =>
    match c.regOf len with
    | some _ => (n, .region k) :: symEnvIn c args regs (k + 1)
    | none => symEnvIn c args regs k
  | (_, .out _) :: args, _ :: regs, k => symEnvIn c args regs k
  | (_, .fixed _) :: args, _ :: regs, k => symEnvIn c args regs k
  | (_, .inout _) :: args, _ :: regs, k => symEnvIn c args regs k
  | (_, .valArray _ _ _) :: args, _ :: regs, k => symEnvIn c args regs k
  | _, _, _ => []

/-- The contract's names on symbols: a number is its register at entry; a run of bytes is a run by its number. -/
def symEnv (c : Contract) : List (String × SVal) := symEnvIn c c.args c.argRegs 0

def Sym.put (s : Sym) (r : Nat) (v : Row) : Sym := { s with reg := fun k => if k = r then v else s.reg k }

/-- How far the stack pointer is from where it was at entry. -/
def Sym.sp (s : Sym) : Option Int := Lin.isConst (Lin.sub (s.reg RSP) (Lin.var RSP))

def top : Int := 2 ^ 64 - 1

def ranged (v : Nat) : List Row := [Lin.var v, Lin.sub (Lin.const top) (Lin.var v)]

/-- Two new unknowns for a number divided by a number above zero, the quotient `q` and the remainder `r`,
and what is so of them: x = m * q + r and 0 <= r < m. -/
def Sym.divide (s : Sym) (x : Row) (m : Int) : Sym :=
  let d := Lin.sub x (Lin.add (Lin.scale m (Lin.var s.nvars)) (Lin.var (s.nvars + 1)))
  { s with nvars := s.nvars + 2,
           facts := d :: Lin.scale (-1) d :: Lin.var (s.nvars + 1) :: Lin.sub (Lin.const (m - 1)) (Lin.var (s.nvars + 1)) :: s.facts,
           known := .div x m s.nvars :: s.known }

/-- The unknowns the state knows as quotients of `x` by `m` (`Sym.divide` notes each division it makes). -/
def quotients (s : Sym) (x : Row) (m : Int) : List Nat :=
  s.known.filterMap fun k =>
    match k with
    | .div x' m' q => if m' == m && Lin.same x' x then some q else none
    | _ => none

/-- The least of some numbers. -/
def leastNat : List Nat → Option Nat
  | [] => none
  | a :: l =>
    match leastNat l with
    | some b => some (if a ≤ b then a else b)
    | none => some a

/-- The quotient's unknown, where the state knows what `x` divided by `m` is: the least such unknown. -/
def divided (s : Sym) (x : Row) (m : Int) : Option Nat := leastNat (quotients s x m)

/-- The least of some numbers. -/
def least : List Int → Option Int
  | [] => none
  | a :: l =>
    match least l with
    | some b => some (if a ≤ b then a else b)
    | none => some a

/-- The least number the facts held say at once that `x` is no more than: a fact is that number less `x`. -/
def boundOf (facts : List Row) (x : Row) : Option Int :=
  least (facts.filterMap fun f => Lin.isConst (Lin.add f x))

/-- Where a number is seen at once to be no more than some number, its quotient `q` by a number above zero
is no more than that number's quotient. -/
def quotientBound (facts : List Row) (x : Row) (m : Int) (q : Nat) : List Row :=
  match boundOf facts x with
  | some c => [Lin.sub (Lin.const (c / m)) (Lin.var q)]
  | none => []

/-- A number of the machine (from 0 to 2^64 - 1) divided by a number above zero: its quotient and its
remainder, and the state that knows of them. They are found once for one number and one divisor; the
quotient is no less than zero, and no more than the quotient of a number the dividend is seen at once to
be no more than. -/
def symDivide (s : Sym) (x : Row) (m : Int) : Row × Row × Sym :=
  match divided s x m with
  | some q => (Lin.var q, Lin.var (q + 1), s)
  | none => (Lin.var s.nvars, Lin.var (s.nvars + 1),
      { s.divide x m with facts := quotientBound s.facts x m s.nvars ++ Lin.var s.nvars :: (s.divide x m).facts })

/-- A row the facts held say is no less than zero: a number of the table, or a row that is itself a fact. -/
def knownNonneg (s : Sym) (r : Row) : Bool :=
  match Lin.isConst r with
  | some k => decide (0 ≤ k)
  | none => among s.facts r

/-- The quotient and the remainder of any number by a number above zero: the unknowns the facts held
already say they are, where they say it; else two new unknowns. Of a number seen at once to be no less than
zero they are the ones `symDivide` makes, with what it says of the quotient (so that the specification's
division and the code's of one number are one division, whichever comes first); of any other number, the
two of `Sym.divide`. -/
def Sym.quotRem (s : Sym) (x : Row) (m : Int) : Row × Row × Sym :=
  if knownNonneg s x then symDivide s x m
  else
    match divided s x m with
    | some q => (Lin.var q, Lin.var (q + 1), s)
    | none => (Lin.var s.nvars, Lin.var (s.nvars + 1), s.divide x m)

def lookupByte (r : Nat) (o : Row) : List (Nat × Nat × Row) → Option Nat
  | [] => none
  | (v, r', o') :: rest => if r' = r ∧ o' = o then some v else lookupByte r o rest

def lookupByteVar (v r : Nat) : List (Nat × Nat × Row) → Option Row
  | [] => none
  | (v', r', o') :: rest => if v' = v ∧ r' = r then some o' else lookupByteVar v r rest

/-- Optional proof-file hint unifying a byte read at offset `o` with a previously read byte `(v, r, o')`
whose offset `o'` is provably equal to `o` by linear arithmetic (e.g. `4 * (j / 3) == in_idx`). -/
def popSameByte (ctx : Ctx) (s : Sym) (r : Nat) (o : Row) : V (Option Nat) := fun items =>
  match items.line items.next with
  | some (.tag name v) =>
    if name == "samebyte" then .ok (some v, { items with next := items.next + 1 })
    else if name == "newbyte" then .ok (none, { items with next := items.next + 1 })
    else .ok (none, items)
  | some _ => .ok (none, items)
  | none =>
    if ctx.advice.sameByte s r o then
      let pairs := (s.bytes.filterMap fun (v, r', o') =>
        if r' == r && !Lin.sameCoeff o.coeff o'.coeff then some [Lin.const (v : Int), Lin.sub o o'] else none).flatten
      if pairs.isEmpty then .ok (none, items)
      else need "samebyte" s.facts pairs items
    else .ok (none, items)

/-- The byte at place `o` of run `r`: shown to be within the run; one unknown for one place. -/
def readByte (ctx : Ctx) (s : Sym) (r : Nat) (o : Row) : V (Row × Sym) :=
  match ctx.contract.regions[r]? with
  | none => refuse "no such run of bytes"
  | some (_, len) => do
    entail s.facts o
    entail s.facts (Lin.sub (Lin.sub (Lin.var len) o) (Lin.const 1))
    match lookupByte r o s.bytes with
    | some v => pure (Lin.var v, s)
    | none => do
      match ← popSameByte ctx s r o with
      | some v =>
        match lookupByteVar v r s.bytes with
        | some o' => do
          entail s.facts (Lin.sub o o')
          entail s.facts (Lin.sub o' o)
          pure (Lin.var v, s)
        | none => refuse "a same-byte step names an unknown that is not a byte of this run"
      | none =>
        pure (Lin.var s.nvars, { s with nvars := s.nvars + 1, bytes := (s.nvars, r, o) :: s.bytes,
                                        facts := Lin.var s.nvars :: Lin.sub (Lin.const 255) (Lin.var s.nvars) :: s.facts })

inductive Where where
  | frame (off : Int)
  | region (r : Nat) (off : Row)
  | out (w : Nat) (off : Row)
  | data (off : Int)              -- so many bytes into the file's read-only data

/-- How many general registers the verifier follows: as many as the machine of the function's contract has
(sixteen on x86-64, thirty-two on AArch64). -/
def Ctx.nreg (ctx : Ctx) : Nat := ctx.contract.regs

/-- The register a name of an EFFECT stands for, where the function's machine has that register. -/
def Ctx.regOf (ctx : Ctx) (bind : Bind) (n : String) : Option Nat := (Ode.regOf bind n).filter fun r => decide (r < ctx.nreg)

/-- The unknown that is where the file's read-only data lies. (The unknowns before it are the registers at
entry: 0 to 15 on x86-64.) -/
def dataVar (ctx : Ctx) : Nat := ctx.nreg

/-- How many bytes into the file's data an address is, where the function's file has data and the address is
the data's plus a number. -/
def dataOff (ctx : Ctx) (addr : Row) : Option Int :=
  if ctx.data.isEmpty then none else Lin.isConst (Lin.sub addr (Lin.var (dataVar ctx)))

/-- The number that `size` bytes of the file's data make, from byte `c` on, the lowest byte first. -/
def dataWord (data : List Nat) (c size : Nat) : Nat := load (fun x => ⟨data.getD x 0 % 256, Nat.mod_lt _ (by decide)⟩) c size

def findRegion (addr : Row) : List (Nat × Nat) → Nat → Option Where
  | [], _ => none
  | (base, _) :: more, k =>
    if Lin.coeffOf addr base == 1 then some (.region k (Lin.sub addr (Lin.var base))) else findRegion addr more (k + 1)

def findOut (addr : Row) : List (String × Nat × Nat) → Nat → Option Where
  | [], _ => none
  | (_, base, _) :: more, k =>
    if Lin.coeffOf addr base == 1 then some (.out k (Lin.sub addr (Lin.var base))) else findOut addr more (k + 1)

/-- Where an address is: in the frame, in the file's read-only data, in a run of bytes given to read, or in
one given to write. -/
def locate (ctx : Ctx) (addr : Row) : Option Where :=
  match Lin.isConst (Lin.sub addr (Lin.var RSP)) with
  | some c => some (.frame c)
  | none =>
    match dataOff ctx addr with
    | some c => some (.data c)
    | none =>
      match findRegion addr ctx.contract.regions 0 with
      | some w => some w
      | none => findOut addr ctx.contract.outs 0

/-- What is known written, when one byte is written at place `o` of the run `w`: what was known of another
run stays; of this run, what was at this very place goes, what was at a place that differs from it by a
number other than zero stays; and where a place is not known to be this one or another, there is no
answer. So the places known of one run are always different places. -/
def keepWrote (w : Nat) (o : Row) : List (Nat × Row × Row) → Option (List (Nat × Row × Row))
  | [] => some []
  | (w', o', x') :: more =>
    match keepWrote w o more with
    | none => none
    | some rest =>
      if w' ≠ w then some ((w', o', x') :: rest)
      else match Lin.isConst (Lin.sub o o') with
        | some k => if k = 0 then some rest else some ((w', o', x') :: rest)
        | none => none

/-- A number nearer 2^64 than 2^63 (one of 3 * 2^62 or more), as the number below zero that is the same
modulo 2^64: so `add rsp, -8` is followed as a subtraction. A number below that is taken as it stands:
2^63 itself is one, which the hash adds to a message's address where the left part has 2^53 chunks.
(Whichever way a number is taken, the sum or difference is then shown to lie from 0 to 2^64 - 1, and is
the machine's, which works modulo 2^64.) -/
def signed (r : Row) : Row :=
  match Lin.isConst r with
  | some k => if 3 * 2 ^ 62 ≤ k then Lin.const (k - 2 ^ 64) else r
  | none => r

/-- Eight bytes of the frame at `c` may be touched: at or above the stack pointer, below the return
address, within what the contract allows. -/
def inFrame (ctx : Ctx) (s : Sym) (c : Int) : Bool :=
  match s.sp with
  | some sp => decide (sp ≤ c) && decide (c + 8 ≤ 0) && decide (-(ctx.contract.stack : Int) ≤ c)
  | none => false

/-! ## An instruction's effect, on symbols -/

/-- The value of an expression of an effect: a number from 0 to 2^64 - 1, or what a flag is to be. -/
inductive EV where
  | lin (r : Row)
  | equal (a b : Row)
  | below (a b : Row)

def inRange (facts : List Row) (r : Row) : V Unit := do
  entail facts r
  entail facts (Lin.sub (Lin.const top) r)

/-- The unknown the state knows as the eight bytes at place `c` of the run `j`. -/
def knownLoad (j c : Nat) : List Known → Option Nat
  | [] => none
  | .load v j' c' :: more => if j' = j ∧ c' = c then some v else knownLoad j c more
  | _ :: more => knownLoad j c more

/-- Eight bytes of a run of a fixed count given to read, at a place that is a number: one number, the
lowest byte first. One unknown stands for one place of one run. It is a number below 2^64, and below what
the contract says of the number at that place (`mbounds`: the caller has seen to it). -/
def symLoadFixed (ctx : Ctx) (s : Sym) (addr : Row) (size : Nat) : V (EV × Sym) :=
  match findOut addr ctx.contract.fixeds 0 with
  | some (.out j off) =>
    match Lin.isConst off, ctx.contract.fixeds[j]? with
    | some c, some (name, _, count) =>
      if size = 8 ∧ 0 ≤ c ∧ c + 8 ≤ count then
        match knownLoad j c.toNat s.known with
        | some v => pure (.lin (Lin.var v), s)
        | none =>
          pure (.lin (Lin.var s.nvars),
            { s with nvars := s.nvars + 1, known := .load s.nvars j c.toNat :: s.known,
                     facts := ranged s.nvars ++
                       (ctx.contract.mbounds.filterMap fun (x, o, b) =>
                         if x == name ∧ o = c.toNat then some (Lin.sub (Lin.const ((b : Int) - 1)) (Lin.var s.nvars)) else none) ++ s.facts })
      else refuse "a read of a run of a fixed count that is not eight bytes within it: not here yet"
    | _, _ => refuse "a read of a run of a fixed count at a place that is no number: not here yet"
  | _ => refuse "a read that is neither of the frame nor of a run given"

def symLoad (ctx : Ctx) (s : Sym) (addr : Row) (size : Nat) : V (EV × Sym) :=
  match locate ctx addr with
  | some (.frame c) =>
    if size = 8 ∧ inFrame ctx s c = true then
      match s.frame.lookup c with
      | some v => pure (.lin v, s)
      | none => refuse "a read of the frame where nothing was written"
    else refuse "a read of the frame that is not eight bytes of the frame in use"
  | some (.region r o) =>
    if size = 1 then do
      let (v, s) ← readByte ctx s r o
      pure (.lin v, s)
    else refuse "a read of a run of bytes that is not one byte: not here yet"
  | some (.out _ _) => refuse "a read of a run given only to write"
  | some (.data c) =>
    -- the file's read-only data: the bytes are the file's, so what is read is a plain number
    if (size = 1 ∨ size = 4 ∨ size = 8) ∧ 0 ≤ c ∧ c + size ≤ ctx.data.length then
      pure (.lin (Lin.const (dataWord ctx.data c.toNat size)), s)
    else refuse "a read of the file's read-only data that is not one, four or eight bytes within it"
  | none => symLoadFixed ctx s addr size

/-- The remainder of a number by a divisor above zero: worked out where every multiple in the number is a
multiple of the divisor (so where the number is one of the table's); the number itself where it is seen at
once to be below the divisor; and else by the one division of it the state knows of. -/
def symLow (s : Sym) (x : Row) (m : Int) : Row × Sym :=
  if x.coeff.all (fun c => c % m == 0) then (Lin.const (x.constant % m), s)
  else if plain s.facts (Lin.sub (Lin.const (m - 1)) x) then (x, s)
  else ((symDivide s x m).2.1, (symDivide s x m).2.2)

/-- The quotient likewise. -/
def symQuot (s : Sym) (x : Row) (m : Int) : Row × Sym :=
  if x.coeff.all (fun c => c % m == 0) then (⟨Lin.strip (x.coeff.map (· / m)), x.constant / m⟩, s)
  else ((symDivide s x m).1, (symDivide s x m).2.2)

/-- The unknown the state knows as the two numbers' bits put together (in either order). -/
def knownOr (x y : Row) : List Known → Option Nat
  | [] => none
  | .or v x' y' :: more => if (x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x) then some v else knownOr x y more
  | _ :: more => knownOr x y more

/-- Where both numbers are seen at once to lie below 2^8, 2^16 or 2^32, the unknown `v` that is their bits
put together lies below it too. -/
def orBound (facts : List Row) (x y : Row) (v : Nat) : List Row :=
  match [8, 16, 32].find? fun (k : Nat) => plain facts (Lin.sub (Lin.const (2 ^ k - 1)) x) && plain facts (Lin.sub (Lin.const (2 ^ k - 1)) y) with
  | some k => [Lin.sub (Lin.const (2 ^ k - 1)) (Lin.var v)]
  | none => []

/-- Two numbers' bits put together (`x | y`). It is no row: one unknown stands for one pair of numbers. It
is a number below 2^64, no less than either of the two. -/
def symOrKnown (s : Sym) (x y : Row) : V (EV × Sym) :=
  match knownOr x y s.known with
  | some v => pure (.lin (Lin.var v), s)
  | none =>
    pure (.lin (Lin.var s.nvars),
      { s with nvars := s.nvars + 1, known := .or s.nvars x y :: s.known,
               facts := ranged s.nvars ++ [Lin.sub (Lin.var s.nvars) x, Lin.sub (Lin.var s.nvars) y] ++ orBound s.facts x y s.nvars ++ s.facts })

/-- The least of 8, 16 and 32 for which the facts say at once that the number lies from 0 to below 2 to that
power. -/
def smallBits (facts : List Row) (x : Row) : Option Nat :=
  [8, 16, 32].find? fun (j : Nat) => plain facts x && plain facts (Lin.sub (Lin.const (2 ^ j - 1)) x)

/-- The bits of a number below 2^j and of a number `k` of the table that is 2^j or more, put together: `k`'s
bits from bit j on are added to what the first number's bits and `k`'s lower bits make. Where `k` has no
lower bit that is the first number itself, and the whole is a row; else it is the unknown that stands for
that pair, and a number of the table more. (So a number that packs a small one into its low bits, as
`flags | 0x40020100` does, is known by its parts.) -/
def symOrSmall (s : Sym) (x : Row) (k : Int) (j : Nat) : V (EV × Sym) :=
  if k % 2 ^ j = 0 then pure (.lin (Lin.add x (Lin.const k)), s)
  else do
    let (u, s) ← symOrKnown s x (Lin.const (k % 2 ^ j))
    match u with
    | .lin ur => pure (.lin (Lin.add ur (Lin.const (k - k % 2 ^ j))), s)
    | _ => refuse "two numbers' bits put together are no number"

/-- Where the first number is seen at once to lie below 2^j (j: 8, 16 or 32) and the second is a number `k` of
the table that is 2^j or more: `k` and j. -/
def orParts (facts : List Row) (x y : Row) : Option (Int × Nat) :=
  match constOf facts y, smallBits facts x with
  | some k, some j => if (2 : Int) ^ j ≤ k then some (k, j) else none
  | _, _ => none

/-- Two numbers' bits put together: where one of the two is the number zero, the other (zero adds no bit);
where one is seen at once to lie below 2^j (j: 8, 16 or 32) and the other is a number of the table that is
2^j or more, by `symOrSmall`; else the unknown that stands for the pair. -/
def symOr (s : Sym) (x y : Row) : V (EV × Sym) :=
  if Lin.isConst y = some 0 then pure (.lin x, s)
  else if Lin.isConst x = some 0 then pure (.lin y, s)
  else
    match orParts s.facts x y with
    | some (k, j) => symOrSmall s x k j
    | none =>
      match orParts s.facts y x with
      | some (k, j) => symOrSmall s y k j
      | none => symOrKnown s x y

/-- Decompose a contiguous 64-bit bitmask `0 < m < 2^64` into `(k, w)` with `m = (2^w - 1) * 2^k`
and `k + w ≤ 64` (covering low-bit masks `k = 0`, alignment masks `k + w = 64`, single-bit tests `w = 1`,
and arbitrary contiguous bitfields such as `0xF0` or `0xFF00`). -/
def maskSpan (m : Int) : Option (Nat × Nat) :=
  if m ≤ 0 || m ≥ 2 ^ 64 then none
  else
    (List.range 64).findSome? fun k =>
      let powk : Int := (2 : Int) ^ k
      if m % powk == 0 then
        let q := m / powk
        (List.range (65 - k)).findSome? fun w =>
          if w ≥ 1 && (2 : Int) ^ w - 1 == q then some (k, w) else none
      else none

/-- Bitwise AND of a symbolic 64-bit value `x` with a known constant mask `m`. -/
def symAndConst (s : Sym) (x : Row) (m : Int) : V (EV × Sym) :=
  if m == 0 then pure (.lin (Lin.const 0), s)
  else match maskSpan m with
  | some (0, w) =>
    let d := symDivide s x ((2 : Int) ^ w)
    pure (.lin d.2.1, d.2.2)
  | some (k, w) =>
    if k + w == 64 then
      let d := symDivide s x ((2 : Int) ^ k)
      pure (.lin (Lin.scale ((2 : Int) ^ k) d.1), d.2.2)
    else
      let d1 := symDivide s x ((2 : Int) ^ k)
      let d2 := symDivide d1.2.2 d1.1 ((2 : Int) ^ w)
      pure (.lin (Lin.scale ((2 : Int) ^ k) d2.2.1), d2.2.2)
  | none =>
    refuse "no proof rule for this AND mask (supported: any contiguous bitmask (2^w - 1) << k, or 0)"

def symPrim (f : String) (s : Sym) (x y : Row) : V (EV × Sym) :=
  if f == "add64" || f == "at" then do
    inRange s.facts (Lin.add (signed x) (signed y))
    pure (.lin (Lin.add (signed x) (signed y)), s)
  else if f == "sub64" then do
    inRange s.facts (Lin.sub (signed x) (signed y))
    pure (.lin (Lin.sub (signed x) (signed y)), s)
  else if f == "equal" then pure (.equal x y, s)
  else if f == "below" then pure (.below x y, s)
  else if f == "shl64" then
    -- a shift to the left by a known constant: so many doublings of what stays below 2^64, which is
    -- the number itself where it is shown to be small enough, else its remainder (the proof says which)
    match constOf s.facts y with
    | some k =>
      if 0 ≤ k ∧ k < 64 then do
        let kept ← staysBelow s.facts x (2 ^ (64 - k.toNat))
        if kept then pure (.lin (Lin.scale (2 ^ k.toNat) x), s)
        else pure (.lin (Lin.scale (2 ^ k.toNat) (symLow s x (2 ^ (64 - k.toNat))).1), (symLow s x (2 ^ (64 - k.toNat))).2)
      else refuse "a shift by 64 or more"
    | none => refuse "a shift by what is no number of the table: not here yet"
  else if f == "shr64" then
    -- a shift to the right by a known constant: the quotient by so many doublings
    match constOf s.facts y with
    | some k =>
      if 0 ≤ k ∧ k < 64 then pure (.lin (symDivide s x (2 ^ k.toNat)).1, (symDivide s x (2 ^ k.toNat)).2.2)
      else refuse "a shift by 64 or more"
    | none => refuse "a shift by what is no number of the table: not here yet"
  else if f == "and64" then
    match constOf s.facts y with
    | some m => symAndConst s x m
    | none =>
      match constOf s.facts x with
      | some m => symAndConst s y m
      | none => refuse "an and with what is no number of the table: not here yet"
  else if f == "sub8" then
    -- a byte less a byte, wrapping: the remainder by 256 of the one, and 256, less the other's low byte
    let y' := symLow s y 256
    let r := symLow y'.2 (Lin.sub (Lin.add x (Lin.const 256)) y'.1) 256
    pure (.lin r.1, r.2)
  else if f == "setlow8" then
    -- the number with its low byte replaced: 256 times its quotient by 256, and the other's low byte
    let q := symQuot s x 256
    let b := symLow q.2 y 256
    pure (.lin (Lin.add (Lin.scale 256 q.1) b.1), b.2)
  else refuse s!"no rule for {f}"

/-- A primitive of one number: its low half, or its low byte (the remainder by 2^32, by 256). -/
def symPrim1 (f : String) (s : Sym) (x : Row) : V (EV × Sym) :=
  if f == "low32" then pure (.lin (symLow s x (2 ^ 32)).1, (symLow s x (2 ^ 32)).2)
  else if f == "low8" then pure (.lin (symLow s x 256).1, (symLow s x 256).2)
  else refuse s!"no rule for {f}"

/-- `data(I)`, the address of a place in the read-only data of the function's own file: the unknown that is
that data's address, plus `I`, where `I` is a number within the data. (The instruction says which file's
data it takes the address in, `pieceOf`: it must be this function's.) -/
def symData (ctx : Ctx) (bind : Bind) (s : Sym) (x : Row) : V (EV × Sym) :=
  if pieceOf bind = ctx.piece then
    match Lin.isConst x with
    | some c =>
      if 0 ≤ c ∧ c < ctx.data.length then pure (.lin (Lin.add (Lin.var (dataVar ctx)) (Lin.const c)), s)
      else refuse "the address of a place that is not in the file's read-only data (or the file has none)"
    | none => refuse "the address of a place in the file's data that is no number"
  else refuse "the address of a place in the read-only data of another file than the function's own"

/-- `on16(sp)`: AArch64's stack pointer as the base of a load or store, where the processor faults unless
it is a multiple of 16. It is one where it is a multiple of 16 away from where it was at entry: there the
caller has seen to it that it is one (`Contract.pre`). -/
def symOn16 (ctx : Ctx) (s : Sym) (x : Row) : V (EV × Sym) :=
  match Lin.isConst (Lin.sub x (Lin.var RSP)) with
  | some c =>
    if ctx.contract.arm64 && decide (c % 16 = 0) then pure (.lin x, s)
    else refuse "the stack pointer is the base of a load or store where it is not shown to be a multiple of 16"
  | none => refuse "what is not the stack pointer is asked to be a multiple of 16"

def symValue (ctx : Ctx) (bind : Bind) : Sym → Expr → V (EV × Sym)
  | s, .number n => if n < 2 ^ 64 then pure (.lin (Lin.const n), s) else refuse "a number of the table that is no 64-bit number"
  | _, .lane _ _ => refuse "a vector register: not here yet"
  | s, .name n =>
    if isNumberLetter n then
      match (bind.lookup n).bind readInt with
      | some i => pure (.lin (Lin.const (i % (M64 : Int))), s)
      | none => refuse "a number that cannot be read"
    else match ctx.regOf bind n with
      | some r => pure (.lin (s.reg r), s)
      | none => refuse s!"no rule for {n}"
  | s, .call f [a] => do
    let (x, s) ← symValue ctx bind s a
    match x with
    | .lin x => if f == "data" then symData ctx bind s x else if f == "on16" then symOn16 ctx s x else symPrim1 f s x
    | _ => refuse "a flag's value where a number is expected"
  | s, .call f [a, b] => do
    let (x, s) ← symValue ctx bind s a
    let (y, s) ← symValue ctx bind s b
    match x, y with
    | .lin x, .lin y =>
      match memSize f with
      | some size => symLoad ctx s (Lin.add (signed x) (signed y)) size
      | none => if f == "or64" then symOr s x y else symPrim f s x y
    | _, _ => refuse "a flag's value where a number is expected"
  | _, .call f _ => refuse s!"no rule for {f}"

/-! ## Vector registers -/

/-- The four low lanes of the vector register named by an effect. -/
def symVec (bind : Bind) (s : Sym) : Expr → Option (List Nat)
  | .name n => (vecOf bind n).bind fun r => (s.vec.lookup r).map (·.take 4)
  | _ => none

/-- One lane, as an EFFECT names it (`Y.2`): one of the four low ones. -/
def symLane (bind : Bind) (s : Sym) : Expr → Option Nat
  | .lane n k => if k < 4 then ((vecOf bind n).bind fun r => s.vec.lookup r).bind fun l => l[k]? else none
  | _ => none

/-- A number of the table in an EFFECT: a number written there, or what a number's letter stands for. -/
def symNumber (bind : Bind) : Expr → Option Int
  | .number n => if n < 2 ^ 64 then some n else none
  | .name n => if isNumberLetter n then ((bind.lookup n).bind readInt).map fun i => i % (M64 : Int) else none
  | _ => none

/-- What a general register holds. -/
def symReg (ctx : Ctx) (bind : Bind) (s : Sym) : Expr → Option Row
  | .name n => if isNumberLetter n then none else (ctx.regOf bind n).map s.reg
  | _ => none

/-- A term for each thing of a list, made one after another: their numbers, and the table then. -/
def termsOf {α : Type} (mk : α → Tab → Nat × Tab) : List α → Tab → List Nat × Tab
  | a :: as, t => ((mk a t).1 :: (termsOf mk as (mk a t).2).1, (termsOf mk as (mk a t).2).2)
  | [], t => ([], t)

/-- The runs whose words are terms (`Node.input`), by their numbers: the runs of a fixed count given to
read, then those given to read and write, then the runs of bytes with a length, then the read-only value
arrays (each with the register its address is in). -/
def Contract.wordRuns (c : Contract) : List (String × Nat × Nat) :=
  c.fixeds ++ c.inouts ++ (c.regions.map fun rl => ("", rl.1, 0)) ++ (c.valArrays.map fun va => (va.1, va.2.1, 0))

/-- Find a read-only value array matching `addr = var r + c` with `0 ≤ c` and `c % 4 = 0`. -/
def findValArray (addr : Row) : List (String × Nat × Nat × Nat × Nat) → Nat → Option (Nat × String × Nat × Nat × Nat × Nat × Int)
  | [], _ => none
  | (x, r, l, ch, el) :: more, k =>
    match Lin.isConst (Lin.sub addr (Lin.var r)) with
    | some c => if 0 ≤ c ∧ c % 4 = 0 then some (k, x, r, l, ch, el, c) else findValArray addr more (k + 1)
    | none => findValArray addr more (k + 1)

/-- Which run of words is at the address a register held at entry. -/
def runAt (r : Nat) : List (String × Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (_, r', _) :: more, j => if r' = r then some j else runAt r more (j + 1)

/-- Two 32-bit word rows from an 8-byte frame cell at `o` (so many bytes from where the stack pointer was at
entry): the low word and high word, where the cell is known and its low 32 bits lie in `[0, 2^32)`. -/
def frameCellWords (s : Sym) (o : Int) : Option (Row × Row) :=
  match s.frame.find? (fun cell => cell.1 == o) with
  | some (_, x) =>
    if knownNonneg s (Lin.word x) && plain s.facts (Lin.sub (Lin.const (W32i - 1)) (Lin.word x)) then
      some (x, Lin.high x)
    else none
  | none => none

/-- `pairs` 8-byte frame cells from `o` on as `2 * pairs` 32-bit word rows. -/
def framePairRows (s : Sym) (o : Int) : Nat → Option (List Row)
  | 0 => some []
  | pairs + 1 =>
    match frameCellWords s o, framePairRows s (o + 8) pairs with
    | some (lo, hi), some rest => some (lo :: hi :: rest)
    | _, _ => none

/-- `count` consecutive 4-byte word term IDs from `s.frameW` starting at offset `o`. -/
def frameWIds (fw : List (Int × Nat)) (o : Int) : Nat → Nat → Option (List Nat)
  | 0, _ => some []
  | count + 1, k =>
    match fw.find? (fun e => e.1 == o + 4 * (k : Int)), frameWIds fw o count (k + 1) with
    | some (_, id), some rest => some (id :: rest)
    | _, _ => none

/-- Read words at a fixed offset divisible by four. They must lie in a read-only run, a read/write run
that has not been written since entry, or known 8-byte cells / 4-byte word terms of the stack frame. -/
def symLoadWords (ctx : Ctx) (s : Sym) (addr : Row) (width : Nat) : V (List Nat × Sym) :=
  let bytes := if width = 4 then "sixteen" else if width = 1 then "four" else "sixty-four"
  let badSize := if width = 4 then "sixteen bytes that are not four words of the run"
                 else if width = 1 then "four bytes that are not a word of the run"
                 else "sixty-four bytes that are not sixteen words of the run"
  match findOut addr ctx.contract.fixeds 0 with
  | some (.out j off) =>
    match Lin.isConst off, ctx.contract.fixeds[j]? with
    | some c, some (_, _, count) =>
      if 0 ≤ c ∧ c % 4 = 0 ∧ c + 4 * width ≤ count then
        let made := termsOf intern ((List.range width).map fun i => Node.input j (c.toNat / 4 + i)) s.tab
        pure (made.1, { s with tab := made.2 })
      else refuse badSize
    | _, _ => refuse s!"{bytes} bytes at a place of a run that is no number"
  | _ =>
    match findOut addr ctx.contract.outs 0 with
    | some (.out w off) =>
      match Lin.isConst off, ctx.contract.outs[w]? with
      | some c, some (_, r, n) =>
        match runAt r (ctx.contract.fixeds ++ ctx.contract.inouts) 0 with
        | some j =>
          match (ctx.contract.fixeds ++ ctx.contract.inouts)[j]? with
          | some (_, _, n') =>
            if !s.intact.contains w then refuse "a read of a run given to read and write after it was written to: not here yet"
            else if 0 ≤ c ∧ c % 4 = 0 ∧ c + 4 * width ≤ n ∧ c + 4 * width ≤ n' then
              let made := termsOf intern ((List.range width).map fun i => Node.input j (c.toNat / 4 + i)) s.tab
              pure (made.1, { s with tab := made.2 })
            else refuse badSize
          | none => refuse s!"{bytes} bytes of a run given only to write"
        | none => refuse s!"{bytes} bytes of a run given only to write"
      | _, _ => refuse s!"{bytes} bytes at a place of a run that is no number"
    | _ =>
      match Lin.isConst (Lin.sub addr (Lin.var RSP)), s.sp with
      | some o, some sp =>
        if sp ≤ o ∧ o + 4 * (width : Int) ≤ 0 then
          match (if width % 2 = 0 then framePairRows s o (width / 2) else none) with
          | some rows =>
            let made := termsOf wAtom rows s.tab
            pure (made.1, { s with tab := made.2 })
          | none =>
            match frameWIds s.frameW o width 0 with
            | some ids => pure (ids, s)
            | none => refuse s!"{bytes} bytes of the frame that are not known words"
        else refuse s!"{bytes} bytes that are of no run of words given to read"
      | _, _ =>
        match findValArray addr ctx.contract.valArrays 0 with
        | some (k, _, _, l, ch, el, c) =>
          let i := c.toNat / el
          if 0 < ch ∧ 0 < el ∧ el % 4 = 0 ∧ c.toNat + 4 * width ≤ el * (i + 1) then do
            entail s.facts (Lin.sub (Lin.var l) (Lin.const ((i + 1) * ch)))
            let j := ctx.contract.fixeds.length + ctx.contract.inouts.length + ctx.contract.regions.length + k
            let made := termsOf intern ((List.range width).map fun m => Node.input j (c.toNat / 4 + m)) s.tab
            pure (made.1, { s with tab := made.2 })
          else refuse badSize
        | none => refuse s!"{bytes} bytes that are of no run of words given to read"

/-- An unscaled address consists of a base register, a displacement and an optional index register. -/
def symWordAddr (ctx : Ctx) (bind : Bind) (s : Sym) : List Expr → Option Row
  | [b, n] => do
    let x ← symReg ctx bind s b
    let k ← symNumber bind n
    some (Lin.add (signed x) (signed (Lin.const k)))
  | [b, n, i] => do
    let x ← symReg ctx bind s b
    let k ← symNumber bind n
    let y ← symReg ctx bind s i
    some (Lin.add (Lin.add (signed x) (signed (Lin.const k))) (signed y))
  | _ => none

def symMemWords (ctx : Ctx) (bind : Bind) (s : Sym) (args : List Expr) (width : Nat) : V (List Nat × Sym) :=
  match symWordAddr ctx bind s args with
  | some a => symLoadWords ctx s a width
  | none => refuse "a word load needs a base register, a displacement and at most one index register"

/-- The two halves of what a general register holds, and two zeros. The low half is the register's number
as a word. The high half: where the number has no multiple of 2^32 in it, its quotient by 2^32, by a
division; else the row of the quotients by 2^32, the row of the remainders being shown to lie below 2^32
(a number put together of two halves). -/
def symHalves (s : Sym) (x : Row) : V (List Nat × Sym) :=
  if Lin.high x == Lin.const 0 && (Lin.isConst x).isNone then
    let d := symDivide s x W32i
    let made := termsOf wAtom [x, d.1, Lin.const 0, Lin.const 0] d.2.2.tab
    pure (made.1, { d.2.2 with tab := made.2 })
  else
    let made := termsOf wAtom [x, Lin.high x, Lin.const 0, Lin.const 0] s.tab
    if (Lin.isConst (Lin.word x)).isNone then do
      entail s.facts (Lin.word x)
      entail s.facts (Lin.sub (Lin.const (W32i - 1)) (Lin.word x))
      pure (made.1, { s with tab := made.2 })
    else pure (made.1, { s with tab := made.2 })

/-- `each32(op, X, Y)`, `each32(op, X, N)`: each word of a register with the same word of another, or with a number. -/
def symEach32 (bind : Bind) (s : Sym) (args : List Expr) : V (List Nat × Sym) :=
  match args with
  | [e1, a, b] =>
    match e1 with
    | .name op =>
        match symVec bind s a with
        | some x =>
          match symVec bind s b with
          | some y =>
            if op == "add32" then
              let made := termsOf (fun (p : Nat × Nat) => wAdd p.1 p.2) (x.zip y) s.tab
              pure (made.1, { s with tab := made.2 })
            else if op == "xor32" then
              let made := termsOf (fun (p : Nat × Nat) => wXor p.1 p.2) (x.zip y) s.tab
              pure (made.1, { s with tab := made.2 })
            else if op == "and32" then
              let made := termsOf (fun (p : Nat × Nat) => wAnd p.1 p.2) (x.zip y) s.tab
              pure (made.1, { s with tab := made.2 })
            else if op == "or32" then
              if x == y then pure (x, s)
              else
              -- the or of a word shifted left and the same word shifted right: the word turned
              match orTurns s.terms (x.zip y) with
              | some turns =>
                let made := termsOf (fun (p : Nat × Nat) => wRotr p.1 p.2) turns s.tab
                pure (made.1, { s with tab := made.2 })
              | none => refuse "an or of two vector registers that is no turn of each word: not here yet"
            else refuse s!"no rule for {op} of two vector registers: not here yet"
          | none =>
            match symNumber bind b with
            | some n =>
              if op == "ror32" then
                let made := termsOf (fun p => wRotr p (n.toNat % 32)) x s.tab
                pure (made.1, { s with tab := made.2 })
              else if op == "shl32" then
                let made := termsOf (fun p => wShl p n.toNat) x s.tab
                pure (made.1, { s with tab := made.2 })
              else if op == "shr32" then
                let made := termsOf (fun p => wShr p n.toNat) x s.tab
                pure (made.1, { s with tab := made.2 })
              else refuse s!"no rule for {op} of a vector register and a number: not here yet"
            | none => refuse "a vector register whose words are not known"
        | none => refuse "a vector register whose words are not known"
    | _ => refuse "a row over a vector register of a form that is not read"
  | _ => refuse "a row over a vector register of a form that is not read"

/-- `shuffle_bytes(X, Z)`: the bytes of each word moved round within the word. -/
def symShuffle (bind : Bind) (s : Sym) (args : List Expr) : V (List Nat × Sym) :=
  -- the bytes of each word moved round within the word: a turn of the word, by a register of four numbers
  match args with
  | [a, b] =>
    match symVec bind s a, symVec bind s b with
    | some x, some y =>
      match (constWords s.terms y).bind shuffleTurn with
      | some n =>
        let made := termsOf (fun p => wRotr p n) x s.tab
        pure (made.1, { s with tab := made.2 })
      | none => refuse "a shuffle of bytes that is no turn of each word by 8 or 16 bits: not here yet"
    | _, _ => refuse "a vector register whose words are not known"
  | _ => refuse "a row over a vector register of a form that is not read"

/-- `pick4`, `blend4`, `blend_halves`: words of two registers, moved. -/
def symMoved (bind : Bind) (s : Sym) (f : String) (args : List Expr) : V (List Nat × Sym) :=
  match args with
  | [a, b, i] =>
    match symVec bind s a, symVec bind s b, symNumber bind i with
    | some x, some y, some i =>
      let i := i.toNat
      if f == "pick4" then pure ([x.getD (i % 4) 0, x.getD (i / 4 % 4) 0, y.getD (i / 16 % 4) 0, y.getD (i / 64 % 4) 0], s)
      else if f == "blend4" then pure ((List.range 4).map (fun k => if i / 2 ^ k % 2 = 1 then y.getD k 0 else x.getD k 0), s)
      else if f == "blend_halves" then
        -- each word wholly from the one register or the other: the two bits of a word are alike
        if (List.range 4).all (fun k => i / 4 ^ k % 4 == 0 || i / 4 ^ k % 4 == 3) then
          pure ((List.range 4).map (fun k => if i / 4 ^ k % 4 = 3 then y.getD k 0 else x.getD k 0), s)
        else refuse "a blend of halves that splits a word: not here yet"
      else refuse s!"no rule for {f}: not here yet"
    | _, _, _ => refuse "a vector register whose words are not known"
  | _ => refuse s!"no rule for {f}: not here yet"

/-- Symbolic SHA-256 32-bit word combinators matching `Machine.lean`'s `sha256*` and `sha256_4way_spec.ode`. -/
def wAdd2 (a b : Nat) (t : Tab) : Nat × Tab := wAdd a b t

def wSha256Ch (e f g : Nat) (t : Tab) : Nat × Tab :=
  let (fg, t) := wXor f g t
  let (efg, t) := wAnd e fg t
  wXor g efg t

def wSha256Maj (a b c : Nat) (t : Tab) : Nat × Tab :=
  let (ab, t) := wAnd a b t
  let (axb, t) := wXor a b t
  let (axbc, t) := wAnd axb c t
  wXor ab axbc t

def wSha256S0 (a : Nat) (t : Tab) : Nat × Tab :=
  let (r2, t) := wRotr a 2 t
  let (r13, t) := wRotr a 13 t
  let (r22, t) := wRotr a 22 t
  let (x1, t) := wXor r2 r13 t
  wXor x1 r22 t

def wSha256S1 (e : Nat) (t : Tab) : Nat × Tab :=
  let (r6, t) := wRotr e 6 t
  let (r11, t) := wRotr e 11 t
  let (r25, t) := wRotr e 25 t
  let (x1, t) := wXor r6 r11 t
  wXor x1 r25 t

def wSha256s0 (x : Nat) (t : Tab) : Nat × Tab :=
  let (r7, t) := wRotr x 7 t
  let (r18, t) := wRotr x 18 t
  let (s3, t) := wShr x 3 t
  let (x1, t) := wXor r7 r18 t
  wXor x1 s3 t

def wSha256s1 (x : Nat) (t : Tab) : Nat × Tab :=
  let (r17, t) := wRotr x 17 t
  let (r19, t) := wRotr x 19 t
  let (s10, t) := wShr x 10 t
  let (x1, t) := wXor r17 r19 t
  wXor x1 s10 t

def wSha256Round (a b c d e f g h wk : Nat) (t : Tab) :
    (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) × Tab :=
  let (s1, t) := wSha256S1 e t
  let (ch, t) := wSha256Ch e f g t
  let (u0, t) := wAdd2 h s1 t
  let (u1, t) := wAdd2 u0 ch t
  let (t1, t) := wAdd2 u1 wk t
  let (s0, t) := wSha256S0 a t
  let (mj, t) := wSha256Maj a b c t
  let (t2, t) := wAdd2 s0 mj t
  let (a', t) := wAdd2 t1 t2 t
  let (e', t) := wAdd2 d t1 t
  ((a', a, b, c, e', e, f, g), t)

def wSha256Msg1 (x y : List Nat) (t : Tab) : List Nat × Tab :=
  let (s0, t) := wSha256s0 (x.getD 1 0) t
  let (r0, t) := wAdd2 (x.getD 0 0) s0 t
  let (s1, t) := wSha256s0 (x.getD 2 0) t
  let (r1, t) := wAdd2 (x.getD 1 0) s1 t
  let (s2, t) := wSha256s0 (x.getD 3 0) t
  let (r2, t) := wAdd2 (x.getD 2 0) s2 t
  let (s3, t) := wSha256s0 (y.getD 0 0) t
  let (r3, t) := wAdd2 (x.getD 3 0) s3 t
  ([r0, r1, r2, r3], t)

def wSha256Msg2 (x z : List Nat) (t : Tab) : List Nat × Tab :=
  let (s0, t) := wSha256s1 (z.getD 2 0) t
  let (r0, t) := wAdd2 (x.getD 0 0) s0 t
  let (s1, t) := wSha256s1 (z.getD 3 0) t
  let (r1, t) := wAdd2 (x.getD 1 0) s1 t
  let (s2, t) := wSha256s1 r0 t
  let (r2, t) := wAdd2 (x.getD 2 0) s2 t
  let (s3, t) := wSha256s1 r1 t
  let (r3, t) := wAdd2 (x.getD 3 0) s3 t
  ([r0, r1, r2, r3], t)

def wSha256Su1 (x y z : List Nat) (t : Tab) : List Nat × Tab :=
  let (t0, t) := wAdd2 (x.getD 0 0) (y.getD 1 0) t
  let (t1, t) := wAdd2 (x.getD 1 0) (y.getD 2 0) t
  let (t2, t) := wAdd2 (x.getD 2 0) (y.getD 3 0) t
  let (t3, t) := wAdd2 (x.getD 3 0) (z.getD 0 0) t
  wSha256Msg2 [t0, t1, t2, t3] z t

def wSha256Rnds2 (x z wk : List Nat) (t : Tab) : List Nat × Tab :=
  let ((a1, b1, c1, d1, e1, f1, g1, h1), t) :=
    wSha256Round (z.getD 3 0) (z.getD 2 0) (x.getD 3 0) (x.getD 2 0)
                 (z.getD 1 0) (z.getD 0 0) (x.getD 1 0) (x.getD 0 0) (wk.getD 0 0) t
  let ((a2, b2, _, _, e2, f2, _, _), t) :=
    wSha256Round a1 b1 c1 d1 e1 f1 g1 h1 (wk.getD 1 0) t
  ([f2, e2, b2, a2], t)

def wSha256H (x y wk : List Nat) (t : Tab) : List Nat × Tab :=
  let ((a1, b1, c1, d1, e1, f1, g1, h1), t) :=
    wSha256Round (x.getD 0 0) (x.getD 1 0) (x.getD 2 0) (x.getD 3 0)
                 (y.getD 0 0) (y.getD 1 0) (y.getD 2 0) (y.getD 3 0) (wk.getD 0 0) t
  let ((a2, b2, c2, d2, e2, f2, g2, h2), t) := wSha256Round a1 b1 c1 d1 e1 f1 g1 h1 (wk.getD 1 0) t
  let ((a3, b3, c3, d3, e3, f3, g3, h3), t) := wSha256Round a2 b2 c2 d2 e2 f2 g2 h2 (wk.getD 2 0) t
  let ((a4, b4, c4, d4, _, _, _, _), t) := wSha256Round a3 b3 c3 d3 e3 f3 g3 h3 (wk.getD 3 0) t
  ([a4, b4, c4, d4], t)

def wSha256H2 (x y wk : List Nat) (t : Tab) : List Nat × Tab :=
  let ((a1, b1, c1, d1, e1, f1, g1, h1), t) :=
    wSha256Round (y.getD 0 0) (y.getD 1 0) (y.getD 2 0) (y.getD 3 0)
                 (x.getD 0 0) (x.getD 1 0) (x.getD 2 0) (x.getD 3 0) (wk.getD 0 0) t
  let ((a2, b2, c2, d2, e2, f2, g2, h2), t) := wSha256Round a1 b1 c1 d1 e1 f1 g1 h1 (wk.getD 1 0) t
  let ((a3, b3, c3, d3, e3, f3, g3, h3), t) := wSha256Round a2 b2 c2 d2 e2 f2 g2 h2 (wk.getD 2 0) t
  let ((_, _, _, _, e4, f4, g4, h4), t) := wSha256Round a3 b3 c3 d3 e3 f3 g3 h3 (wk.getD 3 0) t
  ([e4, f4, g4, h4], t)

def isSha256Op (f : String) : Bool :=
  f == "sha256msg1" || f == "sha256msg2" || f == "sha256su1" ||
  f == "sha256rnds2" || f == "sha256h" || f == "sha256h2"

/-- Hardware SHA-256 vector instructions (`sha256msg1/2`, `sha256rnds2`, `sha256su0/1`, `sha256h/h2`). -/
def symSha256 (bind : Bind) (s : Sym) (f : String) (args : List Expr) : V (List Nat × Sym) :=
  match args with
  | [a, b] =>
    match symVec bind s a, symVec bind s b with
    | some x, some y =>
      if f == "sha256msg1" then
        let made := wSha256Msg1 x y s.tab
        pure (made.1, { s with tab := made.2 })
      else if f == "sha256msg2" then
        let made := wSha256Msg2 x y s.tab
        pure (made.1, { s with tab := made.2 })
      else refuse s!"no rule for {f}: not here yet"
    | _, _ => refuse "a vector register whose words are not known"
  | [a, b, c] =>
    match symVec bind s a, symVec bind s b, symVec bind s c with
    | some x, some y, some z =>
      if f == "sha256su1" then
        let made := wSha256Su1 x y z s.tab
        pure (made.1, { s with tab := made.2 })
      else if f == "sha256rnds2" then
        let made := wSha256Rnds2 x y z s.tab
        pure (made.1, { s with tab := made.2 })
      else if f == "sha256h" then
        let made := wSha256H x y z s.tab
        pure (made.1, { s with tab := made.2 })
      else if f == "sha256h2" then
        let made := wSha256H2 x y z s.tab
        pure (made.1, { s with tab := made.2 })
      else refuse s!"no rule for {f}: not here yet"
    | _, _, _ => refuse "a vector register whose words are not known"
  | _ => refuse s!"no rule for {f}: not here yet"

/-- The four words an EFFECT sets a vector register to (as `lanesOf` of the machine has them), as terms. -/
def symLanes (ctx : Ctx) (bind : Bind) (s : Sym) : Expr → V (List Nat × Sym)
  | .name n =>
    match symVec bind s (.name n) with
    | some l => pure (l, s)
    | none => refuse "a vector register whose words are not known"
  | .call f args =>
    if f == "mem128" then symMemWords ctx bind s args 4
    else if f == "words" then
      -- four numbers of the table
      match args with
      | [a, b, c, d] =>
        match symNumber bind a, symNumber bind b, symNumber bind c, symNumber bind d with
        | some ka, some kb, some kc, some kd =>
          let made := termsOf wAtom [Lin.const ka, Lin.const kb, Lin.const kc, Lin.const kd] s.tab
          pure (made.1, { s with tab := made.2 })
        | _, _, _, _ => refuse "a word that is no number of the table"
      | _ => refuse "four words are not four"
    else if f == "lanes_of64" then
      match args with
      | [a] =>
        match symReg ctx bind s a with
        | some x => symHalves s x
        | none => refuse "the halves of what is no general register"
      | _ => refuse "the halves of what is no one register"
    else if f == "lanes" then
      match args with
      | [a, b, c, d] =>
        match symLane bind s a, symLane bind s b, symLane bind s c, symLane bind s d with
        | some ia, some ib, some ic, some id => pure ([ia, ib, ic, id], s)
        | _, _, _, _ => refuse "a lane of a vector register whose words are not known"
      | _ => refuse "four lanes are not four"
    else if f == "each32" then symEach32 bind s args
    else if f == "shuffle_bytes" then symShuffle bind s args
    else if isSha256Op f then symSha256 bind s f args
    else symMoved bind s f args
  | _ => refuse "a row over a vector register of a form that is not read"

/-- A wide read requires all sixteen lanes. -/
def symVec512 (bind : Bind) (s : Sym) : Expr → Option (List Nat)
  | .name n => ((vecOf512 bind n).bind fun r => s.vec.lookup r).filter (·.length == 16)
  | _ => none

/-- Replicate the low word of a scalar value into a wide register. -/
def symSpreadScalar16 (ctx : Ctx) (bind : Bind) (s : Sym) (a : Expr) : V (List Nat × Sym) := do
  let (v, s) ← symValue ctx bind s a
  match v with
  | .lin x =>
    let made := wAtom x s.tab
    pure (List.replicate 16 made.1, { s with tab := made.2 })
  | _ => refuse "a flag where a word is expected"

def symSpread16 (ctx : Ctx) (bind : Bind) (s : Sym) : Expr → V (List Nat × Sym)
  | .call f args =>
    if f == "mem32" then do
      let (l, s) ← symMemWords ctx bind s args 1
      pure (List.replicate 16 (l.getD 0 0), s)
    else if f == "low32" then
      -- (the low half of a number, as a word, is the number as a word: no remainder is taken first)
      match args with
      | [a] => symSpreadScalar16 ctx bind s a
      | _ => refuse "the low half of what is no one number"
    else symSpreadScalar16 ctx bind s (.call f args)
  | a => symSpreadScalar16 ctx bind s a

def symPair512 (bind : Bind) (s : Sym) (a b : Expr) (f : List Nat → List Nat → V (List Nat × Sym)) : V (List Nat × Sym) :=
  match symVec512 bind s a, symVec512 bind s b with
  | some x, some y => f x y
  | _, _ => refuse "a 512-bit register whose lanes are not all known"

/-- (The table is taken out of the state while terms are added to it, so that it is added to where it
lies: a table that the state still holds would be copied at the first new term.) -/
def symLaneTerms {α : Type} (s : Sym) (mk : α → Tab → Nat × Tab) (xs : List α) : V (List Nat × Sym) :=
  let tab := s.tab
  let s := { s with tab := {} }
  let made := termsOf mk xs tab
  pure (made.1, { s with tab := made.2 })

def symShuffle512 (bind : Bind) (s : Sym) (f : String) (args : List Expr) : V (List Nat × Sym) :=
  match args with
  | [a, b, .number p0, .number p1, .number p2, .number p3] =>
    symPair512 bind s a b fun x y =>
      if f == "in_quarters" && [p0, p1, p2, p3].all (· < 8) then pure (inQuarters x y [p0, p1, p2, p3], s)
      else refuse "invalid shuffle within quarters"
  | [a, b, i] =>
    symPair512 bind s a b fun x y =>
      if f == "quarters" then
        match symNumber bind i with
        | some n => pure (quarters x y n.toNat, s)
        | none => refuse "shuffling quarters needs an immediate"
      else refuse "no proof rule for this 512-bit shuffle"
  | _ => refuse "no proof rule for this 512-bit value"

def frameOffset (a : Row) : Row := Lin.sub a (Lin.var RSP)

def frameSpanGoals (ctx : Ctx) (s : Sym) (a : Row) (size : Nat) : List Row :=
  let o := frameOffset a
  [Lin.sub a (s.reg RSP), Lin.add o (Lin.const ctx.contract.stack), Lin.sub (Lin.const (-(size : Int))) o]

def savedWordGoals (s : Sym) (a : Row) (size : Nat) : List Row :=
  s.frame.map fun (o, _) => Lin.sub (Lin.const (o - size)) (frameOffset a)

def aligned64 (a : Row) : Bool := a.coeff.all (fun x => x % 64 == 0) && a.constant % 64 == 0

/-- Touch the first byte of the current frame without recording a value that can be read back. -/
def symTouchFrame (ctx : Ctx) (s : Sym) (a : Row) : V Sym := do
  each (entail s.facts) (frameSpanGoals ctx s a 1)
  each (entail s.facts) (savedWordGoals s a 1)
  pure { s with spill := [], frameW := [], range := none }

/-- Two aligned 64-byte cells of the frame that are known not to overlap: their offsets differ by a
number alone, of 64 or more. -/
def cellsApart (o o' : Row) : Bool :=
  Lin.sameCoeff o.coeff o'.coeff && (decide (o.constant + 64 ≤ o'.constant) || decide (o'.constant + 64 ≤ o.constant))

def symSpillLoad (ctx : Ctx) (bind : Bind) (s : Sym) (args : List Expr) : V (List Nat × Sym) :=
  match symWordAddr ctx bind s args with
  | some a =>
    match s.spill.find? fun (o, _) => frameOffset a == o with
    | some (_, l) =>
      if aligned64 a then do
        each (entail s.facts) (frameSpanGoals ctx s a 64)
        pure (l, s)
      else refuse "the aligned load's address is not known to be 64-byte aligned"
    | none => refuse "the aligned load does not match a saved stack vector"
  | none => refuse "no saved stack vector for this aligned load"

def symSpillStore (ctx : Ctx) (bind : Bind) (s : Sym) (args : List Expr) (l : List Nat) : V Sym :=
  match symWordAddr ctx bind s args with
  | some a =>
    if aligned64 a then do
      each (entail s.facts) (frameSpanGoals ctx s a 64)
      each (entail s.facts) (savedWordGoals s a 64)
      pure { s with range := none, frameW := [], spill := (frameOffset a, l) :: s.spill.filter fun (o, _) => cellsApart o (frameOffset a) }
    else refuse "the vector store's address is not known to be 64-byte aligned"
  | none => refuse "the aligned vector store needs a known address"

/-- The unknown in an address that the state knows as an address a table holds: the unknown, the table,
the place in it, and the register with the count of blocks. -/
def findLane (c : Contract) (addr : Row) : List Known → Option (Nat × Nat × Nat × Nat)
  | [] => none
  | .load v j p :: more =>
    match c.tableAt j with
    | some (_, _, _, l) => if Lin.coeffOf addr v == 1 then some (v, j, p, l) else findLane c addr more
    | none => findLane c addr more
  | _ :: more => findLane c addr more

/-- Sixty-four bytes read through an address a table holds: a block's sixteen words, at a place shown to
lie within the lane's blocks. Each word is a new unknown, and the state knows which words of the blocks
they are. (The blocks are only read, and lie apart from everything written: they hold what they held at
entry. No fact is added of the unknowns: they are used as words only, and a fact a word would be gone
through at every later step.) -/
def symLoadBlock (s : Sym) (v j p l : Nat) (addr : Row) : V (List Nat × Sym) :=
  if p % 8 != 0 then refuse "a read through an address that is not one of a table's"
  else do
    let off := Lin.sub addr (Lin.var v)
    entail s.facts off
    entail s.facts (Lin.sub (Lin.sub (Lin.scale 64 (Lin.var l)) off) (Lin.const 64))
    let vs := (List.range 16).map (s.nvars + ·)
    symLaneTerms { s with nvars := s.nvars + 16, known := .block j p off vs :: s.known } wAtom (vs.map Lin.var)

/-- An unaligned read of the sixty-four bytes of a cell of the frame that a vector was stored to: that
vector's words. (`symSpillLoad` is the aligned read.) -/
def symCellLoad (ctx : Ctx) (s : Sym) (a : Row) (l : List Nat) : V (List Nat × Sym) := do
  each (entail s.facts) (frameSpanGoals ctx s a 64)
  pure (l, s)

/-- Sixty-four bytes of memory as sixteen words: a block read through an address a table holds, a cell of
the frame that a vector was stored to, or sixteen words of a run. -/
def symMem512 (ctx : Ctx) (bind : Bind) (s : Sym) (f : String) (args : List Expr) : V (List Nat × Sym) :=
  if f == "mem512" then
    match (symWordAddr ctx bind s args).bind fun a => (findLane ctx.contract a s.known).map fun x => (a, x) with
    | some (a, v, j, p, l) => symLoadBlock s v j p l a
    | none =>
      match (symWordAddr ctx bind s args).bind fun a => (s.spill.find? fun (o, _) => frameOffset a == o).map fun c => (a, c) with
      | some (a, _, l) => symCellLoad ctx s a l
      | none => symMemWords ctx bind s args 16
  else if f == "mem512a" then symSpillLoad ctx bind s args
  else refuse "no proof rule for this 512-bit value"

/-- One operation on each pair of words of two lists of sixteen. -/
def symEachOp (s : Sym) (op : String) (x y : List Nat) : V (List Nat × Sym) :=
  if op == "add32" then symLaneTerms s (fun (p : Nat × Nat) => wAdd p.1 p.2) (x.zip y)
  else if op == "xor32" then symLaneTerms s (fun (p : Nat × Nat) => wXor p.1 p.2) (x.zip y)
  else if op == "and32" then symLaneTerms s (fun (p : Nat × Nat) => wAnd p.1 p.2) (x.zip y)
  else if op == "ult32" then symLaneTerms s (fun (p : Nat × Nat) => wUlt p.1 p.2) (x.zip y)
  else refuse "no proof rule for this 512-bit operation"

def symEach512 (ctx : Ctx) (bind : Bind) (s : Sym) (op : String) (a b : Expr) : V (List Nat × Sym) :=
  if op == "ror32" then
    match symVec512 bind s a, symNumber bind b with
    | some x, some n => symLaneTerms s (fun p => wRotr p (n.toNat % 32)) x
    | _, _ => refuse "a rotate needs a known 512-bit register and an immediate"
  else
    match b with
    | .call f args =>
      if f == "words16" then
        -- the second operand is sixteen numbers of the table (a constant of the file): added lane by lane
        match symVec512 bind s a, words16 bind args with
        | some x, some ks =>
          if op == "add32" then symLaneTerms s (fun (p : Nat × Nat) => wAddConst p.1 p.2) (x.zip ks)
          else refuse "no proof rule for this 512-bit operation with a constant"
        | _, _ => refuse "a 512-bit register whose lanes are not all known"
      else do
      -- the second operand is sixty-four bytes of memory (`vpaddd zmm, zmm, [mem]`): it is read first
      let (y, s) ← symMem512 ctx bind s f args
      match symVec512 bind s a with
      | some x => symEachOp s op x y
      | none => refuse "a 512-bit register whose lanes are not all known"
    | _ =>
      -- (the registers are looked up before the state is handed on: a state held here as well would have
      -- its table copied)
      match symVec512 bind s a, symVec512 bind s b with
      | some x, some y => symEachOp s op x y
      | _, _ => refuse "a 512-bit register whose lanes are not all known"

def symLanes512 (ctx : Ctx) (bind : Bind) (s : Sym) : Expr → V (List Nat × Sym)
  | .name n =>
    match symVec512 bind s (.name n) with
    | some l => pure (l, s)
    | none => refuse "a 512-bit register whose lanes are not all known"
  | .call f args =>
    if f == "zeros16" && args.isEmpty then
      let made := wAtom (Lin.const 0) s.tab
      pure (List.replicate 16 made.1, { s with tab := made.2 })
    else if f == "spread16" then
      match args with
      | [.call g [a]] => if g == "lane32" then symSpread16 ctx bind s a else refuse "expected a 32-bit broadcast source"
      | _ => refuse "expected a 32-bit broadcast source"
    else if f == "each32" then
      match args with
      | [.name op, a, b] => symEach512 ctx bind s op a b
      | _ => refuse "expected a 32-bit operation and two operands"
    else if f == "mem512" || f == "mem512a" then symMem512 ctx bind s f args
    else if f == "choose16" then
      -- under a mask: in each lane the operation's result where the mask's bit is set, else what `c` holds
      match args with
      | [m, .call g [.name op, a, b], c] =>
        if g == "each32" then
          match symVec512 bind s m, symVec512 bind s a, symVec512 bind s b, symVec512 bind s c with
          | some k, some x, some y, some old => do
            let (new, s) ← symEachOp s op x y
            symLaneTerms s (fun (p : Nat × Nat × Nat) => wSel p.1 p.2.1 p.2.2) (k.zip (new.zip old))
          | _, _, _, _ => refuse "a 512-bit register or a mask register whose lanes are not all known"
        else refuse "no proof rule for this operation under a mask"
      | _ => refuse "no proof rule for this operation under a mask"
    else symShuffle512 bind s f args
  | _ => refuse "no proof rule for this 512-bit value"

/-- Where a place has said what the run `w` holds on a prefix or suffix, a byte written to the run at `o`
lies outside that range. -/
def belowRange (s : Sym) (w : Nat) (o : Row) : V Unit :=
  match s.range with
  | some rg =>
    if rg.w == w then
      if rg.fromStart then entail s.facts (Lin.sub o rg.lo)
      else entail s.facts (Lin.sub (Lin.sub rg.lo o) (Lin.const 1))
    else pure ()
  | none => pure ()

/-- Keep only the lanes the machine model preserves across `above128 = unknown`. -/
def forgetHigh (vec : List (Nat × List Nat)) : List (Nat × List Nat) :=
  vec.map fun (r, lanes) => (r, if r < 16 then lanes.take 4 else lanes)

/-- A run given to read and write that nothing was written to yet, taken as written with the words it held
at entry: the term of each of its words (the word as it was at entry) is put into the table and is known
as the word written there. (A part of the run can then be written, and the other words stay known.) Any
other run, and a run that is not whole words: the state as it was. -/
def Sym.touch (ctx : Ctx) (s : Sym) (w : Nat) : Sym :=
  match ctx.contract.outs[w]? with
  | some (x, b, n) =>
    if s.intact.contains w = true ∧ ctx.contract.inouts.contains (x, b, n) = true ∧ n % 4 = 0 then
      match runAt b ctx.contract.wordRuns 0 with
      | some j =>
        let made := termsOf intern ((List.range (n / 4)).map fun k => Node.input j k) s.tab
        { s with tab := made.2, intact := s.intact.filter (· != w),
                 wroteW := ((List.range (n / 4)).map fun k => (w, k, made.1.getD k 0)) ++ s.wroteW }
      | none => s
    else s
  | none => s

/-- Replace the known words at the store's offsets. Other word stores remain in force. -/
def rememberStore (s : Sym) (w j : Nat) (l : List Nat) : Sym :=
  { s with intact := s.intact.filter (· != w), spill := [], range := none,
           wroteW := ((List.range l.length).map fun i => (w, j + i, l.getD i 0)) ++
                     s.wroteW.filter fun e => !(e.1 == w && decide (j ≤ e.2.1) && decide (e.2.1 < j + l.length)) }

def symStoreWords (ctx : Ctx) (s : Sym) (addr : Row) (l : List Nat) (width : Nat) : V Sym :=
  let bytes := if width = 4 then "sixteen" else "sixty-four"
  match findOut addr ctx.contract.outs 0 with
  | some (.out w off) =>
    match Lin.isConst off, ctx.contract.outs[w]? with
    | some c, some (_, _, count) =>
      if !(0 ≤ c ∧ c % 4 = 0 ∧ c + 4 * width ≤ count) then
        refuse (if width = 4 then "sixteen bytes that are not four words of the run" else "sixty-four bytes that are not sixteen words of the run")
      else if s.wrote.any (fun e => e.1 == w) then refuse "words written to a run that bytes were written to: not here yet"
      else if l.length != width then refuse "the vector store's width does not match its known lanes"
      else pure (rememberStore s w (c.toNat / 4) l)
    | _, _ => refuse s!"{bytes} bytes at a place of a run that is no number"
  | _ =>
    match Lin.isConst (Lin.sub addr (Lin.var RSP)), s.sp with
    | some o, some sp =>
      if -(ctx.contract.stack : Int) ≤ o ∧ sp ≤ o ∧ o + 4 * (width : Int) ≤ 0 ∧ l.length == width then
        pure { s with
          spill := [], range := none,
          frame := s.frame.filter fun (c, _) => decide (c + 8 ≤ o) || decide (o + 4 * (width : Int) ≤ c),
          frameW := ((List.range width).map fun (k : Nat) => (o + 4 * (k : Int), l.getD k 0)) ++
                    s.frameW.filter fun (c, _) => decide (c + 4 ≤ o) || decide (o + 4 * (width : Int) ≤ c) }
      else refuse s!"{bytes} bytes written to what is no run given to write"
    | _, _ => refuse s!"{bytes} bytes written to what is no run given to write"

/-- Eight bytes, a number, stored at a place of the run `w` given to write (`n` bytes) that is a number
divisible by four: two words of the run now hold the number's low half and its high half (the quotient by
2^32, as a shift finds it). A run given to read and write that nothing was written to is first taken as
written with the words it held at entry, so its other words stay known. No single byte of the run may have
been written. -/
def symStore8 (ctx : Ctx) (s : Sym) (w n : Nat) (o x : Row) : V Sym :=
  match Lin.isConst o with
  | some c =>
    if 0 ≤ c ∧ c % 4 = 0 ∧ c + 8 ≤ n ∧ s.wrote.all (fun e => e.1 != w) = true then
      if Lin.hasHigh x && knownNonneg s (Lin.word x) && plain s.facts (Lin.sub (Lin.const (W32i - 1)) (Lin.word x)) then
        -- (the number is written as a low part and a multiple of 2^32, and the row of the remainders by
        -- 2^32 is seen at once to be a word: the high half is the row of the quotients, and nothing is
        -- divided. So a cell that two known words make gives those two words back. Any other number is
        -- divided, so that the specification's division of it finds the same quotient.)
        let t := s.touch ctx w
        let lo := wAtom x t.tab
        let hi := wAtom (Lin.high x) lo.2
        pure (rememberStore { t with tab := hi.2 } w (c.toNat / 4) [lo.1, hi.1])
      else
        let d := symDivide (s.touch ctx w) x W32i
        let lo := wAtom x d.2.2.tab
        let hi := wAtom d.1 lo.2
        pure (rememberStore { d.2.2 with tab := hi.2 } w (c.toNat / 4) [lo.1, hi.1])
    else refuse "eight bytes that are not two words of the run, or of a run that single bytes were written to"
  | none => refuse "eight bytes at a place of a run that is no number"

def symStmt (ctx : Ctx) (bind : Bind) (s : Sym) : Stmt → V Sym
  | .nothing => pure s
  | .vset512 place v =>
    match place with
    | .name n =>
      match vecOf512 bind n with
      | some r => do
        let (l, s) ← symLanes512 ctx bind s v
        if l.length == 16 then pure { s with vec := (r, l) :: s.vec, vecIntact := s.vecIntact.filter (· != r) } else refuse "expected sixteen lanes"
      | none => refuse "a row that sets what is no 512-bit register"
    | .call f [b, n] =>
      if f == "mem512" then
        match symVec512 bind s v, symReg ctx bind s b, symNumber bind n with
        | some l, some x, some k => symStoreWords ctx s (Lin.add (signed x) (signed (Lin.const k))) l 16
        | _, _, _ => refuse "a 512-bit store needs a known register, a base register and a displacement"
      else if f == "mem512a" then
        match symVec512 bind s v with
        | some l => symSpillStore ctx bind s [b, n] l
        | none => refuse "the spilled vector register needs all sixteen lanes"
      else refuse "no proof rule for this 512-bit destination"
    | _ => refuse "no proof rule for this 512-bit destination"
  | .vset place v =>
    match place with
    | .name n =>
      if n == "above128" then
        if isUnknown v then pure { s with vec := forgetHigh s.vec, vecIntact := s.vecIntact.filter (fun x => decide (16 ≤ x)) } else refuse "a row that sets the high lanes: not here yet"
      else
        match vecOf bind n with
        | some r => do
          let (l, s) ← symLanes ctx bind s v
          if l.length == 4 then pure { s with vec := (r, l) :: s.vec, vecIntact := s.vecIntact.filter (· != r) } else refuse "four words are not four"
        | none => refuse "a row that sets what is no vector register"
    | .call f [b, n] =>
      -- sixteen bytes of a run given to write, at a place that is a number divisible by four: four words
      -- of it now hold the register's four words
      if f == "mem128" then
        match symVec bind s v, symReg ctx bind s b, symNumber bind n with
        | some l, some x, some k => symStoreWords ctx s (Lin.add (signed x) (signed (Lin.const k))) l 4
        | _, _, _ => refuse "a store of a vector register whose words are not known, or at an address that is not a register and a number"
      else refuse "a store of a vector register of a form that is not read"
    | _ => refuse "a store of a vector register of a form that is not read"
  | .set place v =>
    if isUnknown v then
      match place with
      | .name n =>
        if n == "zf" then pure { s with zf := .unknown }
        else if n == "cf" then pure { s with cf := .unknown }
        else refuse "a register of which the row says nothing: not here yet"
      | _ => refuse "memory of which the row says nothing"
    else do
      let (ev, s) ← symValue ctx bind s v
      match place with
      | .name n =>
        if n == "zf" then
          match ev with
          | .equal a b => pure { s with zf := .equal a b }
          | .below a b => pure { s with zf := .below a b }
          | .lin _ => refuse "a number where a flag's value is expected"
        else if n == "cf" then
          match ev with
          | .equal a b => pure { s with cf := .equal a b }
          | .below a b => pure { s with cf := .below a b }
          | .lin _ => refuse "a number where a flag's value is expected"
        else
          match regOf bind n, ev with
          | some r, .lin x => pure (s.put r x)
          | _, _ => refuse s!"no rule for setting {n}"
      | .call f [a, b] => do
        let (ea, s) ← symValue ctx bind s a
        let (eb, s) ← symValue ctx bind s b
        match ev, ea, eb with
        | .lin x, .lin a, .lin b =>
          match locate ctx (Lin.add (signed a) (signed b)) with
          | some (.frame c) =>
            if memSize f = some 8 ∧ inFrame ctx s c = true then
              pure { s with spill := [],
                            frame := (c, x) :: s.frame.filter fun (o, _) => decide (o + 8 ≤ c) || decide (c + 8 ≤ o),
                            frameW := s.frameW.filter fun (o, _) => decide (o + 4 ≤ c) || decide (c + 8 ≤ o) }
            else refuse "a write that is not eight bytes of the frame in use"
          | some (.out w o) =>
            -- one byte, at a place shown to be within the run, the byte shown to be one (0 to 255)
            match ctx.contract.outs[w]? with
            | some (_, _, n) =>
              if memSize f = some 1 then do
                entail s.facts o
                entail s.facts (Lin.sub (Lin.const ((n : Int) - 1)) o)
                entail s.facts x
                entail s.facts (Lin.sub (Lin.const 255) x)
                if s.wroteW.any (fun e => e.1 == w) then refuse "a byte written to a run that words were written to: not here yet"
                else
                match keepWrote w o s.wrote with
                | some rest => do
                  belowRange s w o
                  pure { s with wrote := (w, o, x) :: rest, intact := s.intact.filter (· != w), spill := [] }
                | none => refuse "a write at a place not known apart from one written before: not here yet"
              else if memSize f = some 8 then symStore8 ctx s w n o x        -- (eight bytes: a number, as two words)
              else refuse "a write of two or four bytes to a run given to write: not here yet"
            | none => refuse "no such run of bytes"
          | none =>
            let addr := Lin.add (signed a) (signed b)
            if memSize f = some 1 ∧ addr = s.reg RSP then symTouchFrame ctx s addr
            else refuse "a write to a run given only to read, or to no run given"
          | _ => refuse "a write to a run given only to read, or to no run given"
        | _, _, _ => refuse "a flag's value where a number is expected"
      | _ => refuse "a row that sets what is no place"
  | _ => refuse "a jump, a call or a return among other statements"

/-- After an instruction: the stack pointer is in the frame the contract allows, and nothing is remembered
below it. -/
def stackGoals (ctx : Ctx) (s : Sym) : List Row :=
  let off := Lin.sub (s.reg RSP) (Lin.var RSP)
  Lin.add off (Lin.const ctx.contract.stack) :: Lin.scale (-1) off ::
    ((s.frame.map fun (o, _) => Lin.sub (Lin.const o) off) ++
     (s.spill.map fun (o, _) => Lin.sub o off))

/-- Two lists of cells of the frame are the same. -/
def sameCells : List (Int × Row) → List (Int × Row) → Bool
  | [], [] => true
  | (o, v) :: a, (o', v') :: b => o == o' && Lin.same v v' && sameCells a b
  | _, _ => false

/-- Two lists of spills are the same. -/
def sameSpills : List (Row × List Nat) → List (Row × List Nat) → Bool
  | [], [] => true
  | (o, l) :: a, (o', l') :: b => Lin.same o o' && l == l' && sameSpills a b
  | _, _ => false

/-- The stack pointer, the cells of the frame and the spills are as they were when `settle` last showed
the stack's facts. (Then there is nothing to show again. Nothing rests on this: `settle` only adds facts
it has shown.) -/
def stackSame (s : Sym) : Bool :=
  match s.stackAt with
  | some (sp, frame, spill) => Lin.same sp (s.reg RSP) && sameCells frame s.frame && sameSpills spill s.spill
  | none => false

def settle (ctx : Ctx) (s : Sym) : V Sym :=
  match s.sp with
  | some sp =>
    if sp ≤ 0 ∧ -(ctx.contract.stack : Int) ≤ sp then
      pure { s with spill := [], frame := s.frame.filter fun (o, _) => decide (sp ≤ o),
                                 frameW := s.frameW.filter fun (o, _) => decide (sp ≤ o) }
    else refuse "the stack pointer leaves the frame the contract allows"
  | none =>
    if stackSame s then pure { s with frameW := [] } else do
    -- Every saved word must remain at or above the stack pointer. Remember these facts so
    -- instructions that leave the stack pointer in place do not need another copy of the proofs.
    let missing := (stackGoals ctx s).filter fun g => !plain s.facts g
    each (entail s.facts) missing
    pure { s with facts := missing ++ s.facts, frameW := [], stackAt := some (s.reg RSP, s.frame, s.spill) }

def constBelowZero (r : Row) : Bool :=
  match Lin.isConst r with
  | some k => decide (k < 0)
  | none => false

/-- A way a jump can go: the rows assumed on it. No input takes a way the proof shows impossible. -/
def assume (s : Sym) (rows : List Row) : V (Option Sym) :=
  if rows.any constBelowZero then pure none
  else if rows.all fun r => (Lin.isConst r).isSome then pure (some s)
  else do
    match ← pop with
    | some (.tag name _) =>
      if name == "live" then pure (some { s with facts := rows ++ s.facts })
      else if name == "dead" then do
        match ← pop with
        | some (.proof starts steps) =>
          if Arithmetic.refutes (rows ++ s.facts) (pick (rows ++ s.facts) starts) steps then pure none
          else refuse "a proof of arithmetic does not show that no input goes this way"
        | some (.proofRows starts steps) =>
          if Arithmetic.refutes (rows ++ s.facts) starts steps then pure none
          else refuse "a proof of arithmetic does not show that no input goes this way"
        | _ => refuse "a proof of arithmetic is expected"
      else refuse "live or dead is expected"
    | some _ => refuse "live or dead is expected"
    | none => need "branch" (rows ++ s.facts) []

/-! ## The specification, on symbols -/

inductive SRes where
  | val (v : SVal)
  | tail (c : SCall)      -- the value is that of this use of a definition, which is not opened here
  | list (vs : List SVal) -- the things a definition is used with

/-- True when the specification facts already record `a ≠ b` (i.e. `a - b ≠ 0` or `b - a ≠ 0`). -/
def hasNeq (facts : List SFact) (a b : Row) : Bool :=
  let d := Lin.sub a b
  let d' := Lin.sub b a
  facts.any fun
    | .neq r => Lin.same r d || Lin.same r d'
    | _ => false

def sbin (op : String) (s : Sym) (x y : Row) : V (SRes × Sym) :=
  if op == "+" then pure (.val (.lin (Lin.add x y)), s)
  else if op == "-" then do
    entail s.facts (Lin.sub x y)                  -- a difference has a value only where it is not below zero
    pure (.val (.lin (Lin.sub x y)), s)
  else if op == "*" then
    match Lin.isConst x, Lin.isConst y with
    | some k, _ => pure (.val (.lin (Lin.scale k y)), s)
    | _, some k => pure (.val (.lin (Lin.scale k x)), s)
    | _, _ => refuse "a product of two unknowns: not here yet"
  else if op == "==" then
    if hasNeq s.spec x y then pure (.val (.bool false), s)
    else do let c ← compare s.facts x y; pure (.val (.bool c.isEq), s)
  else if op == "!=" then
    if hasNeq s.spec x y then pure (.val (.bool true), s)
    else do let c ← compare s.facts x y; pure (.val (.bool (!c.isEq)), s)
  -- an order is asked two ways: below or not (where the facts say `x >= y`, they need not say which of the two)
  else if op == "<" then do let t ← isBelow s.facts x y; pure (.val (.bool t), s)
  else if op == "<=" then do let t ← isBelow s.facts y x; pure (.val (.bool (!t)), s)
  else if op == ">" then do let t ← isBelow s.facts y x; pure (.val (.bool t), s)
  else if op == ">=" then do let t ← isBelow s.facts x y; pure (.val (.bool (!t)), s)
  else refuse s!"no rule for {op}"

/-- The remainder of `x` by a number of the specification above zero (`Sym.quotRem`: the one the code
has found, where it has found it). -/
def smod (s : Sym) (x y : Row) : V (SRes × Sym) :=
  match Lin.isConst y with
  | some m =>
    if 0 < m then pure (.val (.lin (s.quotRem x m).2.1), (s.quotRem x m).2.2)
    else refuse "a remainder by a number that is not above zero"
  | none => refuse "a remainder by what is no number of the specification: not here yet"

/-- The quotient of `x` by a number of the specification above zero (`Sym.quotRem`). -/
def sdiv (s : Sym) (x y : Row) : V (SRes × Sym) :=
  match Lin.isConst y with
  | some m =>
    if 0 < m then pure (.val (.lin (s.quotRem x m).1), (s.quotRem x m).2.2)
    else refuse "a quotient by a number that is not above zero"
  | none => refuse "a quotient by what is no number of the specification: not here yet"

def insert (c : SCall) (l : List SCall) : List SCall := if l.contains c then l else l ++ [c]

def reachStep (seen : List SCall) : SFact → List SCall
  | .same a b => if seen.contains a then insert b seen else if seen.contains b then insert a seen else seen
  | .value .. => seen
  | .neq _ => seen

/-- The uses that the facts say are the same as one of `seen`. -/
def reach (facts : List SFact) : Nat → List SCall → List SCall
  | 0, seen => seen
  | fuel + 1, seen => reach facts fuel (facts.foldl reachStep seen)

/-- The value of a use of a definition, where the verifier holds one. -/
def knownValue : List SFact → SCall → Option Row
  | [], _ => none
  | .value c' v :: more, c => if c' == c then some v else knownValue more c
  | .same _ _ :: more, c => knownValue more c
  | .neq _ :: more, c => knownValue more c

/-- The values held, each with the use it is of. -/
def heldValues : List SFact → List (SCall × Row)
  | [] => []
  | .value c v :: more => (c, v) :: heldValues more
  | .same _ _ :: more => heldValues more
  | .neq _ :: more => heldValues more

/-- The things two uses of a definition are used with are the same: the same run of bytes, the same truth,
or numbers shown equal. -/
def sameArgs (facts : List Row) : List SVal → List SVal → V Unit
  | [], [] => pure ()
  | .lin a :: as, .lin b :: bs => do
    entailAs "same" facts (Lin.sub a b)
    entailAs "same" facts (Lin.sub b a)
    sameArgs facts as bs
  | a :: as, b :: bs => if a = b then sameArgs facts as bs else refuse "two uses of a definition with other things"
  | _, _ => refuse "two uses of a definition with other things"

/-- Two uses have the same value: the facts held say so, or they are of one definition with the same things. -/
def sameUse (s : Sym) (c c' : SCall) : V Unit :=
  if (reach s.spec (s.spec.length + 1) [c]).contains c' then pure ()
  else if c'.f == c.f then sameArgs s.facts c.args c'.args
  else refuse "the value held is of another use"

/-- The value of a use of a definition, where a number is needed: the one held for it; or, where the proof
says which (`held K`), the K-th value held, shown to be of a use with the same value; or, where the proof
says to open it (`open`), the value its definition then gives it (`deeper` opens it). -/
def heldFor (deeper : Sym → SCall → V Sym) (s : Sym) (c : SCall) : V (Row × Sym) :=
  match knownValue s.spec c with
  | some v => pure (v, s)
  | none => do
    match ← pop with
    | some (.tag name k) =>
      if name == "held" then
        match (heldValues s.spec)[k]? with
        | some (c', v) => do
          sameUse s c c'
          pure (v, s)
        | none => refuse "no such value is held"
      else if name == "open" then do
        let s' ← deeper s c
        match knownValue s'.spec c with
        | some v => pure (v, s')
        | none => refuse "a use of a definition opened where a number is needed, and its value is still no number"
      else refuse "a number is expected (or a use of a definition whose value is held)"
    | some _ => refuse "a number is expected (or a use of a definition whose value is held)"
    | none => fun _ => .error s!"need held\nc {(heldValues s.spec).length}\n"

/-- A result where a number is needed: a number, or a use of a definition whose value is held or found. -/
def numberV (deeper : Sym → SCall → V Sym) (s : Sym) : SRes → V (Row × Sym)
  | .val (.lin x) => pure (x, s)
  | .tail c => heldFor deeper s c
  | _ => refuse "a number is expected (or a use of a definition whose value is held)"

/-- A result as one of the things a definition is used with: a value, or a use whose value is held or found. -/
def argumentV (deeper : Sym → SCall → V Sym) (s : Sym) : SRes → V (SVal × Sym)
  | .val v => pure (v, s)
  | .tail c => do
    let (v, s) ← heldFor deeper s c
    pure (.lin v, s)
  | .list _ => refuse "a use of a definition inside another, whose value is not held"

def scall (ctx : Ctx) (f : String) (vs : List SVal) (s : Sym) : V (SRes × Sym) :=
  if f == "len" then
    match vs with
    | [.region r] =>
      match ctx.contract.regions[r]? with
      | some (_, len) => pure (.val (.lin (Lin.var len)), s)
      | none => refuse "no such run of bytes"
    | _ => refuse "the length of what is no run of bytes"
  else if own.contains f then refuse s!"{f}, of the language's own: not here yet"
  else match findDef ctx.defs f with
    | some d => if d.params.length == vs.length then pure (.tail ⟨f, vs⟩, s) else refuse s!"{f} takes another number of things"
    | none => refuse s!"no definition {f}"

/-- An expression of the specification, on symbols. `deeper`: how a use of a definition whose value is
needed and not held is opened. -/
def sevalWith (ctx : Ctx) (deeper : Sym → SCall → V Sym) (env : List (String × SVal)) : Sym → SExpr → V (SRes × Sym)
  | s, .num n => if n < 0 then refuse "a number below zero" else pure (.val (.lin (Lin.const n)), s)
  | s, .name x =>
    match env.lookup x with
    | some v => pure (.val v, s)
    | none => refuse s!"the name {x} stands for nothing here"
  | s, .bin op a b => do
    let (x, s) ← sevalWith ctx deeper env s a
    let (y, s) ← sevalWith ctx deeper env s b
    let (x, s) ← numberV deeper s x
    let (y, s) ← numberV deeper s y
    if op == "%" then smod s x y else if op == "/" then sdiv s x y else sbin op s x y
  | s, .ifx c a b => do
    let (c, s) ← sevalWith ctx deeper env s c
    match c with
    | .val (.bool t) => do
      let (r, s) ← if t then sevalWith ctx deeper env s a else sevalWith ctx deeper env s b
      match r with
      | .list _ => refuse "a list of things where a value is expected"
      | _ => pure (r, s)
    | _ => refuse "a condition that is not true or false"
  | s, .index a i => do
    let (a, s) ← sevalWith ctx deeper env s a
    let (i, s) ← sevalWith ctx deeper env s i
    match a, i with
    | .val (.region r), .val (.lin o) => do
      let (v, s) ← readByte ctx s r o
      pure (.val (.lin v), s)
    | _, _ => refuse "a byte of what is no run of bytes"
  | s, .call f args => do
    let (vs, s) ← sevalWith ctx deeper env s args
    match vs with
    | .list vs => scall ctx f vs s
    | _ => refuse "a definition used with what is no list of things"
  | _, .list _ => refuse "a list written out where a number or a use of a definition is expected"
  | s, .nil => pure (.list [], s)
  | s, .cons a rest => do
    let (v, s) ← sevalWith ctx deeper env s a
    let (vs, s) ← sevalWith ctx deeper env s rest
    let (v, s) ← argumentV deeper s v
    match vs with
    | .list vs => pure (.list (v :: vs), s)
    | _ => refuse "what a definition is used with is no list of things"
  | _, .letx _ _ _ => refuse "a `let`: not here yet"
  | _, .each _ _ _ _ => refuse "a list made thing by thing: not here yet"
  | _, .slice _ _ _ => refuse "a part of a list: not here yet"
  | _, .withx _ _ => refuse "a list with places replaced: not here yet"
  | _, .record _ _ => refuse "a record: not here yet"
  | _, .field _ _ => refuse "a field of a record: not here yet"
  | _, .theNumber _ _ _ _ _ => refuse "`the least number`: not here yet"
  | _, .thePower _ _ _ => refuse "`the greatest power of two`: not here yet"

/-- A use of a definition, opened once: a fact of what it is the same as, or of its value. -/
def openCallWith (ctx : Ctx) (deeper : Sym → SCall → V Sym) (s : Sym) (c : SCall) : V Sym :=
  match findDef ctx.defs c.f with
  | none => refuse s!"no definition {c.f}"
  | some d =>
    if d.params.length != c.args.length then refuse s!"{c.f} takes another number of things" else do
      let (res, s) ← sevalWith ctx deeper (d.params.zip c.args) s d.body
      match res with
      | .tail c' => pure { s with spec := .same c c' :: s.spec }
      | .val (.lin v) => pure { s with spec := .value c v :: s.spec }
      | _ => refuse "a definition whose value is no number: not here yet"

/-- Opening a use of a definition, the uses met inside it opened in turn where the proof says so, to so
many deep. -/
def opener (ctx : Ctx) : Nat → Sym → SCall → V Sym
  | 0 => fun _ _ => refuse "definitions opened one inside another, too many deep"
  | n + 1 => openCallWith ctx (opener ctx n)

def DEEP : Nat := 8

def seval (ctx : Ctx) (env : List (String × SVal)) (s : Sym) (e : SExpr) : V (SRes × Sym) :=
  sevalWith ctx (opener ctx DEEP) env s e

def openCall (ctx : Ctx) (s : Sym) (c : SCall) : V Sym := openCallWith ctx (opener ctx DEEP) s c

def holdsSpec (facts : List SFact) : SFact → Bool
  | .same a b => (reach facts (facts.length + 1) [a]).contains b
  | .value c v => (reach facts (facts.length + 1) [c]).any fun c' => facts.contains (.value c' v)
  | .neq _ => false

def callsIn : SFact → List SCall
  | .same a b => [a, b]
  | .value c _ => [c]
  | .neq _ => []

def callsOf (facts : List SFact) (goal : SFact) : List SCall :=
  ((facts.reverse ++ [goal]).map callsIn).flatten.foldl (fun l c => insert c l) []

/-- A fact of a value, from the K-th value held: that one is of a use with the same value, and the two
values are shown equal. -/
def carry (s : Sym) (goal : SFact) (k : Nat) : V Unit :=
  match goal, (heldValues s.spec)[k]? with
  | .value c v, some (c', v') => do
    sameUse s c c'
    entail s.facts (Lin.sub v v')
    entail s.facts (Lin.sub v' v)
  | _, _ => refuse "no such value is held, or the fact is not of a value"

/-- A fact of the specification, from the facts held, uses of definitions the proof says to open (`open K`),
and values held that the proof says to carry over (`carry K`). -/
def specGoal (ctx : Ctx) : Nat → Sym → SFact → V Sym
  | 0, _, _ => refuse "too many definitions opened for one fact"
  | fuel + 1, s, goal =>
    if holdsSpec s.spec goal then pure s else do
      match ← pop with
      | some (.tag name n) =>
        if name == "open" then
          match (callsOf s.spec goal)[n]? with
          | some c => do
            let s ← openCall ctx s c
            specGoal ctx fuel s goal
          | none => refuse "no such use of a definition to open"
        else if name == "carry" then do
          carry s goal n
          pure s
        else refuse "open or carry is expected"
      | some _ => refuse "open or carry is expected"
      | none => fun _ => .error s!"need spec\nc {(callsOf s.spec goal).length}\no {15 - fuel}\nh {(heldValues s.spec).length}\n"

/-- What a line `fact …` of a place says: rows, and facts of the specification. -/
def assertion (ctx : Ctx) (env : List (String × SVal)) (s : Sym) : SExpr → V (List Row × List SFact × Sym)
  | .bin op a b => do
    let (x, s) ← seval ctx env s a
    let (y, s) ← seval ctx env s b
    match x, y with
    | .val (.lin x), .val (.lin y) =>
      if op == "==" then pure ([Lin.sub x y, Lin.sub y x], [], s)
      else if op == "<=" then pure ([Lin.sub y x], [], s)
      else if op == "<" then pure ([Lin.sub (Lin.sub y x) (Lin.const 1)], [], s)
      else if op == ">=" then pure ([Lin.sub x y], [], s)
      else if op == ">" then pure ([Lin.sub (Lin.sub x y) (Lin.const 1)], [], s)
      else refuse s!"a fact with {op}: not here yet"
    | .tail c, .tail c' => if op == "==" then pure ([], [.same c c'], s) else refuse "two uses of definitions can only be said to be equal"
    | .tail c, .val (.lin v) => if op == "==" then pure ([], [.value c v], s) else refuse "a use of a definition can only be said to be equal to a number"
    | .val (.lin v), .tail c => if op == "==" then pure ([], [.value c v], s) else refuse "a use of a definition can only be said to be equal to a number"
    | _, _ => refuse "a fact about what is no number"
  | _ => refuse "a fact that is no comparison"

/-- Show what the assertion says, of the state `s`. -/
def establish (ctx : Ctx) (env : List (String × SVal)) (s : Sym) (e : SExpr) : V Sym := do
  let (rows, facts, s) ← assertion ctx env s e
  each (entail s.facts) rows
  fold (specGoal ctx 16) s facts

/-- Take what the assertion says as known, of the state `s`. -/
def suppose (ctx : Ctx) (env : List (String × SVal)) (s : Sym) (e : SExpr) : V Sym := do
  let (rows, facts, s) ← assertion ctx env s e
  pure { s with facts := rows ++ s.facts, spec := facts ++ s.spec }

/-! ## A list of the specification, on symbols -/

/-- The things of a list written out: numbers, each shown to be no less than zero. -/
def numbers (facts : List Row) : List SVal → V (List Row)
  | [] => pure []
  | .lin v :: more => do
    entail facts v
    let rest ← numbers facts more
    pure (v :: rest)
  | _ => refuse "a list written out of what are no numbers"

/-- The list an expression is, thing by thing: a list written out; two lists joined; one of two lists, by
a condition; a use of a definition, which is opened. `fuel`: how deep this goes at most. -/
def slist (ctx : Ctx) : Nat → List (String × SVal) → Sym → SExpr → V (List Row × Sym)
  | 0, _, _, _ => refuse "a list defined deeper than this verifier follows"
  | _ + 1, env, s, .list items => do
    let (vs, s) ← seval ctx env s items
    match vs with
    | .list vs => do
      let rows ← numbers s.facts vs
      pure (rows, s)
    | _ => refuse "a list written out of what is no list of things"
  | fuel + 1, env, s, .bin op a b =>
    if op == "++" then do
      let (x, s) ← slist ctx fuel env s a
      let (y, s) ← slist ctx fuel env s b
      pure (x ++ y, s)
    else refuse "a list is expected"
  | fuel + 1, env, s, .ifx c a b => do
    let (c, s) ← seval ctx env s c
    match c with
    | .val (.bool t) => if t then slist ctx fuel env s a else slist ctx fuel env s b
    | _ => refuse "a condition that is not true or false"
  | fuel + 1, env, s, .call f args => do
    let (vs, s) ← seval ctx env s args
    match vs with
    | .list vs =>
      if f == "len" then refuse "a list is expected"
      else if own.contains f then refuse s!"{f}, of the language's own: not here yet"
      else match findDef ctx.defs f with
        | some d =>
          if d.params.length == vs.length then slist ctx fuel (d.params.zip vs) s d.body
          else refuse s!"{f} takes another number of things"
        | none => refuse s!"no definition {f}"
    | _ => refuse "a definition used with what is no list of things"
  | _, _, _, _ => refuse "a list is expected"

def LIST : Nat := 100

/-! ## Return, places, paths -/

/-- The contract's names at the return: those at entry, and the name `returns` gives the number returned. -/
def symEnvAfter (c : Contract) (s : Sym) : List (String × SVal) :=
  match c.result with
  | some name => (name, .lin (s.reg c.retReg)) :: symEnv c
  | none => symEnv c

/-- The run given to write of that name: which it is, and how many bytes. -/
def findOutNamed (name : String) : List (String × Nat × Nat) → Nat → Option (Nat × Nat)
  | [], _ => none
  | (x, _, n) :: more, k => if x == name then some (k, n) else findOutNamed name more (k + 1)

/-- The byte known written at that place of the run `w`. -/
def wroteAt (w : Nat) (place : Row) : List (Nat × Row × Row) → Option Row
  | [] => none
  | (w', o, x) :: more => if w' = w ∧ Lin.isConst (Lin.sub o place) = some 0 then some x else wroteAt w place more

/-- The things of a list are what is known written at the places from `lo + k` on of the run `w`. -/
def written (facts : List Row) (wrote : List (Nat × Row × Row)) (w : Nat) (lo : Row) : Nat → List Row → V Unit
  | _, [] => pure ()
  | k, v :: more =>
    match wroteAt w (Lin.add lo (Lin.const (k : Int))) wrote with
    | some x => do
      entail facts (Lin.sub x v)
      entail facts (Lin.sub v x)
      written facts wrote w lo (k + 1) more
    | none => refuse "an `ensures`: a byte of the run is not known written"

/-- The definition `f`, where it is a list made thing by thing from 0 on, used with `n` things: its
names, the name of the place, what the thing at a place is, and how many things there are. -/
def eachOf (ctx : Ctx) (f : String) (n : Nat) : Option (List String × String × SExpr × Nat) :=
  if f == "len" || own.contains f then none
  else match findDef ctx.defs f with
    | some d =>
      match d.body with
      | .each b x (.num 0) (.num hi) => if d.params.length == n && decide (0 ≤ hi) then some (d.params, x, b, hi.toNat) else none
      | _ => none
    | none => none

/-- The places `lo + k`, `lo + k + 1`, … (`count` of them) of the run `w` are known written, each with the
thing the list has there: `b` with the name `x` standing for the place. -/
def filled (ctx : Ctx) (env : List (String × SVal)) (x : String) (b : SExpr) (w : Nat) (lo : Row) : Nat → Nat → Sym → V Sym
  | _, 0, s => pure s
  | k, count + 1, s => do
    let here := Lin.add lo (Lin.const (k : Int))
    match wroteAt w here s.wrote with
    | none => refuse "a place: a byte of the run is not known written"
    | some byte => do
      let (v, s) ← seval ctx ((x, .lin here) :: env) s b
      match v with
      | .val (.lin v) => do
        entail s.facts (Lin.sub v byte)
        entail s.facts (Lin.sub byte v)
        filled ctx env x b w lo (k + 1) count s
      | _ => refuse "a place: a thing of the list is no number"

/-- `ensures RUN[lo .. hi] = f(args)` by what a place has said is written of the run: the same list, from
place 0 on, to its end. -/
def symEnsureRange (ctx : Ctx) (env : List (String × SVal)) (s : Sym) (e : Ensure) (w : Nat) (rg : RangeF) (args : SExpr) : V Sym := do
  let (vs, s) ← seval ctx env s args
  match vs with
  | .list vs =>
    if vs != rg.args then refuse "an `ensures`: the list is of other things than the place said"
    else match eachOf ctx rg.f vs.length with
      | none => refuse "an `ensures`: no list made thing by thing"
      | some (_, _, _, hi) => do
        let (lo, s) ← seval ctx env s e.lo
        let (lo, s) ← numberV (opener ctx DEEP) s lo
        let (top, s) ← seval ctx env s e.hi
        let (top, s) ← numberV (opener ctx DEEP) s top
        entail s.facts lo
        entail s.facts (Lin.scale (-1) lo)
        entail s.facts (Lin.sub top (Lin.const hi))
        entail s.facts (Lin.sub (Lin.const hi) top)
        entail s.facts (if rg.fromStart then Lin.sub rg.lo (Lin.const hi) else Lin.scale (-1) rg.lo)
        if w != rg.w then refuse "an `ensures`: another run than the place said" else pure s
  | _ => refuse "an `ensures`: a definition used with what is no list of things"

/-- The list an `ensures` speaks of is the use of the definition of which a place has said what is written:
what the place said, and the things the definition is used with here. -/
def rangeFor (s : Sym) : SExpr → Option (RangeF × SExpr)
  | .call f args =>
    match s.range with
    | some rg => if rg.f == f then some (rg, args) else none
    | none => none
  | _ => none

/-- One `ensures RUN[lo .. hi] = LIST`, at the return: the list thing by thing, `lo` no less than zero,
`hi - lo` as many as the list's things, `hi` within the run, and each of the places known written with
the list's thing. -/
def symEnsure (ctx : Ctx) (env : List (String × SVal)) (s : Sym) (e : Ensure) : V Sym :=
  match findOutNamed e.run ctx.contract.outs 0 with
  | none => refuse "an `ensures` of what is no run given to write"
  | some (w, n) =>
    match rangeFor s e.value with
    | some (rg, args) => symEnsureRange ctx env s e w rg args
    | none => do
    let (rows, s) ← slist ctx LIST env s e.value
    let (lo, s) ← seval ctx env s e.lo
    let (lo, s) ← numberV (opener ctx DEEP) s lo
    let (hi, s) ← seval ctx env s e.hi
    let (hi, s) ← numberV (opener ctx DEEP) s hi
    entail s.facts lo
    entail s.facts (Lin.sub (Lin.sub hi lo) (Lin.const (rows.length : Int)))
    entail s.facts (Lin.sub (Lin.add lo (Lin.const (rows.length : Int))) hi)
    entail s.facts (Lin.sub (Lin.const (n : Int)) hi)
    written s.facts s.wrote w lo 0 rows
    pure s

/-! ## The specification, on words

What an `ensures` of a whole run of words says is worked out on the terms of the table, and only looked up
there: the function has made every term the specification's words are, or the function is refused. So
nothing is added to the state here, and no line of the proof is read. -/

/-- A value of the specification where a word is terms. -/
inductive WVal where
  | int (n : Int)                 -- a number the specification's text gives
  | bool (b : Bool)
  | num (r : Row)                 -- a number the verifier holds as a row
  | word (xs : List (Nat × Nat)) -- a word: linear combination of terms, wrapping (`[(a, 1)]`: that term)
  | counter (r : Row)             -- the counter of a number that is no less than zero
  | list (l : List WVal)
  | run (r n : Nat)               -- the `n` bytes at the address register `r` held at entry, as they were at entry
  | part (r off n : Nat)          -- `n` of those bytes, from place `off` on
  | pbyte (r off : Nat)           -- one byte of run `r`, at byte offset `off`, as it was at entry
  | region (r l : Nat)            -- the bytes at the address register `r` held at entry, as many as register `l` held then, as they were at entry
  | span (r : Nat) (off len : Row)    -- `len` of the bytes at the address register `r` held at entry, from place `off` on, as they were at entry (place and length are rows)
  | wbytes (ids : List Nat)       -- the bytes of the words of these terms, four a word, the lowest first
  | record (fields : List (String × WVal))    -- a record: its names, each with its thing
  | lanes (j count l : Nat)       -- the table of addresses that the fixed run `j` is: its `count` lanes
  | lane (j c l : Nat)            -- the blocks that the address at place `c` of that table points to (as many as register `l` held at entry)
  | use (h : Nat)                 -- what the use of a definition that has the number `h` gives
  | other                         -- a thing that is not followed here
  deriving Inhabited

/-- The term a word is: the one term, or the sum, which must be in the table. (`look`: where a term is in
the table, if it is there. Here and below the table is only looked up in, through this.) -/
def idOf (look : Node → Option Nat) : List (Nat × Nat) → Option Nat
  | [(a, 1)] => some a
  | xs => look (.add xs)

/-- A row with the remainder by `m` of its number of the table in that number's place: the row is this and
a multiple of `m`. -/
def Lin.rest (x : Row) (m : Int) : Row := ⟨x.coeff, x.constant % m⟩

/-- A row seen at once to lie from 0 to `m - 1`. -/
def within (facts : List Row) (y : Row) (m : Int) : Bool := plain facts y && plain facts (Lin.sub (Lin.const (m - 1)) y)

/-- The remainder by a number above zero, where it is known without a new unknown (as `symLow` has it). -/
def lowOf (s : Sym) (x : Row) (m : Int) : Option Row :=
  if x.coeff.all (fun c => c % m == 0) then some (Lin.const (x.constant % m))
  else if knownNonneg s x && plain s.facts (Lin.sub (Lin.const (m - 1)) x) then some x     -- (a number seen at once to be below the divisor is its own remainder)
  else
    match divided s x m with
    | some q => some (Lin.var (q + 1))
    | none =>
      -- a multiple of the divisor and a number seen at once to lie from 0 to below the divisor: that number
      if within s.facts (Lin.rest x m) m then some (Lin.rest x m) else none

/-- The quotient by a number above zero, where it is known without a new unknown: the unknown the state
knows as that quotient; or, of a multiple of the divisor and a number seen at once to lie from 0 to below
the divisor, the multiple's quotient. -/
def quotOf (s : Sym) (x : Row) (m : Int) : Option Row :=
  match divided s x m with
  | some q => some (Lin.var q)
  | none => if within s.facts (Lin.rest x m) m then some (Lin.const (x.constant / m)) else none

/-- The bits of a number seen at once to lie below 2^j (j: 8, 16 or 32) and of a number `k` of the table that
is 2^j or more, put together, where that is known without a new unknown (as `symOrSmall` makes it): `k`'s
bits from bit j on, added to the first number (where `k` has no lower bit) or to the unknown the state
knows as the first number's bits and `k`'s lower bits put together. -/
def orSmall (s : Sym) (x : Row) (k : Int) : Option Row :=
  match smallBits s.facts x with
  | some j =>
    if (2 : Int) ^ j ≤ k then
      if k % 2 ^ j = 0 then some (Lin.add x (Lin.const k))
      else
        match knownOr x (Lin.const (k % 2 ^ j)) s.known with
        | some v => some (Lin.add (Lin.var v) (Lin.const (k - k % 2 ^ j)))
        | none => none
    else none
  | none => none

/-- The quotient by 2^32, where it is known without a new unknown (as the halves of a register are found). -/
def highOf (s : Sym) (r : Row) : Option Row :=
  if Lin.high r == Lin.const 0 && (Lin.isConst r).isNone then (divided s r W32i).map Lin.var
  else if (Lin.isConst (Lin.word r)).isSome then some (Lin.high r)
  else (divided s r W32i).map Lin.var

/-- Seen at once, a fact being taken more than once: a number not below zero; or so many times a fact (no
fewer than none) and such a number. -/
def plainTimes (facts : List Row) (g : Row) : Bool :=
  plain facts g ||
    -- (the number's own last multiple is looked for once, and no fact is gone through where it has none)
    match g.coeff.getLast? with
    | none => false
    | some b => facts.any fun f =>
      match f.coeff.getLast? with
      | some a =>
        a != 0 && b % a == 0 && decide (0 ≤ b / a) &&
          (match Lin.lessTimes g (b / a) f with
           | some k => decide (0 ≤ k)
           | none => false)
      | none => false

/-- Two rows are one number: the same row, or each seen at once to be no less than the other. -/
def sameRow (facts : List Row) (a b : Row) : Bool := Lin.same a b || (plainTimes facts (Lin.sub a b) && plainTimes facts (Lin.sub b a))

/-- Two numbers held as rows: their sum; their difference, where it is seen at once to be no less than zero;
whether they are equal, where the facts say at once that they are, or that one is the greater; whether
the first is below the second (`<`), or no less than it (`>=`), where one of the two answers is seen at once. -/
def wnum (s : Sym) (op : String) (x y : Row) : Option WVal :=
  if op == "+" then some (.num (Lin.add x y))
  else if op == "-" then (if plain s.facts (Lin.sub x y) then some (.num (Lin.sub x y)) else none)
  else if op == "==" then
    if sameRow s.facts x y then some (.bool true)
    else if plain s.facts (Lin.sub (Lin.sub x y) (Lin.const 1)) || plain s.facts (Lin.sub (Lin.sub y x) (Lin.const 1)) then some (.bool false)
    else none
  else if op == "<" then
    if plain s.facts (Lin.sub (Lin.sub y x) (Lin.const 1)) then some (.bool true)
    else if plain s.facts (Lin.sub x y) then some (.bool false)
    else none
  else if op == ">=" then
    if plain s.facts (Lin.sub x y) then some (.bool true)
    else if plain s.facts (Lin.sub (Lin.sub y x) (Lin.const 1)) then some (.bool false)
    else none
  else if op == "<=" then
    if plain s.facts (Lin.sub y x) then some (.bool true)
    else if plain s.facts (Lin.sub (Lin.sub x y) (Lin.const 1)) then some (.bool false)
    else none
  else if op == ">" then
    if plain s.facts (Lin.sub (Lin.sub x y) (Lin.const 1)) then some (.bool true)
    else if plain s.facts (Lin.sub y x) then some (.bool false)
    else none
  else none

def wbin (look : Node → Option Nat) (s : Sym) (op : String) : WVal → WVal → Option WVal
  | .int a, .int b =>
    match binop op (.int a) (.int b) with
    | some (.int n) => some (.int n)
    | some (.bool c) => some (.bool c)
    | _ => none
  | .word xs, .word ys =>
    if op == "+" then some (.word (mergeAdd xs ys))
    else if op == "^" then
      match idOf look xs, idOf look ys with
      | some a, some b => (look (.xor (min a b) (max a b))).map fun i => .word [(i, 1)]
      | _, _ => none
    else if op == "&" then
      match idOf look xs, idOf look ys with
      | some a, some b => (look (.band (min a b) (max a b))).map fun i => .word [(i, 1)]
      | _, _ => none
    else none
  | .word xs, .int n =>
    if op == ">>>" ∧ 0 ≤ n ∧ n ≤ 32 then
      match idOf look xs with
      | some a => (look (.rotr a n.toNat)).map fun i => .word [(i, 1)]
      | none => none
    else if op == ">>" ∧ 0 ≤ n ∧ n < 32 then
      match idOf look xs with
      | some a => (look (.shr a n.toNat)).map fun i => .word [(i, 1)]
      | none => none
    else none
  | .num r, .int m =>
    if op == "*" ∧ 0 ≤ m then some (.num (Lin.scale m r))
    else if op == "%" then (if 0 < m then (lowOf s r m).map .num else none)
    else if op == "/" then (if 0 < m then (quotOf s r m).map .num else none)   -- (the quotient the state knows of)
    else if op == "|" then
      (if m = 0 ∧ knownNonneg s r = true then some (.num r)          -- (no bit is added)
       else
         match knownOr r (Lin.const m) s.known with
         | some v => some (.num (Lin.var v))
         | none => (orSmall s r m).map .num)
    else wnum s op r (Lin.const m)
  | .int m, .num r =>
    if op == "*" ∧ 0 ≤ m then some (.num (Lin.scale m r))
    else if op == "|" then (if m = 0 ∧ knownNonneg s r = true then some (.num r) else none)
    else wnum s op (Lin.const m) r
  | .num x, .num y =>
    if op == "|" then (knownOr x y s.known).map fun v => .num (Lin.var v)    -- (the unknown the state knows as both numbers' bits)
    else wnum s op x y
  | .counter r, .int n =>
    -- a number of the text added to a counter (it wraps at 2^64, as the account has it)
    if op == "+" ∧ 0 ≤ n then some (.counter (if n = 0 then r else Lin.add r (Lin.const n))) else none
  | .list a, .list b => if op == "++" then some (.list (a ++ b)) else none
  | _, _ => none

/-- The high word of a counter that is a number and a number of the text more (`t + 5`), as code works it
out from the two words of the first number: the low words summed wrap exactly where the sum comes out below
the low word it was made from, and there the high word is one more. So it is the high word of the first
number, or that and one, by whether the one low word is below the other. Every term must be in the table. -/
def hiPlus (look : Node → Option Nat) (s : Sym) (r : Row) : Option Nat :=
  if 0 < r.constant ∧ r.constant < W32i ∧ knownNonneg s ⟨r.coeff, 0⟩ = true then
    match look (.atom (Lin.word r)), look (.atom (Lin.word ⟨r.coeff, 0⟩)),
          (highOf s ⟨r.coeff, 0⟩).bind (fun q => look (.atom (Lin.word q))), look (.atom (Lin.word (Lin.const 1))) with
    | some a, some l, some h, some one =>
      (look (.ult a l)).bind fun m => (look (.add (mergeAdd [(h, 1)] [(one, 1)]))).bind fun h1 => look (.sel m h1 h)
    | _, _, _, _ => none
  else none

/-- The words of a run, from word `k` on, `count` of them: each must be in the table. -/
def inputWords (look : Node → Option Nat) (j : Nat) : Nat → Nat → Option (List WVal)
  | 0, _ => some []
  | count + 1, k =>
    match look (.input j k), inputWords look j count (k + 1) with
    | some i, some rest => some (.word [(i, 1)] :: rest)
    | _, _ => none

/-- Whether a list of `WVal` is the consecutive bytes `off, off+1, ...` of run `r`. -/
def pbytesSpan (r off : Nat) : List WVal → Bool
  | [] => true
  | .pbyte r' off' :: more => decide (r' = r ∧ off' = off) && pbytesSpan r (off + 1) more
  | _ => false

/-- The language's own names (`builtin` of the account), on words. -/
def wown (ctx : Ctx) (look : Node → Option Nat) (s : Sym) (f : String) : List WVal → Option WVal
  | [.int n] =>
    if f == "word" then (if 0 ≤ n then (look (.atom (Lin.word (Lin.const n)))).map fun i => .word [(i, 1)] else none)
    else if f == "counter" then (if 0 ≤ n then some (.counter (Lin.const n)) else none)
    else none
  | [.num r] =>
    if !plain s.facts r then none
    else if f == "word" then (look (.atom (Lin.word r))).map fun i => .word [(i, 1)]
    else if f == "counter" then some (.counter r)
    else none
  | [.word xs] => if f == "word" then some (.word xs) else none
  | [.counter r] =>
    if f == "counter" then some (.counter r)
    else if f == "lo" then (look (.atom (Lin.word r))).map fun i => .word [(i, 1)]
    else if f == "hi" then
      match (highOf s r).bind fun q => (look (.atom (Lin.word q))).map fun i => WVal.word [(i, 1)] with
      | some v => some v
      | none => (hiPlus look s r).map fun i => .word [(i, 1)]
    else none
  | [.run r n] =>
    if f == "words" ∧ n % 4 = 0 then
      (runAt r ctx.contract.wordRuns 0).bind fun j => (inputWords look j (n / 4) 0).map .list
    else none
  | [.part r off n] =>
    -- a part of a run that begins and ends at whole words: those words; eight bytes of a run only read: the
    -- unknown the state knows as that number
    if f == "words" ∧ off % 4 = 0 ∧ n % 4 = 0 then
      (runAt r ctx.contract.wordRuns 0).bind fun j => (inputWords look j (n / 4) (off / 4)).map .list
    else if f == "number.le" ∧ n = 8 then
      (runAt r ctx.contract.fixeds 0).bind fun j => (knownLoad j off s.known).map fun v => .num (Lin.var v)
    else none
  | [.wbytes ids] =>
    if f == "words" then some (.list (ids.map fun i => WVal.word [(i, 1)]))
    else if f == "number.le" then
      match ids with
      | [a, b] =>
        match s.tab.arr[a]?, s.tab.arr[b]? with
        | some (.atom r1), some (.atom r2) =>
          if knownNonneg s r1 && plain s.facts (Lin.sub (Lin.const (W32i - 1)) r1) &&
             knownNonneg s r2 && plain s.facts (Lin.sub (Lin.const (W32i - 1)) r2) then
            some (.num (Lin.add r1 (Lin.scale W32i r2)))
          else none
        | _, _ => none
      | _ => none
    else none
  | [.list (.pbyte r off :: more)] =>
    let n := more.length + 1
    if f == "words" ∧ off % 4 = 0 ∧ n % 4 = 0 ∧ pbytesSpan r off (.pbyte r off :: more) = true then
      (runAt r ctx.contract.wordRuns 0).bind fun j => (inputWords look j (n / 4) (off / 4)).map .list
    else none
  | _ => none

def wevalList (ev : SExpr → Option WVal) : SExpr → Option (List WVal)
  | .nil => some []
  | .cons a rest =>
    match ev a, wevalList ev rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none
  | _ => none

def wevalEach (ev : Int → Option WVal) : Nat → Int → Option (List WVal)
  | 0, _ => some []
  | count + 1, i =>
    match ev i, wevalEach ev count (i + 1) with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- The first of the numbers of which `ev` says true, every one before it being one of which it says false
(as `firstWith` of the account). -/
def wfirstWith (ev : Int → Option WVal) : List Int → Option WVal
  | [] => none
  | n :: rest =>
    match ev n with
    | some (.bool true) => some (.int n)
    | some (.bool false) => wfirstWith ev rest
    | _ => none

def wputAll : List WVal → List WVal → Option (List WVal)
  | l, [] => some l
  | l, .int i :: x :: rest => if 0 ≤ i ∧ i.toNat < l.length then wputAll (l.set i.toNat x) rest else none
  | _, _ => none

/-- The terms of a list of words (a sum must be in the table). -/
def wordIds (look : Node → Option Nat) : List WVal → Option (List Nat)
  | [] => some []
  | .word xs :: rest =>
    match idOf look xs, wordIds look rest with
    | some i, some is => some (i :: is)
    | _, _ => none
  | _ => none

/-- A thing a definition is used with, as a key: a number, a counter, or a list of words by their terms.
(Two things of one key are one value.) -/
def flatKey (look : Node → Option Nat) : WVal → Option Key
  | .int n => some (.num (Lin.const n))
  | .num r => some (.num r)
  | .counter r => some (.counter r)
  | .list l => (wordIds look l).map .words
  | .lane j c l => some (.lane j c l)
  | .use h => some (.use h)
  | .span r off len => some (.span r off len)
  | .region r l => some (.span r (Lin.const 0) (Lin.var l))      -- (a whole run of bytes is the part of it from 0 on, as long as it is)
  | .part r off n => some (.span r (Lin.const off) (Lin.const n))
  | _ => none

def flatKeys (look : Node → Option Nat) : List WVal → Option (List Key)
  | [] => some []
  | v :: rest =>
    match flatKey look v, flatKeys look rest with
    | some k, some ks => some (k :: ks)
    | _, _ => none

/-- A key speaks only of unknowns in use (`n` of them) and of terms of the table (`t` of them). -/
def Key.ok (n t : Nat) : Key → Bool
  | .num r => decide (r.coeff.length ≤ n)
  | .counter r => decide (r.coeff.length ≤ n)
  | .words ids => ids.all (· < t)
  | .lane _ _ _ => true
  | .span _ off len => decide (off.coeff.length ≤ n) && decide (len.coeff.length ≤ n)
  | .use h => decide (h < n)

/-- Two keys are one thing: the same key; or two numbers, or the counters of two numbers, that the facts
say at once are one number. -/
def sameKey (facts : List Row) : Key → Key → Bool
  | .num a, .num b => sameRow facts a b
  | .counter a, .counter b => sameRow facts a b
  | .span r a l, .span r' a' l' => decide (r = r') && sameRow facts a a' && sameRow facts l l'
  | a, b => a == b

def sameKeys (facts : List Row) : List Key → List Key → Bool
  | [], [] => true
  | a :: as, b :: bs => sameKey facts a b && sameKeys facts as bs
  | _, _ => false

/-- The words the state knows the definition `f` to give of these things. -/
def heldIds (facts : List Row) (f : String) (keys : List Key) : List Known → Option (List Nat)
  | [] => none
  | .held f' keys' ids :: more => if f' = f ∧ sameKeys facts keys' keys = true then some ids else heldIds facts f keys more
  | _ :: more => heldIds facts f keys more

/-- The number of the use of the definition `f` with these things, where the state has given that use one. -/
def usedAs (facts : List Row) (f : String) (keys : List Key) : List Known → Option Nat
  | [] => none
  | .use f' keys' h :: more => if f' = f ∧ sameKeys facts keys' keys = true then some h else usedAs facts f keys more
  | _ :: more => usedAs facts f keys more

/-- The words whose bytes the state knows the definition `f` to give of these things. -/
def heldBytes (facts : List Row) (f : String) (keys : List Key) : List Known → Option (List Nat)
  | [] => none
  | .heldB f' keys' ids :: more => if f' = f ∧ sameKeys facts keys' keys = true then some ids else heldBytes facts f keys more
  | _ :: more => heldBytes facts f keys more

/-- Whether the state knows anything of a use of the definition `f`: its words, its bytes, or a number
given to it. (Asked before the three looks above, which first work out what the use is given: the
kernels' states know nothing of any definition, and their specification uses definitions in every round
of every lane's compression. Where this says no, each of the three looks would find nothing.) -/
def knowsOf (f : String) : List Known → Bool
  | [] => false
  | .held f' _ _ :: more => f' == f || knowsOf f more
  | .heldB f' _ _ :: more => f' == f || knowsOf f more
  | .use f' _ _ :: more => f' == f || knowsOf f more
  | _ :: more => knowsOf f more

def isWordIds : List WVal → List Nat → Bool
  | [], [] => true
  | .word [(i, 1)] :: ws, j :: js => i == j && isWordIds ws js
  | _, _ => false

/-- Does a reconstructed record `(names.zip vs)` match a `Known.record h fields ids` entry? -/
def recMatches (facts : List Row) (arr : Array Node) : List RecField → List Nat → List (String × WVal) → Bool
  | [], [], [] => true
  | .words fn n :: fs, ids, (x, .list ws) :: rest =>
    x == fn && decide (n ≤ ids.length) && isWordIds ws (ids.take n) &&
    recMatches facts arr fs (ids.drop n) rest
  | .bytes fn n :: fs, ids, (x, .wbytes bs) :: rest =>
    x == fn && decide (n % 4 = 0) && decide (n / 4 ≤ ids.length) &&
    bs == ids.take (n / 4) &&
    recMatches facts arr fs (ids.drop (n / 4)) rest
  | .u64 fn _ :: fs, a :: b :: more, (x, .num r) :: rest =>
    x == fn &&
    (match arr[a]?, arr[b]? with
     | some (.atom r1), some (.atom r2) =>
       plain facts r1 && plain facts (Lin.sub (Lin.const (W32i - 1)) r1) &&
       plain facts r2 && plain facts (Lin.sub (Lin.const (W32i - 1)) r2) &&
       sameRow facts r (Lin.add r1 (Lin.scale W32i r2))
     | _, _ => false) &&
    recMatches facts arr fs more rest
  | _, _, _ => false

def knownRec (facts : List Row) (arr : Array Node) (fvs : List (String × WVal)) : List Known → Option Nat
  | [] => none
  | .record h fields ids :: more => if recMatches facts arr fields ids fvs then some h else knownRec facts arr fvs more
  | _ :: more => knownRec facts arr fvs more

/-- The unknowns the state knows as the words of the block at byte `off` of the lane at place `c` of the table `j`. -/
def knownBlock (facts : List Row) (j c : Nat) (off : Row) : List Known → Option (List Nat)
  | [] => none
  | .block j' c' off' vs :: more => if j' = j ∧ c' = c ∧ sameRow facts off' off = true then some vs else knownBlock facts j c off more
  | _ :: more => knownBlock facts j c off more

/-- Each unknown as the word it is: its term must be in the table. -/
def atomWords (look : Node → Option Nat) : List Nat → Option (List WVal)
  | [] => some []
  | v :: more =>
    match look (.atom (Lin.word (Lin.var v))), atomWords look more with
    | some i, some rest => some (.word [(i, 1)] :: rest)
    | _, _ => none

/-- The block at byte `off` of a lane, where the function has read it: its sixteen words. -/
def blockAt (look : Node → Option Nat) (s : Sym) (j c : Nat) (off : Row) : Option WVal :=
  (knownBlock s.facts j c off s.known).bind fun vs => (atomWords look vs).map .list

/-- The value of an expression on words (as `evalSpec` of the account has it on numbers), where it is
followed: `none` where it is not. A use of a definition whose value the state knows (a called function's
contract has said it) has that value; any other use is worked out by the definition. -/
def weval (ctx : Ctx) (look : Node → Option Nat) (s : Sym) : Nat → List (String × WVal) → SExpr → Option WVal
  | 0, _, _ => none
  | fuel + 1, env, e =>
    match e with
    | .num n => if 0 ≤ n then some (.int n) else none
    | .name x => env.lookup x
    | .bin op a b =>
      match weval ctx look s fuel env a, weval ctx look s fuel env b with
      | some x, some y => wbin look s op x y
      | _, _ => none
    | .ifx c a b =>
      match weval ctx look s fuel env c with
      | some (.bool true) => weval ctx look s fuel env a
      | some (.bool false) => weval ctx look s fuel env b
      | _ => none
    | .index a i =>
      match weval ctx look s fuel env a, weval ctx look s fuel env i with
      | some (.list l), some (.int k) => if 0 ≤ k then l[k.toNat]? else none
      | some (.run r n), some (.int k) => if 0 ≤ k ∧ k.toNat < n then some (.pbyte r k.toNat) else none
      | some (.part r off n), some (.int k) => if 0 ≤ k ∧ k.toNat < n then some (.pbyte r (off + k.toNat)) else none
      | some (.span r off slen), some (.int k) =>
        match Lin.isConst off with
        | some c => if 0 ≤ c ∧ 0 ≤ k ∧ plain s.facts (Lin.sub slen (Lin.const (k + 1))) = true then some (.pbyte r (c.toNat + k.toNat)) else none
        | none => none
      | some (.lanes j count l), some (.int k) => if 0 ≤ k ∧ k.toNat < count then some (.lane j (8 * k.toNat) l) else none
      | some (.lane j c _), some (.int k) => if 0 ≤ k then blockAt look s j c (Lin.const (64 * k)) else none
      | some (.lane j c _), some (.num r) => blockAt look s j c (Lin.scale 64 r)
      | _, _ => none
    | .call f args =>
      match wevalList (weval ctx look s fuel env) args with
      | none => none
      | some vs =>
        if f == "len" then
          -- how many bytes a run of bytes with a length is, or a part of one
          match vs with
          | [.region _ l] => some (.num (Lin.var l))
          | [.span _ _ len] => some (.num len)
          | [.run _ n] => some (.int n)
          | [.part _ _ n] => some (.int n)
          | [.list l] => some (.int l.length)
          | [.wbytes ids] => some (.int (4 * ids.length))
          | _ => none
        else if own.contains f then wown ctx look s f vs
        else if !knowsOf f s.known then
          -- the state knows nothing of this definition: its text is followed
          match findDef ctx.defs f with
          | some d => if d.params.length == vs.length then weval ctx look s fuel (d.params.zip vs) d.body else none
          | none => none
        else
          match (flatKeys look vs).bind fun keys => heldIds s.facts f keys s.known with
          | some ids => some (.list (ids.map fun i => WVal.word [(i, 1)]))
          | none =>
            match (flatKeys look vs).bind fun keys => heldBytes s.facts f keys s.known with
            | some ids => some (.wbytes ids)
            | none =>
              -- a use that has a number of its own is followed by that number
              match (flatKeys look vs).bind fun keys => usedAs s.facts f keys s.known with
              | some h => some (.use h)
              | none =>
                match findDef ctx.defs f with
                | some d => if d.params.length == vs.length then weval ctx look s fuel (d.params.zip vs) d.body else none
                | none => none
    | .list items => (wevalList (weval ctx look s fuel env) items).map .list
    | .letx x e rest =>
      match weval ctx look s fuel env e with
      | some v => weval ctx look s fuel ((x, v) :: env) rest
      | none => none
    | .each e x a b =>
      match weval ctx look s fuel env a, weval ctx look s fuel env b with
      | some (.int lo), some (.int hi) =>
        (wevalEach (fun i => weval ctx look s fuel ((x, .int i) :: env) e) (hi - lo).toNat lo).map .list
      | _, _ => none
    | .withx a puts =>
      match weval ctx look s fuel env a, wevalList (weval ctx look s fuel env) puts with
      | some (.list l), some ps => (wputAll l ps).map .list
      | _, _ => none
    | .slice a lo hi =>
      -- a part of a run of bytes (of a list of things, none here)
      match weval ctx look s fuel env a, weval ctx look s fuel env lo, weval ctx look s fuel env hi with
      | some (.run r n), some (.int i), some (.int j) =>
        if 0 ≤ i ∧ i ≤ j ∧ j ≤ n then some (.part r i.toNat (j - i).toNat) else none
      | some (.part r off n), some (.int i), some (.int j) =>
        if 0 ≤ i ∧ i ≤ j ∧ j ≤ n then some (.part r (off + i.toNat) (j - i).toNat) else none
      -- a part of a run of bytes with a length: it must be seen at once to end within the run
      | some (.region r l), some (.int i), some (.int j) =>
        if 0 ≤ i ∧ i ≤ j ∧ plain s.facts (Lin.sub (Lin.var l) (Lin.const j)) = true then some (.part r i.toNat (j - i).toNat) else none
      -- a part of such a run up to a place that is a row: it must be seen at once to begin within the part and to end within the run
      | some (.region r l), some (.int i), some (.num j) =>
        if 0 ≤ i ∧ plain s.facts (Lin.sub j (Lin.const i)) = true ∧ plain s.facts (Lin.sub (Lin.var l) j) = true then
          some (.span r (Lin.const i) (Lin.sub j (Lin.const i)))
        else none
      | some (.region r l), some (.num i), some (.num j) =>
        if plain s.facts i = true ∧ plain s.facts (Lin.sub j i) = true ∧ plain s.facts (Lin.sub (Lin.var l) j) = true then
          some (.span r i (Lin.sub j i))
        else none
      | some (.span r off slen), some (.int i), some (.int j) =>
        if 0 ≤ i ∧ i ≤ j ∧ plain s.facts (Lin.sub slen (Lin.const j)) = true then
          match Lin.isConst off with
          | some c => if 0 ≤ c then some (.part r (c.toNat + i.toNat) (j - i).toNat) else some (.span r (Lin.add off (Lin.const i)) (Lin.const (j - i)))
          | none => some (.span r (Lin.add off (Lin.const i)) (Lin.const (j - i)))
        else none
      | some (.span r off slen), some (.num i), some (.num j) =>
        if plain s.facts i = true ∧ plain s.facts (Lin.sub j i) = true ∧ plain s.facts (Lin.sub slen j) = true then
          some (.span r (Lin.add off i) (Lin.sub j i))
        else none
      | some (.wbytes ids), some (.int i), some (.int j) =>
        if 0 ≤ i ∧ i ≤ j ∧ i % 4 = 0 ∧ j % 4 = 0 ∧ j.toNat / 4 ≤ ids.length then
          some (.wbytes ((ids.drop (i.toNat / 4)).take ((j - i).toNat / 4)))
        else none
      | some (.list l), some (.int i), some (.int j) =>
        if 0 ≤ i ∧ i ≤ j ∧ j.toNat ≤ l.length then
          some (.list ((l.drop i.toNat).take (j - i).toNat))
        else none
      | _, _, _ => none
    | .record names items =>
      match wevalList (weval ctx look s fuel env) items with
      | some vs =>
        if names.length == vs.length then
          let fvs := names.zip vs
          match knownRec s.facts s.tab.arr fvs s.known with
          | some h => some (.use h)
          | none => some (.record fvs)
        else none
      | none => none
    | .field e x =>
      match weval ctx look s fuel env e with
      | some (.record fields) => fields.lookup x
      | _ => none
    | .theNumber greatest x a b cond =>
      -- `the least number x in a..b with cond` (or the greatest): the first of them of which the condition
      -- is followed and true, it being followed and false of every one before
      match weval ctx look s fuel env a, weval ctx look s fuel env b with
      | some (.int lo), some (.int hi) =>
        let among := (List.range (hi - lo).toNat).map fun (k : Nat) => lo + (k : Int)
        wfirstWith (fun n => weval ctx look s fuel ((x, .int n) :: env) cond) (if greatest then among.reverse else among)
      | _, _ => none
    | .thePower greatest x cond =>
      -- `the greatest power of two x with cond` (or the least): the first of the sixty-four powers, in
      -- that order, of which the condition is followed and true, it being followed and false of every
      -- one before
      let among := (List.range 64).map fun (k : Nat) => (2 : Int) ^ k
      wfirstWith (fun n => weval ctx look s fuel ((x, .int n) :: env) cond) (if greatest then among.reverse else among)
    | _ => none

/-- The names of the contract for an `ensures` of a whole run (as `envWIn` of the account has them): a
number is the row of its register at entry; a run of a fixed count is itself. -/
def wenvIn (c : Contract) : List (String × Kind) → List Nat → List (String × WVal)
  | (n, .number) :: args, r :: regs => (n, .num (Lin.var r)) :: wenvIn c args regs
  | (n, .bytes len) :: args, r :: regs =>
    match c.regOf len with
    | some l => (n, .region r l) :: wenvIn c args regs
    | none => wenvIn c args regs
  | (_, .out _) :: args, _ :: regs => wenvIn c args regs
  | (n, .fixed count) :: args, r :: regs => (n, .run r count) :: wenvIn c args regs
  | (n, .inout count) :: args, r :: regs => (n, .run r count) :: wenvIn c args regs
  | (_, .valArray _ _ _) :: args, _ :: regs => wenvIn c args regs
  | _, _ => []

/-- The tables of addresses by their names (as `lanesEnv` of the account has them). -/
def lanesW (c : Contract) : List (String × WVal) :=
  (List.range c.fixeds.length).filterMap fun j => (c.tableAt j).map fun (x, _, count, l) => (x, WVal.lanes j count l)

/-- The names of the contract for an `ensures` of a whole run (as `envW` of the account has them). -/
def wenv (c : Contract) : List (String × WVal) := lanesW c ++ wenvIn c c.args c.argRegs

def WFUEL : Nat := 1000

/-- Each word of the list, from word `j` of the run `w` on, is the term known written there. -/
def wordsWritten (look : Node → Option Nat) (wroteW : List (Nat × Nat × Nat)) (w : Nat) : Nat → List WVal → Bool
  | _, [] => true
  | j, .word xs :: rest =>
    (match idOf look xs with
     | some i => wroteW.contains (w, j, i)
     | none => false) && wordsWritten look wroteW w (j + 1) rest
  | _, _ => false

/-- Intern all words of every fixed read-only run whose size is divisible by 4, so `weval` on a
`valArray` specification can refer to them even on paths that never loaded those fixed runs as vectors. -/
def fixedInputNodes : List (String × Nat × Nat) → Nat → List Node
  | [], _ => []
  | (_, _, n) :: more, j =>
    (if n % 4 = 0 then (List.range (n / 4)).map fun k => Node.input j k else []) ++ fixedInputNodes more (j + 1)

mutual
/-- Evaluate one argument of a `valArray` entry expression into a `Key`, assigning fresh `Known.use`
unknowns to nested specification definition calls without unfolding them. -/
def registerValArg (ctx : Ctx) (env : List (String × WVal)) : Nat → Sym → SExpr → Option (Key × Sym)
  | fuel + 1, s, .call g gargs =>
    if own.contains g || g == "len" then
      match weval ctx s.tab.find s WFUEL env (.call g gargs) with
      | some v =>
        match flatKey s.tab.find v with
        | some k => if k.ok s.nvars s.tab.size then some (k, s) else none
        | none => none
      | none => none
    else
      match findDef ctx.defs g, registerValArgs ctx env fuel s gargs with
      | some d, some (gkeys, s1) =>
        if d.params.length == gkeys.length && gkeys.all (Key.ok s1.nvars s1.tab.size) then
          match usedAs s1.facts g gkeys s1.known with
          | some h => some (.use h, s1)
          | none => some (.use s1.nvars, { s1 with nvars := s1.nvars + 1, known := .use g gkeys s1.nvars :: s1.known })
        else none
      | _, _ => none
  | _, s, e =>
    match weval ctx s.tab.find s WFUEL env e with
    | some v =>
      match flatKey s.tab.find v with
      | some k => if k.ok s.nvars s.tab.size then some (k, s) else none
      | none => none
    | none => none

def registerValArgs (ctx : Ctx) (env : List (String × WVal)) : Nat → Sym → SExpr → Option (List Key × Sym)
  | _, s, .nil => some ([], s)
  | fuel, s, .cons a rest =>
    match registerValArg ctx env fuel s a with
    | some (k, s1) =>
      match registerValArgs ctx env fuel s1 rest with
      | some (ks, s2) => some (k :: ks, s2)
      | none => none
    | none => none
  | _, _, _ => none
end

/-- Register `Known.held f keys ids` (and any nested `Known.use`) for entry `i` of a `valArray`. -/
def registerValEntry (ctx : Ctx) (s : Sym) (env : List (String × WVal)) (ids : List Nat) : SExpr → Option Sym
  | .call f args =>
    if own.contains f || f == "len" then none
    else
      match findDef ctx.defs f, registerValArgs ctx env 4 s args with
      | some d, some (keys, s1) =>
        if d.params.length == keys.length && keys.all (Key.ok s1.nvars s1.tab.size) && ids.all (· < s1.tab.size) then
          some { s1 with known := .held f keys ids :: s1.known }
        else none
      | _, _ => none
  | _ => none

/-- Look up the `count` consecutive `Node.input j (start + k)` term IDs already present in `tab`. -/
def findInputIds (look : Node → Option Nat) (j start : Nat) : Nat → Option (List Nat)
  | 0 => some []
  | count + 1 =>
    match look (.input j start), findInputIds look j (start + 1) count with
    | some id, some rest => some (id :: rest)
    | _, _ => none

/-- Attach `Known.held` entries for every `valArray` entry `i` whose words have been loaded into `s.tab`
and whose bound `(i + 1) * ch ≤ len` is seen at once in `s.facts`. -/
def attachValArrays (ctx : Ctx) (s : Sym) : Sym :=
  if ctx.contract.valArrays.isEmpty then s
  else
    let s := { s with tab := (termsOf intern (fixedInputNodes ctx.contract.fixeds 0) s.tab).2 }
    let baseJ := ctx.contract.fixeds.length + ctx.contract.inouts.length + ctx.contract.regions.length
    ctx.contract.valArrays.zipIdx.foldl (fun acc ((x, _, l, ch, el), k) =>
      match ctx.contract.valSpecOf x with
      | none => acc
      | some (idx, expr) =>
        let j := baseJ + k
        let nw := el / 4
        if nw == 0 || ch == 0 then acc
        else
          -- check every distinct entry index `i` referenced in `acc.tab` for run `j`
          let idxs := (acc.tab.list.filterMap fun nd =>
            match nd with
            | .input j' m => if j' == j then some (m / nw) else none
            | _ => none).eraseDups
          idxs.foldl (fun st (i : Nat) =>
            if plain st.facts (Lin.sub (Lin.var l) (Lin.const ((i + 1) * ch))) then
              match findInputIds st.tab.find j (i * nw) nw with
              | some ids => (registerValEntry ctx st ((idx, .int (i : Int)) :: wenv ctx.contract) ids expr).getD st
              | none => st
            else st) acc) s

/-- `ensures RUN = bytes_of(WORDS)`: the specification's words, worked out on the terms, are as many as the
run has, and each is the term known written at its place of the run. (Of a part of the run: as many as the
part has, which begins at a whole word and lies within the run; each is the term written at its place there.) -/
def symEnsureW (ctx : Ctx) (s : Sym) (e : EnsureW) : V Unit :=
  let s := attachValArrays ctx s
  match e.value with
  | .call f (.cons x .nil) =>
    if f == "bytes_of" then
      match findOutNamed e.run ctx.contract.outs 0 with
      | some (w, n) =>
        match weval ctx s.tab.find s WFUEL (wenv ctx.contract) x with
        | some (.list l) =>
          if e.first % 4 = 0 ∧ l.length * 4 = e.size n ∧ e.first + e.size n ≤ n ∧ wordsWritten s.tab.find s.wroteW w (e.first / 4) l = true then pure ()
          else refuse "a word of the run is not known to hold what the specification says"
        | _ => refuse "the specification's words are not followed on the terms the function made"
      | none => refuse "an `ensures` of what is no run given to write"
    else refuse "an `ensures` of a whole run that is not the bytes of words: not here yet"
  | _ => refuse "an `ensures` of a whole run that is not the bytes of words: not here yet"

/-! ### Rows the proof file gives

`weval` follows a comparison of two numbers only where one fact says it, and a call's rules look among
the facts for the bounds of the parts of runs handed over. Where the facts do not say such a thing at
once but it follows from them, the proof file says so: before an `ensures` of a run of words, and before
a call, its next items may be rows (`know`). Each is shown to follow from the facts (`entail`: seen at
once, or by the proof of arithmetic that comes next in the file) and then joins them. Which rows to give
is the prover's business. The verifier only shows them.

Rows are taken at the first such point the verifier comes to. Where rows are meant for a later point, the
file says `next` first: that ends the taking of rows at a point. -/

/-- The next item of the proof file, where it is a row to know; it is then taken. `next` is taken too, and
ends the rows of this point. Any other item is left where it is. (Where the file has run out, nothing is
given. A prover's helper may say there what rows it would try next, `advice`, and that is printed like
anything else a proof lacks. The verifier's program gives no advice.) -/
def popKnow (advice : Sym → List Row) (s : Sym) : V (Option Row) := fun items =>
  match items.line items.next with
  | some (.know g) => .ok (some g, { items with next := items.next + 1 })
  | some (.tag name _) => .ok (none, if name == "next" then { items with next := items.next + 1 } else items)
  | some _ => .ok (none, items)
  | none =>
    match advice s with
    | [] => .ok (none, items)
    | rows => need "know" s.facts rows items

/-- The rows the proof file gives here, at most `fuel` of them: each is shown to follow from the facts and
the rows before it, and joins the facts. A row that speaks of an unknown not in use is refused. -/
def symKnow (advice : Sym → List Row) : Nat → Sym → V Sym
  | 0, s => pure s
  | fuel + 1, s => do
    match ← popKnow advice s with
    | none => pure s
    | some g =>
      if g.coeff.length ≤ s.nvars then do
        entail s.facts g
        symKnow advice fuel { s with facts := g :: s.facts }
      else refuse "a row the proof gives speaks of an unknown that is not in use"

/-- How many rows the proof file may give at one point, at most. -/
def KNOWN : Nat := 200

/-- An `ensures` of a run of words: first the rows the proof file gives here join the facts; then
`symEnsureW`. -/
def symEnsureKnown (ctx : Ctx) (s : Sym) (e : EnsureW) : V Unit := do
  let s ← symKnow (ctx.advice.ensures · e) KNOWN s
  symEnsureW ctx s e

/-- At the return: the stack pointer is where it was, the registers a callee keeps hold what they held at
entry, the runs given to write hold what each `ensures` says, and rax holds what the contract says. -/
def keptRegRefusal (c : Contract) (s : Sym) : String :=
  match c.keeps.find? fun r => s.reg r != Lin.var r with
  | some r =>
    let nm := (if c.arm64 then regNamesArm else regNames).getD r s!"r{r}"
    s!"at the return a register a callee keeps ({nm}) does not hold what it held at entry"
  | none => "at the return a register a callee keeps does not hold what it held at entry"

def symReturn (ctx : Ctx) (s : Sym) : V Unit :=
  if s.sp != some 0 then refuse "at the return the stack pointer is not where it was at entry"
  else if !(ctx.contract.keeps.all fun r => s.reg r == Lin.var r) then refuse (keptRegRefusal ctx.contract s)
  else if !(ctx.contract.keepsVec.all fun r => s.vecIntact.contains r) then refuse "at the return a callee-saved vector register was modified"
  else do
    each (symEnsureKnown ctx s) ctx.contract.ensuresW
    let s ← fold (symEnsure ctx (symEnvAfter ctx.contract s)) s ctx.contract.ensures
    match ctx.contract.returns with
    | none => pure ()
    | some e => do
      let (res, s) ← seval ctx (symEnv ctx.contract) s e
      let rr := ctx.contract.retReg
      match res with
      | .val (.lin v) => do
        entail s.facts (Lin.sub v (s.reg rr))
        entail s.facts (Lin.sub (s.reg rr) v)
      | .tail c => do
        let _ ← specGoal ctx 16 s (.value c (s.reg rr))
        pure ()
      | _ => refuse "a function returns a number"

/-! ## Marks: what may depend on values kept out of the trace

The machine marks what may depend on values kept out of the trace, and stops where something marked is used in an address,
decides a jump, or is the address a return goes to. The verifier follows which registers and flags are
known not to be marked (`Sym.q`), a statement at a time, and refuses where the machine could stop. -/

mutual
  /-- The expression is made of nothing that may be marked: numbers, registers known not to be marked,
  and what is worked out of such; no memory, no vector register. -/
  def cleanExpr (bind : Bind) (q : List Nat) : Expr → Bool
    | .number _ => true
    | .lane _ _ => false
    | .name n =>
      isNumberLetter n ||
        match regOf bind n with
        | some r => q.contains r
        | none => false
    | .call f args => (memWidth f).isNone && cleanAll bind q args
  def cleanAll (bind : Bind) (q : List Nat) : List Expr → Bool
    | [] => true
    | e :: es => cleanExpr bind q e && cleanAll bind q es
end

mutual
  /-- Every address in the expression is made of nothing that may be marked. -/
  def quietExprS (bind : Bind) (q : List Nat) : Expr → Bool
    | .call f args => quietAllS bind q args && ((memWidth f).isNone || cleanAll bind q args)
    | _ => true
  def quietAllS (bind : Bind) (q : List Nat) : List Expr → Bool
    | [] => true
    | e :: es => quietExprS bind q e && quietAllS bind q es
end

/-- A register's row, or a number's: what a part of an address is. (Or `on16` of a register: AArch64's stack
pointer as a base, where it is shown to be a multiple of 16, as `symOn16` shows it.) -/
def plainRow (ctx : Ctx) (bind : Bind) (s : Sym) : Expr → Option Row
  | .number n => if n < 2 ^ 64 then some (Lin.const n) else none
  | .name n =>
    if isNumberLetter n then ((bind.lookup n).bind readInt).map fun i => Lin.const (i % (M64 : Int))
    else (ctx.regOf bind n).map s.reg
  | .call f [.name n] =>
    if f == "on16" && !isNumberLetter n then
      (ctx.regOf bind n).bind fun r =>
        match Lin.isConst (Lin.sub (s.reg r) (Lin.var RSP)) with
        | some c => if ctx.contract.arm64 && decide (c % 16 = 0) then some (s.reg r) else none
        | none => none
    else none
  | _ => none

/-- A load of `size` bytes at `a + b` reads memory that is given to read only and is not hidden: a byte
of a run of bytes that the contract does not say is hidden, at a place the statement has shown to be
within the run (`s1` is the state after the statement: the byte is known there); or bytes at a place that is a number, within a run of a fixed count
that the contract does not say is hidden. Such bytes are not marked at entry, and nothing can write them. -/
def publicLoad (ctx : Ctx) (bind : Bind) (s s1 : Sym) (size : Nat) (a b : Expr) : Bool :=
  match plainRow ctx bind s a, plainRow ctx bind s b with
  | some x, some y =>
    let addr := Lin.add (signed x) (signed y)
    match locate ctx addr with
    | some (.frame c) => size == 8 && s.q.fq.contains c       -- (a cell of the frame known not to be marked)
    | some (.region r o) =>
      size == 1 && (lookupByte r o s1.bytes).isSome &&
        match ctx.contract.regions[r]? with
        | some (base, _) => !ctx.contract.hiddenAt base
        | none => false
    | some (.out _ _) => false
    | some (.data c) => decide (0 ≤ c) && decide (c + size ≤ ctx.data.length)     -- (the file's data is not marked)
    | none =>
      match findOut addr ctx.contract.fixeds 0 with
      | some (.out j off) =>
        match Lin.isConst off, ctx.contract.fixeds[j]? with
        | some c, some (name, _, count) => decide (0 ≤ c) && decide (c + size ≤ count) && !ctx.contract.hidden.contains name
        | _, _ => false
      | _ => false
  | _, _ => false

mutual
  /-- May what the expression stands for be marked? No answer: an address in it is made of something
  that may be marked. -/
  def markOf (ctx : Ctx) (bind : Bind) (s s1 : Sym) : Expr → Option Bool
    | .number _ => some false
    | .lane _ _ => some true
    | .name n => some !(cleanExpr bind s.q.regq (.name n))
    | .call f args =>
      match lowOnly bind f args with
      | some r => some !(s.q.regq.contains r || s.q.lowq.contains r)      -- (the lowest byte of a general register)
      | none =>
        if (memWidth f).isSome then
          if cleanAll bind s.q.regq args then
            match memSize f, args with
            | some size, [a, b] => some !(publicLoad ctx bind s s1 size a b)
            | _, _ => some true
          else none
        else marksOf ctx bind s s1 args
  def marksOf (ctx : Ctx) (bind : Bind) (s s1 : Sym) : List Expr → Option Bool
    | [] => some false
    | e :: es =>
      match markOf ctx bind s s1 e, marksOf ctx bind s s1 es with
      | some x, some y => some (x || y)
      | _, _ => none
end

/-- The cells of the frame known not to be marked, after a store to memory at `args` of something that
may be marked (`m`) or may not. A store at a place of the frame that is a number: the cells apart from the
bytes stored to stay, and where eight bytes are stored and what is stored is not marked, they are a cell
known not to be marked. A store within a run given to write, at a place that is a number: every cell stays
(the run is no part of the frame). Any other store: nothing is known of any cell after it. -/
def cellsAfterSize (ctx : Ctx) (bind : Bind) (s s1 : Sym) (size : Nat) (args : List Expr) (m : Bool) : List Int :=
  match args with
  | [a, b] =>
    match plainRow ctx bind s a, plainRow ctx bind s b with
    | some x, some y =>
      match locate ctx (Lin.add (signed x) (signed y)) with
      | some (.frame c) =>
        if decide (-(ctx.contract.stack : Int) ≤ c) && decide (c + size ≤ 0) then
          (if size == 8 && !m then [c] else []) ++ s.q.fq.filter fun o => decide (o + 8 ≤ c) || decide (c + size ≤ o)
        else []
      | some (.out w o) =>
        -- a store within a run given to write (constant offset, or 1-byte store recorded in `s1.wrote`):
        -- no cell of the frame is stored to
        match ctx.contract.outs[w]? with
        | some (_, _, n) =>
          let constOk := match Lin.isConst o with
            | some c => decide (0 ≤ c) && decide (c + size ≤ n)
            | none => false
          let wroteOk := size == 1 && s1.wrote.any (fun e => e.1 == w && Lin.same e.2.1 o)
          if constOk || wroteOk then s.q.fq else []
        | none => []
      | _ => []
    | _, _ => []
  | _ => []

def cellsAfter (ctx : Ctx) (bind : Bind) (s s1 : Sym) (f : String) (args : List Expr) (m : Bool) : List Int :=
  match memSize f with
  | some size => cellsAfterSize ctx bind s s1 size args m
  | none => []

/-- Is the lowest byte of what the expression stands for known not to be marked? Only of `setlow8(x, w)`,
whose lowest byte is `w`'s, with `w` known not to be marked. -/
def lowClean (ctx : Ctx) (bind : Bind) (s s1 : Sym) : Expr → Bool
  | .call f [_, w] => f == "setlow8" && markOf ctx bind s s1 w == some false
  | _ => false

/-- What is known not to be marked after a statement, `s` being the state before it and `s1` the state
after. No answer: the statement could use something marked in an address. -/
def stmtMarks (ctx : Ctx) (bind : Bind) (s s1 : Sym) : Stmt → Option SMarks
  | .nothing => some s.q
  | .set place v =>
    match markOf ctx bind s s1 v with
    | none => none
    | some m =>
      match place with
      | .name n =>
        if n == "zf" then some { s.q with zq := !m }
        else if n == "cf" then some { s.q with cq := !m }
        else match regOf bind n with
          | some r => some { s.q with regq := if m then s.q.regq.filter (· != r) else r :: s.q.regq.filter (· != r),     -- (once in the list)
                                      lowq := if lowClean ctx bind s s1 v then r :: s.q.lowq.filter (· != r) else s.q.lowq.filter (· != r) }
          | none => none
      | .call f args => if cleanAll bind s.q.regq args then some { s.q with fq := cellsAfter ctx bind s s1 f args m } else none
      | _ => none
  | .vset place v =>
    if quietExprS bind s.q.regq v then
      match place with
      | .call _ args => if cleanAll bind s.q.regq args then some { s.q with fq := cellsAfterSize ctx bind s s1 16 args true } else none
      | _ => some s.q
    else none
  | .vset512 place v =>
    if quietExprS bind s.q.regq v then
      match place with
      | .call _ args => if cleanAll bind s.q.regq args then some { s.q with fq := [] } else none
      | _ => some s.q
    else none
  | _ => none

/-- What the marks of a statement are worked out from, of the state before it: its registers and what is
known not to be marked. (So that the state before need not be kept while the statement is gone through:
its table of words is then changed where it is, not copied.) -/
def Sym.light (s : Sym) : Sym :=
  { reg := s.reg, zf := .unknown, cf := .unknown, frame := [], facts := [], bytes := [], spec := [], nvars := 0, wrote := [], q := s.q }

/-- A statement, with what is known not to be marked brought up to date. -/
def symStmtQ (ctx : Ctx) (bind : Bind) (s : Sym) (st : Stmt) : V Sym := do
  let before := s.light
  let s1 ← symStmt ctx bind s st
  match stmtMarks ctx bind before s1 st with
  | some q => pure { s1 with q := q }
  | none => refuse "an address may depend on values kept out of the trace: what can be observed of the run would depend on them"

inductive Next where
  | at (pc : Nat)
  | returned

/-- The ways a jump on a flag can go, each with what is assumed on it. -/
def ways (s : Sym) (want : Bool) (target next : Nat) : List (Bool × List Row) → V (List (Sym × Next))
  | [] => pure []
  | (set, rows) :: more => do
    let now ← assume s rows
    let rest ← ways s want target next more
    match now with
    | some s' => pure ((s', Next.at (if set == want then target else next)) :: rest)
    | none => pure rest

def jumpTarget (bind : Bind) : Expr → Option Nat
  | .name n => if isNumberLetter n then ((bind.lookup n).bind readInt).map fun i => (i % (M64 : Int)).toNat else none
  | _ => none

/-- The false branch of an equality jump: `t neq` keeps one state recording `a - b ≠ 0` in `s.spec`,
avoiding exponential `<` / `>` splitting on chained equality dispatches; otherwise falls back to the
classic `<` / `>` split. -/
def assumeNeq (s : Sym) (a b : Row) (want : Bool) (target next : Nat) : V (List (Sym × Next)) :=
  match Lin.isConst (Lin.sub a b) with
  | some k => if k == 0 then pure [] else pure [(s, Next.at (if want == false then target else next))]
  | none => fun items =>
    match items.line items.next with
    | none => need "branch_neq" s.facts [Lin.sub a b] items
    | some (.tag nm _) =>
      if nm == "neq" then
        .ok ([({ s with spec := .neq (Lin.sub a b) :: s.spec }, Next.at (if want == false then target else next))],
          { items with next := items.next + 1 })
      else
        ways s want target next
          [(false, [Lin.sub (Lin.sub a b) (Lin.const 1)]), (false, [Lin.sub (Lin.sub b a) (Lin.const 1)])]
          items
    | some _ =>
      ways s want target next
        [(false, [Lin.sub (Lin.sub a b) (Lin.const 1)]), (false, [Lin.sub (Lin.sub b a) (Lin.const 1)])]
        items

def assumeEq (s : Sym) (a b : Row) (want : Bool) (target next : Nat) : V (List (Sym × Next)) :=
  if hasNeq s.spec a b then pure []
  else do
    match ← assume s [Lin.sub a b, Lin.sub b a] with
    | some s' => pure [(s', Next.at (if want then target else next))]
    | none => pure []

/-- Whether the symbolic flag(s) read by a jump condition are known clean of trace-hidden values. -/
def symCondClean (q : SMarks) (flag : String) : Bool :=
  if flag == "zf" then q.zq else if flag == "hi" then q.cq && q.zq else q.cq

/-- Symbolic condition relation for a jump (`"hi"` = `!cf && !zf` = `below b a` when `zf = equal a b` and `cf = below a b`). -/
def symCondFlag (s : Sym) (flag : String) : Flag :=
  if flag == "zf" then s.zf
  else if flag == "hi" then
    match s.zf, s.cf with
    | .equal a b, .below a' b' => if Lin.same a a' && Lin.same b b' then .below b a else .unknown
    | _, _ => .unknown
  else s.cf

/-- All reachable successors of a conditional jump on a symbolic flag. -/
def jumpWays (s : Sym) (want : Bool) (target next : Nat) : Flag → V (List (Sym × Next))
  | .unknown => refuse "a jump on a flag of which nothing is known"
  | .below a b => ways s want target next [(true, [Lin.sub (Lin.sub b a) (Lin.const 1)]), (false, [Lin.sub a b])]
  | .equal a b => do
    let yes ← assumeEq s a b want target next
    let no ← assumeNeq s a b want target next
    pure (yes ++ no)

def flagWays : Flag → Option (List (Bool × List Row))
  | .unknown => none
  | .equal a b => some [(true, [Lin.sub a b, Lin.sub b a]), (false, [Lin.sub (Lin.sub a b) (Lin.const 1)]), (false, [Lin.sub (Lin.sub b a) (Lin.const 1)])]
  | .below a b => some [(true, [Lin.sub (Lin.sub b a) (Lin.const 1)]), (false, [Lin.sub a b])]

/-- Parse the condition predicate name used in `select(cond, a, b)`. -/
def selectCond (cond : String) : Option (String × Bool) :=
  if cond == "zf" then some ("zf", true)
  else if cond == "nzf" then some ("zf", false)
  else if cond == "cf" then some ("cf", true)
  else if cond == "ncf" then some ("cf", false)
  else if cond == "hi" then some ("hi", true)
  else if cond == "nhi" then some ("hi", false)
  else none

def setSelectReg (s : Sym) (d : Nat) (v : Row) (q : SMarks) : Sym :=
  { s with reg := fun r => if r == d then v else s.reg r, q := q }

/-- All reachable successors of a conditional select `d := if cond then va else vb` (constant-time: no trace event). -/
def selectWays (s : Sym) (want : Bool) (d : Nat) (va vb : Row) (q' : SMarks) (next : Nat) (f : Flag) : V (List (Sym × Next)) := do
  let w ← jumpWays s want 1 0 f
  pure (w.map fun (s', nxt) =>
    match nxt with
    | .at 1 => (setSelectReg s' d va q', .at next)
    | _ => (setSelectReg s' d vb q', .at next))

/-- An effect is a return (to the address at the stack pointer, or to the address a register holds), a
jump, a conditional select, or statements that set registers, flags and memory. -/
inductive Shape where
  | ret
  | jump (target : Expr) (cond : Option (String × Bool))
  | select (dst cond : String) (a b : Expr)
  | plain
  | retLink (link : String)

def shape : List Stmt → Shape
  | [.ret] => .ret
  | [.jump target cond] => .jump target cond
  | [.retLink r] => .retLink r
  | [.set (.name dst) (.call "select" [.name cond, a, b])] => .select dst cond a b
  | _ => .plain

def retMarkRefusal (arm64 : Bool) (resultFollowsTrace : Bool) (regq : List Nat) : String :=
  if !regq.contains RSP then
    "at the return the stack pointer (sp) may depend on values kept out of the trace"
  else if arm64 && !regq.contains LINK then
    "at the return the return address (x30) may depend on values kept out of the trace"
  else if resultFollowsTrace && !regq.contains 0 then
    "at the return the returned value may depend on values kept out of the trace"
  else
    "at the return a register may depend on values kept out of the trace"

def symInstr (ctx : Ctx) (s : Sym) (i : Instr) : V (List (Sym × Next)) :=
  match shape i.effect with
  | .ret =>
    if ctx.contract.arm64 then refuse "a return to the address at the stack pointer, in a function for AArch64"
    else do
      symReturn ctx s
      if !(s.q.regq.contains RSP && (!ctx.contract.resultFollowsTrace || s.q.regq.contains 0)) then
        refuse (retMarkRefusal false ctx.contract.resultFollowsTrace s.q.regq)
      else pure [(s, .returned)]
  | .retLink r =>
    -- a return to the address a register holds: the register is the one the contract's machine returns by, it
    -- holds what it held at entry, and it is known not to be marked
    if !(ctx.contract.arm64 && regIndex r == some LINK) then refuse "a return by a register, in a function whose machine does not return by that register"
    else if !(s.reg LINK == Lin.var LINK) then refuse "at the return the register that held the address to return to does not hold what it held at entry"
    else do
      symReturn ctx s
      if !(s.q.regq.contains RSP && (s.q.regq.contains LINK && (!ctx.contract.resultFollowsTrace || s.q.regq.contains 0))) then
        refuse (retMarkRefusal true ctx.contract.resultFollowsTrace s.q.regq)
      else pure [(s, .returned)]
  | .jump target cond =>
    match jumpTarget i.bind target with
    | none => refuse "a jump to a place that cannot be read"
    | some t =>
      match cond with
      | none => pure [(s, .at t)]
      | some (flag, want) =>
        if !symCondClean s.q flag then
          refuse "a jump on a flag that may depend on values kept out of the trace: which instructions run would depend on them"
        else
        jumpWays s want t i.next (symCondFlag s flag)
  | .select dst cond a b =>
    match selectCond cond, ctx.regOf i.bind dst, a, b with
    | some (flag, want), some d, .name na, .name nb =>
      if isNumberLetter na || isNumberLetter nb then refuse "conditional select requires general registers"
      else match ctx.regOf i.bind na, ctx.regOf i.bind nb with
      | some ra, some rb =>
        if d == RSP then refuse "conditional select into the stack pointer is not supported"
        else if !ctx.contract.traceExprs.isEmpty then
          refuse "conditional select cannot be combined with computed `trace depends on` values"
        else
          let m := !(symCondClean s.q flag && s.q.regq.contains ra && s.q.regq.contains rb)
          let q' : SMarks := { s.q with
            regq := if m then s.q.regq.filter (· != d) else d :: s.q.regq.filter (· != d),
            lowq := if m then s.q.lowq.filter (· != d) else d :: s.q.lowq.filter (· != d) }
          selectWays s want d (s.reg ra) (s.reg rb) q' i.next (symCondFlag s flag)
      | _, _ => refuse "conditional select requires general registers"
    | _, _, _, _ => refuse "conditional select of a form not supported"
  | .plain => do
    let s1 ← fold (symStmtQ ctx i.bind) s i.effect
    let s2 ← settle ctx s1
    pure [({ s2 with q := s1.q }, .at i.next)]

/-! ## A call, by the called function's contract -/

/-- The registers a function with this contract may leave anything in: every general register of the
machine except `RSP` and those listed in `c.keeps`. -/
def Contract.scratch (c : Contract) : List Nat :=
  (List.range c.regs).filter fun r => r != RSP && !c.keeps.contains r

/-- Among the runs of bytes this function was given: the one whose address register `b` holds and whose
length register `l` holds, both as they were at entry. -/
def findRun (s : Sym) (b l : Nat) : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (b0, l0) :: more, k => if s.reg b == Lin.var b0 && s.reg l == Lin.var l0 then some k else findRun s b l more (k + 1)

/-- What a called function's names are, on symbols: a number is what its register holds at the call; a run
of bytes must be one of the runs this function was itself given, whole. -/
def calleeEnv (ctx : Ctx) (c : Contract) (s : Sym) : List (String × Kind) → List Nat → Option (List (String × SVal))
  | (n, .number) :: args, r :: regs => (calleeEnv ctx c s args regs).map fun env => (n, SVal.lin (s.reg r)) :: env
  | (n, .bytes len) :: args, r :: regs =>
    match c.regOf len with
    | some l =>
      match findRun s r l ctx.contract.regions 0, calleeEnv ctx c s args regs with
      | some j, some env => some ((n, SVal.region j) :: env)
      | _, _ => none
    | none => calleeEnv ctx c s args regs
  | (_, .out _) :: _, _ :: _ => none            -- (a called function that writes for its caller: not here yet)
  | (_, .fixed _) :: _, _ :: _ => none          -- (a called function given a run of a fixed count: not here yet)
  | (_, .inout _) :: _, _ :: _ => none
  | (_, .valArray _ _ _) :: _, _ :: _ => none
  | _, _ => some []

/-- The state after a call, before anything is known of what was returned: the stack pointer and the
registers a callee keeps are as before; every other register holds a number below 2^64 and no more is
known; nothing is known of the flags; of the frame, only what lies above the stack pointer is kept (the
called function's frame and its return address were below). -/
def Sym.afterCall (c : Contract) (s : Sym) (sp : Int) : Sym :=
  { reg := fun r => if c.scratch.contains r then Lin.var (s.nvars + r) else s.reg r,
    zf := .unknown, cf := .unknown,
    frame := s.frame.filter fun cell => decide (sp ≤ cell.1),
    frameW := s.frameW.filter fun cell => decide (sp ≤ cell.1),
    facts := (c.scratch.map fun r => ranged (s.nvars + r)).flatten ++ s.facts,
    bytes := s.bytes, spec := s.spec, nvars := s.nvars + c.regs, wrote := s.wrote,
    tab := s.tab,         -- (and nothing is known of a vector register after a call, nor of the words of a run given to write)
    vecIntact := s.vecIntact.filter c.keepsVec.contains,
    known := s.known, range := s.range }

/-- The linear row for an entry precondition `(k, ts)` evaluated under register rows `val`. -/
def preLineRow (c : Contract) (val : Nat → Row) (k : Int) (ts : List (String × Int)) : Row :=
  ts.foldl (fun acc (x, a) =>
    match c.regOf x with
    | some r => Lin.add acc (Lin.scale a (val r))
    | none => acc) (Lin.const k)

/-- Does the callee's stack budget `c.stackAt` plus `extra` (`c.slot` for a normal call, `0` for a tail call)
fit below `sp` inside the caller's stack budget `ctx.contract.stackAt`? Checked by pure linear arithmetic on
`s.facts`, using the exact `Nat` identities:
`(a - sub) / div < 2^d ↔ a < sub + div * 2^d` and `2^d ≤ (a - sub) / div ↔ sub + div * 2^d ≤ a`. -/
def stackFitsAt (ctx : Ctx) (s : Sym) (sp : Int) (extra : Nat) (c : Contract) : Bool :=
  decide (sp ≤ 0) &&
  match c.stackBits with
  | none => decide (-(ctx.contract.stack : Int) ≤ sp - extra - c.stack)
  | some cb =>
    match c.regOf cb.arg with
    | none => decide (-(ctx.contract.stack : Int) ≤ sp - extra - c.stack)
    | some rcal =>
      let acal := s.reg rcal
      ((List.range 64).any fun d =>
        decide (0 < cb.div) &&
        decide (-(ctx.contract.stack : Int) ≤ sp - extra - (c.stack + cb.step * d : Nat)) &&
        plain s.facts (Lin.sub (Lin.const (((cb.sub + cb.div * 2 ^ d : Nat) : Int) - 1)) acal)) ||
      match ctx.contract.stackBits with
      | none => false
      | some pb =>
        match ctx.contract.regOf pb.arg with
        | none => false
        | some rpar =>
          decide (cb.step ≤ pb.step) &&
          ((decide (cb.div = pb.div) && decide (pb.sub ≤ cb.sub) &&
            decide (-(ctx.contract.stack : Int) ≤ sp - extra - c.stack) &&
            plain s.facts (Lin.sub (Lin.var rpar) acal)) ||
           (decide (0 < cb.div) && decide (0 < pb.div) &&
            decide (-(ctx.contract.stack : Int) - (pb.step : Int) ≤ sp - extra - c.stack) &&
            (List.range 64).any fun d =>
              plain s.facts (Lin.sub (Lin.const (((cb.sub + cb.div * 2 ^ d : Nat) : Int) - 1)) acal) &&
              plain s.facts (Lin.sub (Lin.var rpar) (Lin.const ((pb.sub + pb.div * 2 ^ d : Nat) : Int)))) ||
           (decide (cb.div = pb.div) && decide (cb.sub = pb.sub) && decide (0 < cb.div) &&
            decide (-(ctx.contract.stack : Int) - (pb.step : Int) ≤ sp - extra - c.stack) &&
            plain s.facts (Lin.sub (Lin.add (Lin.var rpar) (Lin.const cb.sub)) (Lin.scale 2 acal)) &&
            plain s.facts (Lin.sub (Lin.var rpar) (Lin.const (cb.sub + cb.div : Nat)))))

def stackFits (ctx : Ctx) (s : Sym) (sp : Int) (c : Contract) : Bool :=
  stackFitsAt ctx s sp c.slot c

/-- Monadic stack-budget check at a call or tail call: first tries the zero-item `stackFitsAt` fast path,
then uses `entail` for symbolic arithmetic (fixed-caller cap, monotone, power-of-two split, or halving). -/
def stackFitsMAt (ctx : Ctx) (s : Sym) (sp : Int) (extra : Nat) (c : Contract) : V Unit :=
  if stackFitsAt ctx s sp extra c then pure ()
  else if !(sp ≤ 0) then refuse "a call needs more stack than this function's contract allows"
  else match c.stackBits with
  | none => refuse "a call needs more stack than this function's contract allows"
  | some cb =>
    match c.regOf cb.arg with
    | none => refuse "a call needs more stack than this function's contract allows"
    | some rcal =>
      if !(0 < cb.div) then refuse "a call needs more stack than this function's contract allows"
      else
        let acal := s.reg rcal
        match ctx.contract.stackBits with
        | none =>
          let rem := (ctx.contract.stack : Int) + sp - extra - c.stack
          if 0 ≤ rem then
            let d := if cb.step == 0 then 63 else min 63 (rem.toNat / cb.step)
            entail s.facts (Lin.sub (Lin.const (((cb.sub + cb.div * 2 ^ d : Nat) : Int) - 1)) acal)
          else refuse "a call needs more stack than this function's contract allows"
        | some pb =>
          match ctx.contract.regOf pb.arg with
          | none => refuse "a call needs more stack than this function's contract allows"
          | some rpar =>
            if !(cb.step ≤ pb.step && 0 < pb.div) then
              refuse "a call needs more stack than this function's contract allows"
            else if cb.div == pb.div && pb.sub ≤ cb.sub && -(ctx.contract.stack : Int) ≤ sp - extra - c.stack then
              entail s.facts (Lin.sub (Lin.var rpar) acal)
            else if -(ctx.contract.stack : Int) - (pb.step : Int) ≤ sp - extra - c.stack then
              match Lin.isConst acal with
              | some k =>
                if 0 ≤ k then
                  let d := bitsNat ((k.toNat - cb.sub) / cb.div)
                  if d < 64 then
                    entail s.facts (Lin.sub (Lin.var rpar) (Lin.const ((pb.sub + pb.div * 2 ^ d : Nat) : Int)))
                  else refuse "a call needs more stack than this function's contract allows"
                else refuse "a call needs more stack than this function's contract allows"
              | none =>
                match Lin.isConst (Lin.sub (Lin.var rpar) acal) with
                | some diff =>
                  if 0 < diff && diff.toNat / cb.div > 0 then
                    let d := Nat.log2 (diff.toNat / cb.div)
                    if d < 64 then do
                      entail s.facts (Lin.sub (Lin.const (((cb.sub + cb.div * 2 ^ d : Nat) : Int) - 1)) acal)
                      entail s.facts (Lin.sub (Lin.var rpar) (Lin.const ((pb.sub + pb.div * 2 ^ d : Nat) : Int)))
                    else refuse "a call needs more stack than this function's contract allows"
                  else refuse "a call needs more stack than this function's contract allows"
                | none =>
                  if cb.div == pb.div && cb.sub == pb.sub then do
                    entail s.facts (Lin.sub (Lin.add (Lin.var rpar) (Lin.const cb.sub)) (Lin.scale 2 acal))
                    entail s.facts (Lin.sub (Lin.var rpar) (Lin.const (cb.sub + cb.div : Nat)))
                  else refuse "a call needs more stack than this function's contract allows"
            else refuse "a call needs more stack than this function's contract allows"

def stackFitsM (ctx : Ctx) (s : Sym) (sp : Int) (c : Contract) : V Unit :=
  stackFitsMAt ctx s sp c.slot c

def symCallPlain (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    if !(c.outs.isEmpty && c.ensures.isEmpty && (c.fixeds.isEmpty && (c.inouts.isEmpty && c.ensuresW.isEmpty))) then
      refuse "a called function that writes for its caller: not here yet"
    else
      match calleeEnv ctx c s c.args c.argRegs with
      | none => refuse "a called function is given a run of bytes that is not one this function was given, whole"
      | some env => do
        each (fun (xb : String × Nat) =>
          match c.regOf xb.1 with
          | some rb => entail s.facts (Lin.sub (Lin.const ((xb.2 : Int) - 1)) (s.reg rb))
          | none => pure ()) c.bounds
        match c.returns with
        | none => pure (s.afterCall c sp)
        | some e => do
          let (res, s2) ← seval ctx env (s.afterCall c sp) e
          let rv := s.nvars + c.retReg
          match res with
          | .val (.lin v) => pure { s2 with facts := [Lin.sub v (Lin.var rv), Lin.sub (Lin.var rv) v] ++ s2.facts }
          | .tail call => pure { s2 with spec := .value call (Lin.var rv) :: s2.spec }
          | _ => refuse "a function returns a number"

/-! ## A call of a function that writes a run of words for its caller

The called function reads and writes one run of words, and reads parts of runs of a fixed count; its
contract says the run then holds the bytes of the words a definition gives of its arguments. The call is
taken by that: what the contract asks is shown first; after it each word of the run is a new unknown, and
the definition, used with what the function was given, is known to be those words. -/

def ranged32 (v : Nat) : List Row := [Lin.var v, Lin.sub (Lin.const (W32i - 1)) (Lin.var v)]

/-- The terms of the words of the run `w` known written, from word `k` on, `count` of them. -/
def writtenIds (wroteW : List (Nat × Nat × Nat)) (w : Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some []
  | count + 1, k =>
    match wroteW.find? (fun e => e.1 == w && e.2.1 == k), writtenIds wroteW w count (k + 1) with
    | some e, some rest => some (e.2.2 :: rest)
    | _, _ => none

/-! ### A part of the frame handed to a called function to read

The frame's 8-byte cells say what the frame holds. A word of the frame is a half of a cell: the cell's
number modulo 2^32, or its quotient by 2^32. A called function that reads a run of a fixed count may be
given a part of the frame, in whole cells, each of them known. -/

/-- So many bytes from where the stack pointer was at entry: where a register points, if into the frame. -/
def frameAt (s : Sym) (r : Nat) : Option Int := Lin.isConst (Lin.sub (s.reg r) (Lin.var RSP))

/-- The quotient by 2^32 of a cell's number: the row of the quotients, where the row of the remainders is
seen at once to be a word; else as `highOf` finds it. -/
def highHalf (s : Sym) (x : Row) : Option Row :=
  if knownNonneg s (Lin.word x) && plain s.facts (Lin.sub (Lin.const (W32i - 1)) (Lin.word x)) then some (Lin.high x)
  else highOf s x

/-- The four bytes of the frame at `o` (so many bytes from where the stack pointer was at entry) as a word:
the low half of the cell that begins there, or the high half of the cell that begins four bytes before.
(The row whose atom the word is.) -/
def frameWord (s : Sym) (o : Int) : Option Row :=
  match s.frame.find? (fun cell => cell.1 == o) with
  | some (_, x) => some x
  | none =>
    match s.frame.find? (fun cell => cell.1 + 4 == o) with
    | some (_, x) => highHalf s x
    | none => none

/-- `count` words of the frame from `c` on, each of them known from a cell. -/
def frameRows (s : Sym) (c : Int) : Nat → Nat → Option (List Row)
  | 0, _ => some []
  | count + 1, k =>
    match frameWord s (c + 4 * (k : Int)), frameRows s c count (k + 1) with
    | some x, some rest => some (x :: rest)
    | _, _ => none

/-- A 4-byte word of the frame at offset `o`, as a term ID: first from `s.frameW` (vector stores), else from
an 8-byte cell in `s.frame` (`frameWord`) whose `wAtom` is already in `s.tab`. -/
def frameWordId (s : Sym) (o : Int) : Option Nat :=
  match s.frameW.find? (fun cell => cell.1 == o) with
  | some (_, id) => some id
  | none => (frameWord s o).bind fun x => s.tab.find (.atom (Lin.word x))

/-- `count` consecutive 4-byte word term IDs of the frame from `c` on. -/
def frameRunIds (s : Sym) (c : Int) : Nat → Nat → Option (List Nat)
  | 0, _ => some []
  | count + 1, k =>
    match frameWordId s (c + 4 * (k : Int)), frameRunIds s c count (k + 1) with
    | some id, some rest => some (id :: rest)
    | _, _ => none

/-- Before a call: the words of each run the called function is given that lies in the frame are put into
the table of terms (including partially filled frames where some words are in `s.frameW`). -/
def touchFrameRange (s : Sym) (c : Int) : Nat → Nat → Tab
  | 0, _ => s.tab
  | count + 1, k =>
    let t := match s.frameW.find? (fun cell => cell.1 == c + 4 * (k : Int)) with
      | some _ => s.tab
      | none =>
        match frameWord s (c + 4 * (k : Int)) with
        | some x => (wAtom x s.tab).2
        | none => s.tab
    touchFrameRange { s with tab := t } c count (k + 1)

def callFrameTouch (s : Sym) (c : Contract) : Sym :=
  (c.fixeds ++ c.inouts).foldl (fun s (x : String × Nat × Nat) =>
    match frameAt s x.2.1 with
    | some k => { s with tab := touchFrameRange s k (x.2.2 / 4) 0 }
    | none => s) s

/-- The terms of words that are the atoms of these rows, each of them in the table. -/
def frameIds (s : Sym) : List Row → Option (List Nat)
  | [] => some []
  | x :: rest =>
    match s.tab.find (.atom (Lin.word x)), frameIds s rest with
    | some i, some ids => some (i :: ids)
    | _, _ => none

/-- The part of the frame a called function is given: the register `r` holds an address at or above the
stack pointer, `n` bytes from there (whole cells) lie below the address to return to, and every word of
the part is known (from `s.frameW` or `s.frame`) and is in the table. Where it lies, and the words' terms. -/
def frameRun (s : Sym) (r n : Nat) : Option (Int × List Nat) :=
  match frameAt s r, s.sp with
  | some c, some sp =>
    if sp ≤ c ∧ c + n ≤ 0 ∧ n % 8 = 0 then
      (frameRunIds s c (n / 4) 0).map fun ids => (c, ids)
    else none
  | _, _ => none

/-- Fill `count` 4-byte word term IDs of a writable frame buffer at `cw`: use `frameWordId` where known, else
allocate a fresh free variable (whose denotation is the real memory word already at `cw + 4*k`). -/
def frameFill (s : Sym) (cw : Int) : Nat → Nat → List Nat × Sym
  | 0, _ => ([], s)
  | count + 1, k =>
    match frameWordId s (cw + 4 * (k : Int)) with
    | some id =>
      let (rest, s') := frameFill s cw count (k + 1)
      (id :: rest, s')
    | none =>
      let v := s.nvars
      let (id, t') := wAtom (Lin.var v) s.tab
      let (rest, s') := frameFill { s with nvars := v + 1, tab := t' } cw count (k + 1)
      (id :: rest, s')

/-- Before a call of a function that writes a run: where the register it is given in holds an
address in a run of this function's that nothing was written to yet, that run is taken as written with
the words it held at entry (`Sym.touch`). -/
def callTouch (ctx : Ctx) (s : Sym) (c : Contract) : Sym :=
  match c.outs with
  | [(_, r, _)] =>
    match findOut (s.reg r) ctx.contract.outs 0 with
    | some (.out w _) => s.touch ctx w
    | _ => s
  | _ => s

/-- The run a called function is given to read and write: a part of a run this function may read and
write. The register `r` holds an address so far from where that run begins: a number of bytes that is a
multiple of four; `n` bytes from there lie in the run; no single byte of the run was written; and every
word of the part is known written. The run's number among the runs given to write, the part's first word,
and the words' terms. -/
def callRun (ctx : Ctx) (s : Sym) (r n : Nat) : Option (Nat × Nat × List Nat) :=
  match findOut (s.reg r) ctx.contract.outs 0 with
  | some (.out w off) =>
    match Lin.isConst off, ctx.contract.outs[w]? with
    | some c, some (x, b, n0) =>
      if 0 ≤ c ∧ c % 4 = 0 ∧ c + n ≤ n0 ∧ n % 4 = 0 ∧ ctx.contract.inouts.contains (x, b, n0) = true ∧
          s.wrote.all (fun e => e.1 != w) = true then
        (writtenIds s.wroteW w (n / 4) (c.toNat / 4)).map fun ids => (w, c.toNat / 4, ids)
      else none
    | _, _ => none
  | _ => none

/-- The part of a run this function was given to read that a called function is given to read, as a run of
a fixed count: the register `r` holds an address so far from where the run begins, and `n` bytes from there
lie in the run. (The run by its number among the runs of words, the register its address was in at entry,
and the place.) -/
def fixedPart (ctx : Ctx) (s : Sym) (r n : Nat) : Option (Nat × Nat × Nat) :=
  match findOut (s.reg r) ctx.contract.fixeds 0 with
  | some (.out j off) =>
    match Lin.isConst off, ctx.contract.fixeds[j]? with
    | some c, some (_, b, n0) => if 0 ≤ c ∧ c + n ≤ n0 then some (j, b, c.toNat) else none
    | _, _ => none
  | _ =>
    -- or a part of a run of bytes with a length, at a place that is a number, seen at once to end within the run
    match findRegion (s.reg r) ctx.contract.regions 0 with
    | some (.region k off) =>
      match Lin.isConst off, ctx.contract.regions[k]? with
      | some c, some (b, l) =>
        if 0 ≤ c ∧ plain s.facts (Lin.sub (Lin.var l) (Lin.const (c + n))) = true then
          some (ctx.contract.fixeds.length + ctx.contract.inouts.length + k, b, c.toNat)
        else none
      | _, _ => none
    | _ => none

/-- Parse one field part of a serialized record (`statement.py`'s `record_words`). The else branch must be
`[0][1]` (no value in `evalSpec`), so any successful evaluation forces the guard to be true. -/
def parseRecPart (x : String) : SExpr → Option RecField
  | .ifx (.bin "==" (.call "len" (.cons (.field (.name x1) fn1) .nil)) (.num k)) (.field (.name x2) fn2)
         (.index (.list (.cons (.num 0) .nil)) (.num 1)) =>
    if x1 == x && x2 == x && fn1 == fn2 && 0 ≤ k then some (.words fn1 k.toNat) else none
  | .ifx (.bin "==" (.call "len" (.cons (.field (.name x1) fn1) .nil)) (.num k))
         (.call "words" (.cons (.field (.name x2) fn2) .nil))
         (.index (.list (.cons (.num 0) .nil)) (.num 1)) =>
    if x1 == x && x2 == x && fn1 == fn2 && 0 ≤ k && k % 4 = 0 then some (.bytes fn1 k.toNat) else none
  | .ifx (.bin "<" (.field (.name x1) fn1) (.num bd))
         (.list (.cons (.call "lo" (.cons (.call "counter" (.cons (.field (.name x2) fn2) .nil)) .nil))
                (.cons (.call "hi" (.cons (.call "counter" (.cons (.field (.name x3) fn3) .nil)) .nil)) .nil)))
         (.index (.list (.cons (.num 0) .nil)) (.num 1)) =>
    if x1 == x && x2 == x && x3 == x && fn1 == fn2 && fn1 == fn3 && 0 < bd && bd ≤ M64 then some (.u64 fn1 bd.toNat) else none
  | _ => none

def parseRecBody (x : String) : SExpr → Option (List RecField)
  | .bin "++" a b =>
    match parseRecPart x a, parseRecBody x b with
    | some f, some rest => some (f :: rest)
    | _, _ => none
  | a => (parseRecPart x a).map ([·])

/-- Does a list of names contain no duplicates? -/
def allDistinct : List String → Bool
  | [] => true
  | a :: rest => !rest.contains a && allDistinct rest

/-- Does every evaluation result of `e` (if any) have the shape `Val.record (names.zip vs)`? -/
def returnsRecord (names : List String) : SExpr → Bool
  | .letx _ _ body => returnsRecord names body
  | .ifx _ a b => returnsRecord names a && returnsRecord names b
  | .record ns _ => ns == names
  | _ => false

/-- Upper-bound linear facts for every `u64` field written at word index `off` from base variable `base`. -/
def recBoundFacts (base : Nat) : Nat → List RecField → List Row
  | _, [] => []
  | off, .words _ n :: rest => recBoundFacts base (off + n) rest
  | off, .bytes _ n :: rest => recBoundFacts base (off + n / 4) rest
  | off, .u64 _ bd :: rest =>
    Lin.sub (Lin.const ((bd : Int) - 1)) (Lin.add (Lin.var (base + off)) (Lin.scale W32i (Lin.var (base + off + 1)))) ::
    recBoundFacts base (off + 2) rest

/-- The part of a run of bytes with a length that a called function is given as such a run: the register
`r` holds an address so far from where a run of this function's begins, the register `l` a length, and the
facts say at once that the place is no less than zero and that the part ends within the run. (The register
the run's address was in at entry, the place and the length.) -/
def regionPart (ctx : Ctx) (s : Sym) (r l : Nat) : Option (Nat × Row × Row) :=
  match findRegion (s.reg r) ctx.contract.regions 0 with
  | some (.region k off) =>
    match ctx.contract.regions[k]? with
    | some (b, lb) =>
      if plain s.facts off = true ∧ plain s.facts (Lin.sub (Lin.var lb) (Lin.add off (s.reg l))) = true then some (b, off, s.reg l)
      else none
    | none => none
  | _ => none

/-- A called function's names on words, where its arguments are numbers, parts of runs of a fixed count
this function was given, parts of runs of bytes with a length, and the run it reads and writes (the bytes
of the words of `ids`). -/
def calleeW (ctx : Ctx) (c : Contract) (s : Sym) (ids : List Nat) : List (String × Kind) → List Nat → Option (List (String × WVal))
  | (x, .number) :: args, r :: regs => (calleeW ctx c s ids args regs).map fun env => (x, WVal.num (s.reg r)) :: env
  | (x, .fixed n) :: args, r :: regs =>
    match fixedPart ctx s r n, calleeW ctx c s ids args regs with
    | some (_, b, c0), some env => some ((x, WVal.part b c0 n) :: env)
    | none, some env => (frameRun s r n).map fun (_, fids) => (x, WVal.wbytes fids) :: env     -- (or a part of the frame)
    | _, _ => none
  | (x, .bytes len) :: args, r :: regs =>
    match c.regOf len with
    | some l =>
      match regionPart ctx s r l, calleeW ctx c s ids args regs with
      | some (b, off, rlen), some env => some ((x, WVal.span b off rlen) :: env)
      | _, _ => none
    | none => none
  | (x, .inout _) :: args, _ :: regs => (calleeW ctx c s ids args regs).map fun env => (x, WVal.wbytes ids) :: env
  | (_, .valArray _ _ _) :: args, _ :: regs => calleeW ctx c s ids args regs
  | (_, .out _) :: _, _ :: _ => none
  | _, _ => some []

/-- The words of the parts of runs handed to a called function to read, as terms to be in the table (so
that the specification's `words` of such a part finds them). -/
def partNodes (ctx : Ctx) (s : Sym) : List (String × Kind) → List Nat → List Node
  | (_, .fixed n) :: args, r :: regs =>
    (match fixedPart ctx s r n with
     | some (j, _, c) => if c % 4 = 0 then (List.range (n / 4)).map fun k => Node.input j (c / 4 + k) else []
     | none => []) ++ partNodes ctx s args regs
  | _ :: args, _ :: regs => partNodes ctx s args regs
  | _, _ => []

/-- The state after a call of a function that has written `m` words of the run `w`, from word `o` on: as
after any call (`Sym.afterCall`); and each word written is a new unknown from 0 to 2^32 - 1, those words
of the run are these, and the definition `g`, used with `keys`, is known to be the list of them (or, with
`bytes`, the list of their bytes, or with `recFields`, a serialized record). What was known of the run's
other words and of the other runs given to write stays. -/
def Sym.afterCallW (c : Contract) (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (bytes : Bool := false) (recFields : List RecField := []) : Sym :=
  let base := s.nvars + c.regs
  let made := termsOf wAtom ((List.range m).map fun k => Lin.var (base + k)) s.tab
  let isRec := !recFields.isEmpty
  let u := base + m
  { reg := fun r => if c.scratch.contains r then Lin.var (s.nvars + r) else s.reg r,
    zf := .unknown, cf := .unknown,
    frame := s.frame.filter fun cell => decide (sp ≤ cell.1),
    frameW := s.frameW.filter fun cell => decide (sp ≤ cell.1),
    facts := (if isRec then recBoundFacts base 0 recFields else []) ++
             ((List.range m).map fun k => ranged32 (base + k)).flatten ++
             ((c.scratch.map fun r => ranged (s.nvars + r)).flatten ++ s.facts),
    bytes := s.bytes, spec := s.spec, nvars := base + m + (if isRec then 1 else 0), wrote := s.wrote,
    tab := made.2,
    intact := s.intact.filter (· != w),
    vecIntact := s.vecIntact.filter c.keepsVec.contains,
    wroteW := ((List.range m).map fun k => (w, o + k, made.1.getD k 0)) ++
              s.wroteW.filter fun e => e.1 != w || decide (e.2.1 < o) || decide (o + m ≤ e.2.1),
    known := (if isRec then [Known.use g keys u, Known.record u recFields made.1]
              else [if bytes then Known.heldB g keys made.1 else Known.held g keys made.1]) ++ s.known }

/-- The state after a call of a function that has written `m` words (an even count) of the frame, from `c`
bytes from where the stack pointer was at entry: as `Sym.afterCallW`, but what is written is cells of the
frame. Each new word is a new unknown; two words make a cell's number, the first its low half. The cells
the part overlaps are forgotten; the others at or above the stack pointer stay. -/
def Sym.afterCallF (ct : Contract) (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) (recFields : List RecField := []) : Sym :=
  let base := s.nvars + ct.regs
  let made := termsOf wAtom ((List.range m).map fun k => Lin.var (base + k)) s.tab
  let isRec := !recFields.isEmpty
  let u := base + m
  { reg := fun r => if ct.scratch.contains r then Lin.var (s.nvars + r) else s.reg r,
    zf := .unknown, cf := .unknown,
    frame := ((List.range (m / 2)).map fun (j : Nat) =>
                (c + 8 * (j : Int), Lin.add (Lin.var (base + 2 * j)) (Lin.scale W32i (Lin.var (base + 2 * j + 1))))) ++
             s.frame.filter fun cell => decide (sp ≤ cell.1) && (decide (cell.1 + 8 ≤ c) || decide (c + 4 * (m : Int) ≤ cell.1)),
    frameW := s.frameW.filter fun cell => decide (sp ≤ cell.1) && (decide (cell.1 + 4 ≤ c) || decide (c + 4 * (m : Int) ≤ cell.1)),
    facts := (if isRec then recBoundFacts base 0 recFields else []) ++
             ((List.range m).map fun k => ranged32 (base + k)).flatten ++
             ((ct.scratch.map fun r => ranged (s.nvars + r)).flatten ++ s.facts),
    bytes := s.bytes, spec := s.spec, nvars := base + m + (if isRec then 1 else 0), wrote := s.wrote,
    tab := made.2,
    intact := s.intact, vecIntact := s.vecIntact.filter ct.keepsVec.contains, wroteW := s.wroteW,
    known := (if isRec then [Known.use g keys u, Known.record u recFields made.1]
              else [Known.held g keys made.1]) ++ s.known }

/-- What a call of a function that writes a run of words is taken by: the part of a run of this function
that it writes (the run's number among the runs given to write, the part's first word, and how many words
the part has), the definition its contract names, the keys of the things the definition is used with
there, the table with the words of the parts handed over put in, and (if serialized record) its fields. -/
structure CallW where
  w : Nat
  first : Nat
  words : Nat
  g : String
  keys : List Key
  tab : Tab
  recFields : List RecField := []
  env : List (String × WVal) := []

/-- The terms of the table a call is taken by, in order. -/
abbrev CallW.terms (p : CallW) : List Node := p.tab.list

/-- That, where the call can be taken so; else why not. (No proof is read here.) -/
def callWby (find : Nat → Nat → Option (Nat × Nat × List Nat)) (ctx : Ctx) (s : Sym) (c : Contract) : Except String CallW :=
  match c.outs, c.inouts, c.ensuresW with
  | [(run, r, n)], [(run', r', n')], [e] =>
    if !(run == run' && r == r' && n == n' && e.run == run && e.part.isNone) then
      .error "a called function that writes for its caller, but not one run of words it also reads: not here yet"
    else
      let T := (termsOf intern (partNodes ctx s c.args c.argRegs) s.tab).2
      match find r n with
      | none => .error "a called function is given to write what is not whole words of a run this function may read and write, each of them known"
      | some (w, o, ids) =>
        match calleeW ctx c s ids c.args c.argRegs with
        | none => .error "a called function is given a run that is no part of a run this function was given to read"
        | some env =>
          -- its promise: the run is the bytes of the words a definition gives of its arguments, or a serialized record
          match e.value with
          | .call f (.cons (.call g args) .nil) =>
            if f == "bytes_of" && !own.contains g && g != "len" then
              match wevalList (weval ctx T.find { s with tab := T } WFUEL env) args, findDef ctx.defs g with
              | some vs, some d =>
                match flatKeys T.find vs with
                | some keys =>
                  if !(keys.all (Key.ok s.nvars T.size)) then .error "what a called function's contract says of its arguments is not followed"
                  else if d.params.length == keys.length then .ok ⟨w, o, n / 4, g, keys, T, [], env⟩
                  else .error "a called function's contract uses a definition with another number of things"
                | none => .error "what a called function's contract says of its arguments is not followed"
              | _, _ => .error "what a called function's contract says of its arguments is not followed"
            else .error "a called function's `ensures` that is not the bytes of the words a definition gives: not here yet"
          | .call f (.cons (.letx x (.call g args) body) .nil) =>
            if f == "bytes_of" && !own.contains g && g != "len" && c.valArrays.isEmpty then
              match parseRecBody x body, wevalList (weval ctx T.find { s with tab := T } WFUEL env) args, findDef ctx.defs g with
              | some fields, some vs, some d =>
                let fnames := fields.map RecField.name
                if (fields.map RecField.nwords).sum == n / 4 && allDistinct fnames &&
                   returnsRecord fnames d.body && !fields.isEmpty then
                  match flatKeys T.find vs with
                  | some keys =>
                    if !(keys.all (Key.ok s.nvars T.size)) then .error "what a called function's contract says of its arguments is not followed"
                    else if d.params.length == keys.length then .ok ⟨w, o, n / 4, g, keys, T, fields, env⟩
                    else .error "a called function's contract uses a definition with another number of things"
                  | none => .error "what a called function's contract says of its arguments is not followed"
                else .error "a called function's serialized record layout does not match the definition"
              | _, _, _ => .error "what a called function's contract says of its arguments is not followed"
            else .error "a called function's `ensures` that is not the bytes of the words a definition gives: not here yet"
          | _ => .error "a called function's `ensures` that is not the bytes of the words a definition gives: not here yet"
  | _, _, _ => .error "a called function that writes for its caller, but not one run of words it also reads: not here yet"

mutual
/-- Structural + symbolic equivalence of two `valArray` entry expressions (for slicing a caller's `valArray`
at a call without unfolding specification definitions). -/
def valExprMatch (ctx : Ctx) (s : Sym) (env1 env2 : List (String × WVal)) : SExpr → SExpr → Bool
  | .call f1 a1, .call f2 a2 =>
    if own.contains f1 || f1 == "len" then
      match weval ctx s.tab.find s WFUEL env1 (.call f1 a1), weval ctx s.tab.find s WFUEL env2 (.call f2 a2) with
      | some v1, some v2 =>
        match flatKey s.tab.find v1, flatKey s.tab.find v2 with
        | some k1, some k2 => sameKey s.facts k1 k2
        | _, _ => false
      | _, _ => false
    else
      f1 == f2 && valExprMatchList ctx s env1 env2 a1 a2
  | e1, e2 =>
    match weval ctx s.tab.find s WFUEL env1 e1, weval ctx s.tab.find s WFUEL env2 e2 with
    | some v1, some v2 =>
      match flatKey s.tab.find v1, flatKey s.tab.find v2 with
      | some k1, some k2 => sameKey s.facts k1 k2
      | _, _ => false
    | _, _ => false

def valExprMatchList (ctx : Ctx) (s : Sym) (env1 env2 : List (String × WVal)) : SExpr → SExpr → Bool
  | .nil, .nil => true
  | .cons a1 r1, .cons a2 r2 => valExprMatch ctx s env1 env2 a1 a2 && valExprMatchList ctx s env1 env2 r1 r2
  | _, _ => false
end

/-- Extract `nw` known word term IDs from the caller's stack frame starting at `off` (from 8-byte cells
in `s.frame`, or 4-byte word entries in `s.frameW`). -/
def frameWordIds (s : Sym) (off : Int) (nw : Nat) : Option (List Nat) :=
  match (if nw % 2 == 0 then framePairRows s off (nw / 2) else none) with
  | some rows => rows.mapM fun r => s.tab.find (.atom (Lin.word r))
  | none => frameWIds s.frameW off nw 0

/-- Do the `WVal` words `ws` match the term IDs `ids` one for one? -/
def wvalsMatchIds (look : Node → Option Nat) : List WVal → List Nat → Bool
  | [], [] => true
  | .word xs :: ws, i :: ids => idOf look xs == some i && wvalsMatchIds look ws ids
  | _, _ => false

/-- Count consecutive frame entries starting at `i` whose words match `weval` of `expr` with `idx := i`,
within `cf + el * (i + 1) ≤ 0`. -/
def countFrameValEntries (ctx : Ctx) (s : Sym) (env : List (String × WVal)) (cf : Int) (el : Nat)
    (idx : String) (expr : SExpr) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    let off := cf + (el : Int) * (i : Int)
    if !(off + (el : Int) ≤ 0) then i
    else
      match frameWordIds s off (el / 4), weval ctx s.tab.find s WFUEL ((idx, .int i) :: env) expr with
      | some ids, some (.list ws) =>
        if ws.length == el / 4 && wvalsMatchIds s.tab.find ws ids then
          countFrameValEntries ctx s env cf el idx expr fuel (i + 1)
        else i
      | _, _ => i

/-- Check every callee `valArray` argument: either a slice of a caller `valArray`, or a frame buffer
filled with matching entry values (e.g. from a wide kernel). `cw` is `some (cwOff, nout)` when the callee's
output buffer lies in the caller's frame (and must not overlap a frame `valArray`), or `none` when it lies
in the caller's `outs`. -/
def callValArraysOk (ctx : Ctx) (s : Sym) (sp : Int) (cw : Option (Int × Nat)) (env : List (String × WVal)) (c : Contract) : V Unit :=
  each (fun (va : String × Nat × Nat × Nat × Nat) =>
    let (x, r, l, ch, el) := va
    if !(0 < ch ∧ 0 < el ∧ el % 4 = 0) then refuse "invalid value-array parameters"
    else do
      entail s.facts (s.reg l)
      match findValArray (s.reg r) ctx.contract.valArrays 0 with
      | some (_, x0, _, l0, ch0, el0, d) =>
        if !(ch == ch0 ∧ el == el0 ∧ d % (el : Int) = 0) then
          refuse "a called function's value array does not align with this function's value array"
        else do
          let shift := d.toNat / el
          entail s.facts (Lin.sub (Lin.var l0) (Lin.add (Lin.const (shift * ch)) (s.reg l)))
          match c.valSpecOf x with
          | none => pure ()
          | some (idx, expr) =>
            match ctx.contract.valSpecOf x0 with
            | none => refuse "a called function asks for values in a value array whose specification is missing here"
            | some (idx0, expr0) =>
              let u := s.nvars
              let facts' := [Lin.var u,
                             Lin.scale ch (Lin.var u),
                             Lin.sub (s.reg l) (Lin.add (Lin.scale ch (Lin.var u)) (Lin.const ch)),
                             Lin.sub (Lin.var l0) (Lin.add (Lin.scale ch (Lin.var u)) (Lin.const ((shift + 1) * ch)))] ++ s.facts
              let s' := { s with nvars := u + 1, facts := facts' }
              if valExprMatch ctx s' ((idx, .num (Lin.var u)) :: env)
                   ((idx0, .num (Lin.add (Lin.const shift) (Lin.var u))) :: wenv ctx.contract) expr expr0 then pure ()
              else refuse "a called function's value-array entries do not match this function's value array"
      | none =>
        match frameAt s r with
        | none => refuse "a called function's value array is neither a slice of a value array nor in this function's frame"
        | some cf =>
          if !(sp ≤ cf ∧ cf ≤ 0) then
            refuse "a called function's value array lies outside this function's frame"
          else
            let maxN := (-cf).toNat / el
            let count := match c.valSpecOf x with
              | none => maxN
              | some (idx, expr) => countFrameValEntries ctx s env cf el idx expr (min maxN 64) 0
            let disjoint := match cw with
              | none => true
              | some (cwo, nout) => decide (cf + (el : Int) * (count : Int) ≤ cwo) || decide (cwo + (nout : Int) ≤ cf)
            if !(decide (sp ≤ cf) && decide (cf + (el : Int) * (count : Int) ≤ 0) && disjoint) then
              refuse "a called function's value array in the frame overlaps the buffer it writes or exceeds the frame"
            else
              entail s.facts (Lin.sub (Lin.const ((((count + 1) : Int) * (ch : Int)) - 1)) (s.reg l))) c.valArrays

/-- The run it writes is looked for among the runs of words this function may read and write (`callRun`). -/
def callW (ctx : Ctx) (s : Sym) (c : Contract) : Except String CallW := callWby (callRun ctx s) ctx s c

def symCallW' (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    match callW ctx s c with
      | .error what => refuse what
      | .ok plan => do
        -- what its contract asks of the numbers it is given
        each (fun (xb : String × Nat) =>
          match c.regOf xb.1 with
          | some rb => entail s.facts (Lin.sub (Lin.const ((xb.2 : Int) - 1)) (s.reg rb))
          | none => pure ()) c.bounds
        callValArraysOk ctx { s with tab := plan.tab } sp none plan.env c
        pure (Sym.afterCallW c { s with tab := plan.tab } sp plan.w plan.first plan.words plan.g plan.keys false plan.recFields)

/-- A call of a function that writes a run of words: the run of this function that it is given a part of
is first taken as written with the words it held at entry, where nothing was written to it yet. -/
def symCallW (ctx : Ctx) (s : Sym) (c : Contract) : V Sym := symCallW' ctx (callFrameTouch (callTouch ctx s c) c) c

/-! ## A call of a function that writes a part of this function's frame -/

/-- A call of a function that writes a run of words it also reads, where that run is a part of this
function's frame: in whole cells, at or above the stack pointer and below the address to return to;
words of the output buffer not yet written are allocated as fresh free terms (`frameFill`). A part
of the frame that the called function is given to read must lie apart from it. After the call the part's
words are new unknowns, two to a cell (`Sym.afterCallF`). -/
def symCallF' (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    match c.outs with
      | [(_, r, n)] =>
        match frameAt s r with
        | none => refuse "a called function is given to write what is not whole cells of this function's frame"
        | some cw =>
          if !(sp ≤ cw ∧ cw + n ≤ 0 ∧ n % 8 = 0) then
            refuse "a called function is given to write what is not whole cells of this function's frame"
          else if !(c.fixeds.all fun x =>
                match frameAt s x.2.1 with
                | some cf => decide (cf + (x.2.2 : Int) ≤ cw) || decide (cw + (n : Int) ≤ cf)
                | none => true) then
            refuse "a called function is given a part of the frame to read that the part it writes overlaps"
          else
            let (outIds, s0) := frameFill s cw (n / 4) 0
            match callWby (fun r' n' => if r' == r && n' == n then some (0, 0, outIds) else none) ctx s0 c with
            | .error what => refuse what
            | .ok plan => do
              each (fun (xb : String × Nat) =>
                match c.regOf xb.1 with
                | some rb => entail s0.facts (Lin.sub (Lin.const ((xb.2 : Int) - 1)) (s0.reg rb))
                | none => pure ()) c.bounds
              callValArraysOk ctx { s0 with tab := plan.tab } sp (some (cw, n)) plan.env c
              pure (Sym.afterCallF c { s0 with tab := plan.tab } sp cw plan.words plan.g plan.keys plan.recFields)
      | _ => refuse "a called function that writes for its caller, but not one run of words it also reads: not here yet"

/-- Such a call: the words of the parts of the frame it is given are first put into the table. -/
def symCallF (ctx : Ctx) (s : Sym) (c : Contract) : V Sym := symCallF' ctx (callFrameTouch s c) c

/-! ## A call of a function that writes a run of bytes for its caller

The called function writes one run, which it does not read, and reads one run of bytes with a length; its
contract says the run then holds, byte by byte, the list a definition gives of its arguments (`b3l_pad`:
`ensures block = padded(src)`). The run it writes must be whole words of a run this function may read and
write, each of them known; the run it reads, a part of a run of bytes this function was given. After the
call each word of the part written is a new unknown, and the definition, used with what the function was
given, is known to be the bytes of those words. -/

/-- A called function's names on words, where its arguments are numbers, parts of runs of bytes with a
length that this function was given, and a run it only writes (which has no name there). -/
def calleeB (ctx : Ctx) (c : Contract) (s : Sym) : List (String × Kind) → List Nat → Option (List (String × WVal))
  | (x, .number) :: args, r :: regs => (calleeB ctx c s args regs).map fun env => (x, WVal.num (s.reg r)) :: env
  | (x, .bytes len) :: args, r :: regs =>
    match c.regOf len with
    | some l =>
      match regionPart ctx s r l, calleeB ctx c s args regs with
      | some (b, off, n), some env => some ((x, WVal.span b off n) :: env)
      | _, _ => none
    | none => calleeB ctx c s args regs
  | (_, .out _) :: args, _ :: regs => calleeB ctx c s args regs
  | (_, .fixed _) :: _, _ :: _ => none
  | (_, .inout _) :: _, _ :: _ => none
  | (_, .valArray _ _ _) :: _, _ :: _ => none
  | _, _ => some []

/-- That, where the call can be taken so; else why not. (No proof is read here.) -/
def callB (ctx : Ctx) (s : Sym) (c : Contract) : Except String CallW :=
  if !(c.mbounds.isEmpty && c.fixeds.isEmpty && c.inouts.isEmpty && c.ensuresW.isEmpty && c.returns.isNone && c.result.isNone) then
    .error "a called function that writes a run of bytes for its caller and does more: not here yet"
  else
    match c.outs, c.ensures with
    | [(run, r, n)], [e] =>
      match e.lo, e.hi with
      | .num a, .num b =>
        if !(e.run == run && a == 0 && b == (n : Int)) then
          .error "a called function's `ensures` of a part of the run it writes: not here yet"
        else
          match callRun ctx s r n with
          | none => .error "a called function is given to write what is not whole words of a run this function may read and write, each of them known"
          | some (w, o, _) =>
            match calleeB ctx c s c.args c.argRegs with
            | none => .error "a called function is given a run of bytes that is no part of a run of bytes this function was given"
            | some env =>
              -- its promise: the run is the list a definition gives of its arguments
              match e.value with
              | .call g args =>
                if !own.contains g && g != "len" then
                  match wevalList (weval ctx s.tab.find s WFUEL env) args, findDef ctx.defs g with
                  | some vs, some d =>
                    match flatKeys s.tab.find vs with
                    | some keys =>
                      if !(keys.all (Key.ok s.nvars s.tab.size)) then .error "what a called function's contract says of its arguments is not followed"
                      else if d.params.length == keys.length then .ok ⟨w, o, n / 4, g, keys, {}, [], []⟩
                      else .error "a called function's contract uses a definition with another number of things"
                    | none => .error "what a called function's contract says of its arguments is not followed"
                  | _, _ => .error "what a called function's contract says of its arguments is not followed"
                else .error "a called function's `ensures` that is not the list a definition gives: not here yet"
              | _ => .error "a called function's `ensures` that is not the list a definition gives: not here yet"
      | _, _ => .error "a called function's `ensures` of a part of the run it writes: not here yet"
    | _, _ => .error "a called function that writes for its caller, but not one run: not here yet"

def symCallB' (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    match callB ctx s c with
      | .error what => refuse what
      | .ok plan => do
        -- what its contract asks of the numbers it is given
        each (fun (xb : String × Nat) =>
          match c.regOf xb.1 with
          | some rb => entail s.facts (Lin.sub (Lin.const ((xb.2 : Int) - 1)) (s.reg rb))
          | none => pure ()) c.bounds
        pure (Sym.afterCallW c s sp plan.w plan.first plan.words plan.g plan.keys true)

/-- A call of a function that writes a run of bytes: the run of this function that it is given a part of is
first taken as written with the words it held at entry, where nothing was written to it yet. -/
def symCallB (ctx : Ctx) (s : Sym) (c : Contract) : V Sym := symCallB' ctx (callTouch ctx s c) c

/-! ## A call of a function that is given a table of addresses

The called function (a wide kernel) reads a table of addresses, each the address of so many blocks, and
writes one run: for each lane of the table some bytes of it, which its contract says are the bytes of the
words of what a definition gives of the lane's blocks. Here the table and the run written are parts of
this function's frame, and a lane's blocks are a part of a run this function was given to read, or a part
of its frame.

What a lane leaves is followed as far as it can be (`nameval`): the contract's expression is worked out on
this function's terms; a use of a definition that cannot be worked out is given a number of its own
(`Known.use`). The contract says the whole has a value, so that use has one. After the call each word
written is a new unknown; where a lane's expression came to a use that has a number, that use is known to
give the lane's words (`Known.held`). -/

mutual
/-- A thing worked out speaks only of unknowns in use (`n` of them) and of terms of the table (`t` of them):
a number, a word, a counter, a use's number, bytes of a run as they were at entry, or a list of such. (Of the
other kinds this says no: `nameval` does not let them through.) -/
def WVal.ok (n t : Nat) : WVal → Bool
  | .int _ => true
  | .bool _ => true
  | .num r => decide (r.coeff.length ≤ n)
  | .counter r => decide (r.coeff.length ≤ n)
  | .word xs => xs.all (fun p => p.1 < t)
  | .list l => WVal.okAll n t l
  | .use h => decide (h < n)
  | .run _ _ => true
  | .part _ _ _ => true
  | .pbyte _ _ => true
  | .wbytes xs => xs.all (· < t)
  | .other => true
  | _ => false
def WVal.okAll (n t : Nat) : List WVal → Bool
  | [] => true
  | v :: rest => WVal.ok n t v && WVal.okAll n t rest
end

/-- A number held as a row that is a number of the table, as that number. -/
def wnorm : WVal → WVal
  | .num r =>
    match Lin.isConst r with
    | some k => .int k
    | none => .num r
  | v => v

/-- Two numbers' bits put together, each seen at once to lie from 0 to below 2^64: the unknown the state
knows as that, or a new one (`symOrKnown`). -/
def nameOr (s : Sym) (x y : Row) : Option (WVal × Sym) :=
  if knownNonneg s x && plain s.facts (Lin.sub (Lin.const top) x) && knownNonneg s y && plain s.facts (Lin.sub (Lin.const top) y) then
    match symOrKnown s x y (Items.ofList []) with
    | .ok ((.lin r, s'), _) => some (.num r, s')
    | _ => none
  else none

/-- `a op b` of two things worked out: as `wbin` has it; and the bits of a row and of a number of the text
put together, with a new unknown where the state has none for the pair. -/
def namebin (s : Sym) (op : String) (x y : WVal) : Option (WVal × Sym) :=
  match wbin s.tab.find s op x y with
  | some v => if v.ok s.nvars s.tab.size then some (v, s) else none
  | none =>
    match x, y with
    | .num a, .int b => if op == "|" ∧ 0 ≤ b then nameOr s a (Lin.const b) else none
    | _, _ => none

def namevalList (ev : Sym → SExpr → Option (WVal × Sym)) : Sym → SExpr → Option (List WVal × Sym)
  | s, .nil => some ([], s)
  | s, .cons a rest =>
    match ev s a with
    | some (v, s) =>
      match namevalList ev s rest with
      | some (vs, s) => some (v :: vs, s)
      | none => none
    | none => none
  | _, _ => none

/-- Could `nameval` produce a value by stepping into `e` (rather than `weval`, which already failed)?
Definitions whose body returns an `.each` comprehension (like `compress`) cannot be named by stepping
into their `let` bindings, so skipping the doomed recursion avoids thousands of wasted `round`/`g` calls. -/
def canName : SExpr → Bool
  | .bin _ _ _ => true
  | .ifx _ _ _ => true
  | .call _ _ => true
  | .letx _ _ rest => canName rest
  | _ => false

/-- An expression of a called function's `ensures`, worked out on this function's terms. What `weval` works
out as it is, is taken so. Else `a op b`, `if`, `let` and a use of a definition are gone into: a use of a
definition the state holds the words of, or has given a number, is that; else the definition is opened; and
where that cannot be worked out either, the use is given a number of its own. (The state comes back with
what was added: the uses' numbers, and unknowns for two numbers' bits put together. Only a thing that speaks
of unknowns in use and of terms of the table is let through: `WVal.ok`.) -/
def nameval (ctx : Ctx) : Nat → Sym → List (String × WVal) → SExpr → Option (WVal × Sym)
  | 0, _, _, _ => none
  | fuel + 1, s, env, e =>
    match weval ctx s.tab.find s WFUEL env e with
    | some v => if (wnorm v).ok s.nvars s.tab.size then some (wnorm v, s) else none
    | none =>
      match e with
      | .bin op a b =>
        match nameval ctx fuel s env a with
        | some (x, s) =>
          match nameval ctx fuel s env b with
          | some (y, s) => namebin s op x y
          | none => none
        | none => none
      | .ifx c a b =>
        match weval ctx s.tab.find s WFUEL env c with
        | some (.bool true) => nameval ctx fuel s env a
        | some (.bool false) => nameval ctx fuel s env b
        | _ => none
      | .letx x a rest =>
        match nameval ctx fuel s env a with
        | some (v, s) => nameval ctx fuel s ((x, v) :: env) rest
        | none => none
      | .call f args =>
        if f == "len" || own.contains f then none
        else
          match namevalList (fun s e => nameval ctx fuel s env e) s args, findDef ctx.defs f with
          | some (vs, s), some d =>
            if d.params.length != vs.length then none
            else
              match flatKeys s.tab.find vs with
              | none => nameval ctx fuel s (d.params.zip vs) d.body
              | some keys =>
                match heldIds s.facts f keys s.known with
                | some ids => if ids.all (· < s.tab.size) then some (.list (ids.map fun i => WVal.word [(i, 1)]), s) else none
                | none =>
                  match usedAs s.facts f keys s.known with
                  | some h => if h < s.nvars then some (.use h, s) else none
                  | none =>
                    match (if canName d.body then nameval ctx fuel s (d.params.zip vs) d.body else none) with
                    | some r => some r
                    | none =>
                      if keys.all (Key.ok s.nvars s.tab.size) then
                        some (.use s.nvars, { s with nvars := s.nvars + 1, known := .use f keys s.nvars :: s.known })
                      else none
          | _, _ => none
      | _ => none

/-- The use that has the number `h`: its definition and what it is used with. -/
def useOf (h : Nat) : List Known → Option (String × List Key)
  | [] => none
  | .use f keys h' :: more => if h' = h then some (f, keys) else useOf h more
  | _ :: more => useOf h more

/-- A list of words in blocks of sixteen, `k` blocks. -/
def blocksOf : Nat → List WVal → List WVal
  | 0, _ => []
  | k + 1, l => .list (l.take 16) :: blocksOf k (l.drop 16)

/-- The words of the `nb` blocks at the address `a`, as terms put into the table: the blocks are a part of
a run of a fixed count this function was given to read, at a whole word; or a part of this function's frame
(at or above the stack pointer, below the address to return to) that lies apart from the part the called
function writes (`nout` bytes from `cw`), every word of it known from a cell. -/
def laneWords (ctx : Ctx) (s : Sym) (a : Row) (nb : Nat) (cw : Int) (nout : Nat) : Option (List Nat × Tab) :=
  match findOut a ctx.contract.fixeds 0 with
  | some (.out j off) =>
    match Lin.isConst off, ctx.contract.fixeds[j]? with
    | some c, some (_, _, n0) =>
      if 0 ≤ c ∧ c % 4 = 0 ∧ c + 64 * (nb : Int) ≤ (n0 : Int) then
        some (termsOf intern ((List.range (16 * nb)).map fun k => Node.input j (c.toNat / 4 + k)) s.tab)
      else none
    | _, _ => none
  | _ =>
    match findRegion a ctx.contract.regions 0 with
    | some (.region k off) =>
      match Lin.isConst off, ctx.contract.regions[k]? with
      | some c, some (_, l) =>
        if 0 ≤ c ∧ c % 4 = 0 ∧ plain s.facts (Lin.sub (Lin.var l) (Lin.const (c + 64 * (nb : Int)))) = true then
          let j := ctx.contract.fixeds.length + ctx.contract.inouts.length + k
          some (termsOf intern ((List.range (16 * nb)).map fun i => Node.input j (c.toNat / 4 + i)) s.tab)
        else none
      | _, _ => none
    | _ =>
      match Lin.isConst (Lin.sub a (Lin.var RSP)), s.sp with
      | some o, some sp =>
        if sp ≤ o ∧ o + 64 * (nb : Int) ≤ 0 ∧ (o + 64 * (nb : Int) ≤ cw ∨ cw + (nout : Int) ≤ o) then
          (frameRows s o (16 * nb) 0).map fun rows => termsOf wAtom rows s.tab
        else none
      | _, _ => none

/-- The lanes of a table of addresses that lies in the frame from `ct` on, from lane `i` on, `count` of them:
each address is a cell of the frame, and each lane is the list of its `nb` blocks (`laneWords`). -/
def tableLanes (ctx : Ctx) (s : Sym) (ct : Int) (nb : Nat) (cw : Int) (nout : Nat) : Nat → Nat → Tab → Option (List WVal × Tab)
  | 0, _, T => some ([], T)
  | count + 1, i, T =>
    match s.frame.find? (fun cell => cell.1 == ct + 8 * (i : Int)) with
    | some (_, a) =>
      match laneWords ctx { s with tab := T } a nb cw nout with
      | some (ids, T) =>
        match tableLanes ctx s ct nb cw nout count (i + 1) T with
        | some (rest, T) => some (.list (blocksOf nb (ids.map fun i => WVal.word [(i, 1)])) :: rest, T)
        | none => none
      | none => none
    | none => none

/-- The called function's names on words: a number is its register; a run of a fixed count is a part of a
run this function was given to read; the table's own bytes are not followed (its name stands for its lanes,
which come first), and the run of that name is the table: in the register `tr`, `nt` bytes; a run it only
writes has no name there. -/
def calleeL (ctx : Ctx) (s : Sym) (tx : String) (tr nt : Nat) : List (String × Kind) → List Nat → Option (List (String × WVal))
  | (x, .number) :: args, r :: regs => (calleeL ctx s tx tr nt args regs).map fun env => (x, WVal.num (s.reg r)) :: env
  | (x, .fixed n) :: args, r :: regs =>
    if x == tx then
      if r = tr ∧ n = nt then (calleeL ctx s tx tr nt args regs).map fun env => (x, WVal.other) :: env else none
    else
      match fixedPart ctx s r n, calleeL ctx s tx tr nt args regs with
      | some (_, b, c), some env => some ((x, WVal.part b c n) :: env)
      | none, some env => (frameRun s r n).map fun (_, fids) => (x, WVal.wbytes fids) :: env
      | _, _ => none
  | (_, .out _) :: args, _ :: regs => calleeL ctx s tx tr nt args regs
  | (_, .inout _) :: _, _ :: _ => none
  | (_, .bytes _) :: _, _ :: _ => none
  | (_, .valArray _ _ _) :: _, _ :: _ => none
  | _, _ => some []

/-- The use, if any, that a lane's expression comes to: where the expression is the bytes of the words of
something `nameval` brings to a use that has a number. (The state with what `nameval` added; the use's
definition and what it is used with.) -/
def laneUse (ctx : Ctx) (s : Sym) (env : List (String × WVal)) : SExpr → Sym × Option (String × List Key)
  | .call f (.cons x .nil) =>
    if f == "bytes_of" then
      match nameval ctx WFUEL s env x with
      | some (.use h, s1) => (s1, useOf h s1.known)
      | _ => (s, none)
    else (s, none)
  | _ => (s, none)

/-- `m` words written by a called function, as new unknowns, each from 0 to 2^32 - 1, with their terms in
the table; where they are what a use gives, that is known. (The rows of the words, and the state.) -/
def Sym.newWords (s : Sym) (m : Nat) (use : Option (String × List Key)) : List Row × Sym :=
  let rows := (List.range m).map fun k => Lin.var (s.nvars + k)
  let made := termsOf wAtom rows s.tab
  (rows, { s with nvars := s.nvars + m, tab := made.2,
                  facts := ((List.range m).map fun k => ranged32 (s.nvars + k)).flatten ++ s.facts,
                  known := match use with
                    | some (f, keys) => Known.held f keys made.1 :: s.known
                    | none => s.known })

/-- What the lanes leave. The contract has one `ensures` for each lane, in the run's order: so many bytes of
the run, whole words, from where the lane before ended. Each lane's words are new unknowns, each from 0 to
2^32 - 1. Where the lane's expression is the bytes of the words of something `nameval` brings to a use that
has a number, that use is known to give the lane's words. (The rows of the words in the run's order, and the
state with what was added. `a`: where the next lane's bytes begin.) -/
def nameLanes (ctx : Ctx) (run : String) (env : List (String × WVal)) : Sym → Nat → List EnsureW → Option (List Row × Sym)
  | s, _, [] => some ([], s)
  | s, a, e :: rest =>
    match e.part with
    | some (a', m) =>
      if e.run == run ∧ a' = a ∧ m % 4 = 0 then
        let named := laneUse ctx s env e.value
        let made := named.1.newWords (m / 4) named.2
        (nameLanes ctx run env made.2 (a + m) rest).map fun p => (made.1 ++ p.1, p.2)
      else none
    | none => none

/-- The cells that pairs of words make, from `c` on: the first word of a pair is its cell's low half. -/
def cellsOf (c : Int) : Nat → List Row → List (Int × Row)
  | j, lo :: hi :: rest => (c + 8 * (j : Int), Lin.add lo (Lin.scale W32i hi)) :: cellsOf c (j + 1) rest
  | _, _ => []

/-- The state after a call of a function that has written `n` bytes of the frame from `cw` on, the words
written being these rows: as after any call, and the cells of that part are made of the rows, two to a
cell. The cells the part overlaps are forgotten; the others at or above the stack pointer stay. -/
def Sym.afterCallL (c : Contract) (s : Sym) (sp cw : Int) (n : Nat) (rows : List Row) : Sym :=
  { reg := fun r => if c.scratch.contains r then Lin.var (s.nvars + r) else s.reg r,
    zf := .unknown, cf := .unknown,
    frame := cellsOf cw 0 rows ++
             s.frame.filter fun cell => decide (sp ≤ cell.1) && (decide (cell.1 + 8 ≤ cw) || decide (cw + (n : Int) ≤ cell.1)),
    frameW := s.frameW.filter fun cell => decide (sp ≤ cell.1) && (decide (cell.1 + 4 ≤ cw) || decide (cw + (n : Int) ≤ cell.1)),
    facts := (c.scratch.map fun r => ranged (s.nvars + r)).flatten ++ s.facts,
    bytes := s.bytes, spec := s.spec, nvars := s.nvars + c.regs, wrote := s.wrote,
    tab := s.tab, intact := s.intact, vecIntact := s.vecIntact.filter c.keepsVec.contains, wroteW := s.wroteW, known := s.known }

/-- A call of a function that is given a table of addresses and writes one run, where both are parts of
this function's frame, apart from each other, at or above the stack pointer and below the address to return
to; the table's cells are known; the count of blocks is a number of the table; each lane's blocks are a
part of a run this function was given to read or of the frame (`tableLanes`). What the contract asks of its
numbers is shown first. After the call the run's words are new unknowns (`nameLanes`, `Sym.afterCallL`). -/
def symCallL' (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    if !(c.inouts.isEmpty && c.ensures.isEmpty && c.regions.isEmpty &&
              c.returns.isNone && c.result.isNone) then
      refuse "a called function that is given a table of addresses and does more than write one run: not here yet"
    else if !(c.atLeast.all fun (xk : String × Nat) =>
        match c.regOf xk.1 with
        | some rb => plain s.facts (Lin.sub (s.reg rb) (Lin.const xk.2))
        | none => true) then
      refuse "a number that a called function's contract asks to be no less than another is not seen at once to be so"
    else
      match c.outs, c.tables with
      | [(run, r, n)], [(tx, tr, count, l)] =>
        match Lin.isConst (s.reg l), frameAt s r, frameAt s tr with
        | some nb, some cw, some ct =>
          if !(decide (0 ≤ nb) && decide (sp ≤ cw) && decide (cw + (n : Int) ≤ 0) && decide (n % 8 = 0) && decide (sp ≤ ct) &&
               decide (ct + 8 * (count : Int) ≤ 0) && (decide (ct + 8 * (count : Int) ≤ cw) || decide (cw + (n : Int) ≤ ct)) &&
               c.fixeds.all fun x =>
                 match frameAt s x.2.1 with
                 | some cf => decide (cf + (x.2.2 : Int) ≤ cw) || decide (cw + (n : Int) ≤ cf)
                 | none => true) then
            refuse "a called function's table of addresses, or the run it writes, is no part of this function's frame, or the two overlap"
          else
            match tableLanes ctx s ct nb.toNat cw n count 0 (termsOf intern (partNodes ctx s c.args c.argRegs) s.tab).2 with
            | none => refuse "a lane of a called function's table is not blocks this function may read, every word of them known"
            | some (lanes, T) =>
              match calleeL ctx { s with tab := T } tx tr (8 * count) c.args c.argRegs with
              | none => refuse "a called function is given a run that is no part of a run this function was given to read"
              | some env =>
                match nameLanes ctx run ((tx, WVal.list lanes) :: env) { s with tab := T } 0 c.ensuresW with
                | none => refuse "a called function's contract does not say of each lane, one after another, what whole words of the run it leaves"
                | some (rows, s1) =>
                  if rows.length * 4 != n then
                    refuse "a called function's contract does not say of each lane, one after another, what whole words of the run it leaves"
                  else do
                    each (fun (xb : String × Nat) =>
                      match c.regOf xb.1 with
                      | some rb => entail s.facts (Lin.sub (Lin.const ((xb.2 : Int) - 1)) (s.reg rb))
                      | none => pure ()) c.bounds
                    pure (Sym.afterCallL c s1 sp cw n rows)
        | _, _, _ => refuse "a called function's count of blocks is no number of the table, or its table or the run it writes is not in this function's frame"
      | _, _ => refuse "a called function that is given a table of addresses, but not one table and one run to write: not here yet"

def symCallL (ctx : Ctx) (s : Sym) (c : Contract) : V Sym := symCallL' ctx (callFrameTouch s c) c

/-- Check callee `mbounds` (`mbelow x o bd`): either `x` is a fixed part of a caller fixed run carrying
`mbelow x0 (c0 + o) bd0` with `bd0 ≤ bd`, or `x` lies in the caller's frame with a known 8-byte cell
at `cf + o` entailed to lie below `bd`. -/
def callMboundsOk (ctx : Ctx) (s : Sym) (sp : Int) (c : Contract) : V Unit :=
  each (fun (xob : String × Nat × Nat) =>
    let (x, o, bd) := xob
    each (fun (xrn : String × Nat × Nat) =>
      if xrn.1 != x then pure ()
      else
        let (_, r, n) := xrn
        if !(o + 8 ≤ n) then refuse "a called function bounds bytes outside its fixed run"
        else
          match fixedPart ctx s r n with
          | some (j, _, c0) =>
            match ctx.contract.fixeds[j]? with
            | some (x0, _, _) =>
              if ctx.contract.mbounds.any fun (x', o', bd') => x' == x0 && o' == c0 + o && bd' ≤ bd then pure ()
              else refuse "a called function bounds a number in a fixed run that is not bounded in this function's contract"
            | none => refuse "a called function bounds a number in memory that is not known to lie below that bound"
          | none =>
            match frameAt s r with
            | some cf =>
              if sp ≤ cf + (o : Int) ∧ cf + (o : Int) + 8 ≤ 0 then
                match s.frame.find? (fun cell => cell.1 == cf + (o : Int)) with
                | some (_, row) => entail s.facts (Lin.sub (Lin.const ((bd : Int) - 1)) row)
                | none => refuse "a called function bounds a number in the frame that is not a known cell"
              else refuse "a called function bounds a number outside the frame"
            | none => refuse "a called function bounds a number in memory that is not known to lie below that bound") c.fixeds) c.mbounds

/-- Check stack budget (`stackFitsM`), callee `mbounds`, callee numeric lower bounds (`atLeast`),
multi-variable linear preconditions (`preLines`), and strict decrease of `decreases` on a direct recursive self-call. -/
def callPreOk (ctx : Ctx) (s : Sym) (name : String) (c : Contract) : V Unit := do
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    stackFitsM ctx s sp c
    callMboundsOk ctx s sp c
  each (fun (xk : String × Nat) =>
    match c.regOf xk.1 with
    | some rb => entail s.facts (Lin.sub (s.reg rb) (Lin.const xk.2))
    | none => pure ()) c.atLeast
  each (fun (kt : Int × List (String × Int)) =>
    entail s.facts (preLineRow c s.reg kt.1 kt.2)) c.preLines
  if ctx.selfName == some name then
    match c.decreases with
    | some d =>
      match c.regOf d with
      | some r => entail s.facts (Lin.sub (Lin.sub (Lin.var r) (s.reg r)) (Lin.const 1))
      | none => refuse "recursive call: decreasing argument is not a parameter of the function"
    | none => refuse "recursive call: function has no `decreases` argument"
  else pure ()

/-- A call: by the rule for a function that is given a table of addresses; by the rule for a function that
writes nothing for its caller, by the rule for one that writes a run of words it also reads, or by the rule
for one that writes a run of bytes. -/
def symCall' (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  if !c.lanes.isEmpty then
    if c.valArrays.isEmpty then symCallL ctx s c else refuse "a called function with both a table of addresses and a value array: not here yet"
  else if c.outs.isEmpty && c.ensures.isEmpty && (c.fixeds.isEmpty && (c.inouts.isEmpty && c.ensuresW.isEmpty)) then
    if c.valArrays.isEmpty then symCallPlain ctx s c else refuse "a called function with a value array and no output run: not here yet"
  else if c.inouts.isEmpty && c.ensuresW.isEmpty then
    if c.valArrays.isEmpty then symCallB ctx s c else refuse "a called function with a value array and byte-level ensures: not here yet"
  else if c.outs.any (fun x => (frameAt s x.2.1).isSome) then symCallF ctx s c
  else symCallW ctx s c

/-- A call: first the rows the proof file gives here join the facts (the bounds of the parts of runs
handed over, where the facts do not say them at once); then `callPreOk` and `symCall'`. -/
def symCall (ctx : Ctx) (s : Sym) (name : String) (c : Contract) : V Sym := do
  let s ← symKnow (ctx.advice.call · c) KNOWN s
  callPreOk ctx s name c
  symCall' ctx s c

/-- What a called function needs of the processor (`needs avx512`, `needs avx512 if plat == 5`), this function's
contract says too. (The machine of the account has every row of the table, so no theorem asks this. A reader of
this function's contract is told what processor it wants, and that must cover the functions it calls.) -/
def needsOf (ctx : Ctx) (s : Sym) (c : Contract) : V Unit :=
  let covers (what : String) : Bool :=
    ctx.contract.needs.contains what ||
    ctx.contract.needsIf.any fun (w0, arg0, k0) => w0 == what &&
      match ctx.contract.regOf arg0 with
      | some r0 => plain s.facts (Lin.sub (Lin.var r0) (Lin.const k0)) && plain s.facts (Lin.sub (Lin.const k0) (Lin.var r0))
      | none => false
  let ifOk (x : String × String × Nat) : Bool :=
    let (what, arg, k) := x
    covers what ||
    match c.regOf arg with
    | none => false
    | some r =>
      plain s.facts (Lin.sub (Lin.const ((k : Int) - 1)) (s.reg r)) ||
      plain s.facts (Lin.sub (s.reg r) (Lin.const ((k : Int) + 1))) ||
      ctx.contract.needsIf.any fun (w0, arg0, k0) => w0 == what && k == k0 &&
        match ctx.contract.regOf arg0 with
        | some r0 => sameRow s.facts (s.reg r) (Lin.var r0)
        | none => false
  if c.needs.all covers && c.needsIf.all ifOk then pure ()
  else refuse "a called function needs of the processor what this function's contract does not say it needs"

/-- Is `x` a callee argument whose value at the call is already unmarked in `s`? -/
def callArgClean (ctx : Ctx) (s : Sym) (c : Contract) (x : String) : Bool :=
  let rec go : List (String × Kind) → List Nat → Bool
    | (n, .number) :: args, r :: regs => if n == x then s.q.regq.contains r else go args regs
    | (n, .bytes len) :: args, r :: regs =>
      if n == x then
        match c.regOf len with
        | some l =>
          s.q.regq.contains l &&
          match findRun s r l ctx.contract.regions 0 with
          | some j =>
            match ctx.contract.regions[j]? with
            | some (base, _) => !ctx.contract.hiddenAt base
            | none => false
          | none => false
        | none => false
      else go args regs
    | _ :: args, _ :: regs => go args regs
    | _, _ => false
  go c.args c.argRegs

/-- Is every free variable of `e` (not in `bound`) an argument of `c` that is unmarked at the call? -/
def callAllClean (ctx : Ctx) (s : Sym) (c : Contract) (bound : List String) : SExpr → Bool
  | .num _ => true
  | .nil => true
  | .name x => bound.contains x || callArgClean ctx s c x
  | .bin _ a b => callAllClean ctx s c bound a && callAllClean ctx s c bound b
  | .ifx cond a b => callAllClean ctx s c bound cond && callAllClean ctx s c bound a && callAllClean ctx s c bound b
  | .index a i => callAllClean ctx s c bound a && callAllClean ctx s c bound i
  | .call _ args => callAllClean ctx s c bound args
  | .list items => callAllClean ctx s c bound items
  | .cons a rest => callAllClean ctx s c bound a && callAllClean ctx s c bound rest
  | .letx x rhs body => callAllClean ctx s c bound rhs && callAllClean ctx s c (x :: bound) body
  | .each body x a b => callAllClean ctx s c bound a && callAllClean ctx s c bound b && callAllClean ctx s c (x :: bound) body
  | .slice a lo hi => callAllClean ctx s c bound a && callAllClean ctx s c bound lo && callAllClean ctx s c bound hi
  | .withx a puts => callAllClean ctx s c bound a && callAllClean ctx s c bound puts
  | .record _ items => callAllClean ctx s c bound items
  | .field e _ => callAllClean ctx s c bound e
  | .theNumber _ x a b cond => callAllClean ctx s c bound a && callAllClean ctx s c bound b && callAllClean ctx s c (x :: bound) cond
  | .thePower _ x cond => callAllClean ctx s c (x :: bound) cond

/-- First `.number` argument of `c` in register `r0` (provided no earlier argument shares its name). -/
def callerNumName (c : Contract) (r0 : Nat) : Option String :=
  let rec go (seen : List String) : List (String × Kind) → List Nat → Option String
    | (x, .number) :: args, r :: regs => if r == r0 && !seen.contains x then some x else go (x :: seen) args regs
    | (x, _) :: args, _ :: regs => go (x :: seen) args regs
    | _, _ => none
  go [] c.args c.argRegs

/-- Name of the `j`-th `.bytes` region in `c.regions` (provided no earlier argument shares its name). -/
def callerRegionName (c : Contract) (j : Nat) : Option String :=
  let rec go (seen : List String) : List (String × Kind) → List Nat → Nat → Option String
    | (x, .bytes len) :: args, _ :: regs, k =>
      match c.regOf len with
      | some _ => if k == j && !seen.contains x then some x else go (x :: seen) args regs (k + 1)
      | none => go (x :: seen) args regs k
    | (x, _) :: args, _ :: regs, k => go (x :: seen) args regs k
    | _, _, _ => none
  go [] c.args c.argRegs 0

/-- Map a callee argument `x` to a caller entry expression with the same value at the call. -/
def callArgExpr (ctx : Ctx) (s : Sym) (c : Contract) (x : String) : Option SExpr :=
  let rec go : List (String × Kind) → List Nat → Option SExpr
    | (n, .number) :: args, r :: regs =>
      if n == x then
        match Lin.isConst (s.reg r) with
        | some k => if 0 ≤ k then some (.num k) else none
        | none =>
          (List.range ctx.nreg).findSome? fun r0 =>
            if s.reg r == Lin.var r0 then (callerNumName ctx.contract r0).map .name else none
      else go args regs
    | (n, .bytes len) :: args, r :: regs =>
      if n == x then
        match c.regOf len with
        | some l =>
          match findRun s r l ctx.contract.regions 0 with
          | some j => (callerRegionName ctx.contract j).map .name
          | none => none
        | none => none
      else go args regs
    | _ :: args, _ :: regs => go args regs
    | _, _ => none
  go c.args c.argRegs

/-- Substitute free callee argument names by caller entry expressions (never capturing bound variables). -/
def substCallExpr (ctx : Ctx) (s : Sym) (c : Contract) (bound : List String) : SExpr → Option SExpr
  | .num n => some (.num n)
  | .nil => some .nil
  | .name x =>
    if bound.contains x then some (.name x)
    else match callArgExpr ctx s c x with
      | some (.name y) => if bound.contains y then none else some (.name y)
      | other => other
  | .bin op a b => do pure (.bin op (← substCallExpr ctx s c bound a) (← substCallExpr ctx s c bound b))
  | .ifx cond a b => do pure (.ifx (← substCallExpr ctx s c bound cond) (← substCallExpr ctx s c bound a) (← substCallExpr ctx s c bound b))
  | .index a i => do pure (.index (← substCallExpr ctx s c bound a) (← substCallExpr ctx s c bound i))
  | .call f args => do pure (.call f (← substCallExpr ctx s c bound args))
  | .list items => do pure (.list (← substCallExpr ctx s c bound items))
  | .cons a rest => do pure (.cons (← substCallExpr ctx s c bound a) (← substCallExpr ctx s c bound rest))
  | .letx x rhs body => do pure (.letx x (← substCallExpr ctx s c bound rhs) (← substCallExpr ctx s c (x :: bound) body))
  | .each body x a b => do pure (.each (← substCallExpr ctx s c (x :: bound) body) x (← substCallExpr ctx s c bound a) (← substCallExpr ctx s c bound b))
  | .slice a lo hi => do pure (.slice (← substCallExpr ctx s c bound a) (← substCallExpr ctx s c bound lo) (← substCallExpr ctx s c bound hi))
  | .withx a puts => do pure (.withx (← substCallExpr ctx s c bound a) (← substCallExpr ctx s c bound puts))
  | .record ns items => do pure (.record ns (← substCallExpr ctx s c bound items))
  | .field e f => do pure (.field (← substCallExpr ctx s c bound e) f)
  | .theNumber g x a b cond => do pure (.theNumber g x (← substCallExpr ctx s c bound a) (← substCallExpr ctx s c bound b) (← substCallExpr ctx s c (x :: bound) cond))
  | .thePower g x cond => do pure (.thePower g x (← substCallExpr ctx s c (x :: bound) cond))

/-- Is a callee expression `e` guaranteed to take the same value in any two runs agreeing at this call? -/
def callExprClean (ctx : Ctx) (s : Sym) (c : Contract) (e : SExpr) : Bool :=
  callAllClean ctx s c [] e ||
  match substCallExpr ctx s c [] e with
  | some e' => ctx.contract.traceClean e'
  | none => false

/-- What a called function's contract asks about marks is so at the call: the stack pointer and the
registers of its arguments, but for the numbers its contract says are hidden, are known not to be marked;
each run of bytes it is given to read is one its contract says is hidden (so nothing is asked of its bytes),
or one this function was given to read, whole, that this function's contract does not say is hidden;
a run of a fixed count it reads is one its contract says is hidden, or a part of the frame whose cells are
known not to be marked; and every computed expression in its `trace depends on` line is computed only from
constants and what this function's `trace depends on` line lists. -/
def callQuiet (ctx : Ctx) (s : Sym) (c : Contract) : Bool :=
  c.cleanAtEntry.all s.q.regq.contains &&
  c.fixeds.all (fun x => c.hidden.contains x.1 ||
    -- (or a part of the frame, in whole cells, each of them known not to be marked: a table of addresses made here)
    match frameAt s x.2.1 with
    | some o => decide (x.2.2 % 8 = 0) && (List.range (x.2.2 / 8)).all fun (i : Nat) => s.q.fq.contains (o + 8 * (i : Int))
    | none => false) &&
  (s.q.fq.isEmpty || c.outs.all fun (_, r, n) => decide (r ≠ RSP) && decide (r < ctx.nreg) &&
    ((ctx.contract.outs.any fun (_, b, n0) =>
      match Lin.isConst (Lin.sub (s.reg r) (Lin.var b)) with
      | some k => decide (0 ≤ k) && decide (b < ctx.nreg) && decide (k + n ≤ n0)
      | none => false) ||
     (match frameAt s r with
      | some o => s.q.fq.all fun cell => decide (cell + 8 ≤ o) || decide (o + (n : Int) ≤ cell)
      | none => false))) &&
  c.regions.all (fun (r, l) =>
    c.hiddenAt r ||
      (s.q.regq.contains l &&
        match findRun s r l ctx.contract.regions 0 with
        | some j =>
          match ctx.contract.regions[j]? with
          | some (base, _) => !ctx.contract.hiddenAt base
          | none => false
        | none => false)) &&
  c.traceExprs.all (callExprClean ctx s c)

/-- Is the returned number (register 0) known to depend only on what this caller's `trace depends on` line
lists after calling `c`?
- `returns E`: yes when `E` is clean at the call (`callExprClean`).
- `returns r` with no `result depends on`: yes (`callQuiet` already ensured `c`'s trace inputs are clean).
- `returns r` with `result depends on` (`resultHidden = some rh`): yes when `c.forResult rh` is also quiet at the call. -/
def callReturnsClean (ctx : Ctx) (s : Sym) (c : Contract) : Bool :=
  match c.returns with
  | some e => callExprClean ctx s c e
  | none =>
    if c.resultFollowsTrace then true
    else if c.result.isSome then
      match c.resultHidden with
      | some rh => callQuiet ctx s (c.forResult rh)
      | none => false
    else false

/-- What is known not to be marked after a call: the stack pointer; the number returned, where
`cleanRet` holds; each register a callee keeps that was not marked before; and each cell of the frame
not marked before that is not below the stack pointer. -/
def afterCallQ (cleanRet : Bool) (c : Contract) (s : Sym) : SMarks :=
  { regq := (if cleanRet then [c.retReg, RSP] else [RSP]) ++ s.q.regq.filter c.keeps.contains,
    fq := match s.sp with
      | some sp => s.q.fq.filter fun c => decide (sp ≤ c)
      | none => [] }

/-- The state whose marks a call is judged by: where the called function is given a part of the frame to
write, the cells of the frame that do not lie apart from that part are no longer known not to be marked
(the called function may write marked bytes there). A cell that lies apart from every such part stays. -/
def quietAtCall (s : Sym) (c : Contract) : Sym :=
  let apart (cell : Int) : Bool := c.outs.all fun x =>
    match frameAt s x.2.1 with
    | some o => decide (cell + 8 ≤ o) || decide (o + (x.2.2 : Int) ≤ cell)
    | none => true
  { s with q := { s.q with fq := s.q.fq.filter apart } }

/-- The call is one this function's machine makes, of a function for the same machine: the instruction puts
the address to come back to where the called function's contract has it. On AArch64 the stack pointer is
then a multiple of 16 away from where it was at entry (the called function's contract asks that it be a
multiple of 16, as this function's does of its own entry). -/
def callFits (ctx : Ctx) (s : Sym) (i : Instr) (c : Contract) : Bool :=
  c.arm64 == ctx.contract.arm64 && (callLink i == c.link &&
    (!c.arm64 || match s.sp with
      | some sp => decide (sp % 16 = 0)
      | none => false))

/-- Check whether a tail call to `c` is valid at state `s`: non-self target, same architecture, stack pointer
restored to entry (`sp = 0`) and clean, AArch64 link register restored and clean, every register and
vector register this function promises to preserve restored and also preserved by `c`, no table of lane
addresses, and no callee input or output pointing into this function's dead stack frame. -/
def tailFits (ctx : Ctx) (s : Sym) (name : String) (c : Contract) : Bool :=
  ctx.selfName != some name &&
  c.arm64 == ctx.contract.arm64 &&
  s.sp == some 0 &&
  s.q.regq.contains RSP &&
  (!ctx.contract.arm64 || (s.reg LINK == Lin.var LINK && s.q.regq.contains LINK)) &&
  (ctx.contract.keeps.all fun r => s.reg r == Lin.var r && c.keeps.contains r) &&
  (ctx.contract.keepsVec.all fun v => s.vecIntact.contains v && c.keepsVec.contains v) &&
  c.lanes.isEmpty &&
  c.valArrays.isEmpty &&
  (c.outs.all fun x => (frameAt s x.2.1).isNone) &&
  (c.fixeds.all fun x => (frameAt s x.2.1).isNone)

/-- Entry preconditions at a tail call: callee stack fits with zero extra return-address slot (`extra = 0`),
plus callee `mbounds`, `atLeast`, and `preLines`. -/
def tailPreOk (ctx : Ctx) (s : Sym) (c : Contract) : V Unit := do
  stackFitsMAt ctx s 0 0 c
  callMboundsOk ctx s 0 c
  each (fun (xk : String × Nat) =>
    match c.regOf xk.1 with
    | some rb => entail s.facts (Lin.sub (s.reg rb) (Lin.const xk.2))
    | none => pure ()) c.atLeast
  each (fun (kt : Int × List (String × Int)) =>
    entail s.facts (preLineRow c s.reg kt.1 kt.2)) c.preLines

/-- A tail call: checks `tailFits`, `needsOf`, `symKnow`, `tailPreOk`, `symCall'`, `callQuiet`,
`resultFollowsTrace` on `retReg`, and `symReturn` on the resulting post-call state. -/
def symTail (ctx : Ctx) (s : Sym) (name : String) (c : Contract) : V Unit := do
  if !tailFits ctx s name c then
    refuse "a tail call requires the same machine, sp at entry, preserved registers and link restored and kept by the callee, and no stack-frame operand"
  else do
    needsOf ctx s c
    let s ← symKnow (ctx.advice.call · c) KNOWN s
    tailPreOk ctx s c
    let s' ← symCall' ctx s c
    if !callQuiet ctx (quietAtCall s c) c then
      refuse "at a tail call, something the called function's contract requires to stay out of the trace may depend on values kept out of the trace"
    else
      let cleanRet := if hasSelect ctx.code then c.resultFollowsTrace && callReturnsClean ctx (quietAtCall s c) c
                      else callReturnsClean ctx (quietAtCall s c) c
      let q' := afterCallQ cleanRet c (quietAtCall s c)
      if hasSelect ctx.code && !(ctx.runsCallees.contains name || ctx.selfName == some name) then
        refuse "a function using conditional select can only tail-call helpers without computed `trace depends on` values"
      else if hasSelect ctx.code && ctx.contract.resultFollowsTrace && !cleanRet then
        refuse "at a tail call from a function using conditional select, the called function's result must depend only on values allowed in the trace"
      else if ctx.contract.resultFollowsTrace && !q'.regq.contains ctx.contract.retReg then
        refuse "at a tail call, the returned value may depend on data kept out of the trace"
      else
        symReturn ctx { s' with q := q' }

/-- An instruction: a call, a tail call, or any other instruction by its row's effect. -/
def symNext (ctx : Ctx) (s : Sym) (i : Instr) : V (List (Sym × Next)) :=
  match callTarget i with
  | some name =>
    match ctx.callees.lookup name with
    | none => refuse s!"a call of {name}, which is not a function shown before this one"
    | some c =>
      if !callFits ctx s i c then refuse "a call that is not one this function's machine makes of a function for that machine, or a stack pointer that is not shown to be a multiple of 16 at a call"
      else if hasSelect ctx.code && !(ctx.runsCallees.contains name || ctx.selfName == some name) then
        refuse "a function using conditional select can only call helpers without computed `trace depends on` values"
      else do
      needsOf ctx s c
      let s' ← symCall ctx s name c
      if !callQuiet ctx (quietAtCall s c) c then
        refuse "at a call, something the called function's contract requires to stay out of the trace may depend on values kept out of the trace"
      else
        let cleanRet := if hasSelect ctx.code then c.resultFollowsTrace && callReturnsClean ctx (quietAtCall s c) c
                        else callReturnsClean ctx (quietAtCall s c) c
        pure [({ s' with q := afterCallQ cleanRet c (quietAtCall s c) }, .at i.next)]
  | none =>
    match tailTarget i with
    | some name =>
      match ctx.callees.lookup name with
      | none => refuse s!"a tail call of {name}, which is not a function shown before this one"
      | some c => do
        symTail ctx s name c
        pure []
    | none => symInstr ctx s i

def placeEnv (ctx : Ctx) (p : Place) (value : Nat → Row) : List (String × SVal) :=
  p.names.map (fun (n, r) => (n, SVal.lin (value r))) ++ symEnv ctx.contract

/-- What is known at entry: each register a number below 2^64; the frame the contract allows and the return
address lie in memory; so does each run of bytes given, to read or to write; a number the contract bounds is
below its bound, and one it asks to be no less than another is so; the blocks a table's addresses point to
lie in memory, and end at least 64 bytes below 2^64 (they lie apart from the frame and from the bytes of the
address to return to: so they do where there is such a byte, as there always is on x86-64).
(What is newer comes later: the facts before keep their numbers, by which proofs name them.) -/
def entryFacts (ctx : Ctx) : List Row :=
  ((List.range ctx.nreg).map ranged).flatten ++
  [Lin.sub (Lin.var RSP) (Lin.const ctx.contract.stack), Lin.sub (Lin.const (2 ^ 64 - 1 - (ctx.contract.slot : Int))) (Lin.var RSP)] ++
  (ctx.contract.regions.map fun (base, len) => Lin.sub (Lin.sub (Lin.const (2 ^ 64)) (Lin.var base)) (Lin.var len)) ++
  (ctx.contract.outs.map fun (_, base, n) => Lin.sub (Lin.const (2 ^ 64 - (n : Int))) (Lin.var base)) ++
  (ctx.contract.bounds.filterMap fun (name, b) => (ctx.contract.regOf name).map fun r => Lin.sub (Lin.const ((b : Int) - 1)) (Lin.var r)) ++
  (ctx.contract.fixeds.map fun (_, base, n) => Lin.sub (Lin.const (2 ^ 64 - (n : Int))) (Lin.var base)) ++
  (ctx.contract.atLeast.filterMap fun (name, k) => (ctx.contract.regOf name).map fun r => Lin.sub (Lin.var r) (Lin.const k)) ++
  (ctx.contract.tables.filterMap fun (_, _, count, l) =>
    if 0 < count ∧ 0 < ctx.contract.stack + ctx.contract.slot then some (Lin.sub (Lin.const (2 ^ 64 - 64)) (Lin.scale 64 (Lin.var l))) else none) ++
  (ctx.contract.preLines.map fun (k, ts) => preLineRow ctx.contract Lin.var k ts)

/-- Where the function's file has data: the data's address is a number from 0 up, and the data ends below
2^64. (After the other facts: they keep their numbers.) -/
def dataFacts (ctx : Ctx) : List Row :=
  if ctx.data.isEmpty then []
  else [Lin.var (dataVar ctx), Lin.sub (Lin.const (2 ^ 64 - 1 - (ctx.data.length : Int))) (Lin.var (dataVar ctx))]

/-- Add entry quotient/bound facts `r + el * (l / ch) < 2^64` for every read-only `valArray` argument. -/
def addValArrayFacts (s : Sym) : List (String × Nat × Nat × Nat × Nat) → Sym
  | [] => s
  | (_, r, l, ch, el) :: more =>
    let d := symDivide s (Lin.var l) (ch : Int)
    let s1 := { d.2.2 with facts := Lin.sub (Lin.const top) (Lin.add (Lin.var r) (Lin.scale (el : Int) d.1)) :: d.2.2.facts }
    addValArrayFacts s1 more

def entrySym (ctx : Ctx) : Sym :=
  addValArrayFacts
    { reg := Lin.var, zf := .unknown, cf := .unknown, frame := [], facts := entryFacts ctx ++ dataFacts ctx, bytes := [], spec := [], nvars := ctx.nreg + 1,       -- (the unknown after the registers': where the file's data lies)
      wrote := [], intact := List.range ctx.contract.outs.length,
      vecIntact := ctx.contract.keepsVec,
      q := { regq := ctx.contract.cleanAtEntry ++ ctx.contract.link.toList } }      -- (and the register that holds the address to return to, where one does)
    ctx.contract.valArrays

/-- The state that stands for every coming to the place on a path that first came there in `s`: the kept
registers and the frame as in `s`, every other register any number below 2^64. What `s` knows of the
unknowns it has (its facts, the bytes of the runs given, the values of uses of definitions) is still so:
those unknowns are what they were. -/
def Sym.general (n : Nat) (p : Place) (s : Sym) : Sym :=
  { reg := fun r => if p.keep.contains r then s.reg r else Lin.var (s.nvars + r),
    zf := .unknown, cf := .unknown, frame := s.frame, bytes := s.bytes, spec := s.spec, nvars := s.nvars + n,
    wrote := [],    -- (what was written before a loop is not carried into it yet)
    tab := s.tab,         -- (nor that a run is as it was at entry; what the vector registers hold is said by the place's lanes)
    vecIntact := s.vecIntact,
    known := s.known,
    facts := (((List.range n).filter fun r => !p.keep.contains r).map fun r => ranged (s.nvars + r)).flatten ++ s.facts }

/-! ### What a place says of vector registers -/

/-- The names at a place, on words: a name the place gives is the row of its register; then the contract's. -/
def placeW (ctx : Ctx) (p : Place) (s : Sym) : List (String × WVal) :=
  p.names.map (fun nr => (nr.1, WVal.num (s.reg nr.2))) ++ wenv ctx.contract

/-- The terms the state holds in lane `i` of these vector registers, where it holds one for each. -/
def laneTerms (s : Sym) (i : Nat) : List Nat → Option (List Nat)
  | [] => some []
  | r :: more =>
    match (s.vec.lookup r).bind (·[i]?), laneTerms s i more with
    | some a, some rest => some (a :: rest)
    | _, _ => none

/-- What the place says of lane `i` is so of this state: the words the definition gives, worked out on the
terms, are the terms the registers hold in that lane. (No proof is read here.) -/
def laneShown (ctx : Ctx) (look : Node → Option Nat) (env : List (String × WVal)) (s : Sym) (L : PlaceLanes) (i : Nat) : Bool :=
  match weval ctx look s WFUEL ((L.x, .int i) :: env) (.call L.f L.args) with
  | some (.list l) =>
    match wordIds look l, laneTerms s i L.regs with
    | some ids, some held => ids == held
    | _, _ => false
  | _ => false

/-- Each of some numbers by a thing that may give none. -/
def eachSome (f : Nat → Option Nat) : List Nat → Option (List Nat)
  | [] => some []
  | i :: more =>
    match f i, eachSome f more with
    | some a, some rest => some (a :: rest)
    | _, _ => none

/-- The terms of the sixteen words the place says a cell holds, where each is a term of the table. -/
def cellIds (ctx : Ctx) (look : Node → Option Nat) (env : List (String × WVal)) (s : Sym) (C : PlaceCell) : Option (List Nat) :=
  eachSome (fun i =>
    match weval ctx look s WFUEL ((C.x, .int i) :: env) C.e with
    | some (.word xs) => (idOf look xs).filter fun a => decide (a < s.tab.size)
    | _ => none) (List.range 16)

/-- Where the cell lies: so far above the stack pointer the state holds, counted as the frame's cells are. -/
def cellRow (s : Sym) (C : PlaceCell) : Row := Lin.add (frameOffset (s.reg RSP)) (Lin.const C.off)

/-- What the place says of a cell of the frame is so of this state: the state holds a vector stored there,
and its terms are the words the place says. (No proof is read here.) -/
def cellShown (ctx : Ctx) (p : Place) (s : Sym) (C : PlaceCell) : Bool :=
  match cellIds ctx s.tab.find (placeW ctx p s) s C, s.spill.find? fun (o, _) => o == cellRow s C with
  | some ids, some (_, held) => ids == held
  | _, _ => false

/-- What the place says of a cell of the frame, taken as known of the general state: the cell holds the
words the place says, as terms worked out in that state. -/
def supposeCell (ctx : Ctx) (p : Place) (g : Sym) (C : PlaceCell) : V Sym :=
  match cellIds ctx g.tab.find (placeW ctx p g) g C with
  | some ids => pure { g with spill := (cellRow g C, ids) :: g.spill }
  | none => refuse "what a place says of a cell of the frame is not followed in its general state"

/-- What the place says of vector registers is so of this state, lane by lane. -/
def lanesShown (ctx : Ctx) (p : Place) (s : Sym) (L : PlaceLanes) : Bool :=
  (List.range 16).all fun i => laneShown ctx s.tab.find (placeW ctx p s) s L i

/-- The things the place's definition is used with in lane `i`, as keys: in the state `g`. -/
def laneKey (ctx : Ctx) (look : Node → Option Nat) (env : List (String × WVal)) (g : Sym) (L : PlaceLanes) (i : Nat) : Option (List Key) :=
  match wevalList (weval ctx look g WFUEL ((L.x, .int i) :: env)) L.args with
  | some vs =>
    match flatKeys look vs with
    | some keys => if keys.all (Key.ok g.nvars g.tab.size) then some keys else none
    | none => none
  | none => none

def laneKeysOf (key : Nat → Option (List Key)) : List Nat → Option (List (List Key))
  | [] => some []
  | i :: more =>
    match key i, laneKeysOf key more with
    | some k, some ks => some (k :: ks)
    | _, _ => none

/-- The state with what a place says of vector registers taken as known. Each word of each lane is a new
unknown: with `m` registers, the unknown `g.nvars + m * i + k` is the word in lane `i` of the `k`-th of
them. The registers hold those words, and the definition, used with the things of each lane (`keys`: lane
by lane), is known to be that lane's words. (No fact is added of the unknowns: they are used as words only.) -/
def Sym.withLanes (g : Sym) (L : PlaceLanes) (keys : List (List Key)) : Sym :=
  let m := L.regs.length
  let made := termsOf wAtom ((List.range (16 * m)).map fun u => Lin.var (g.nvars + u)) g.tab
  { g with
    nvars := g.nvars + 16 * m, tab := made.2,
    vec := ((List.range m).map fun k => (L.regs.getD k 0, (List.range 16).map fun i => made.1.getD (m * i + k) 0)) ++ g.vec,
    known := ((List.range 16).map fun i => Known.held L.f (keys.getD i []) ((List.range m).map fun k => made.1.getD (m * i + k) 0)) ++ g.known }

/-- What the place says of vector registers, taken as known of the general state. -/
def supposeLanes (ctx : Ctx) (p : Place) (g : Sym) (L : PlaceLanes) : V Sym :=
  if L.f == "len" || own.contains L.f then refuse "a place's lanes are said by a definition of the specification"
  else
    match laneKeysOf (laneKey ctx g.tab.find (placeW ctx p g) g L) (List.range 16) with
    | some keys => pure (g.withLanes L keys)
    | none => refuse "what a place says of vector registers is not followed in its general state"

/-- The boundary already held for the run `w` with the list `f(vs)` by an earlier coming to the place; where
nothing is held of that, `0` for a prefix range or `hi` for a suffix range. -/
def rangeBase (s : Sym) (w : Nat) (f : String) (vs : List SVal) (hi : Nat) (fromStart : Bool) : Row :=
  match s.range with
  | some rg => if rg.w == w && rg.f == f && rg.args == vs && rg.fromStart == fromStart then rg.lo
               else if fromStart then Lin.const 0 else Lin.const hi
  | none => if fromStart then Lin.const 0 else Lin.const hi

/-- The most places a place's range may grow by at one coming there. -/
def GROW : Int := 64

/-- What the place says a loop has written is so of this state: the places in the prefix (`0..lo`) or suffix
(`lo..hi`) not already held written by an earlier coming (`Sym.range`) are known written, each with the
list's thing. -/
def rangeShown (ctx : Ctx) (p : Place) (s : Sym) : V (Option RangeF × Sym) :=
  match p.wrote with
  | none => pure (none, s)
  | some (run, lo, f, args, fromStart) =>
    match findOutNamed run ctx.contract.outs 0 with
    | none => refuse "a place says what is written of what is no run given to write"
    | some (w, n) => do
      let env := placeEnv ctx p s.reg
      let (lo, s) ← seval ctx env s lo
      let (lo, s) ← numberV (opener ctx DEEP) s lo
      let (vs, s) ← seval ctx env s args
      match vs with
      | .list vs =>
        match eachOf ctx f vs.length with
        | none => refuse "a place says what is written by what is no list made thing by thing from 0 on"
        | some (params, x, b, hi) =>
          if n < hi then refuse "a place says more is written than the run has places"
          else do
            entail s.facts lo
            let base := rangeBase s w f vs hi fromStart
            let diff := if fromStart then Lin.sub lo base else Lin.sub base lo
            let start := if fromStart then base else lo
            match Lin.isConst diff with
            | some k =>
              if k < 0 || GROW < k then refuse "a place: what is written does not reach from where the place says"
              else do
                let s ← filled ctx (params.zip vs) x b w start 0 k.toNat s
                pure (some ⟨w, lo, f, vs, fromStart⟩, s)
            | none => refuse "a place: where the written places begin is not known by a number from where they began before"
      | _ => refuse "a place: a definition used with what is no list of things"

/-- In the state that stands for every coming to the place: what the place says a loop has written is taken
as known. -/
def supposeRange (ctx : Ctx) (p : Place) (g : Sym) : V Sym :=
  match p.wrote with
  | none => pure g
  | some (run, lo, f, args, fromStart) =>
    match findOutNamed run ctx.contract.outs 0 with
    | none => refuse "a place says what is written of what is no run given to write"
    | some (w, _) => do
      let env := placeEnv ctx p g.reg
      let (lo, g) ← seval ctx env g lo
      let (lo, g) ← numberV (opener ctx DEEP) g lo
      let (vs, g) ← seval ctx env g args
      match vs with
      | .list vs => pure { g with range := some ⟨w, lo, f, vs, fromStart⟩ }
      | _ => refuse "a place: a definition used with what is no list of things"

/-- On first coming to the place: what holds there is shown of this state; then the state that stands for
every coming there, of which the place's facts are taken as known, and its number that decreases, which is
shown to be no less than zero. Given back with them: the state as it first came, with which every later
coming is compared. -/
def generalize (ctx : Ctx) (p : Place) (s : Sym) : V (Sym × Row × Sym) :=
  if !p.keep.contains RSP || p.names.any (fun (_, r) => decide (ctx.nreg ≤ r)) || (!p.cells.isEmpty && !ctx.contract.valArrays.isEmpty) then
    refuse "a place must keep the stack pointer, and name registers"
  else do
    let s ← fold (establish ctx (placeEnv ctx p s.reg)) s p.facts
    if !(p.lanes.all (lanesShown ctx p s)) then refuse s!"at the place {p.pc} the vector registers are not shown to hold what the place says"
    else if !(p.cells.all (cellShown ctx p s)) then refuse s!"at the place {p.pc} a cell of the frame is not shown to hold what the place says"
    else do
      let (_, s) ← rangeShown ctx p s
      let g ← fold (suppose ctx (placeEnv ctx p (s.general ctx.nreg p).reg)) (s.general ctx.nreg p) p.facts
      let g ← fold (supposeLanes ctx p) g p.lanes
      let g ← fold (supposeCell ctx p) g p.cells
      let g ← supposeRange ctx p g
      let (d, g) ← seval ctx (placeEnv ctx p (s.general ctx.nreg p).reg) g p.decreases
      match d with
      | .val (.lin d) => do
        entail g.facts d
        pure (g, d, s)
      | _ => refuse "a place's number that decreases is no number"

/-- On coming to the place again: this state is one the general state stands for (it keeps what the first
coming had in the kept registers and the frame, and the place's facts are shown of it), and the number is
less than `d`, the number of the general state the path began in. -/
def arrive (ctx : Ctx) (p : Place) (first : Sym) (d : Row) (s : Sym) : V Unit :=
  match p.keep.find? fun r => s.reg r != first.reg r with
  | some r => refuse s!"at the place {p.pc} register {r} does not hold what it held on first coming there"
  | none =>
  if !(first.q.regq.all s.q.regq.contains) then refuse s!"at the place {p.pc} register {(first.q.regq.find? fun r => !s.q.regq.contains r).getD 0} may depend on values kept out of the trace, which it did not on first coming there"
  else
  if !(first.q.fq.all s.q.fq.contains) then refuse s!"at the place {p.pc} stack slot {(first.q.fq.find? fun c => !s.q.fq.contains c).getD 0} may depend on values kept out of the trace, which it did not on first coming there"
  else
  if !(first.frame.all fun cell => s.frame.contains cell) then refuse "at the place the frame does not hold what it held on first coming there"
  else if !(first.vecIntact.all s.vecIntact.contains) then refuse "at the place a callee-saved vector register was modified in the loop"
  else do
    let s1 ← fold (establish ctx (placeEnv ctx p s.reg)) s p.facts
    if !(p.lanes.all (lanesShown ctx p s1)) then refuse s!"at the place {p.pc} the vector registers are not shown to hold what the place says, on coming there again"
    else if !(p.cells.all (cellShown ctx p s1)) then refuse s!"at the place {p.pc} a cell of the frame is not shown to hold what the place says, on coming there again"
    else do
      let (_, s1) ← rangeShown ctx p s1
      let (d', s2) ← seval ctx (placeEnv ctx p s.reg) s1 p.decreases
      match d' with
      | .val (.lin d') => entail s2.facts (Lin.sub (Lin.sub d d') (Lin.const 1))
      | _ => refuse "a place's number that decreases is no number"

/-- A place a path has come to: the place, the number of its general state, and the state as the path first
came there. -/
structure Seen where
  place : Place
  d : Row
  first : Sym

/-- A join place already verified in the current scope, with the scope-bounded snapshot `first` shared by all
paths arriving there. -/
structure JoinEntry where
  place : Place
  first : Sym

/-- Of the registers known not to be marked on first coming to a place, those the place does not say may be
marked on a later coming (using `markedResult` during the second pass for `result depends on`). -/
def placeQuiet (ctx : Ctx) (p : Place) (regq : List Nat) : List Nat :=
  let m := if ctx.resultPass then p.markedResult else p.marked
  regq.filter fun r => !m.contains r

/-- Build the scope-bounded snapshot `first` for a join place `p` from the enclosing scope's `base` state and
the first arriving path state `s`. All kept registers and retained frame cells are checked to refer solely to
unknowns already in `base` (`< base.nvars`), so `first` never leaks branch-specific facts or variables from
the first arriving path to sibling paths. -/
def joinFirst (ctx : Ctx) (base s : Sym) (p : Place) : Option Sym :=
  let keptOk := p.keep.all fun r => decide (r < ctx.nreg) && decide ((s.reg r).coeff.length ≤ base.nvars)
  if !keptOk || !p.keep.contains RSP || p.names.any (fun (_, r) => decide (ctx.nreg ≤ r)) ||
     (!p.cells.isEmpty && !ctx.contract.valArrays.isEmpty) then none
  else
    let fr := s.frame.filter fun (_, v) => decide (v.coeff.length ≤ base.nvars)
    let regq := placeQuiet ctx p s.q.regq
    let fq := s.q.fq.filter fun o => fr.any fun c => c.1 == o
    some { base with
      reg := fun r => if p.keep.contains r then s.reg r else base.reg r,
      frame := fr,
      vecIntact := base.vecIntact.filter s.vecIntact.contains,
      q := { regq := regq, fq := fq } }

/-- Check that an arriving state `s` at join place `p` satisfies the shared snapshot `first` and every
assertion of `p` (no `decreases` check: join places are acyclic). -/
def arriveJoin (ctx : Ctx) (p : Place) (first : Sym) (s : Sym) : V Unit :=
  match p.keep.find? fun r => s.reg r != first.reg r with
  | some r => refuse s!"at the join place {p.pc} register {r} does not hold what it held on first coming there"
  | none =>
  if !(first.q.regq.all s.q.regq.contains) then refuse s!"at the join place {p.pc} register {(first.q.regq.find? fun r => !s.q.regq.contains r).getD 0} may depend on values kept out of the trace, which it did not on first coming there"
  else
  if !(first.q.fq.all s.q.fq.contains) then refuse s!"at the join place {p.pc} stack slot {(first.q.fq.find? fun c => !s.q.fq.contains c).getD 0} may depend on values kept out of the trace, which it did not on first coming there"
  else
  if !(first.frame.all fun cell => s.frame.contains cell) then refuse "at the join place the frame does not hold what it held on first coming there"
  else if !(first.vecIntact.all s.vecIntact.contains) then refuse "at the join place a callee-saved vector register was modified"
  else do
    let s1 ← fold (establish ctx (placeEnv ctx p s.reg)) s p.facts
    if !(p.lanes.all (lanesShown ctx p s1)) then refuse s!"at the join place {p.pc} the vector registers are not shown to hold what the place says"
    else if !(p.cells.all (cellShown ctx p s1)) then refuse s!"at the join place {p.pc} a cell of the frame is not shown to hold what the place says"
    else do
      let (_, _) ← rangeShown ctx p s1
      pure ()

/-- Generalize a join place `p` directly from its scope-bounded snapshot `first` (independent of any
particular arriving path). -/
def generalizeJoin (ctx : Ctx) (p : Place) (first : Sym) : V Sym := do
  let g ← fold (suppose ctx (placeEnv ctx p (first.general ctx.nreg p).reg)) (first.general ctx.nreg p) p.facts
  let g ← fold (supposeLanes ctx p) g p.lanes
  let g ← fold (supposeCell ctx p) g p.cells
  supposeRange ctx p g

/-- Thread state `acc` across every element of a list. -/
def eachState {α β : Type} (f : β → α → V β) : β → List α → V β
  | acc, [] => pure acc
  | acc, x :: more => do
    let acc' ← f acc x
    eachState f acc' more

/-- Peek for a `clear` item for the current `pc` sitting next in the proof stream. -/
def popClear (pc : Nat) : V (Option (Nat × SExpr)) := fun items =>
  match items.line items.next with
  | some (.clear atPc r e) =>
    if atPc == pc then .ok (some (r, e), { items with next := items.next + 1 })
    else .ok (none, items)
  | _ => .ok (none, items)

/-- Prove that register `r` equals specification expression `e` (evaluated in `symEnv ctx.contract`) and
that `e` is computed only from what `ctx.contract`'s `trace depends on` line lists; then mark `r` clean. -/
def symRevealReg (ctx : Ctx) (s : Sym) (r : Nat) (e : SExpr) : V Sym :=
  if !(r < ctx.nreg) then refuse "a trace-clear step names a register out of range"
  else if ctx.contract.traceExprs.isEmpty then
    refuse "a trace-clear step requires a computed value listed in `trace depends on`"
  else if !ctx.contract.traceClean e then
    refuse "a trace-clear step names an expression that may depend on values kept out of the trace"
  else do
    let (res, s1) ← seval ctx (symEnv ctx.contract) s e
    match res with
    | .val (.lin v) => do
      entail s1.facts (Lin.sub v (s1.reg r))
      entail s1.facts (Lin.sub (s1.reg r) v)
      pure { s with q := { s.q with regq := r :: s.q.regq } }
    | .tail c => do
      let _ ← specGoal ctx 16 s1 (.value c (s1.reg r))
      pure { s with q := { s.q with regq := r :: s.q.regq } }
    | _ => refuse "a trace-clear step names an expression that is not a number"

def CLEARS : Nat := 16

/-- Consume any `clear` items for `pc` sitting next in the proof stream. -/
def symClears (ctx : Ctx) (pc : Nat) : Nat → Sym → V Sym
  | 0, s => pure s
  | fuel + 1, s => do
    match ← popClear pc with
    | none => pure s
    | some (r, e) => do
      let s' ← symRevealReg ctx s r e
      symClears ctx pc fuel s'

/-- Where a path goes on after an instruction. At the function's return it ends. At an acyclic join place,
first arrival verifies the shared tail once from the scope-bounded generalized state and records the join in
`jdone`; every subsequent sibling path only checks `arriveJoin` and stops. At a loop place, first arrival
inducts on `decreases` with a fresh inner join scope, and a back-edge checks `arrive`. -/
def onward (ctx : Ctx) (base : Sym) (seen : List Seen) (jstack : List Nat)
    (go : Sym → List Seen → List Nat → List JoinEntry → Sym → Nat → V (List JoinEntry))
    (jdone : List JoinEntry) (next : Sym × Next) : V (List JoinEntry) :=
  match next.2 with
  | .returned => pure jdone
  | .at pc' =>
    match ctx.places.find? (fun p => p.pc == pc') with
    | none => go base seen jstack jdone next.1 pc'
    | some p =>
      if p.isJoin then
        if jstack.contains pc' then
          refuse s!"at the join place {pc'} a path returns to it (add `decreases` for a loop)"
        else
          match jdone.find? (fun e => e.place.pc == pc') with
          | some e => do
            arriveJoin ctx e.place e.first next.1
            pure jdone
          | none =>
            match joinFirst ctx base next.1 p with
            | none =>
              refuse (match p.keep.find? fun r => !(decide (r < ctx.nreg) && decide ((next.1.reg r).coeff.length ≤ base.nvars)) with
                | some r => s!"at the join place {pc'} register {r} depends on a value not in scope"
                | none => s!"at the join place {pc'} a kept register depends on a value not in scope")
            | some first => do
              arriveJoin ctx p first next.1
              let g ← generalizeJoin ctx p first
              let jdone' ← go base seen (pc' :: jstack) jdone { g with q := { regq := first.q.regq, fq := first.q.fq } } pc'
              pure (⟨p, first⟩ :: jdone')
      else
        match seen.find? (fun e => e.place.pc == pc') with
        | some e => do
          arrive ctx e.place e.first e.d next.1
          pure jdone
        | none => do
          let (g, d, first) ← generalize ctx p next.1
          -- (what is known not to be marked at the place: the registers that are not on this first coming,
          -- minus those the place says may be on a later one, plus the clean frame slots kept across the loop)
          let q0 : SMarks := { regq := placeQuiet ctx p next.1.q.regq, fq := next.1.q.fq }
          let g0 := { g with q := q0 }
          let _ ← go g0 (⟨p, d, { first with q := q0 }⟩ :: seen) [] [] g0 pc'
          pure jdone

/-- Every path from `pc`: each to the function's return, a previously verified join place, or an enclosing
loop place. Returns the updated list of join places verified in the current scope `base`. -/
def explore (ctx : Ctx) : Nat → Sym → List Seen → List Nat → List JoinEntry → Sym → Nat → V (List JoinEntry)
  | 0, _, _, _, _, _, _ => refuse "a path longer than the verifier goes"
  | fuel + 1, base, seen, jstack, jdone, s, pc =>
    match ctx.code.lookup pc with
    | none => refuse s!"no instruction at {pc}"
    | some i => do
      let s ← symClears ctx pc CLEARS s
      let nexts ← symNext ctx s i
      eachState (onward ctx base seen jstack (explore ctx fuel)) jdone nexts

def PATH : Nat := 100000

/-- The verifier. -/
def verify (ctx : Ctx) : V Unit := do
  let s0 := entrySym ctx
  let _ ← explore ctx PATH s0 [] [] [] s0 0
  if ← finished then pure () else refuse "the proof says more than is asked of it"

/-- Does the contract's `stackBits` (if any) have a positive divisor and an argument listed in `trace depends on`? -/
def Contract.stackBitsOk (c : Contract) : Bool :=
  match c.stackBits with
  | none => true
  | some sb => decide (0 < sb.div) &&
    match c.regOf sb.arg with
    | some r => c.cleanAtEntry.contains r
    | none => false

/-- Does the contract's `decreases` (if any) name a parameter listed in `trace depends on`? -/
def Contract.decreasesOk (c : Contract) : Bool :=
  match c.decreases with
  | none => true
  | some d =>
    match c.regOf d with
    | some r => c.cleanAtEntry.contains r
    | none => false

/-- One verification pass. `none`: yes. -/
def verdictOne (ctx : Ctx) (proof : List Item) : Option String :=
  if !ctx.contract.callingOk then
    some "refused: invalid custom calling convention (register out of range, duplicate, RSP/LINK, or return register preserved)"
  else if !ctx.contract.stackBitsOk then
    some "refused: stack bits argument must be a parameter listed in `trace depends on` with a positive divisor"
  else if !ctx.contract.decreasesOk then
    some "refused: `decreases` argument must be a parameter listed in `trace depends on`"
  else if hasSelect ctx.code && !ctx.contract.traceExprs.isEmpty then
    some "refused: conditional select cannot be combined with computed `trace depends on` values"
  else match verify ctx (Items.ofList proof) with
  | .ok _ => none
  | .error why => some why

/-- Does the function meet its contract, by this proof? `none`: yes.
Where the contract has `result depends on` (`resultHidden = some rh`), runs a second pass against
`c.forResult rh` to verify the returned number depends only on `trace depends on` and `result depends on`. -/
def verdict (ctx : Ctx) (proof : List Item) : Option String :=
  match verdictOne ctx proof with
  | some why => some why
  | none =>
    match ctx.contract.resultHidden with
    | none => none
    | some rh =>
      if !rh.all ctx.contract.hidden.contains then
        some "result depends on: arguments kept out of the result must be a subset of those kept out of the trace"
      else if !ctx.contract.result.isSome then
        some "result depends on requires a named return value"
      else
        match verdictOne { ctx with contract := ctx.contract.forResult rh, resultPass := true } proof with
        | none => none
        | some why => some s!"for `result depends on`: {why}"

/-- A function of a statement: its name, its instructions and its contract; the object file it is of, by
number, where it takes an address in that file's read-only data; and, the maker's, its places and its proof. -/
structure Fn where
  name : String
  code : List (Nat × Instr) := []
  contract : Contract := { args := [], returns := none, stack := 0 }
  piece : Option Nat := none
  places : List Place := []
  proof : List Item := []

/-- Does this function qualify for single-run `Runs` tracking (and thus as a callee of functions using `cmov`/`csel`)? -/
def fnRunsCapable (f : Fn) : Bool :=
  f.contract.traceExprs.isEmpty && (hasSelect f.code || !hasCallOrTail f.code)

/-- The functions one after another, `done` being those already shown, each with its contract. A call is
taken by the contract of a function already shown, and by nothing else: so no function calls itself, or
one that calls it, or one that is not in the statement. -/
def verdictFrom (pieces : List Piece) (defs : List Def) : List (String × Contract) → List Fn → Option String :=
  go []
where
  go (runsOk : List String) : List (String × Contract) → List Fn → Option String
  | _, [] => none
  | done, f :: more =>
    if done.any (fun d => d.1 == f.name) then some s!"refused: two functions are named {f.name}"
    else
      let callees := if f.contract.decreases.isSome then (f.name, f.contract) :: done else done
      let selfName := if f.contract.decreases.isSome then some f.name else none
      match verdict { code := f.code, contract := f.contract, defs := defs, places := f.places, callees := callees,
                      selfName := selfName, pieces := pieces, piece := f.piece, runsCallees := runsOk } f.proof with
      | some why => some s!"{why}\nin {f.name}"
      | none =>
        let runsOk' := if fnRunsCapable f then f.name :: runsOk else runsOk
        go runsOk' ((f.name, f.contract) :: done) more

/-- Do the functions of a statement meet their contracts, by these proofs? `none`: yes, every one. (`pieces`:
the read-only data of the object files the functions are of.) -/
def verdictAll (pieces : List Piece) (defs : List Def) (fns : List Fn) : Option String := verdictFrom pieces defs [] fns

end Ode
