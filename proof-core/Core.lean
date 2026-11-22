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
  | know (g : Row)                                  -- a row for the verifier to show from the facts, and then to keep among them
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
  | none => facts.any fun f => Lin.sameCoeff g.coeff f.coeff && decide (f.constant ≤ g.constant)

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
  | add (xs : List Nat)         -- the terms of these numbers summed, wrapping
  | xor (a b : Nat)
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
  | .add xs => xs
  | .xor a b => [a, b]
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

def insertSorted (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insertSorted a l

/-- A row with each of its numbers reduced to the remainder by 2^32: as a word it is the same word. -/
def Lin.word (r : Row) : Row := ⟨Lin.strip (r.coeff.map (· % W32i)), r.constant % W32i⟩

/-- The row of the quotients by 2^32: `r` is `Lin.word r` and 2^32 times this. -/
def Lin.high (r : Row) : Row := ⟨Lin.strip (r.coeff.map (· / W32i)), r.constant / W32i⟩

/-- The row has, as it is written, a part that is a multiple of 2^32: a low word and something above it. -/
def Lin.hasHigh (r : Row) : Bool := r.coeff.any fun c => c != 0 && c % W32i == 0

def wAtom (r : Row) (t : Tab) : Nat × Tab := intern (.atom (Lin.word r)) t

/-- What a term is a sum of: itself, or the terms it sums. -/
def addends (t : Tab) (a : Nat) : List Nat :=
  match t.arr[a]? with
  | some (.add xs) => xs
  | _ => [a]

def wAdd (a b : Nat) (t : Tab) : Nat × Tab :=
  intern (.add ((addends t a ++ addends t b).foldr insertSorted [])) t

def wXor (a b : Nat) (t : Tab) : Nat × Tab := intern (.xor (min a b) (max a b)) t

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

/-- What is known beyond the facts. -/
inductive Known where
  | load (v j c : Nat)            -- the unknown `v` is the eight bytes at place `c` of the run `j` (of a fixed count, given to read) as they were at entry: one number, the lowest byte first
  | or (v : Nat) (x y : Row)      -- the unknown `v` is `x | y`: the bits of both
  | held (f : String) (keys : List Key) (ids : List Nat)    -- the definition `f`, used with these things, is the list of the words of these terms
  | heldB (f : String) (keys : List Key) (ids : List Nat)   -- the definition `f`, used with these things, is the list of the bytes of the words of these terms, four a word, the lowest first
  | div (x : Row) (m : Int) (q : Nat)   -- the unknown `q` is `x` divided by `m` (a number above zero) rounded down, and the unknown after it is the remainder
  | block (j c : Nat) (off : Row) (vs : List Nat)   -- the sixteen unknowns `vs` are the sixteen words at byte `off` of the blocks that the address at place `c` of the table `j` points to, as they were at entry
  | use (f : String) (keys : List Key) (h : Nat)    -- the definition `f`, used with these things, gives something; `h` is that use's own number (an unknown's number, which no row speaks of)
  deriving DecidableEq, Repr, Inhabited

/-- What is known NOT to be marked (not to depend on a secret): general registers, the two flags, and
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
  wroteW : List (Nat × Nat × Nat) := []   -- (run given to write, which word of it, the term): that word of that run now holds that term
  spill : List (Row × List Nat) := []  -- the aligned vector spills still known: each one's entry-relative offset and lane terms
  known : List Known := []        -- what is known of numbers that are no rows
  q : SMarks := {}                -- what is known not to be marked
  range : Option RangeF := none   -- what a place says a loop has written so far, where one says so
  stackAt : Option (Row × List (Int × Row) × List (Row × List Nat)) := none   -- the stack pointer, the frame's cells and the spills as they were when `settle` last showed the stack's facts: advice, and nothing rests on it
  deriving Inhabited

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
  marked : List Nat := []         -- registers that may depend on a secret on a later coming there (they need not on the first)
  wrote : Option (String × SExpr × String × SExpr) := none
                                  -- (run, lo, f, args): from the place `lo` on, the run given to write holds the list `f(args)`, place by place
  deriving Inhabited

/-- What a prover's helper may say where a proof that is still being written has run out: the rows it
would try to show next, before an `ensures` of a run of words and before a call. The verifier's program
gives none. Nothing is concluded from these rows: they are only printed (`popKnow`). -/
structure Advice where
  ensures : Sym → EnsureW → List Row := fun _ _ => []
  call : Sym → Contract → List Row := fun _ _ => []
  deriving Inhabited

structure Ctx where
  code : List (Nat × Instr)
  contract : Contract
  defs : List Def
  places : List Place := []                     -- the maker's: where the paths of loops are cut
  callees : List (String × Contract) := []      -- the functions this one calls, each with its contract
  advice : Advice := {}                         -- a prover's helper's; the verifier's program leaves it empty
  deriving Inhabited

def symEnvIn (c : Contract) : List (String × Kind) → List Nat → Nat → List (String × SVal)
  | (n, .number) :: args, r :: regs, k => (n, .lin (Lin.var r)) :: symEnvIn c args regs k
  | (n, .bytes len) :: args, _ :: regs, k =>
    match c.regOf len with
    | some _ => (n, .region k) :: symEnvIn c args regs (k + 1)
    | none => symEnvIn c args regs k
  | (_, .out _) :: args, _ :: regs, k => symEnvIn c args regs k
  | (_, .fixed _) :: args, _ :: regs, k => symEnvIn c args regs k
  | (_, .inout _) :: args, _ :: regs, k => symEnvIn c args regs k
  | _, _, _ => []

/-- The contract's names on symbols: a number is its register at entry; a run of bytes is a run by its number. -/
def symEnv (c : Contract) : List (String × SVal) := symEnvIn c c.args argRegs 0

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

/-- The byte at place `o` of run `r`: shown to be within the run; one unknown for one place. -/
def readByte (ctx : Ctx) (s : Sym) (r : Nat) (o : Row) : V (Row × Sym) :=
  match ctx.contract.regions[r]? with
  | none => refuse "no such run of bytes"
  | some (_, len) => do
    entail s.facts o
    entail s.facts (Lin.sub (Lin.sub (Lin.var len) o) (Lin.const 1))
    match lookupByte r o s.bytes with
    | some v => pure (Lin.var v, s)
    | none =>
      pure (Lin.var s.nvars, { s with nvars := s.nvars + 1, bytes := (s.nvars, r, o) :: s.bytes,
                                      facts := Lin.var s.nvars :: Lin.sub (Lin.const 255) (Lin.var s.nvars) :: s.facts })

inductive Where where
  | frame (off : Int)
  | region (r : Nat) (off : Row)
  | out (w : Nat) (off : Row)
  | data (off : Int)              -- so many bytes into the file's read-only data

/-- The unknown that is where the file's read-only data lies. (Unknowns 0 to 15 are the registers at entry.) -/
def dataVar : Nat := 16

/-- How many bytes into the file's data an address is, where the contract has data and the address is the
data's plus a number. -/
def dataOff (ctx : Ctx) (addr : Row) : Option Int :=
  if ctx.contract.data.isEmpty then none else Lin.isConst (Lin.sub addr (Lin.var dataVar))

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
    if (size = 1 ∨ size = 4 ∨ size = 8) ∧ 0 ≤ c ∧ c + size ≤ ctx.contract.data.length then
      pure (.lin (Lin.const (dataWord ctx.contract.data c.toNat size)), s)
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
  match Lin.isConst y, smallBits facts x with
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
    -- a shift to the left by a number of the table: so many doublings of what stays below 2^64, which is
    -- the number itself where it is shown to be small enough, else its remainder (the proof says which)
    match Lin.isConst y with
    | some k =>
      if 0 ≤ k ∧ k < 64 then do
        let kept ← staysBelow s.facts x (2 ^ (64 - k.toNat))
        if kept then pure (.lin (Lin.scale (2 ^ k.toNat) x), s)
        else pure (.lin (Lin.scale (2 ^ k.toNat) (symLow s x (2 ^ (64 - k.toNat))).1), (symLow s x (2 ^ (64 - k.toNat))).2)
      else refuse "a shift by 64 or more"
    | none => refuse "a shift by what is no number of the table: not here yet"
  else if f == "shr64" then
    -- a shift to the right by a number of the table: the quotient by so many doublings
    match Lin.isConst y with
    | some k =>
      if 0 ≤ k ∧ k < 64 then pure (.lin (symDivide s x (2 ^ k.toNat)).1, (symDivide s x (2 ^ k.toNat)).2.2)
      else refuse "a shift by 64 or more"
    | none => refuse "a shift by what is no number of the table: not here yet"
  else if f == "and64" then
    match Lin.isConst y with
    | some m =>
      if m == 2 ^ 64 - 64 then
        -- Round down to a 64-byte boundary, keeping the quotient explicit.
        let d := symDivide s x 64
        pure (.lin (Lin.scale 64 d.1), d.2.2)
      else
        -- A mask of low bits takes the remainder by a power of two.
        match (List.range 65).find? (fun k => (2 : Int) ^ k - 1 == m) with
        | some k => pure (.lin (symDivide s x (2 ^ k)).2.1, (symDivide s x (2 ^ k)).2.2)
        | none => refuse "no proof rule for this AND mask"
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

/-- `data(I)`, the address of a place in the file's read-only data: the unknown that is the data's address,
plus `I`, where `I` is a number within the data the contract has. -/
def symData (ctx : Ctx) (s : Sym) (x : Row) : V (EV × Sym) :=
  match Lin.isConst x with
  | some c =>
    if 0 ≤ c ∧ c < ctx.contract.data.length then pure (.lin (Lin.add (Lin.var dataVar) (Lin.const c)), s)
    else refuse "the address of a place that is not in the file's read-only data (or the contract has no data)"
  | none => refuse "the address of a place in the file's data that is no number"

def symValue (ctx : Ctx) (bind : Bind) : Sym → Expr → V (EV × Sym)
  | s, .number n => if n < 2 ^ 64 then pure (.lin (Lin.const n), s) else refuse "a number of the table that is no 64-bit number"
  | _, .lane _ _ => refuse "a vector register: not here yet"
  | s, .name n =>
    if isNumberLetter n then
      match (bind.lookup n).bind readInt with
      | some i => pure (.lin (Lin.const (i % (M64 : Int))), s)
      | none => refuse "a number that cannot be read"
    else match regOf bind n with
      | some r => pure (.lin (s.reg r), s)
      | none => refuse s!"no rule for {n}"
  | s, .call f [a] => do
    let (x, s) ← symValue ctx bind s a
    match x with
    | .lin x => if f == "data" then symData ctx s x else symPrim1 f s x
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
def symReg (bind : Bind) (s : Sym) : Expr → Option Row
  | .name n => if isNumberLetter n then none else (regOf bind n).map s.reg
  | _ => none

/-- A term for each thing of a list, made one after another: their numbers, and the table then. -/
def termsOf {α : Type} (mk : α → Tab → Nat × Tab) : List α → Tab → List Nat × Tab
  | a :: as, t => ((mk a t).1 :: (termsOf mk as (mk a t).2).1, (termsOf mk as (mk a t).2).2)
  | [], t => ([], t)

/-- The runs whose words are terms (`Node.input`), by their numbers: the runs of a fixed count given to
read, then those given to read and write, then the runs of bytes with a length (each with the register its
address is in; no name, no count). -/
def Contract.wordRuns (c : Contract) : List (String × Nat × Nat) :=
  c.fixeds ++ c.inouts ++ c.regions.map fun rl => ("", rl.1, 0)

/-- Which run of words is at the address a register held at entry. -/
def runAt (r : Nat) : List (String × Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (_, r', _) :: more, j => if r' = r then some j else runAt r more (j + 1)

/-- Read words at a fixed offset divisible by four. They must lie in a read-only run or a read/write run
that has not been written since entry. -/
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
    | _ => refuse s!"{bytes} bytes that are of no run of words given to read"

/-- An unscaled address consists of a base register, a displacement and an optional index register. -/
def symWordAddr (bind : Bind) (s : Sym) : List Expr → Option Row
  | [b, n] => do
    let x ← symReg bind s b
    let k ← symNumber bind n
    some (Lin.add (signed x) (signed (Lin.const k)))
  | [b, n, i] => do
    let x ← symReg bind s b
    let k ← symNumber bind n
    let y ← symReg bind s i
    some (Lin.add (Lin.add (signed x) (signed (Lin.const k))) (signed y))
  | _ => none

def symMemWords (ctx : Ctx) (bind : Bind) (s : Sym) (args : List Expr) (width : Nat) : V (List Nat × Sym) :=
  match symWordAddr bind s args with
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
            else if op == "or32" then
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
        match symReg bind s a with
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
  pure { s with spill := [], range := none }

/-- Two aligned 64-byte cells of the frame that are known not to overlap: their offsets differ by a
number alone, of 64 or more. -/
def cellsApart (o o' : Row) : Bool :=
  Lin.sameCoeff o.coeff o'.coeff && (decide (o.constant + 64 ≤ o'.constant) || decide (o'.constant + 64 ≤ o.constant))

def symSpillLoad (ctx : Ctx) (bind : Bind) (s : Sym) (args : List Expr) : V (List Nat × Sym) :=
  match symWordAddr bind s args with
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
  match symWordAddr bind s args with
  | some a =>
    if aligned64 a then do
      each (entail s.facts) (frameSpanGoals ctx s a 64)
      each (entail s.facts) (savedWordGoals s a 64)
      pure { s with range := none, spill := (frameOffset a, l) :: s.spill.filter fun (o, _) => cellsApart o (frameOffset a) }
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
    match (symWordAddr bind s args).bind fun a => (findLane ctx.contract a s.known).map fun x => (a, x) with
    | some (a, v, j, p, l) => symLoadBlock s v j p l a
    | none =>
      match (symWordAddr bind s args).bind fun a => (s.spill.find? fun (o, _) => frameOffset a == o).map fun c => (a, c) with
      | some (a, _, l) => symCellLoad ctx s a l
      | none => symMemWords ctx bind s args 16
  else if f == "mem512a" then symSpillLoad ctx bind s args
  else refuse "no proof rule for this 512-bit value"

/-- One operation on each pair of words of two lists of sixteen. -/
def symEachOp (s : Sym) (op : String) (x y : List Nat) : V (List Nat × Sym) :=
  if op == "add32" then symLaneTerms s (fun (p : Nat × Nat) => wAdd p.1 p.2) (x.zip y)
  else if op == "xor32" then symLaneTerms s (fun (p : Nat × Nat) => wXor p.1 p.2) (x.zip y)
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

/-- Where a place has said what the run `w` holds from some place on, a byte written to the run at `o` goes
below that. -/
def belowRange (s : Sym) (w : Nat) (o : Row) : V Unit :=
  match s.range with
  | some rg => if rg.w == w then entail s.facts (Lin.sub (Lin.sub rg.lo o) (Lin.const 1)) else pure ()
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
  | _ => refuse s!"{bytes} bytes written to what is no run given to write"

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
        if l.length == 16 then pure { s with vec := (r, l) :: s.vec } else refuse "expected sixteen lanes"
      | none => refuse "a row that sets what is no 512-bit register"
    | .call f [b, n] =>
      if f == "mem512" then
        match symVec512 bind s v, symReg bind s b, symNumber bind n with
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
        if isUnknown v then pure { s with vec := forgetHigh s.vec } else refuse "a row that sets the high lanes: not here yet"
      else
        match vecOf bind n with
        | some r => do
          let (l, s) ← symLanes ctx bind s v
          if l.length == 4 then pure { s with vec := (r, l) :: s.vec } else refuse "four words are not four"
        | none => refuse "a row that sets what is no vector register"
    | .call f [b, n] =>
      -- sixteen bytes of a run given to write, at a place that is a number divisible by four: four words
      -- of it now hold the register's four words
      if f == "mem128" then
        match symVec bind s v, symReg bind s b, symNumber bind n with
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
              pure { s with spill := [], range := none, frame := (c, x) :: s.frame.filter fun (o, _) => decide (o + 8 ≤ c) || decide (c + 8 ≤ o) }
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
      pure { s with spill := [], frame := s.frame.filter fun (o, _) => decide (sp ≤ o) }
    else refuse "the stack pointer leaves the frame the contract allows"
  | none =>
    if stackSame s then pure s else do
    -- Every saved word must remain at or above the stack pointer. Remember these facts so
    -- instructions that leave the stack pointer in place do not need another copy of the proofs.
    let missing := (stackGoals ctx s).filter fun g => !plain s.facts g
    each (entail s.facts) missing
    pure { s with facts := missing ++ s.facts, stackAt := some (s.reg RSP, s.frame, s.spill) }

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
        | _ => refuse "a proof of arithmetic is expected"
      else refuse "live or dead is expected"
    | some _ => refuse "live or dead is expected"
    | none => need "branch" (rows ++ s.facts) []

/-! ## The specification, on symbols -/

inductive SRes where
  | val (v : SVal)
  | tail (c : SCall)      -- the value is that of this use of a definition, which is not opened here
  | list (vs : List SVal) -- the things a definition is used with

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
  else if op == "==" then do let c ← compare s.facts x y; pure (.val (.bool c.isEq), s)
  else if op == "!=" then do let c ← compare s.facts x y; pure (.val (.bool (!c.isEq)), s)
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

/-- The uses that the facts say are the same as one of `seen`. -/
def reach (facts : List SFact) : Nat → List SCall → List SCall
  | 0, seen => seen
  | fuel + 1, seen => reach facts fuel (facts.foldl reachStep seen)

/-- The value of a use of a definition, where the verifier holds one. -/
def knownValue : List SFact → SCall → Option Row
  | [], _ => none
  | .value c' v :: more, c => if c' == c then some v else knownValue more c
  | .same _ _ :: more, c => knownValue more c

/-- The values held, each with the use it is of. -/
def heldValues : List SFact → List (SCall × Row)
  | [] => []
  | .value c v :: more => (c, v) :: heldValues more
  | .same _ _ :: more => heldValues more

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

def callsIn : SFact → List SCall
  | .same a b => [a, b]
  | .value c _ => [c]

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
  | fuel + 1, env, s, .list items => do
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
  | some name => (name, .lin (s.reg 0)) :: symEnv c
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
        entail s.facts (Lin.scale (-1) rg.lo)
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
  | word (xs : List Nat)          -- a word: the terms of these numbers summed, wrapping (one number: that term)
  | counter (r : Row)             -- the counter of a number that is no less than zero
  | list (l : List WVal)
  | run (r n : Nat)               -- the `n` bytes at the address register `r` held at entry, as they were at entry
  | part (r off n : Nat)          -- `n` of those bytes, from place `off` on
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
def idOf (look : Node → Option Nat) : List Nat → Option Nat
  | [a] => some a
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
  else none

def wbin (look : Node → Option Nat) (s : Sym) (op : String) : WVal → WVal → Option WVal
  | .int a, .int b =>
    match binop op (.int a) (.int b) with
    | some (.int n) => some (.int n)
    | some (.bool c) => some (.bool c)
    | _ => none
  | .word xs, .word ys =>
    if op == "+" then some (.word ((xs ++ ys).foldr insertSorted []))
    else if op == "^" then
      match idOf look xs, idOf look ys with
      | some a, some b => (look (.xor (min a b) (max a b))).map fun i => .word [i]
      | _, _ => none
    else none
  | .word xs, .int n =>
    if op == ">>>" ∧ 0 ≤ n ∧ n ≤ 32 then
      match idOf look xs with
      | some a => (look (.rotr a n.toNat)).map fun i => .word [i]
      | none => none
    else none
  | .num r, .int m =>
    if op == "%" then (if 0 < m then (lowOf s r m).map .num else none)
    else if op == "/" then (if 0 < m then (quotOf s r m).map .num else none)   -- (the quotient the state knows of)
    else if op == "|" then
      (if m = 0 ∧ knownNonneg s r = true then some (.num r)          -- (no bit is added)
       else
         match knownOr r (Lin.const m) s.known with
         | some v => some (.num (Lin.var v))
         | none => (orSmall s r m).map .num)
    else wnum s op r (Lin.const m)
  | .int m, .num r =>
    if op == "|" then (if m = 0 ∧ knownNonneg s r = true then some (.num r) else none)
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
      (look (.ult a l)).bind fun m => (look (.add (insertSorted h (insertSorted one [])))).bind fun h1 => look (.sel m h1 h)
    | _, _, _, _ => none
  else none

/-- The words of a run, from word `k` on, `count` of them: each must be in the table. -/
def inputWords (look : Node → Option Nat) (j : Nat) : Nat → Nat → Option (List WVal)
  | 0, _ => some []
  | count + 1, k =>
    match look (.input j k), inputWords look j count (k + 1) with
    | some i, some rest => some (.word [i] :: rest)
    | _, _ => none

/-- The language's own names (`builtin` of the account), on words. -/
def wown (ctx : Ctx) (look : Node → Option Nat) (s : Sym) (f : String) : List WVal → Option WVal
  | [.int n] =>
    if f == "word" then (if 0 ≤ n then (look (.atom (Lin.word (Lin.const n)))).map fun i => .word [i] else none)
    else if f == "counter" then (if 0 ≤ n then some (.counter (Lin.const n)) else none)
    else none
  | [.num r] =>
    if !plain s.facts r then none
    else if f == "word" then (look (.atom (Lin.word r))).map fun i => .word [i]
    else if f == "counter" then some (.counter r)
    else none
  | [.word xs] => if f == "word" then some (.word xs) else none
  | [.counter r] =>
    if f == "counter" then some (.counter r)
    else if f == "lo" then (look (.atom (Lin.word r))).map fun i => .word [i]
    else if f == "hi" then
      match (highOf s r).bind fun q => (look (.atom (Lin.word q))).map fun i => WVal.word [i] with
      | some v => some v
      | none => (hiPlus look s r).map fun i => .word [i]
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
  | [.wbytes ids] => if f == "words" then some (.list (ids.map fun i => WVal.word [i])) else none
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
    | some i, some rest => some (.word [i] :: rest)
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
          | _ => none
        else if own.contains f then wown ctx look s f vs
        else
          match (flatKeys look vs).bind fun keys => heldIds s.facts f keys s.known with
          | some ids => some (.list (ids.map fun i => WVal.word [i]))
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
      | _, _, _ => none
    | .record names items =>
      match wevalList (weval ctx look s fuel env) items with
      | some vs => if names.length == vs.length then some (.record (names.zip vs)) else none
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
  | _, _ => []

/-- The tables of addresses by their names (as `lanesEnv` of the account has them). -/
def lanesW (c : Contract) : List (String × WVal) :=
  (List.range c.fixeds.length).filterMap fun j => (c.tableAt j).map fun (x, _, count, l) => (x, WVal.lanes j count l)

/-- The names of the contract for an `ensures` of a whole run (as `envW` of the account has them). -/
def wenv (c : Contract) : List (String × WVal) := lanesW c ++ wenvIn c c.args argRegs

def WFUEL : Nat := 1000

/-- Each word of the list, from word `j` of the run `w` on, is the term known written there. -/
def wordsWritten (look : Node → Option Nat) (wroteW : List (Nat × Nat × Nat)) (w : Nat) : Nat → List WVal → Bool
  | _, [] => true
  | j, .word xs :: rest =>
    (match idOf look xs with
     | some i => wroteW.contains (w, j, i)
     | none => false) && wordsWritten look wroteW w (j + 1) rest
  | _, _ => false

/-- `ensures RUN = bytes_of(WORDS)`: the specification's words, worked out on the terms, are as many as the
run has, and each is the term known written at its place of the run. (Of a part of the run: as many as the
part has, which begins at a whole word and lies within the run; each is the term written at its place there.) -/
def symEnsureW (ctx : Ctx) (s : Sym) (e : EnsureW) : V Unit :=
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
def symReturn (ctx : Ctx) (s : Sym) : V Unit :=
  if s.sp != some 0 then refuse "at the return the stack pointer is not where it was at entry"
  else if !(calleeSaved.all fun r => s.reg r == Lin.var r) then refuse "at the return a register a callee keeps does not hold what it held at entry"
  else do
    each (symEnsureKnown ctx s) ctx.contract.ensuresW
    let s ← fold (symEnsure ctx (symEnvAfter ctx.contract s)) s ctx.contract.ensures
    match ctx.contract.returns with
    | none => pure ()
    | some e => do
      let (res, s) ← seval ctx (symEnv ctx.contract) s e
      match res with
      | .val (.lin v) => do
        entail s.facts (Lin.sub v (s.reg 0))
        entail s.facts (Lin.sub (s.reg 0) v)
      | .tail c => do
        let _ ← specGoal ctx 16 s (.value c (s.reg 0))
        pure ()
      | _ => refuse "a function returns a number"

/-! ## Marks: what may depend on a secret

The machine marks what may depend on a secret, and stops where something marked is used in an address,
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

/-- A register's row, or a number's: what a part of an address is. -/
def plainRow (bind : Bind) (s : Sym) : Expr → Option Row
  | .number n => if n < 2 ^ 64 then some (Lin.const n) else none
  | .name n =>
    if isNumberLetter n then ((bind.lookup n).bind readInt).map fun i => Lin.const (i % (M64 : Int))
    else (regOf bind n).map s.reg
  | _ => none

/-- A load of `size` bytes at `a + b` reads memory that is given to read only and is not hidden: a byte
of a run of bytes that the contract does not say is hidden, at a place the statement has shown to be
within the run (`s1` is the state after the statement: the byte is known there); or bytes at a place that is a number, within a run of a fixed count
that the contract does not say is hidden. Such bytes are not marked at entry, and nothing can write them. -/
def publicLoad (ctx : Ctx) (bind : Bind) (s s1 : Sym) (size : Nat) (a b : Expr) : Bool :=
  match plainRow bind s a, plainRow bind s b with
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
    | some (.data c) => decide (0 ≤ c) && decide (c + size ≤ ctx.contract.data.length)     -- (the file's data is not marked)
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
def cellsAfter (ctx : Ctx) (bind : Bind) (s : Sym) (f : String) (args : List Expr) (m : Bool) : List Int :=
  match memSize f, args with
  | some size, [a, b] =>
    match plainRow bind s a, plainRow bind s b with
    | some x, some y =>
      match locate ctx (Lin.add (signed x) (signed y)) with
      | some (.frame c) =>
        if decide (-(ctx.contract.stack : Int) ≤ c) && decide (c + size ≤ 0) then
          (if size == 8 && !m then [c] else []) ++ s.q.fq.filter fun o => decide (o + 8 ≤ c) || decide (c + size ≤ o)
        else []
      | some (.out w o) =>
        -- a store within a run given to write, at a place that is a number: no cell of the frame is stored to
        match Lin.isConst o, ctx.contract.outs[w]? with
        | some c, some (_, _, n) => if decide (0 ≤ c) && decide (c + size ≤ n) then s.q.fq else []
        | _, _ => []
      | _ => []
    | _, _ => []
  | _, _ => []

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
      | .call f args => if cleanAll bind s.q.regq args then some { s.q with fq := cellsAfter ctx bind s f args m } else none
      | _ => none
  | .vset place v =>
    if quietExprS bind s.q.regq v then
      match place with
      | .call _ args => if cleanAll bind s.q.regq args then some { s.q with fq := [] } else none
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
  | none => refuse "an address is made of something that may depend on a secret: what can be observed of the run would depend on it"

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

def flagWays : Flag → Option (List (Bool × List Row))
  | .unknown => none
  | .equal a b => some [(true, [Lin.sub a b, Lin.sub b a]), (false, [Lin.sub (Lin.sub a b) (Lin.const 1)]), (false, [Lin.sub (Lin.sub b a) (Lin.const 1)])]
  | .below a b => some [(true, [Lin.sub (Lin.sub b a) (Lin.const 1)]), (false, [Lin.sub a b])]

/-- An effect is a return, a jump, or statements that set registers, flags and memory. -/
inductive Shape where
  | ret
  | jump (target : Expr) (cond : Option (String × Bool))
  | plain

def shape : List Stmt → Shape
  | [.ret] => .ret
  | [.jump target cond] => .jump target cond
  | _ => .plain

def symInstr (ctx : Ctx) (s : Sym) (i : Instr) : V (List (Sym × Next)) :=
  match shape i.effect with
  | .ret =>
    do
      symReturn ctx s
      if !(s.q.regq.contains RSP && (!ctx.contract.givesNumber || s.q.regq.contains 0)) then
        refuse "at the return the stack pointer, or the number returned, may depend on a secret"
      else pure [(s, .returned)]
  | .jump target cond =>
    match jumpTarget i.bind target with
    | none => refuse "a jump to a place that cannot be read"
    | some t =>
      match cond with
      | none => pure [(s, .at t)]
      | some (flag, want) =>
        if !(if flag == "zf" then s.q.zq else s.q.cq) then
          refuse "a jump on a flag that may depend on a secret: which instructions run would depend on it"
        else
        match flagWays (if flag == "zf" then s.zf else s.cf) with
        | none => refuse "a jump on a flag of which nothing is known"
        | some w => ways s want t i.next w
  | .plain => do
    let s1 ← fold (symStmtQ ctx i.bind) s i.effect
    let s2 ← settle ctx s1
    pure [({ s2 with q := s1.q }, .at i.next)]

/-! ## A call, by the called function's contract -/

/-- The registers a called function may leave anything in: rax, rcx, rdx, rsi, rdi, r8 to r11. -/
def callerSaved : List Nat := [0, 1, 2, 6, 7, 8, 9, 10, 11]

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
  | _, _ => some []

/-- The state after a call, before anything is known of what was returned: the stack pointer and the
registers a callee keeps are as before; every other register holds a number below 2^64 and no more is
known; nothing is known of the flags; of the frame, only what lies above the stack pointer is kept (the
called function's frame and its return address were below). -/
def Sym.afterCall (s : Sym) (sp : Int) : Sym :=
  { reg := fun r => if callerSaved.contains r then Lin.var (s.nvars + r) else s.reg r,
    zf := .unknown, cf := .unknown,
    frame := s.frame.filter fun cell => decide (sp ≤ cell.1),
    facts := (callerSaved.map fun r => ranged (s.nvars + r)).flatten ++ s.facts,
    bytes := s.bytes, spec := s.spec, nvars := s.nvars + 16, wrote := s.wrote,
    tab := s.tab,         -- (and nothing is known of a vector register after a call, nor of the words of a run given to write)
    known := s.known }

/-- A call, taken by the called function's contract `c` and nothing else. What the contract asks is shown
first: its frame and the address to come back to fit in this function's frame, and each run of bytes it is
given is one this function was given (so it lies in memory, apart from that frame, as the contract
asks). Then the state is what the contract leaves: `Sym.afterCall`, and rax holds what `returns` says. -/
def symCallPlain (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    if !(decide (sp ≤ 0) && decide (-(ctx.contract.stack : Int) ≤ sp - 8 - c.stack)) then
      refuse "a call needs more stack than this function's contract allows"
    else if !(c.outs.isEmpty && c.ensures.isEmpty && (c.fixeds.isEmpty && (c.inouts.isEmpty && c.ensuresW.isEmpty))) then
      refuse "a called function that writes for its caller: not here yet"
    else if !c.bounds.isEmpty then refuse "a called function whose contract bounds a number: not here yet"
    else
      match calleeEnv ctx c s c.args argRegs with
      | none => refuse "a called function is given a run of bytes that is not one this function was given, whole"
      | some env =>
        match c.returns with
        | none => pure (s.afterCall sp)
        | some e => do
          let (res, s2) ← seval ctx env (s.afterCall sp) e
          match res with
          | .val (.lin v) => pure { s2 with facts := [Lin.sub v (Lin.var s.nvars), Lin.sub (Lin.var s.nvars) v] ++ s2.facts }
          | .tail call => pure { s2 with spec := .value call (Lin.var s.nvars) :: s2.spec }
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

/-- Before a call: the words of each run the called function is given that lies in the frame are put into
the table of terms. -/
def callFrameTouch (s : Sym) (c : Contract) : Sym :=
  (c.fixeds ++ c.inouts).foldl (fun s (x : String × Nat × Nat) =>
    match (frameAt s x.2.1).bind fun k => frameRows s k (x.2.2 / 4) 0 with
    | some rows => { s with tab := (termsOf wAtom rows s.tab).2 }
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
the part is known from a cell and is in the table. Where it lies, and the words' terms. -/
def frameRun (s : Sym) (r n : Nat) : Option (Int × List Nat) :=
  match frameAt s r, s.sp with
  | some c, some sp =>
    if sp ≤ c ∧ c + n ≤ 0 ∧ n % 8 = 0 then
      ((frameRows s c (n / 4) 0).bind (frameIds s)).map fun ids => (c, ids)
    else none
  | _, _ => none

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

/-- A called function's names on words, where its arguments are numbers, parts of runs of a fixed count
this function was given, and the run it reads and writes (the bytes of the words of `ids`). -/
def calleeW (ctx : Ctx) (s : Sym) (ids : List Nat) : List (String × Kind) → List Nat → Option (List (String × WVal))
  | (x, .number) :: args, r :: regs => (calleeW ctx s ids args regs).map fun env => (x, WVal.num (s.reg r)) :: env
  | (x, .fixed n) :: args, r :: regs =>
    match fixedPart ctx s r n, calleeW ctx s ids args regs with
    | some (_, b, c), some env => some ((x, WVal.part b c n) :: env)
    | none, some env => (frameRun s r n).map fun (_, fids) => (x, WVal.wbytes fids) :: env     -- (or a part of the frame)
    | _, _ => none
  | (x, .inout _) :: args, _ :: regs => (calleeW ctx s ids args regs).map fun env => (x, WVal.wbytes ids) :: env
  | (_, .bytes _) :: _, _ :: _ => none
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
`bytes`, the list of their bytes). What was known of the run's other words and of the other runs given to
write stays. -/
def Sym.afterCallW (s : Sym) (sp : Int) (w o m : Nat) (g : String) (keys : List Key) (bytes : Bool := false) : Sym :=
  let made := termsOf wAtom ((List.range m).map fun k => Lin.var (s.nvars + 16 + k)) s.tab
  { reg := fun r => if callerSaved.contains r then Lin.var (s.nvars + r) else s.reg r,
    zf := .unknown, cf := .unknown,
    frame := s.frame.filter fun cell => decide (sp ≤ cell.1),
    facts := ((List.range m).map fun k => ranged32 (s.nvars + 16 + k)).flatten ++
             ((callerSaved.map fun r => ranged (s.nvars + r)).flatten ++ s.facts),
    bytes := s.bytes, spec := s.spec, nvars := s.nvars + 16 + m, wrote := s.wrote,
    tab := made.2,
    intact := s.intact.filter (· != w),
    wroteW := ((List.range m).map fun k => (w, o + k, made.1.getD k 0)) ++
              s.wroteW.filter fun e => e.1 != w || decide (e.2.1 < o) || decide (o + m ≤ e.2.1),
    known := (if bytes then Known.heldB g keys made.1 else Known.held g keys made.1) :: s.known }

/-- The state after a call of a function that has written `m` words (an even count) of the frame, from `c`
bytes from where the stack pointer was at entry: as `Sym.afterCallW`, but what is written is cells of the
frame. Each new word is a new unknown; two words make a cell's number, the first its low half. The cells
the part overlaps are forgotten; the others at or above the stack pointer stay. -/
def Sym.afterCallF (s : Sym) (sp c : Int) (m : Nat) (g : String) (keys : List Key) : Sym :=
  let made := termsOf wAtom ((List.range m).map fun k => Lin.var (s.nvars + 16 + k)) s.tab
  { reg := fun r => if callerSaved.contains r then Lin.var (s.nvars + r) else s.reg r,
    zf := .unknown, cf := .unknown,
    frame := ((List.range (m / 2)).map fun (j : Nat) =>
                (c + 8 * (j : Int), Lin.add (Lin.var (s.nvars + 16 + 2 * j)) (Lin.scale W32i (Lin.var (s.nvars + 16 + 2 * j + 1))))) ++
             s.frame.filter fun cell => decide (sp ≤ cell.1) && (decide (cell.1 + 8 ≤ c) || decide (c + 4 * (m : Int) ≤ cell.1)),
    facts := ((List.range m).map fun k => ranged32 (s.nvars + 16 + k)).flatten ++
             ((callerSaved.map fun r => ranged (s.nvars + r)).flatten ++ s.facts),
    bytes := s.bytes, spec := s.spec, nvars := s.nvars + 16 + m, wrote := s.wrote,
    tab := made.2,
    intact := s.intact, wroteW := s.wroteW,
    known := Known.held g keys made.1 :: s.known }

/-- What a call of a function that writes a run of words is taken by: the part of a run of this function
that it writes (the run's number among the runs given to write, the part's first word, and how many words
the part has), the definition its contract names, the keys of the things the definition is used with
there, and the table with the words of the parts handed over put in. -/
structure CallW where
  w : Nat
  first : Nat
  words : Nat
  g : String
  keys : List Key
  tab : Tab

/-- The terms of the table a call is taken by, in order. -/
abbrev CallW.terms (p : CallW) : List Node := p.tab.list

/-- That, where the call can be taken so; else why not. (No proof is read here.) -/
def callWby (find : Nat → Nat → Option (Nat × Nat × List Nat)) (ctx : Ctx) (s : Sym) (c : Contract) : Except String CallW :=
  if !c.mbounds.isEmpty then .error "a called function whose contract bounds a number in memory: not here yet"
  else
    match c.outs, c.inouts, c.ensuresW with
    | [(run, r, n)], [(run', r', n')], [e] =>
      if !(run == run' && r == r' && n == n' && e.run == run && e.part.isNone) then
        .error "a called function that writes for its caller, but not one run of words it also reads: not here yet"
      else
        let T := (termsOf intern (partNodes ctx s c.args argRegs) s.tab).2
        match find r n with
        | none => .error "a called function is given to write what is not whole words of a run this function may read and write, each of them known"
        | some (w, o, ids) =>
          match calleeW ctx s ids c.args argRegs with
          | none => .error "a called function is given a run that is no part of a run this function was given to read"
          | some env =>
            -- its promise: the run is the bytes of the words a definition gives of its arguments
            match e.value with
            | .call f (.cons (.call g args) .nil) =>
              if f == "bytes_of" && !own.contains g && g != "len" then
                match wevalList (weval ctx T.find { s with tab := T } WFUEL env) args, findDef ctx.defs g with
                | some vs, some d =>
                  match flatKeys T.find vs with
                  | some keys =>
                    if !(keys.all (Key.ok s.nvars T.list.length)) then .error "what a called function's contract says of its arguments is not followed"
                    else if d.params.length == keys.length then .ok ⟨w, o, n / 4, g, keys, T⟩
                    else .error "a called function's contract uses a definition with another number of things"
                  | none => .error "what a called function's contract says of its arguments is not followed"
                | _, _ => .error "what a called function's contract says of its arguments is not followed"
              else .error "a called function's `ensures` that is not the bytes of the words a definition gives: not here yet"
            | _ => .error "a called function's `ensures` that is not the bytes of the words a definition gives: not here yet"
    | _, _, _ => .error "a called function that writes for its caller, but not one run of words it also reads: not here yet"

/-- The run it writes is looked for among the runs of words this function may read and write (`callRun`). -/
def callW (ctx : Ctx) (s : Sym) (c : Contract) : Except String CallW := callWby (callRun ctx s) ctx s c

def symCallW' (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    if !(decide (sp ≤ 0) && decide (-(ctx.contract.stack : Int) ≤ sp - 8 - c.stack)) then
      refuse "a call needs more stack than this function's contract allows"
    else
      match callW ctx s c with
      | .error what => refuse what
      | .ok plan => do
        -- what its contract asks of the numbers it is given
        each (fun (xb : String × Nat) =>
          match c.regOf xb.1 with
          | some rb => entail s.facts (Lin.sub (Lin.const ((xb.2 : Int) - 1)) (s.reg rb))
          | none => pure ()) c.bounds
        pure (Sym.afterCallW { s with tab := plan.tab } sp plan.w plan.first plan.words plan.g plan.keys)

/-- A call of a function that writes a run of words: the run of this function that it is given a part of
is first taken as written with the words it held at entry, where nothing was written to it yet. -/
def symCallW (ctx : Ctx) (s : Sym) (c : Contract) : V Sym := symCallW' ctx (callFrameTouch (callTouch ctx s c) c) c

/-! ## A call of a function that writes a part of this function's frame -/

/-- A call of a function that writes a run of words it also reads, where that run is a part of this
function's frame: in whole cells, each of them known, at or above the stack pointer and below the address
to return to (`frameRun`). A part of the frame that the called function is given to read must lie apart
from it. After the call the part's words are new unknowns, two to a cell (`Sym.afterCallF`). -/
def symCallF' (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    if !(decide (sp ≤ 0) && decide (-(ctx.contract.stack : Int) ≤ sp - 8 - c.stack)) then
      refuse "a call needs more stack than this function's contract allows"
    else
      match c.outs with
      | [(_, r, n)] =>
        match frameRun s r n with
        | none => refuse "a called function is given to write what is not whole cells of this function's frame, each of them known"
        | some (cw, _) =>
          if !(c.fixeds.all fun x =>
                match frameAt s x.2.1 with
                | some cf => decide (cf + (x.2.2 : Int) ≤ cw) || decide (cw + (n : Int) ≤ cf)
                | none => true) then
            refuse "a called function is given a part of the frame to read that the part it writes overlaps"
          else
            match callWby (fun r n => (frameRun s r n).map fun x => (0, 0, x.2)) ctx s c with
            | .error what => refuse what
            | .ok plan => do
              each (fun (xb : String × Nat) =>
                match c.regOf xb.1 with
                | some rb => entail s.facts (Lin.sub (Lin.const ((xb.2 : Int) - 1)) (s.reg rb))
                | none => pure ()) c.bounds
              pure (Sym.afterCallF { s with tab := plan.tab } sp cw plan.words plan.g plan.keys)
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
            match calleeB ctx c s c.args argRegs with
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
                      if !(keys.all (Key.ok s.nvars s.terms.length)) then .error "what a called function's contract says of its arguments is not followed"
                      else if d.params.length == keys.length then .ok ⟨w, o, n / 4, g, keys, {}⟩
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
    if !(decide (sp ≤ 0) && decide (-(ctx.contract.stack : Int) ≤ sp - 8 - c.stack)) then
      refuse "a call needs more stack than this function's contract allows"
    else
      match callB ctx s c with
      | .error what => refuse what
      | .ok plan => do
        -- what its contract asks of the numbers it is given
        each (fun (xb : String × Nat) =>
          match c.regOf xb.1 with
          | some rb => entail s.facts (Lin.sub (Lin.const ((xb.2 : Int) - 1)) (s.reg rb))
          | none => pure ()) c.bounds
        pure (Sym.afterCallW s sp plan.w plan.first plan.words plan.g plan.keys true)

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
  | .word xs => xs.all (· < t)
  | .list l => WVal.okAll n t l
  | .use h => decide (h < n)
  | .run _ _ => true
  | .part _ _ _ => true
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
  | some v => if v.ok s.nvars s.terms.length then some (v, s) else none
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
    | some v => if (wnorm v).ok s.nvars s.terms.length then some (wnorm v, s) else none
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
                | some ids => if ids.all (· < s.terms.length) then some (.list (ids.map fun i => WVal.word [i]), s) else none
                | none =>
                  match usedAs s.facts f keys s.known with
                  | some h => if h < s.nvars then some (.use h, s) else none
                  | none =>
                    match nameval ctx fuel s (d.params.zip vs) d.body with
                    | some r => some r
                    | none =>
                      if keys.all (Key.ok s.nvars s.terms.length) then
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
        | some (rest, T) => some (.list (blocksOf nb (ids.map fun i => WVal.word [i])) :: rest, T)
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
      | _, _ => none
  | (_, .out _) :: args, _ :: regs => calleeL ctx s tx tr nt args regs
  | (_, .inout _) :: _, _ :: _ => none
  | (_, .bytes _) :: _, _ :: _ => none
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
def Sym.afterCallL (s : Sym) (sp cw : Int) (n : Nat) (rows : List Row) : Sym :=
  { reg := fun r => if callerSaved.contains r then Lin.var (s.nvars + r) else s.reg r,
    zf := .unknown, cf := .unknown,
    frame := cellsOf cw 0 rows ++
             s.frame.filter fun cell => decide (sp ≤ cell.1) && (decide (cell.1 + 8 ≤ cw) || decide (cw + (n : Int) ≤ cell.1)),
    facts := (callerSaved.map fun r => ranged (s.nvars + r)).flatten ++ s.facts,
    bytes := s.bytes, spec := s.spec, nvars := s.nvars + 16, wrote := s.wrote,
    tab := s.tab, intact := s.intact, wroteW := s.wroteW, known := s.known }

/-- A call of a function that is given a table of addresses and writes one run, where both are parts of
this function's frame, apart from each other, at or above the stack pointer and below the address to return
to; the table's cells are known; the count of blocks is a number of the table; each lane's blocks are a
part of a run this function was given to read or of the frame (`tableLanes`). What the contract asks of its
numbers is shown first. After the call the run's words are new unknowns (`nameLanes`, `Sym.afterCallL`). -/
def symCallL (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    if !(decide (sp ≤ 0) && decide (-(ctx.contract.stack : Int) ≤ sp - 8 - c.stack)) then
      refuse "a call needs more stack than this function's contract allows"
    else if !(c.data.isEmpty && c.mbounds.isEmpty && c.inouts.isEmpty && c.ensures.isEmpty && c.regions.isEmpty &&
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
               decide (ct + 8 * (count : Int) ≤ 0) && (decide (ct + 8 * (count : Int) ≤ cw) || decide (cw + (n : Int) ≤ ct))) then
            refuse "a called function's table of addresses, or the run it writes, is no part of this function's frame, or the two overlap"
          else
            match tableLanes ctx s ct nb.toNat cw n count 0 (termsOf intern (partNodes ctx s c.args argRegs) s.tab).2 with
            | none => refuse "a lane of a called function's table is not blocks this function may read, every word of them known"
            | some (lanes, T) =>
              match calleeL ctx { s with tab := T } tx tr (8 * count) c.args argRegs with
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
                    pure (Sym.afterCallL s1 sp cw n rows)
        | _, _, _ => refuse "a called function's count of blocks is no number of the table, or its table or the run it writes is not in this function's frame"
      | _, _ => refuse "a called function that is given a table of addresses, but not one table and one run to write: not here yet"

/-- A call: by the rule for a function that is given a table of addresses; by the rule for a function that
writes nothing for its caller, by the rule for one that writes a run of words it also reads, or by the rule
for one that writes a run of bytes. -/
def symCall' (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  if !c.lanes.isEmpty then symCallL ctx s c
  else if !(c.atLeast.isEmpty && c.data.isEmpty) then
    refuse "a called function that asks that a number be no less than another, or takes the address of the file's data: not here yet"
  else if c.outs.isEmpty && c.ensures.isEmpty && (c.fixeds.isEmpty && (c.inouts.isEmpty && c.ensuresW.isEmpty)) then symCallPlain ctx s c
  else if c.inouts.isEmpty && c.ensuresW.isEmpty then symCallB ctx s c
  else if c.outs.any (fun x => (frameAt s x.2.1).isSome) then symCallF ctx s c
  else symCallW ctx s c

/-- A call: first the rows the proof file gives here join the facts (the bounds of the parts of runs
handed over, where the facts do not say them at once); then `symCall'`. -/
def symCall (ctx : Ctx) (s : Sym) (c : Contract) : V Sym := do
  let s ← symKnow (ctx.advice.call · c) KNOWN s
  symCall' ctx s c

/-- What a called function needs of the processor (`needs avx512`), this function's contract says too. (The
machine of the account has every row of the table, so no theorem asks this. A reader of this function's
contract is told what processor it wants, and that must cover the functions it calls. Where the contract says
`needs avx512 if plat == 5`, a call of a function that needs AVX-512 is covered on a path on which `plat` is 5.) -/
def needsOf (ctx : Ctx) (s : Sym) (c : Contract) : V Unit :=
  if !c.needsIf.isEmpty then refuse "a called function that needs something of the processor on a condition: not here yet"
  else if c.needs.all (fun n => ctx.contract.needs.contains n ||
      -- or this function's contract says it needs that if an argument is a number, and on this path the
      -- argument is seen at once to be that number
      ctx.contract.needsIf.any fun (what, arg, k) => what == n &&
        match ctx.contract.regOf arg with
        | some r => plain s.facts (Lin.sub (Lin.var r) (Lin.const k)) && plain s.facts (Lin.sub (Lin.const k) (Lin.var r))
        | none => false) then pure ()
  else refuse "a called function needs of the processor what this function's contract does not say it needs"

/-- What a called function's contract asks about marks is so at the call: the stack pointer and the
registers of its arguments, but for the numbers its contract says are hidden, are known not to be marked; each run of bytes it is given to read is one its contract
says is hidden (so nothing is asked of its bytes), or one this function was given to read, whole, that
this function's contract does not say is hidden; and a run of a fixed count it reads is one its contract
says is hidden, or a part of the frame whose cells are known not to be marked. And where a cell of the frame is known not to be marked, each run the called function
may write is within a run this function was given to write (so it is no part of the frame), or is a part
of the frame that every such cell lies apart from. -/
def callQuiet (ctx : Ctx) (s : Sym) (c : Contract) : Bool :=
  c.cleanAtEntry.all s.q.regq.contains &&
  c.data.isEmpty &&         -- (a called function that takes the address of the file's data: not here yet)
  c.fixeds.all (fun x => c.hidden.contains x.1 ||
    -- (or a part of the frame, in whole cells, each of them known not to be marked: a table of addresses made here)
    match frameAt s x.2.1 with
    | some o => decide (x.2.2 % 8 = 0) && (List.range (x.2.2 / 8)).all fun (i : Nat) => s.q.fq.contains (o + 8 * (i : Int))
    | none => false) &&
  (s.q.fq.isEmpty || c.outs.all fun (_, r, n) => decide (r ≠ RSP) && decide (r < 16) &&
    ((ctx.contract.outs.any fun (_, b, n0) =>
      match Lin.isConst (Lin.sub (s.reg r) (Lin.var b)) with
      | some k => decide (0 ≤ k) && decide (b < 16) && decide (k + n ≤ n0)
      | none => false) ||
     (match frameAt s r with
      | some o => s.q.fq.all fun cell => decide (cell + 8 ≤ o) || decide (o + (n : Int) ≤ cell)
      | none => false))) &&
  c.regions.all fun (r, l) =>
    c.hiddenAt r ||
      match findRun s r l ctx.contract.regions 0 with
      | some j =>
        match ctx.contract.regions[j]? with
        | some (base, _) => !ctx.contract.hiddenAt base
        | none => false
      | none => false

/-- What is known not to be marked after a call: the stack pointer; the number returned, where the called
function's contract says one is (of the other registers a callee does not keep, nothing: the contract says
nothing of them); each register a callee keeps that was not marked before; and each cell of the frame not
marked before that is not below the stack pointer. -/
def afterCallQ (c : Contract) (s : Sym) : SMarks :=
  { regq := (if c.givesNumber then [0, RSP] else [RSP]) ++ s.q.regq.filter calleeSaved.contains,
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

/-- An instruction: a call, by the called function's contract; any other, by its row's effect. -/
def symNext (ctx : Ctx) (s : Sym) (i : Instr) : V (List (Sym × Next)) :=
  match callTarget i with
  | some name =>
    match ctx.callees.lookup name with
    | none => refuse s!"a call of {name}, which is not a function shown before this one"
    | some c => do
      needsOf ctx s c
      let s' ← symCall ctx s c
      if !callQuiet ctx (quietAtCall s c) c then
        refuse "at a call, something the called function's contract asks not to depend on a secret may depend on one"
      else pure [({ s' with q := afterCallQ c (quietAtCall s c) }, .at i.next)]
  | none => symInstr ctx s i

def placeEnv (ctx : Ctx) (p : Place) (value : Nat → Row) : List (String × SVal) :=
  p.names.map (fun (n, r) => (n, SVal.lin (value r))) ++ symEnv ctx.contract

/-- What is known at entry: each register a number below 2^64; the frame the contract allows and the return
address lie in memory; so does each run of bytes given, to read or to write; a number the contract bounds is
below its bound, and one it asks to be no less than another is so; the blocks a table's addresses point to
lie in memory. (What is newer comes later: the facts before keep their numbers, by which proofs name them.) -/
def entryFacts (ctx : Ctx) : List Row :=
  ((List.range 16).map ranged).flatten ++
  [Lin.sub (Lin.var RSP) (Lin.const ctx.contract.stack), Lin.sub (Lin.const (2 ^ 64 - 9)) (Lin.var RSP)] ++
  (ctx.contract.regions.map fun (base, len) => Lin.sub (Lin.sub (Lin.const (2 ^ 64)) (Lin.var base)) (Lin.var len)) ++
  (ctx.contract.outs.map fun (_, base, n) => Lin.sub (Lin.const (2 ^ 64 - (n : Int))) (Lin.var base)) ++
  (ctx.contract.bounds.filterMap fun (name, b) => (ctx.contract.regOf name).map fun r => Lin.sub (Lin.const ((b : Int) - 1)) (Lin.var r)) ++
  (ctx.contract.fixeds.map fun (_, base, n) => Lin.sub (Lin.const (2 ^ 64 - (n : Int))) (Lin.var base)) ++
  (ctx.contract.atLeast.filterMap fun (name, k) => (ctx.contract.regOf name).map fun r => Lin.sub (Lin.var r) (Lin.const k)) ++
  ctx.contract.tables.filterMap fun (_, _, count, l) => if 0 < count then some (Lin.sub (Lin.const (2 ^ 64 - 64)) (Lin.scale 64 (Lin.var l))) else none

/-- Where the contract has data: the data's address is a number from 0 up, and the data ends below 2^64.
(After the other facts: they keep their numbers.) -/
def dataFacts (ctx : Ctx) : List Row :=
  if ctx.contract.data.isEmpty then []
  else [Lin.var dataVar, Lin.sub (Lin.const (2 ^ 64 - 1 - (ctx.contract.data.length : Int))) (Lin.var dataVar)]

def entrySym (ctx : Ctx) : Sym :=
  { reg := Lin.var, zf := .unknown, cf := .unknown, frame := [], facts := entryFacts ctx ++ dataFacts ctx, bytes := [], spec := [], nvars := 17,       -- (unknown 16: where the file's data lies)
    wrote := [], intact := List.range ctx.contract.outs.length, q := { regq := ctx.contract.cleanAtEntry } }

/-- The state that stands for every coming to the place on a path that first came there in `s`: the kept
registers and the frame as in `s`, every other register any number below 2^64. What `s` knows of the
unknowns it has (its facts, the bytes of the runs given, the values of uses of definitions) is still so:
those unknowns are what they were. -/
def Sym.general (p : Place) (s : Sym) : Sym :=
  { reg := fun r => if p.keep.contains r then s.reg r else Lin.var (s.nvars + r),
    zf := .unknown, cf := .unknown, frame := s.frame, bytes := s.bytes, spec := s.spec, nvars := s.nvars + 16,
    wrote := [],    -- (what was written before a loop is not carried into it yet)
    tab := s.tab,         -- (nor that a run is as it was at entry; what the vector registers hold is said by the place's lanes)
    known := s.known,
    facts := (((List.range 16).filter fun r => !p.keep.contains r).map fun r => ranged (s.nvars + r)).flatten ++ s.facts }

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
    | some (.word xs) => (idOf look xs).filter fun a => decide (a < s.terms.length)
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
    | some keys => if keys.all (Key.ok g.nvars g.terms.length) then some keys else none
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

/-- The place from which the state already holds the run `w` as written with the list `f(vs)`, by an earlier
coming to the place; where it holds nothing of that, the list's end. -/
def rangeBase (s : Sym) (w : Nat) (f : String) (vs : List SVal) (hi : Nat) : Row :=
  match s.range with
  | some rg => if rg.w == w && rg.f == f && rg.args == vs then rg.lo else Lin.const hi
  | none => Lin.const hi

/-- The most places a place's range may grow by at one coming there. -/
def GROW : Int := 64

/-- What the place says a loop has written is so of this state: the places from `lo` on that the state
does not already hold as written by an earlier coming (`Sym.range`) are known written, each with the
list's thing. Given back: the run's number, `lo`, and the things the definition is used with. -/
def rangeShown (ctx : Ctx) (p : Place) (s : Sym) : V (Option RangeF × Sym) :=
  match p.wrote with
  | none => pure (none, s)
  | some (run, lo, f, args) =>
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
            match Lin.isConst (Lin.sub (rangeBase s w f vs hi) lo) with
            | some k =>
              if k < 0 || GROW < k then refuse "a place: what is written does not reach from where the place says"
              else do
                let s ← filled ctx (params.zip vs) x b w lo 0 k.toNat s
                pure (some ⟨w, lo, f, vs⟩, s)
            | none => refuse "a place: where the written places begin is not known by a number from where they began before"
      | _ => refuse "a place: a definition used with what is no list of things"

/-- In the state that stands for every coming to the place: what the place says a loop has written is taken
as known. -/
def supposeRange (ctx : Ctx) (p : Place) (g : Sym) : V Sym :=
  match p.wrote with
  | none => pure g
  | some (run, lo, f, args) =>
    match findOutNamed run ctx.contract.outs 0 with
    | none => refuse "a place says what is written of what is no run given to write"
    | some (w, _) => do
      let env := placeEnv ctx p g.reg
      let (lo, g) ← seval ctx env g lo
      let (lo, g) ← numberV (opener ctx DEEP) g lo
      let (vs, g) ← seval ctx env g args
      match vs with
      | .list vs => pure { g with range := some ⟨w, lo, f, vs⟩ }
      | _ => refuse "a place: a definition used with what is no list of things"

/-- On first coming to the place: what holds there is shown of this state; then the state that stands for
every coming there, of which the place's facts are taken as known, and its number that decreases, which is
shown to be no less than zero. Given back with them: the state as it first came, with which every later
coming is compared. -/
def generalize (ctx : Ctx) (p : Place) (s : Sym) : V (Sym × Row × Sym) :=
  if !p.keep.contains RSP || p.names.any (fun (_, r) => decide (16 ≤ r)) then
    refuse "a place must keep the stack pointer, and name registers"
  else do
    let s ← fold (establish ctx (placeEnv ctx p s.reg)) s p.facts
    if !(p.lanes.all (lanesShown ctx p s)) then refuse s!"at the place {p.pc} the vector registers are not shown to hold what the place says"
    else if !(p.cells.all (cellShown ctx p s)) then refuse s!"at the place {p.pc} a cell of the frame is not shown to hold what the place says"
    else do
      let (_, s) ← rangeShown ctx p s
      let g ← fold (suppose ctx (placeEnv ctx p (s.general p).reg)) (s.general p) p.facts
      let g ← fold (supposeLanes ctx p) g p.lanes
      let g ← fold (supposeCell ctx p) g p.cells
      let g ← supposeRange ctx p g
      let (d, g) ← seval ctx (placeEnv ctx p (s.general p).reg) g p.decreases
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
  if !(first.q.regq.all s.q.regq.contains) then refuse s!"at the place {p.pc} register {(first.q.regq.find? fun r => !s.q.regq.contains r).getD 0} may depend on a secret, which it did not on first coming there"
  else
  if !(first.frame.all fun cell => s.frame.contains cell) then refuse "at the place the frame does not hold what it held on first coming there"
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

/-- Of the registers known not to be marked on first coming to a place, those the place does not say may be
marked on a later coming. -/
def placeQuiet (p : Place) (regq : List Nat) : List Nat :=
  regq.filter fun r => !p.marked.contains r

/-- Where a path goes on after an instruction. At the function's return it ends. At a place this path has
come to before, the coming there is shown to be one that place's general state stands for, with a number
less than the general state's: there the path ends. At a place it has not come to before, the place's
general state is made and the path goes on from that, the place remembered. Anywhere else the path is
gone on with. -/
def onward (ctx : Ctx) (seen : List Seen) (go : List Seen → Sym → Nat → V Unit) (next : Sym × Next) : V Unit :=
  match next.2 with
  | .returned => pure ()
  | .at pc' =>
    match ctx.places.find? (fun p => p.pc == pc') with
    | none => go seen next.1 pc'
    | some p =>
      match seen.find? (fun e => e.place.pc == pc') with
      | some e => arrive ctx e.place e.first e.d next.1
      | none => do
        let (g, d, first) ← generalize ctx p next.1
        -- (what is known not to be marked at the place: the registers that are not on this first coming,
        -- but for those the place says may be on a later one)
        go (⟨p, d, { first with q := { regq := placeQuiet p next.1.q.regq } }⟩ :: seen) { g with q := { regq := placeQuiet p next.1.q.regq } } pc'

/-- Every path from `pc`: each to the function's return, or to a place it has come to before. -/
def explore (ctx : Ctx) : Nat → List Seen → Sym → Nat → V Unit
  | 0, _, _, _ => refuse "a path longer than the verifier goes"
  | fuel + 1, seen, s, pc =>
    match ctx.code.lookup pc with
    | none => refuse s!"no instruction at {pc}"
    | some i => do
      let nexts ← symNext ctx s i
      each (onward ctx seen (explore ctx fuel)) nexts

def PATH : Nat := 100000

/-- The verifier. -/
def verify (ctx : Ctx) : V Unit := do
  explore ctx PATH [] (entrySym ctx) 0
  if ← finished then pure () else refuse "the proof says more than is asked of it"

/-- Does the function meet its contract, by this proof? `none`: yes. -/
def verdict (ctx : Ctx) (proof : List Item) : Option String :=
  match verify ctx (Items.ofList proof) with
  | .ok _ => none
  | .error why => some why

/-- A function of a statement: its name, its instructions and its contract; and, the maker's, its places
and its proof. -/
structure Fn where
  name : String
  code : List (Nat × Instr) := []
  contract : Contract := { args := [], returns := none, stack := 0 }
  places : List Place := []
  proof : List Item := []

/-- The functions one after another, `done` being those already shown, each with its contract. A call is
taken by the contract of a function already shown, and by nothing else: so no function calls itself, or
one that calls it, or one that is not in the statement. -/
def verdictFrom (defs : List Def) : List (String × Contract) → List Fn → Option String
  | _, [] => none
  | done, f :: more =>
    if done.any (fun d => d.1 == f.name) then some s!"refused: two functions are named {f.name}"
    else match verdict { code := f.code, contract := f.contract, defs := defs, places := f.places, callees := done } f.proof with
      | some why => some s!"{why}\nin {f.name}"
      | none => verdictFrom defs ((f.name, f.contract) :: done) more

/-- Do the functions of a statement meet their contracts, by these proofs? `none`: yes, every one. -/
def verdictAll (defs : List Def) (fns : List Fn) : Option String := verdictFrom defs [] fns

end Ode
