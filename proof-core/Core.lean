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
  * which use of a definition to open (`open N`) on the way to a fact of the specification.

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

end Lin

/-! ## The proof, and asking it -/

inductive Item where
  | tag (name : String) (n : Nat)
  | proof (starts : List Nat) (steps : List Step)   -- of arithmetic: the rows it starts from, by their numbers among those the verifier holds
  deriving Inhabited

/-- A step of the verifier: it takes what it needs from the front of the proof, and gives an answer and the
rest of the proof, or stops with the reason. -/
def V (α : Type) := List Item → Except String (α × List Item)

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
  match items with
  | [] => .ok (none, [])
  | i :: rest => .ok (some i, rest)

def finished : V Bool := fun items => .ok (items.isEmpty, items)

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
  | none => facts.any fun f =>
    match Lin.isConst (Lin.sub g f) with
    | some k => decide (0 ≤ k)
    | none => false

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
    | some (.tag ..) => refuse "a proof of arithmetic is expected"
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
    | some (.proof ..) => refuse "lt, eq or gt is expected"
    | none => need "compare" facts [Lin.sub a b]

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
  deriving Inhabited

structure Place where
  pc : Nat
  names : List (String × Nat)     -- a name for what a register holds there
  keep : List Nat                 -- registers that hold there what they held when the path first came there
  facts : List SExpr
  decreases : SExpr
  deriving Inhabited

structure Ctx where
  code : List (Nat × Instr)
  contract : Contract
  defs : List Def
  places : List Place := []                     -- the maker's: where the paths of loops are cut
  callees : List (String × Contract) := []      -- the functions this one calls, each with its contract
  deriving Inhabited

def symEnvIn (c : Contract) : List (String × Kind) → List Nat → Nat → List (String × SVal)
  | (n, .number) :: args, r :: regs, k => (n, .lin (Lin.var r)) :: symEnvIn c args regs k
  | (n, .bytes len) :: args, _ :: regs, k =>
    match c.regOf len with
    | some _ => (n, .region k) :: symEnvIn c args regs (k + 1)
    | none => symEnvIn c args regs k
  | (_, .out _) :: args, _ :: regs, k => symEnvIn c args regs k
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
           facts := d :: Lin.scale (-1) d :: Lin.var (s.nvars + 1) :: Lin.sub (Lin.const (m - 1)) (Lin.var (s.nvars + 1)) :: s.facts }

/-- The unknowns a fact names as a quotient of `x` by `m`: the fact is `x` less `m` times that unknown, less
the next unknown. (Only to look at few unknowns in `divided`: nothing rests on it.) -/
def quotients (s : Sym) (x : Row) (m : Int) : List Nat :=
  s.facts.filterMap fun f =>
    let e := Lin.sub x f
    let q := e.coeff.length - 2
    if 2 ≤ e.coeff.length && e == Lin.add (Lin.scale m (Lin.var q)) (Lin.var (q + 1)) then some q else none

/-- The quotient's unknown, where the facts held already say what `x` divided by `m` is: the four facts of
`Sym.divide`, of one unknown and the next. -/
def divided (s : Sym) (x : Row) (m : Int) : Option Nat :=
  let named := quotients s x m
  (List.range s.nvars).find? fun q =>
    named.contains q &&
    (let d := Lin.sub x (Lin.add (Lin.scale m (Lin.var q)) (Lin.var (q + 1)))
     s.facts.contains d && s.facts.contains (Lin.scale (-1) d) && s.facts.contains (Lin.var (q + 1)) &&
       s.facts.contains (Lin.sub (Lin.const (m - 1)) (Lin.var (q + 1))))

/-- A number of the machine (from 0 to 2^64 - 1) divided by a number above zero: its quotient and its
remainder, and the state that knows of them. They are found once for one number and one divisor; the
quotient is no less than zero. -/
def symDivide (s : Sym) (x : Row) (m : Int) : Row × Row × Sym :=
  match divided s x m with
  | some q => (Lin.var q, Lin.var (q + 1), s)
  | none => (Lin.var s.nvars, Lin.var (s.nvars + 1), { s.divide x m with facts := Lin.var s.nvars :: (s.divide x m).facts })

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

def findRegion (addr : Row) : List (Nat × Nat) → Nat → Option Where
  | [], _ => none
  | (base, _) :: more, k =>
    if Lin.coeffOf addr base == 1 then some (.region k (Lin.sub addr (Lin.var base))) else findRegion addr more (k + 1)

def findOut (addr : Row) : List (String × Nat × Nat) → Nat → Option Where
  | [], _ => none
  | (_, base, _) :: more, k =>
    if Lin.coeffOf addr base == 1 then some (.out k (Lin.sub addr (Lin.var base))) else findOut addr more (k + 1)

/-- Where an address is: in the frame, in a run of bytes given to read, or in one given to write. -/
def locate (ctx : Ctx) (addr : Row) : Option Where :=
  match Lin.isConst (Lin.sub addr (Lin.var RSP)) with
  | some c => some (.frame c)
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

/-- A number of 2^63 or more, as the number below zero that is the same modulo 2^64. -/
def signed (r : Row) : Row :=
  match Lin.isConst r with
  | some k => if 2 ^ 63 ≤ k then Lin.const (k - 2 ^ 64) else r
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
  | none => refuse "a read that is neither of the frame nor of a run given"

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
    -- a shift to the left by a number of the table: so many doublings, shown to stay below 2^64
    match Lin.isConst y with
    | some k =>
      if 0 ≤ k ∧ k < 64 then do
        inRange s.facts (Lin.scale (2 ^ k.toNat) x)
        pure (.lin (Lin.scale (2 ^ k.toNat) x), s)
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
    -- the bits below a power of two (an and with one less than it): the remainder by it
    match Lin.isConst y with
    | some m =>
      match (List.range 65).find? (fun k => (2 : Int) ^ k - 1 == m) with
      | some k => pure (.lin (symDivide s x (2 ^ k)).2.1, (symDivide s x (2 ^ k)).2.2)
      | none => refuse "an and with a number that is not one less than a power of two: not here yet"
    | none => refuse "an and with what is no number of the table: not here yet"
  else refuse s!"no rule for {f}"

/-- The remainder of a number by a divisor above zero: worked out where the number is one of the table's,
and else by the one division of it the state knows of. -/
def symLow (s : Sym) (x : Row) (m : Int) : Row × Sym :=
  match Lin.isConst x with
  | some k => (Lin.const (k % m), s)
  | none => ((symDivide s x m).2.1, (symDivide s x m).2.2)

/-- A primitive of one number: its low half, or its low byte (the remainder by 2^32, by 256). -/
def symPrim1 (f : String) (s : Sym) (x : Row) : V (EV × Sym) :=
  if f == "low32" then pure (.lin (symLow s x (2 ^ 32)).1, (symLow s x (2 ^ 32)).2)
  else if f == "low8" then pure (.lin (symLow s x 256).1, (symLow s x 256).2)
  else refuse s!"no rule for {f}"

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
    | .lin x => symPrim1 f s x
    | _ => refuse "a flag's value where a number is expected"
  | s, .call f [a, b] => do
    let (x, s) ← symValue ctx bind s a
    let (y, s) ← symValue ctx bind s b
    match x, y with
    | .lin x, .lin y =>
      match memSize f with
      | some size => symLoad ctx s (Lin.add (signed x) (signed y)) size
      | none => symPrim f s x y
    | _, _ => refuse "a flag's value where a number is expected"
  | _, .call f _ => refuse s!"no rule for {f}"

def symStmt (ctx : Ctx) (bind : Bind) (s : Sym) : Stmt → V Sym
  | .nothing => pure s
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
              pure { s with frame := (c, x) :: s.frame.filter fun (o, _) => decide (o + 8 ≤ c) || decide (c + 8 ≤ o) }
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
                match keepWrote w o s.wrote with
                | some rest => pure { s with wrote := (w, o, x) :: rest }
                | none => refuse "a write at a place not known apart from one written before: not here yet"
              else refuse "a write of more than one byte to a run given to write: not here yet"
            | none => refuse "no such run of bytes"
          | _ => refuse "a write to a run given only to read, or to no run given"
        | _, _, _ => refuse "a flag's value where a number is expected"
      | _ => refuse "a row that sets what is no place"
  | _ => refuse "a jump, a call or a return among other statements"

/-- After an instruction: the stack pointer is in the frame the contract allows, and nothing is remembered
below it. -/
def settle (ctx : Ctx) (s : Sym) : V Sym :=
  match s.sp with
  | some sp =>
    if sp ≤ 0 ∧ -(ctx.contract.stack : Int) ≤ sp then pure { s with frame := s.frame.filter fun (o, _) => decide (sp ≤ o) }
    else refuse "the stack pointer leaves the frame the contract allows"
  | none => refuse "the stack pointer is not in the frame"

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
    | some (.proof ..) => refuse "live or dead is expected"
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
  else do
    let c ← compare s.facts x y
    if op == "==" then pure (.val (.bool c.isEq), s)
    else if op == "!=" then pure (.val (.bool (!c.isEq)), s)
    else if op == "<" then pure (.val (.bool c.isLt), s)
    else if op == "<=" then pure (.val (.bool (!c.isGt)), s)
    else if op == ">" then pure (.val (.bool c.isGt), s)
    else if op == ">=" then pure (.val (.bool (!c.isLt)), s)
    else refuse s!"no rule for {op}"

/-- The remainder of `x` by a number of the specification above zero: the remainder of the two new
unknowns of `Sym.divide`. -/
def smod (s : Sym) (x y : Row) : V (SRes × Sym) :=
  match Lin.isConst y with
  | some m =>
    if 0 < m then pure (.val (.lin (Lin.var (s.nvars + 1))), s.divide x m)
    else refuse "a remainder by a number that is not above zero"
  | none => refuse "a remainder by what is no number of the specification: not here yet"

/-- The quotient of `x` by a number of the specification above zero: the quotient of the two new unknowns
of `Sym.divide`. -/
def sdiv (s : Sym) (x y : Row) : V (SRes × Sym) :=
  match Lin.isConst y with
  | some m =>
    if 0 < m then pure (.val (.lin (Lin.var s.nvars)), s.divide x m)
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
    | some (.proof ..) => refuse "a number is expected (or a use of a definition whose value is held)"
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
      | some (.proof ..) => refuse "open or carry is expected"
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

/-! ## Return, places, paths -/

/-- At the return: the stack pointer is where it was, the registers a callee keeps hold what they held at
entry, and rax holds what the contract says. -/
def symReturn (ctx : Ctx) (s : Sym) : V Unit :=
  if !ctx.contract.ensures.isEmpty then refuse "an `ensures` of the contract: not here yet"
  else if s.sp != some 0 then refuse "at the return the stack pointer is not where it was at entry"
  else if !(calleeSaved.all fun r => s.reg r == Lin.var r) then refuse "at the return a register a callee keeps does not hold what it held at entry"
  else
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
  | .ret => do symReturn ctx s; pure [(s, .returned)]
  | .jump target cond =>
    match jumpTarget i.bind target with
    | none => refuse "a jump to a place that cannot be read"
    | some t =>
      match cond with
      | none => pure [(s, .at t)]
      | some (flag, want) =>
        match flagWays (if flag == "zf" then s.zf else s.cf) with
        | none => refuse "a jump on a flag of which nothing is known"
        | some w => ways s want t i.next w
  | .plain => do
    let s ← fold (symStmt ctx i.bind) s i.effect
    let s ← settle ctx s
    pure [(s, .at i.next)]

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
    bytes := s.bytes, spec := s.spec, nvars := s.nvars + 16, wrote := s.wrote }

/-- A call, taken by the called function's contract `c` and nothing else. What the contract asks is shown
first: its frame and the address to come back to fit in this function's frame, and each run of bytes it is
given is one this function was given (so it lies in memory, apart from that frame, as the contract
asks). Then the state is what the contract leaves: `Sym.afterCall`, and rax holds what `returns` says. -/
def symCall (ctx : Ctx) (s : Sym) (c : Contract) : V Sym :=
  match s.sp with
  | none => refuse "at a call the stack pointer is not known"
  | some sp =>
    if !(decide (sp ≤ 0) && decide (-(ctx.contract.stack : Int) ≤ sp - 8 - c.stack)) then
      refuse "a call needs more stack than this function's contract allows"
    else if !(c.outs.isEmpty && c.ensures.isEmpty) then
      refuse "a called function that writes for its caller: not here yet"
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

/-- An instruction: a call, by the called function's contract; any other, by its row's effect. -/
def symNext (ctx : Ctx) (s : Sym) (i : Instr) : V (List (Sym × Next)) :=
  match callTarget i with
  | some name =>
    match ctx.callees.lookup name with
    | none => refuse s!"a call of {name}, which is not a function shown before this one"
    | some c => do
      let s' ← symCall ctx s c
      pure [(s', .at i.next)]
  | none => symInstr ctx s i

def placeEnv (ctx : Ctx) (p : Place) (value : Nat → Row) : List (String × SVal) :=
  p.names.map (fun (n, r) => (n, SVal.lin (value r))) ++ symEnv ctx.contract

/-- What is known at entry: each register a number below 2^64; the frame the contract allows and the return
address lie in memory; so does each run of bytes given. -/
def entryFacts (ctx : Ctx) : List Row :=
  ((List.range 16).map ranged).flatten ++
  [Lin.sub (Lin.var RSP) (Lin.const ctx.contract.stack), Lin.sub (Lin.const (2 ^ 64 - 9)) (Lin.var RSP)] ++
  ctx.contract.regions.map fun (base, len) => Lin.sub (Lin.sub (Lin.const (2 ^ 64)) (Lin.var base)) (Lin.var len)

def entrySym (ctx : Ctx) : Sym :=
  { reg := Lin.var, zf := .unknown, cf := .unknown, frame := [], facts := entryFacts ctx, bytes := [], spec := [], nvars := 16,
    wrote := [] }

/-- The state that stands for every coming to the place on a path that first came there in `s`: the kept
registers and the frame as in `s`, every other register any number below 2^64. What `s` knows of the
unknowns it has (its facts, the bytes of the runs given, the values of uses of definitions) is still so:
those unknowns are what they were. -/
def Sym.general (p : Place) (s : Sym) : Sym :=
  { reg := fun r => if p.keep.contains r then s.reg r else Lin.var (s.nvars + r),
    zf := .unknown, cf := .unknown, frame := s.frame, bytes := s.bytes, spec := s.spec, nvars := s.nvars + 16,
    wrote := [],    -- (what was written before a loop is not carried into it yet)
    facts := (((List.range 16).filter fun r => !p.keep.contains r).map fun r => ranged (s.nvars + r)).flatten ++ s.facts }

/-- On first coming to the place: what holds there is shown of this state; then the state that stands for
every coming there, of which the place's facts are taken as known, and its number that decreases, which is
shown to be no less than zero. Given back with them: the state as it first came, with which every later
coming is compared. -/
def generalize (ctx : Ctx) (p : Place) (s : Sym) : V (Sym × Row × Sym) :=
  if !p.keep.contains RSP || p.names.any (fun (_, r) => decide (16 ≤ r)) then
    refuse "a place must keep the stack pointer, and name registers"
  else do
    let s ← fold (establish ctx (placeEnv ctx p s.reg)) s p.facts
    let g ← fold (suppose ctx (placeEnv ctx p (s.general p).reg)) (s.general p) p.facts
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
  if !(first.frame.all fun cell => s.frame.contains cell) then refuse "at the place the frame does not hold what it held on first coming there"
  else do
    let s1 ← fold (establish ctx (placeEnv ctx p s.reg)) s p.facts
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
        go (⟨p, d, first⟩ :: seen) g pc'

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
  match verify ctx proof with
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
