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
  | proof (starts : List Row) (steps : List Step)
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

/-- `g ≥ 0` follows from the facts. -/
def entail (facts : List Row) (g : Row) : V Unit :=
  if plain facts g then pure () else do
    match ← pop with
    | some (.proof starts steps) =>
      if Arithmetic.refutes (negation g :: facts) starts steps then pure ()
      else refuse "a proof of arithmetic does not show what is to be shown"
    | some (.tag ..) => refuse "a proof of arithmetic is expected"
    | none => need "entail" facts [g]

inductive Cmp where
  | lt | eq | gt
  deriving DecidableEq

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
  deriving Inhabited

structure Place where
  pc : Nat
  names : List (String × Nat)     -- a name for what a register holds there
  keep : List Nat                 -- registers that hold there what they held on first coming there
  facts : List SExpr
  decreases : SExpr
  deriving Inhabited

structure Ctx where
  code : List (Nat × Instr)
  contract : Contract
  defs : List Def
  place : Option Place
  deriving Inhabited

def symEnvIn (c : Contract) : List (String × Kind) → List Nat → Nat → List (String × SVal)
  | (n, .number) :: args, r :: regs, k => (n, .lin (Lin.var r)) :: symEnvIn c args regs k
  | (n, .bytes len) :: args, _ :: regs, k =>
    match c.regOf len with
    | some _ => (n, .region k) :: symEnvIn c args regs (k + 1)
    | none => symEnvIn c args regs k
  | _, _, _ => []

/-- The contract's names on symbols: a number is its register at entry; a run of bytes is a run by its number. -/
def symEnv (c : Contract) : List (String × SVal) := symEnvIn c c.args argRegs 0

def Sym.put (s : Sym) (r : Nat) (v : Row) : Sym := { s with reg := fun k => if k = r then v else s.reg k }

/-- How far the stack pointer is from where it was at entry. -/
def Sym.sp (s : Sym) : Option Int := Lin.isConst (Lin.sub (s.reg RSP) (Lin.var RSP))

def top : Int := 2 ^ 64 - 1

def ranged (v : Nat) : List Row := [Lin.var v, Lin.sub (Lin.const top) (Lin.var v)]

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

def findRegion (addr : Row) : List (Nat × Nat) → Nat → Option Where
  | [], _ => none
  | (base, _) :: more, k =>
    if Lin.coeffOf addr base == 1 then some (.region k (Lin.sub addr (Lin.var base))) else findRegion addr more (k + 1)

/-- Where an address is: in the frame, or in a run of bytes given. -/
def locate (ctx : Ctx) (addr : Row) : Option Where :=
  match Lin.isConst (Lin.sub addr (Lin.var RSP)) with
  | some c => some (.frame c)
  | none => findRegion addr ctx.contract.regions 0

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
          | _ => refuse "a write outside the frame: not here yet"
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
          if Arithmetic.refutes (rows ++ s.facts) starts steps then pure none
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
  else if op == "-" then pure (.val (.lin (Lin.sub x y)), s)
  else if op == "*" then
    match Lin.isConst x, Lin.isConst y with
    | some k, _ => pure (.val (.lin (Lin.scale k y)), s)
    | _, some k => pure (.val (.lin (Lin.scale k x)), s)
    | _, _ => refuse "a product of two unknowns: not here yet"
  else do
    let c ← compare s.facts x y
    if op == "==" then pure (.val (.bool (c == .eq)), s)
    else if op == "!=" then pure (.val (.bool (c != .eq)), s)
    else if op == "<" then pure (.val (.bool (c == .lt)), s)
    else if op == "<=" then pure (.val (.bool (c != .gt)), s)
    else if op == ">" then pure (.val (.bool (c == .gt)), s)
    else if op == ">=" then pure (.val (.bool (c != .lt)), s)
    else refuse s!"no rule for {op}"

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

def seval (ctx : Ctx) (env : List (String × SVal)) : Sym → SExpr → V (SRes × Sym)
  | s, .num n => pure (.val (.lin (Lin.const n)), s)
  | s, .name x =>
    match env.lookup x with
    | some v => pure (.val v, s)
    | none => refuse s!"the name {x} stands for nothing here"
  | s, .bin op a b => do
    let (x, s) ← seval ctx env s a
    let (y, s) ← seval ctx env s b
    match x, y with
    | .val (.lin x), .val (.lin y) => sbin op s x y
    | _, _ => refuse "a number is expected (a use of a definition where its value is needed: not here yet)"
  | s, .ifx c a b => do
    let (c, s) ← seval ctx env s c
    match c with
    | .val (.bool true) => seval ctx env s a
    | .val (.bool false) => seval ctx env s b
    | _ => refuse "a condition that is not true or false"
  | s, .index a i => do
    let (a, s) ← seval ctx env s a
    let (i, s) ← seval ctx env s i
    match a, i with
    | .val (.region r), .val (.lin o) => do
      let (v, s) ← readByte ctx s r o
      pure (.val (.lin v), s)
    | _, _ => refuse "a byte of what is no run of bytes"
  | s, .call f args => do
    let (vs, s) ← seval ctx env s args
    match vs with
    | .list vs => scall ctx f vs s
    | _ => refuse "a definition used with what is no list of things"
  | s, .nil => pure (.list [], s)
  | s, .cons a rest => do
    let (v, s) ← seval ctx env s a
    let (vs, s) ← seval ctx env s rest
    match v, vs with
    | .val v, .list vs => pure (.list (v :: vs), s)
    | _, _ => refuse "a use of a definition inside another: not here yet"

/-- A use of a definition, opened once: a fact of what it is the same as, or of its value. -/
def openCall (ctx : Ctx) (s : Sym) (c : SCall) : V Sym :=
  match findDef ctx.defs c.f with
  | none => refuse s!"no definition {c.f}"
  | some d =>
    if d.params.length != c.args.length then refuse s!"{c.f} takes another number of things" else do
      let (res, s) ← seval ctx (d.params.zip c.args) s d.body
      match res with
      | .tail c' => pure { s with spec := .same c c' :: s.spec }
      | .val (.lin v) => pure { s with spec := .value c v :: s.spec }
      | _ => refuse "a definition whose value is no number: not here yet"

def insert (c : SCall) (l : List SCall) : List SCall := if l.contains c then l else l ++ [c]

def reachStep (seen : List SCall) : SFact → List SCall
  | .same a b => if seen.contains a then insert b seen else if seen.contains b then insert a seen else seen
  | .value .. => seen

/-- The uses that the facts say are the same as one of `seen`. -/
def reach (facts : List SFact) : Nat → List SCall → List SCall
  | 0, seen => seen
  | fuel + 1, seen => reach facts fuel (facts.foldl reachStep seen)

def holdsSpec (facts : List SFact) : SFact → Bool
  | .same a b => (reach facts (facts.length + 1) [a]).contains b
  | .value c v => (reach facts (facts.length + 1) [c]).any fun c' => facts.contains (.value c' v)

def callsIn : SFact → List SCall
  | .same a b => [a, b]
  | .value c _ => [c]

def callsOf (facts : List SFact) (goal : SFact) : List SCall :=
  ((facts.reverse ++ [goal]).map callsIn).flatten.foldl (fun l c => insert c l) []

/-- A fact of the specification, from the facts held and uses of definitions the proof says to open. -/
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
        else refuse "open is expected"
      | some (.proof ..) => refuse "open is expected"
      | none => fun _ => .error s!"need spec\nc {(callsOf s.spec goal).length}\no {15 - fuel}\n"

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
  if s.sp != some 0 then refuse "at the return the stack pointer is not where it was at entry"
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

def placeEnv (ctx : Ctx) (p : Place) (value : Nat → Row) : List (String × SVal) :=
  p.names.map (fun (n, r) => (n, SVal.lin (value r))) ++ symEnv ctx.contract

/-- What is known at entry: each register a number below 2^64; the frame the contract allows and the return
address lie in memory; so does each run of bytes given. -/
def entryFacts (ctx : Ctx) : List Row :=
  ((List.range 16).map ranged).flatten ++
  [Lin.sub (Lin.var RSP) (Lin.const ctx.contract.stack), Lin.sub (Lin.const (2 ^ 64 - 9)) (Lin.var RSP)] ++
  ctx.contract.regions.map fun (base, len) => Lin.sub (Lin.sub (Lin.const (2 ^ 64)) (Lin.var base)) (Lin.var len)

def entrySym (ctx : Ctx) : Sym :=
  { reg := Lin.var, zf := .unknown, cf := .unknown, frame := [], facts := entryFacts ctx, bytes := [], spec := [], nvars := 16 }

/-- On first coming to the place: what holds there is shown of this state; then the state that stands for
every coming there (the kept registers and the frame as they are now, every other register any number,
and of the named ones the place's facts), and its number that decreases. -/
def generalize (ctx : Ctx) (p : Place) (s : Sym) : V (Sym × Row) :=
  if !p.keep.contains RSP || p.names.any (fun (_, r) => p.keep.contains r) then refuse "a place must keep the stack pointer, and no register it names"
  else do
    let s ← fold (establish ctx (placeEnv ctx p s.reg)) s p.facts
    let fresh := (List.range 16).filter fun r => !p.keep.contains r
    let g : Sym := { reg := fun r => if p.keep.contains r then s.reg r else Lin.var (s.nvars + r),
                     zf := .unknown, cf := .unknown, frame := s.frame, bytes := [], spec := [], nvars := s.nvars + 16,
                     facts := (fresh.map fun r => ranged (s.nvars + r)).flatten ++ entryFacts ctx }
    let env := placeEnv ctx p g.reg
    let g ← fold (suppose ctx env) g p.facts
    let (d, g) ← seval ctx env g p.decreases
    match d with
    | .val (.lin d) => do
      entail g.facts d
      pure (g, d)
    | _ => refuse "a place's number that decreases is no number"

/-- On coming to the place again: this state is one the general state stands for, and the number is less. -/
def arrive (ctx : Ctx) (p : Place) (g : Sym) (d : Row) (s : Sym) : V Unit :=
  match p.keep.find? fun r => s.reg r != g.reg r with
  | some r => refuse s!"at the place register {r} does not hold what it held on first coming there"
  | none =>
  if !(g.frame.all fun cell => s.frame.contains cell) then refuse "at the place the frame does not hold what it held on first coming there"
  else do
    let env := placeEnv ctx p s.reg
    let s ← fold (establish ctx env) s p.facts
    let (d', s) ← seval ctx env s p.decreases
    match d' with
    | .val (.lin d') => entail s.facts (Lin.sub (Lin.sub d d') (Lin.const 1))
    | _ => refuse "a place's number that decreases is no number"

/-- Every path from `pc`, to the function's return or to the place. With no general state yet, the states
in which the place is come to are given back; with one, each coming there is shown to be one of its. -/
def explore (ctx : Ctx) (general : Option (Sym × Row)) : Nat → Sym → Nat → V (List Sym)
  | 0, _, _ => refuse "a path longer than the verifier goes"
  | fuel + 1, s, pc =>
    match ctx.code.lookup pc with
    | none => refuse s!"no instruction at {pc}"
    | some i => do
      let nexts ← symInstr ctx s i
      fold (fun found (next : Sym × Next) =>
        match next.2 with
        | .returned => pure found
        | .at pc' =>
          match ctx.place with
          | some p =>
            if p.pc == pc' then
              match general with
              | some (g, d) => do arrive ctx p g d next.1; pure found
              | none => pure (found ++ [next.1])
            else do
              let more ← explore ctx general fuel next.1 pc'
              pure (found ++ more)
          | none => do
            let more ← explore ctx general fuel next.1 pc'
            pure (found ++ more)) [] nexts

def PATH : Nat := 100000

/-- The verifier. -/
def verify (ctx : Ctx) : V Unit := do
  let arrivals ← explore ctx none PATH (entrySym ctx) 0
  match ctx.place, arrivals with
  | _, [] => pure ()
  | some p, [s] => do
    let (g, d) ← generalize ctx p s
    let _ ← explore ctx (some (g, d)) PATH g p.pc
    pure ()
  | _, _ => refuse "more than one way from the entry to the place: not here yet"
  if ← finished then pure () else refuse "the proof says more than is asked of it"

/-- Does the function meet its contract, by this proof? `none`: yes. -/
def verdict (ctx : Ctx) (proof : List Item) : Option String :=
  match verify ctx proof with
  | .ok _ => none
  | .error why => some why

end Ode
