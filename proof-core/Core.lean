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
    | rest => c :: rest

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

abbrev V := StateT (List Item) (Except String)

def refuse (why : String) : V α := throw ("refused: " ++ why)

def showRow (r : Row) : String := " ".intercalate (toString r.constant :: r.coeff.map toString)

def need (what : String) (facts goals : List Row) : V α :=
  throw ("need " ++ what ++ "\n" ++ String.join (facts.map fun f => "f " ++ showRow f ++ "\n")
    ++ String.join (goals.map fun g => "g " ++ showRow g ++ "\n"))

def pop : V (Option Item) := do
  match ← get with
  | [] => return none
  | i :: rest => set rest; return some i

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
def entail (facts : List Row) (g : Row) : V Unit := do
  if plain facts g then return
  match ← pop with
  | some (.proof starts steps) =>
    if Arithmetic.refutes (negation g :: facts) starts steps then return
    else refuse "a proof of arithmetic does not show what is to be shown"
  | some (.tag ..) => refuse "a proof of arithmetic is expected"
  | none => need "entail" facts [g]

inductive Cmp where
  | lt | eq | gt
  deriving DecidableEq

/-- Which of the two is the greater, by the facts. -/
def compare (facts : List Row) (a b : Row) : V Cmp := do
  let d := Lin.sub a b
  match Lin.isConst d with
  | some k => return if k < 0 then .lt else if k == 0 then .eq else .gt
  | none =>
    match ← pop with
    | some (.tag "eq" _) => entail facts d; entail facts (Lin.scale (-1) d); return .eq
    | some (.tag "lt" _) => entail facts (Lin.sub (Lin.scale (-1) d) (Lin.const 1)); return .lt
    | some (.tag "gt" _) => entail facts (Lin.sub d (Lin.const 1)); return .gt
    | some _ => refuse "lt, eq or gt is expected"
    | none => need "compare" facts [d]

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
  reg : List Row                  -- the sixteen registers
  zf : Flag
  cf : Flag
  frame : List (Int × Row)        -- eight bytes at so many bytes from where the stack pointer was at entry
  facts : List Row                -- each `≥ 0`
  bytes : List (Nat × Nat × Row)  -- (unknown, run, place): the unknown is the byte at that place of that run
  spec : List SFact
  nvars : Nat                     -- unknowns in use: 0 to 15 are the registers at entry
  deriving Inhabited

/-- A run of bytes the function is given: the registers (at entry) with its address and its length. -/
structure Region where
  base : Nat
  len : Nat
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
  regions : List Region
  env : List (String × SVal)      -- the contract's names
  place : Option Place
  deriving Inhabited

def Sym.get (s : Sym) (r : Nat) : Row := s.reg.getD r (Lin.const 0)
def Sym.put (s : Sym) (r : Nat) (v : Row) : Sym := { s with reg := s.reg.set r v }

/-- How far the stack pointer is from where it was at entry. -/
def Sym.sp (s : Sym) : Option Int := Lin.isConst (Lin.sub (s.get RSP) (Lin.var RSP))

def top : Int := 2 ^ 64 - 1

def ranged (v : Nat) : List Row := [Lin.var v, Lin.sub (Lin.const top) (Lin.var v)]

/-- The byte at place `o` of run `r`: shown to be within the run; one unknown for one place. -/
def readByte (ctx : Ctx) (s : Sym) (r : Nat) (o : Row) : V (Row × Sym) := do
  let some region := ctx.regions[r]? | refuse "no such run of bytes"
  entail s.facts o
  entail s.facts (Lin.sub (Lin.sub (Lin.var region.len) o) (Lin.const 1))
  match s.bytes.find? fun (_, r', o') => r' == r && o' == o with
  | some (v, _, _) => return (Lin.var v, s)
  | none =>
    let v := s.nvars
    return (Lin.var v, { s with nvars := v + 1, bytes := (v, r, o) :: s.bytes,
                                facts := Lin.var v :: Lin.sub (Lin.const 255) (Lin.var v) :: s.facts })

inductive Where where
  | frame (off : Int)
  | region (r : Nat) (off : Row)

def findRegion (addr : Row) : List Region → Nat → Option Where
  | [], _ => none
  | g :: gs, k => if Lin.coeffOf addr g.base == 1 then some (.region k (Lin.sub addr (Lin.var g.base))) else findRegion addr gs (k + 1)

/-- Where an address is: in the frame, or in a run of bytes given. -/
def locate (ctx : Ctx) (addr : Row) : Option Where :=
  match Lin.isConst (Lin.sub addr (Lin.var RSP)) with
  | some c => some (.frame c)
  | none => findRegion addr ctx.regions 0

/-- A number of 2^63 or more, as the number below zero that is the same modulo 2^64. -/
def signed (r : Row) : Row :=
  match Lin.isConst r with
  | some k => if 2 ^ 63 ≤ k then Lin.const (k - 2 ^ 64) else r
  | none => r

/-! ## An instruction's effect, on symbols -/

inductive EV where
  | lin (r : Row)
  | equal (a b : Row)
  | below (a b : Row)

def EV.row : EV → V Row
  | .lin r => pure r
  | _ => refuse "a flag's value where a number is expected"

def address (vs : List EV) : V Row := do
  let rows ← vs.mapM EV.row
  return rows.foldl (fun a r => Lin.add a (signed r)) (Lin.const 0)

def inRange (facts : List Row) (r : Row) : V Unit := do
  entail facts r
  entail facts (Lin.sub (Lin.const top) r)

mutual
  def symValue (ctx : Ctx) (bind : Bind) : Sym → Expr → V (EV × Sym)
    | s, .number n => pure (.lin (Lin.const n), s)
    | _, .lane _ _ => refuse "a vector register: not here yet"
    | s, .name n =>
      if isNumberLetter n then
        match (bind.lookup n).bind readInt with
        | some i => pure (.lin (Lin.const (i % (2 ^ 64))), s)
        | none => refuse "a number that cannot be read"
      else match regOf bind n with
        | some r => pure (.lin (s.get r), s)
        | none => refuse s!"no rule for {n}"
    | s, .call f args => do
      let (vs, s) ← symValues ctx bind s args
      match memSize f with
      | some size =>
        let addr ← address vs
        match locate ctx addr, size with
        | some (.frame c), 8 =>
          let some sp := s.sp | refuse "the stack pointer is not in the frame"
          if sp ≤ c && c + 8 ≤ 0 then
            match s.frame.lookup c with
            | some v => pure (.lin v, s)
            | none => refuse "a read of the frame where nothing was written"
          else refuse "a read outside the frame in use"
        | some (.region r o), 1 => do
          let (v, s) ← readByte ctx s r o
          pure (.lin v, s)
        | _, _ => refuse "a read that is neither eight bytes of the frame nor a byte of a run given"
      | none =>
        match vs with
        | [.lin a, .lin b] =>
          if f == "add64" || f == "at" then do
            let r := Lin.add (signed a) (signed b)
            inRange s.facts r
            pure (.lin r, s)
          else if f == "sub64" then do
            let r := Lin.sub (signed a) (signed b)
            inRange s.facts r
            pure (.lin r, s)
          else if f == "equal" then pure (.equal a b, s)
          else if f == "below" then pure (.below a b, s)
          else refuse s!"no rule for {f}"
        | _ => refuse s!"no rule for {f}"
  def symValues (ctx : Ctx) (bind : Bind) : Sym → List Expr → V (List EV × Sym)
    | s, [] => pure ([], s)
    | s, e :: es => do
      let (v, s) ← symValue ctx bind s e
      let (vs, s) ← symValues ctx bind s es
      pure (v :: vs, s)
end

def symStmt (ctx : Ctx) (bind : Bind) (s : Sym) : Stmt → V Sym
  | .nothing => pure s
  | .set place v => do
    let unknown := match v with
      | .name n => n == "unknown"
      | _ => false
    match place with
    | .name n =>
      if n == "zf" || n == "cf" then do
        let (flag, s) ← if unknown then pure (Flag.unknown, s) else do
          let (ev, s) ← symValue ctx bind s v
          match ev with
          | .equal a b => pure (Flag.equal a b, s)
          | .below a b => pure (Flag.below a b, s)
          | .lin _ => refuse "a number where a flag's value is expected"
        pure (if n == "zf" then { s with zf := flag } else { s with cf := flag })
      else if unknown then refuse "a register of which the row says nothing: not here yet"
      else do
        let some r := regOf bind n | refuse s!"no rule for {n}"
        let (ev, s) ← symValue ctx bind s v
        pure (s.put r (← ev.row))
    | .call f args => do
      if unknown then refuse "memory of which the row says nothing"
      let (ev, s) ← symValue ctx bind s v
      let x ← ev.row
      let (vs, s) ← symValues ctx bind s args
      let addr ← address vs
      match memSize f, locate ctx addr with
      | some 8, some (.frame c) =>
        let some sp := s.sp | refuse "the stack pointer is not in the frame"
        if sp ≤ c && c + 8 ≤ 0 then
          pure { s with frame := (c, x) :: s.frame.filter fun (o, _) => o + 8 ≤ c || c + 8 ≤ o }
        else refuse "a write outside the frame in use"
      | _, _ => refuse "a write that is not eight bytes of the frame: not here yet"
    | _ => refuse "a row that sets what is no place"
  | _ => refuse "a jump, a call or a return among other statements"

/-- After an instruction: the stack pointer is in the frame the contract allows, and nothing is remembered
below it. -/
def settle (ctx : Ctx) (s : Sym) : V Sym := do
  let some sp := s.sp | refuse "the stack pointer is not in the frame"
  if sp ≤ 0 && -(ctx.contract.stack : Int) ≤ sp then pure { s with frame := s.frame.filter fun (o, _) => sp ≤ o }
  else refuse "the stack pointer leaves the frame the contract allows"

/-- A way a jump can go: the rows assumed on it. No input takes a way the proof shows impossible. -/
def assume (s : Sym) (rows : List Row) : V (Option Sym) := do
  if rows.any fun r => match Lin.isConst r with
      | some k => decide (k < 0)
      | none => false
  then return none
  let rows := rows.filter fun r => (Lin.isConst r).isNone
  if rows.isEmpty then return some s
  let s' := { s with facts := rows ++ s.facts }
  match ← pop with
  | some (.tag "live" _) => return some s'
  | some (.tag "dead" _) =>
    match ← pop with
    | some (.proof starts steps) =>
      if Arithmetic.refutes s'.facts starts steps then return none
      else refuse "a proof of arithmetic does not show that no input goes this way"
    | _ => refuse "a proof of arithmetic is expected"
  | some _ => refuse "live or dead is expected"
  | none => need "branch" s'.facts []

/-! ## The specification, on symbols -/

inductive SRes where
  | val (v : SVal)
  | tail (c : SCall)      -- the value is that of this use of a definition, which is not opened here

def SRes.lin : SRes → V Row
  | .val (.lin r) => pure r
  | _ => refuse "a number is expected (a use of a definition where its value is needed: not here yet)"

mutual
  def seval (ctx : Ctx) (env : List (String × SVal)) : Sym → SExpr → V (SRes × Sym)
    | s, .num n => pure (.val (.lin (Lin.const n)), s)
    | s, .name x =>
      match env.lookup x with
      | some v => pure (.val v, s)
      | none => refuse s!"the name {x} stands for nothing here"
    | s, .bin op a b => do
      let (x, s) ← seval ctx env s a
      let (y, s) ← seval ctx env s b
      let x ← x.lin
      let y ← y.lin
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
      let (vs, s) ← sevalArgs ctx env s args
      if f == "len" then
        match vs with
        | [.region r] =>
          match ctx.regions[r]? with
          | some g => pure (.val (.lin (Lin.var g.len)), s)
          | none => refuse "no such run of bytes"
        | _ => refuse "the length of what is no run of bytes"
      else match findDef ctx.defs f with
        | some d => if d.params.length == vs.length then pure (.tail ⟨f, vs⟩, s) else refuse s!"{f} takes another number of things"
        | none => refuse s!"no definition {f}"
  def sevalArgs (ctx : Ctx) (env : List (String × SVal)) : Sym → List SExpr → V (List SVal × Sym)
    | s, [] => pure ([], s)
    | s, e :: es => do
      let (v, s) ← seval ctx env s e
      let (vs, s) ← sevalArgs ctx env s es
      match v with
      | .val v => pure (v :: vs, s)
      | .tail _ => refuse "a use of a definition inside another: not here yet"
end

/-- A use of a definition, opened once: a fact of what it is the same as, or of its value. -/
def openCall (ctx : Ctx) (s : Sym) (c : SCall) : V Sym := do
  let some d := findDef ctx.defs c.f | refuse s!"no definition {c.f}"
  if d.params.length != c.args.length then refuse s!"{c.f} takes another number of things"
  let (res, s) ← seval ctx (d.params.zip c.args) s d.body
  match res with
  | .tail c' => pure { s with spec := .same c c' :: s.spec }
  | .val (.lin v) => pure { s with spec := .value c v :: s.spec }
  | .val _ => refuse "a definition whose value is no number: not here yet"

def insert (c : SCall) (l : List SCall) : List SCall := if l.contains c then l else l ++ [c]

/-- The uses that the facts say are the same as one of `seen`. -/
def reach (facts : List SFact) : Nat → List SCall → List SCall
  | 0, seen => seen
  | fuel + 1, seen =>
    reach facts fuel (facts.foldl (fun seen f =>
      match f with
      | .same a b => if seen.contains a then insert b seen else if seen.contains b then insert a seen else seen
      | .value .. => seen) seen)

def holdsSpec (facts : List SFact) : SFact → Bool
  | .same a b => (reach facts (facts.length + 1) [a]).contains b
  | .value c v => (reach facts (facts.length + 1) [c]).any fun c' => facts.contains (.value c' v)

def callsOf (facts : List SFact) (goal : SFact) : List SCall :=
  let of : SFact → List SCall
    | .same a b => [a, b]
    | .value c _ => [c]
  ((facts.reverse ++ [goal]).map of).flatten.foldl (fun l c => insert c l) []

/-- A fact of the specification, from the facts held and uses of definitions the proof says to open. -/
def specGoal (ctx : Ctx) : Nat → Sym → SFact → V Sym
  | 0, _, _ => refuse "too many definitions opened for one fact"
  | fuel + 1, s, goal => do
    if holdsSpec s.spec goal then return s
    match ← pop with
    | some (.tag "open" n) =>
      match (callsOf s.spec goal)[n]? with
      | some c => do
        let s ← openCall ctx s c
        specGoal ctx fuel s goal
      | none => refuse "no such use of a definition to open"
    | some _ => refuse "open is expected"
    | none => throw s!"need spec\nc {(callsOf s.spec goal).length}\no {15 - fuel}\n"

/-- What a line `fact …` of a place, or the contract's `returns`, says: rows, and facts of the specification. -/
def assertion (ctx : Ctx) (env : List (String × SVal)) (s : Sym) : SExpr → V (List Row × List SFact × Sym)
  | .bin op a b => do
    let (x, s) ← seval ctx env s a
    let (y, s) ← seval ctx env s b
    match x, y with
    | .val (.lin x), .val (.lin y) =>
      let d := Lin.sub x y
      let one := Lin.const 1
      if op == "==" then pure ([d, Lin.scale (-1) d], [], s)
      else if op == "<=" then pure ([Lin.scale (-1) d], [], s)
      else if op == "<" then pure ([Lin.sub (Lin.scale (-1) d) one], [], s)
      else if op == ">=" then pure ([d], [], s)
      else if op == ">" then pure ([Lin.sub d one], [], s)
      else refuse s!"a fact with {op}: not here yet"
    | .tail c, .tail c' => if op == "==" then pure ([], [.same c c'], s) else refuse "two uses of definitions can only be said to be equal"
    | .tail c, .val (.lin v) => if op == "==" then pure ([], [.value c v], s) else refuse "a use of a definition can only be said to be equal to a number"
    | .val (.lin v), .tail c => if op == "==" then pure ([], [.value c v], s) else refuse "a use of a definition can only be said to be equal to a number"
    | _, _ => refuse "a fact about what is no number"
  | _ => refuse "a fact that is no comparison"

/-- Show what the assertion says, of the state `s`. -/
def establish (ctx : Ctx) (env : List (String × SVal)) (s : Sym) (e : SExpr) : V Sym := do
  let (rows, facts, s) ← assertion ctx env s e
  rows.forM (entail s.facts)
  facts.foldlM (specGoal ctx 16) s

/-! ## Return, places, paths -/

/-- At the return: the stack pointer is where it was, the registers a callee keeps hold what they held at
entry, and rax holds what the contract says. -/
def symReturn (ctx : Ctx) (s : Sym) : V Unit := do
  if s.sp != some 0 then refuse "at the return the stack pointer is not where it was at entry"
  for r in calleeSaved do
    if s.get r != Lin.var r then refuse s!"at the return register {r} does not hold what it held at entry"
  match ctx.contract.returns with
  | none => pure ()
  | some e => do
    let (res, s) ← seval ctx ctx.env s e
    match res with
    | .val (.lin v) =>
      let d := Lin.sub v (s.get 0)
      entail s.facts d
      entail s.facts (Lin.scale (-1) d)
    | .tail c => let _ ← specGoal ctx 16 s (.value c (s.get 0))
    | .val _ => refuse "a function returns a number"

inductive Next where
  | at (pc : Nat)
  | returned

def symInstr (ctx : Ctx) (s : Sym) (i : Instr) : V (List (Sym × Next)) := do
  match i.effect with
  | [.ret] => symReturn ctx s; pure [(s, .returned)]
  | [.jump target cond] =>
    let target := match target with
      | .name n => ((i.bind.lookup n).bind readInt).map Int.toNat
      | _ => none
    let some t := target | refuse "a jump to a place that cannot be read"
    match cond with
    | none => pure [(s, .at t)]
    | some (flag, want) =>
      let ways ← match (if flag == "zf" then s.zf else s.cf) with
        | .unknown => refuse "a jump on a flag of which nothing is known"
        | .equal a b =>
          let d := Lin.sub a b
          pure [(true, [d, Lin.scale (-1) d]), (false, [Lin.sub d (Lin.const 1)]), (false, [Lin.sub (Lin.scale (-1) d) (Lin.const 1)])]
        | .below a b => pure [(true, [Lin.sub (Lin.sub b a) (Lin.const 1)]), (false, [Lin.sub a b])]
      let mut out := []
      for (set, rows) in ways do
        match ← assume s rows with
        | some s' => out := out ++ [(s', Next.at (if set == want then t else i.next))]
        | none => pure ()
      pure out
  | effect => do
    let s ← effect.foldlM (symStmt ctx i.bind) s
    let s ← settle ctx s
    pure [(s, .at i.next)]

def placeEnv (ctx : Ctx) (p : Place) (value : Nat → Row) : List (String × SVal) :=
  p.names.map (fun (n, r) => (n, SVal.lin (value r))) ++ ctx.env

/-- On first coming to the place: what holds there is shown of this state; then the state that stands for
every coming there (the named registers any numbers of which the place's facts hold, the kept registers
and the frame as they are now, the other registers anything), and its number that decreases. -/
def generalize (ctx : Ctx) (p : Place) (entry : List Row) (s : Sym) : V (Sym × Row) := do
  if !p.keep.contains RSP then refuse "a place must keep the stack pointer"
  let s ← p.facts.foldlM (establish ctx (placeEnv ctx p s.get)) s
  let fresh := (List.range 16).filter fun r => !p.keep.contains r
  let reg := (List.range 16).map fun r => if p.keep.contains r then s.get r else Lin.var (s.nvars + r)
  let facts := (fresh.map fun r => ranged (s.nvars + r)).flatten ++ entry
  let g0 : Sym := { reg := reg, zf := .unknown, cf := .unknown, frame := s.frame, facts := facts, bytes := [], spec := [], nvars := s.nvars + 16 }
  let env := placeEnv ctx p g0.get
  let mut g := g0
  for e in p.facts do
    let (rows, facts, g') ← assertion ctx env g e
    g := { g' with facts := rows ++ g'.facts, spec := facts ++ g'.spec }
  let (d, general) ← seval ctx env g p.decreases
  let d ← d.lin
  entail general.facts d
  pure (general, d)

/-- On coming to the place again: this state is one the general state stands for, and the number is less. -/
def arrive (ctx : Ctx) (p : Place) (g : Sym) (d : Row) (s : Sym) : V Unit := do
  for r in p.keep do
    if s.get r != g.get r then refuse s!"at the place register {r} does not hold what it held on first coming there"
  for cell in g.frame do
    if !s.frame.contains cell then refuse "at the place the frame does not hold what it held on first coming there"
  let env := placeEnv ctx p s.get
  let s ← p.facts.foldlM (establish ctx env) s
  let (d', s) ← seval ctx env s p.decreases
  let d' ← d'.lin
  entail s.facts (Lin.sub (Lin.sub d d') (Lin.const 1))

/-- Every path from `pc`, to the function's return or to the place. With no general state yet, the states
in which the place is come to are given back; with one, each coming there is shown to be one of its. -/
def explore (ctx : Ctx) (general : Option (Sym × Row)) : Nat → Sym → Nat → V (List Sym)
  | 0, _, _ => refuse "a path longer than the verifier goes"
  | fuel + 1, s, pc => do
    let some i := ctx.code.lookup pc | refuse s!"no instruction at {pc}"
    let nexts ← symInstr ctx s i
    nexts.foldlM (fun found (s', next) => do
      match next with
      | .returned => pure found
      | .at pc' =>
        match ctx.place with
        | some p =>
          if p.pc == pc' then
            match general with
            | some (g, d) => do arrive ctx p g d s'; pure found
            | none => pure (found ++ [s'])
          else do pure (found ++ (← explore ctx general fuel s' pc'))
        | none => do pure (found ++ (← explore ctx general fuel s' pc'))) []

def PATH : Nat := 100000

/-- What is known at entry: each register a number below 2^64; the frame the contract allows and the return
address lie in memory; so does each run of bytes given. -/
def entryFacts (ctx : Ctx) : List Row :=
  ((List.range 16).map ranged).flatten ++
  [Lin.sub (Lin.var RSP) (Lin.const ctx.contract.stack), Lin.sub (Lin.const (2 ^ 64 - 8)) (Lin.var RSP)] ++
  ctx.regions.map fun g => Lin.sub (Lin.sub (Lin.const (2 ^ 64)) (Lin.var g.base)) (Lin.var g.len)

def entrySym (ctx : Ctx) : Sym :=
  { reg := (List.range 16).map Lin.var, zf := .unknown, cf := .unknown, frame := [], facts := entryFacts ctx,
    bytes := [], spec := [], nvars := 16 }

/-- The verifier. -/
def verify (ctx : Ctx) : V Unit := do
  let arrivals ← explore ctx none PATH (entrySym ctx) 0
  match ctx.place, arrivals with
  | _, [] => pure ()
  | some p, [s] => do
    let (g, d) ← generalize ctx p (entryFacts ctx) s
    let _ ← explore ctx (some (g, d)) PATH g p.pc
  | _, _ => refuse "more than one way from the entry to the place: not here yet"
  if !(← get).isEmpty then refuse "the proof says more than is asked of it"

/-- Does the function meet its contract, by this proof? `none`: yes. -/
def verdict (ctx : Ctx) (proof : List Item) : Option String :=
  match (verify ctx).run proof with
  | .ok _ => none
  | .error why => some why

end Ode
