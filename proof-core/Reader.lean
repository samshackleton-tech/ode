import Core
/-!
The lines of a statement and of a proof, read (Main.lean says what the lines are). No theorem covers this
reading.
-/
open Ode Ode.Arithmetic

partial def toSExpr : Sexp → Option SExpr
  | .list [.atom "num", .atom n] => (readInt n).map .num
  | .list [.atom "name", .atom x] => some (.name x)
  | .list [.atom "bin", .atom op, a, b] => do some (.bin op (← toSExpr a) (← toSExpr b))
  | .list [.atom "ifx", c, a, b] => do some (.ifx (← toSExpr c) (← toSExpr a) (← toSExpr b))
  | .list [.atom "index", a, i] => do some (.index (← toSExpr a) (← toSExpr i))
  | .list (.atom "call" :: .atom f :: args) => do some (.call f ((← args.mapM toSExpr).foldr .cons .nil))
  | _ => none

def readSExpr (text : String) : Except String SExpr :=
  match parseSexp text with
  | some [e] => match toSExpr e with
    | some e => pure e
    | none => throw s!"cannot read the expression {text}"
  | _ => throw s!"cannot read the expression {text}"

structure Job where
  code : List (Nat × Instr) := []
  args : List (String × Kind) := []
  returns : Option SExpr := none
  stack : Nat := 0
  defs : List Def := []
  callees : List (String × Contract) := []
  place : Option Place := none
  items : List Item := []
  starts : List Row := []
  steps : List Step := []

def words (line : String) : List String := (line.splitOn " ").filter (· ≠ "")

def rest (line : String) (n : Nat) : String := " ".intercalate ((words line).drop n)

def regOrFail (name : String) : Except String Nat :=
  match regIndex name with
  | some r => pure r
  | none => throw s!"no register {name}"

def statementKinds : List String := ["i", "arg", "returns", "stack", "def", "callee", "carg", "creturns", "cstack"]

def Job.line (table : Array TRow) (inProof : Bool) (t : Job) (line : String) : Except String Job := do
  let inPlace (f : Place → Place) : Except String Job :=
    match t.place with
    | some p => pure { t with place := some (f p) }
    | none => throw s!"outside a place: {line}"
  let inCallee (f : Contract → Contract) : Except String Job :=
    match t.callees.reverse with
    | (name, c) :: before => pure { t with callees := before.reverse ++ [(name, f c)] }
    | [] => throw s!"outside a called function's contract: {line}"
  match (words line).head? with
  | some kind =>
    if inProof && statementKinds.contains kind then throw s!"refused: a line of the statement in the proof: {line}"
    if !inProof && !statementKinds.contains kind then throw s!"refused: a line of a proof in the statement: {line}"
  | none => pure ()
  match words line with
  | [] => pure t
  | "i" :: a :: b :: _ =>
    let some ins := parseSexp (rest line 3) | throw s!"cannot read {line}"
    let some (row, bind) := findRow table ins | throw s!"refused: an instruction that is no row of the table: {rest line 3}"
    let (some a, some b) := (a.toNat?, b.toNat?) | throw s!"cannot read {line}"
    pure { t with code := t.code ++ [(a, ⟨row.effect, bind, b⟩)] }
  | ["callee", name] => pure { t with callees := t.callees ++ [(name, ⟨[], none, 0⟩)] }
  | "carg" :: name :: kind =>
    let k ← match kind with
      | ["number"] => pure Kind.number
      | ["bytes", len] => pure (Kind.bytes len)
      | _ => throw s!"cannot read {line}"
    inCallee fun c => { c with args := c.args ++ [(name, k)] }
  | "creturns" :: _ => do let e ← readSExpr (rest line 1); inCallee fun c => { c with returns := some e }
  | ["cstack", n] => match n.toNat? with
    | some n => inCallee fun c => { c with stack := n }
    | none => throw s!"cannot read {line}"
  | ["arg", name, "number"] => pure { t with args := t.args ++ [(name, .number)] }
  | ["arg", name, "bytes", len] => pure { t with args := t.args ++ [(name, .bytes len)] }
  | "returns" :: _ => pure { t with returns := some (← readSExpr (rest line 1)) }
  | ["stack", n] => match n.toNat? with
    | some n => pure { t with stack := n }
    | none => throw s!"cannot read {line}"
  | "def" :: name :: more =>
    let params := more.takeWhile (· ≠ "=")
    pure { t with defs := t.defs ++ [⟨name, params, ← readSExpr (rest line (3 + params.length))⟩] }
  | ["place", pc] => match pc.toNat?, t.place with
    | some pc, none => pure { t with place := some ⟨pc, [], [], [], .num 0⟩ }
    | _, _ => throw s!"cannot read {line} (one place a function: not more yet)"
  | ["name", name, reg] => do let r ← regOrFail reg; inPlace fun p => { p with names := p.names ++ [(name, r)] }
  | "keep" :: regs => do let rs ← regs.mapM regOrFail; inPlace fun p => { p with keep := p.keep ++ rs }
  | "fact" :: _ => do let e ← readSExpr (rest line 1); inPlace fun p => { p with facts := p.facts ++ [e] }
  | "decreases" :: _ => do let e ← readSExpr (rest line 1); inPlace fun p => { p with decreases := e }
  | ["t", name] => pure { t with items := t.items ++ [.tag name 0] }
  | ["t", name, n] => match n.toNat? with
    | some n => pure { t with items := t.items ++ [.tag name n] }
    | none => throw s!"cannot read {line}"
  | "r" :: numbers => match numbers.mapM String.toInt? with
    | some (k :: cs) => pure { t with starts := t.starts ++ [⟨cs, k⟩] }
    | _ => throw s!"cannot read {line}"
  | "s" :: numbers => match numbers.mapM String.toNat? with
    | some [i, a, j, b, d] => pure { t with steps := t.steps ++ [⟨i, a, j, b, d⟩] }
    | _ => throw s!"cannot read {line}"
  | ["q"] => pure { t with items := t.items ++ [.proof t.starts t.steps], starts := [], steps := [] }
  | _ => throw s!"cannot read {line}"

def Job.ctx (t : Job) : Ctx :=
  { code := t.code, contract := ⟨t.args, t.returns, t.stack⟩, defs := t.defs, place := t.place, callees := t.callees }
