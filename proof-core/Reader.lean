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
  | .list (.atom "list" :: items) => do some (.list ((← items.mapM toSExpr).foldr .cons .nil))
  | .list [.atom "let", .atom x, e, rest] => do some (.letx x (← toSExpr e) (← toSExpr rest))
  | .list [.atom "each", e, .atom x, a, b] => do some (.each (← toSExpr e) x (← toSExpr a) (← toSExpr b))
  | .list [.atom "slice", a, lo, hi] => do some (.slice (← toSExpr a) (← toSExpr lo) (← toSExpr hi))
  | .list (.atom "with" :: a :: puts) => do some (.withx (← toSExpr a) ((← puts.mapM toSExpr).foldr .cons .nil))
  | .list (.atom "record" :: fields) => do
    -- (record (NAME E) (NAME E) …)
    let pairs ← fields.mapM fun f => match f with
      | .list [.atom n, e] => do some (n, ← toSExpr e)
      | _ => none
    some (.record (pairs.map (·.1)) ((pairs.map (·.2)).foldr .cons .nil))
  | .list [.atom "field", e, .atom x] => do some (.field (← toSExpr e) x)
  | .list [.atom "thenumber", .atom which, .atom x, a, b, cond] =>
    if which == "least" || which == "greatest" then do
      some (.theNumber (which == "greatest") x (← toSExpr a) (← toSExpr b) (← toSExpr cond))
    else none
  | .list [.atom "thepower", .atom which, .atom x, cond] =>
    if which == "least" || which == "greatest" then do some (.thePower (which == "greatest") x (← toSExpr cond)) else none
  | _ => none

def readSExpr (text : String) : Except String SExpr :=
  match parseSexp text with
  | some [e] => match toSExpr e with
    | some e => pure e
    | none => throw s!"cannot read the expression {text}"
  | _ => throw s!"cannot read the expression {text}"

structure Job where
  fns : List Fn := []               -- the statement's functions, in its order
  defs : List Def := []
  cur : Option String := none       -- in the proof: the function the lines are for
  starts : List Nat := []
  steps : List Step := []

def words (line : String) : List String := (line.splitOn " ").filter (· ≠ "")

def rest (line : String) (n : Nat) : String := " ".intercalate ((words line).drop n)

def regOrFail (name : String) : Except String Nat :=
  match regIndex name with
  | some r => pure r
  | none => throw s!"no register {name}"

/-- A vector register by its name: `zmm0` to `zmm31`. -/
def vecOrFail (name : String) : Except String Nat :=
  match if name.startsWith "zmm" then (name.drop 3).toNat? else none with
  | some r => if r < 32 then pure r else throw s!"no vector register {name}"
  | none => throw s!"no vector register {name}"

def statementKinds : List String := ["fn", "i", "arg", "returns", "result", "ensures", "ensuresw", "needs", "needsif", "below", "mbelow", "lanes", "atleast", "stack", "def"]

def Job.line (table : Array TRow) (inProof : Bool) (t : Job) (line : String) : Except String Job := do
  -- a line of the statement is of the function last named there; a line of the proof, of the one its `for` names
  let onLast (f : Fn → Fn) : Except String Job :=
    match t.fns.reverse with
    | last :: before => pure { t with fns := before.reverse ++ [f last] }
    | [] => throw s!"outside a function: {line}"
  let onCur (f : Fn → Except String Fn) : Except String Job :=
    match t.cur with
    | none => throw s!"refused: a line of a proof before any `for NAME`: {line}"
    | some name => do
      let fns ← t.fns.mapM fun g => if g.name == name then f g else pure g
      pure { t with fns := fns }
  let inPlace (f : Place → Place) : Except String Job := onCur fun g =>
    -- a line of a place is of the place last begun
    match g.places.reverse with
    | p :: before => pure { g with places := before.reverse ++ [f p] }
    | [] => throw s!"outside a place: {line}"
  match (words line).head? with
  | some kind =>
    if inProof && statementKinds.contains kind then throw s!"refused: a line of the statement in the proof: {line}"
    if !inProof && !statementKinds.contains kind then throw s!"refused: a line of a proof in the statement: {line}"
  | none => pure ()
  match words line with
  | [] => pure t
  | ["fn", name] =>
    if t.fns.any (fun g => g.name == name) then throw s!"refused: two functions are named {name}"
    else pure { t with fns := t.fns ++ [{ name := name }] }
  | "i" :: a :: b :: _ =>
    let some ins := parseSexp (rest line 3) | throw s!"cannot read {line}"
    let some (row, bind) := findRow table ins | throw s!"refused: an instruction that is no row of the table: {rest line 3}"
    let (some a, some b) := (a.toNat?, b.toNat?) | throw s!"cannot read {line}"
    onLast fun g => { g with code := g.code ++ [(a, ⟨row.effect, bind, b⟩)] }
  | ["arg", name, "number"] => onLast fun g => { g with contract := { g.contract with args := g.contract.args ++ [(name, .number)] } }
  | ["arg", name, "bytes", len] => onLast fun g => { g with contract := { g.contract with args := g.contract.args ++ [(name, .bytes len)] } }
  | ["arg", name, "out", n] => match n.toNat? with
    | some n => onLast fun g => { g with contract := { g.contract with args := g.contract.args ++ [(name, .out n)] } }
    | none => throw s!"cannot read {line}"
  | ["arg", name, "fixed", n] => match n.toNat? with
    | some n => onLast fun g => { g with contract := { g.contract with args := g.contract.args ++ [(name, .fixed n)] } }
    | none => throw s!"cannot read {line}"
  | ["arg", name, "inout", n] => match n.toNat? with
    | some n => onLast fun g => { g with contract := { g.contract with args := g.contract.args ++ [(name, .inout n)] } }
    | none => throw s!"cannot read {line}"
  | "ensuresw" :: name :: _ => do
    let e ← readSExpr (rest line 2)
    onLast fun g => { g with contract := { g.contract with ensuresW := g.contract.ensuresW ++ [⟨name, e⟩] } }
  | ["needs", what] => onLast fun g => { g with contract := { g.contract with needs := g.contract.needs ++ [what] } }
  | ["below", name, n] => match n.toNat? with
    | some n => onLast fun g => { g with contract := { g.contract with bounds := g.contract.bounds ++ [(name, n)] } }
    | none => throw s!"cannot read {line}"
  | ["mbelow", name, off, n] => match off.toNat?, n.toNat? with
    | some off, some n => onLast fun g => { g with contract := { g.contract with mbounds := g.contract.mbounds ++ [(name, off, n)] } }
    | _, _ => throw s!"cannot read {line}"
  | ["lanes", table, count] => onLast fun g => { g with contract := { g.contract with lanes := g.contract.lanes ++ [(table, count)] } }
  | ["atleast", name, n] => match n.toNat? with
    | some n => onLast fun g => { g with contract := { g.contract with atLeast := g.contract.atLeast ++ [(name, n)] } }
    | none => throw s!"cannot read {line}"
  | ["needsif", what, name, n] => match n.toNat? with
    | some n => onLast fun g => { g with contract := { g.contract with needsIf := g.contract.needsIf ++ [(what, name, n)] } }
    | none => throw s!"cannot read {line}"
  | "returns" :: _ => do
    let e ← readSExpr (rest line 1)
    onLast fun g => { g with contract := { g.contract with returns := some e } }
  | ["result", name] => onLast fun g => { g with contract := { g.contract with result := some name } }
  | "ensures" :: run :: _ =>
    match parseSexp (rest line 2) with
    | some [lo, hi, value] =>
      match toSExpr lo, toSExpr hi, toSExpr value with
      | some lo, some hi, some value =>
        onLast fun g => { g with contract := { g.contract with ensures := g.contract.ensures ++ [⟨run, lo, hi, value⟩] } }
      | _, _, _ => throw s!"cannot read {line}"
    | _ => throw s!"cannot read {line}"
  | ["stack", n] => match n.toNat? with
    | some n => onLast fun g => { g with contract := { g.contract with stack := n } }
    | none => throw s!"cannot read {line}"
  | "def" :: name :: more =>
    let params := more.takeWhile (· ≠ "=")
    pure { t with defs := t.defs ++ [⟨name, params, ← readSExpr (rest line (3 + params.length))⟩] }
  | ["for", name] =>
    if t.fns.any (fun g => g.name == name) then pure { t with cur := some name }
    else throw s!"refused: the proof speaks of {name}, which is no function of the statement"
  | ["place", pc] => onCur fun g => match pc.toNat? with
    | some pc =>
      if g.places.any (fun p => p.pc == pc) then throw s!"refused: two places at {pc}"
      else pure { g with places := g.places ++ [{ pc := pc, names := [], keep := [], facts := [], decreases := .num 0 }] }
    | none => throw s!"cannot read {line}"
  | ["name", name, reg] => do let r ← regOrFail reg; inPlace fun p => { p with names := p.names ++ [(name, r)] }
  | "keep" :: regs => do let rs ← regs.mapM regOrFail; inPlace fun p => { p with keep := p.keep ++ rs }
  | "fact" :: _ => do let e ← readSExpr (rest line 1); inPlace fun p => { p with facts := p.facts ++ [e] }
  | "decreases" :: _ => do let e ← readSExpr (rest line 1); inPlace fun p => { p with decreases := e }
  | "lane" :: x :: more => do
    -- lane X REG … = (call F THING …): in each lane X, the words of the vector registers are what F gives
    let regs := more.takeWhile (· ≠ "=")
    let rs ← regs.mapM vecOrFail
    match ← readSExpr (rest line (3 + regs.length)) with
    | .call f args => inPlace fun p => { p with lanes := p.lanes ++ [⟨rs, x, f, args⟩] }
    | _ => throw s!"refused: a place's lanes are said by the use of a definition: {line}"
  | ["t", name] => onCur fun g => pure { g with proof := g.proof ++ [.tag name 0] }
  | ["t", name, n] => match n.toNat? with
    | some n => onCur fun g => pure { g with proof := g.proof ++ [.tag name n] }
    | none => throw s!"cannot read {line}"
  | "p" :: numbers => match numbers.mapM String.toNat? with
    | some ns => pure { t with starts := t.starts ++ ns }
    | none => throw s!"cannot read {line}"
  | "s" :: numbers => match numbers.mapM String.toNat? with
    | some [i, a, j, b, d] => pure { t with steps := t.steps ++ [⟨i, a, j, b, d⟩] }
    | _ => throw s!"cannot read {line}"
  | ["q"] => do
    let t' ← onCur fun g => pure { g with proof := g.proof ++ [.proof t.starts t.steps] }
    pure { t' with starts := [], steps := [] }
  | _ => throw s!"cannot read {line}"
