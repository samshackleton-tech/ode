import Core
/-!
The verifier as a program:  `odeverify TABLE TASK`

TABLE is `../core/x86.tab`. TASK is text, a line a thing:

    i START END ROW…          an instruction of the function, as the reader of code writes it
    arg NAME number           the contract's arguments, in order
    arg NAME bytes LEN
    returns EXPRESSION
    stack N
    def NAME PARAMETER… = EXPRESSION      a definition of the specification
    place PC                  the proof: a place, then what holds there
    name NAME REGISTER
    keep REGISTER…
    fact EXPRESSION
    decreases EXPRESSION
    t NAME [N]                the proof: what the verifier asks for, in the order it asks
    r … / s … / q             a proof of arithmetic (as ArithMain.lean reads it)

An EXPRESSION is written with brackets: (num 1) (name x) (bin + A B) (ifx C A B) (index A I) (call f A…).
It answers `shown`, or what it needs or why it refuses, and ends with 0 only for `shown`.
Reading this text is not covered by any theorem.
-/
open Ode Ode.Arithmetic

partial def toSExpr : Sexp → Option SExpr
  | .list [.atom "num", .atom n] => (readInt n).map .num
  | .list [.atom "name", .atom x] => some (.name x)
  | .list [.atom "bin", .atom op, a, b] => do some (.bin op (← toSExpr a) (← toSExpr b))
  | .list [.atom "ifx", c, a, b] => do some (.ifx (← toSExpr c) (← toSExpr a) (← toSExpr b))
  | .list [.atom "index", a, i] => do some (.index (← toSExpr a) (← toSExpr i))
  | .list (.atom "call" :: .atom f :: args) => do some (.call f (← args.mapM toSExpr))
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

def Job.line (table : Array TRow) (t : Job) (line : String) : Except String Job := do
  let inPlace (f : Place → Place) : Except String Job :=
    match t.place with
    | some p => pure { t with place := some (f p) }
    | none => throw s!"outside a place: {line}"
  match words line with
  | [] => pure t
  | "i" :: a :: b :: _ =>
    let some ins := parseSexp (rest line 3) | throw s!"cannot read {line}"
    let some (row, bind) := findRow table ins | throw s!"refused: an instruction that is no row of the table: {rest line 3}"
    let (some a, some b) := (a.toNat?, b.toNat?) | throw s!"cannot read {line}"
    pure { t with code := t.code ++ [(a, ⟨row.effect, bind, b⟩)] }
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
  let c : Contract := ⟨t.args, t.returns, t.stack⟩
  let regions := c.regions.map fun (r, l) => (⟨r, l⟩ : Region)
  let rec env : List (String × Kind) → List Nat → Nat → List (String × SVal)
    | (n, .number) :: args, r :: regs, k => (n, .lin (Lin.var r)) :: env args regs k
    | (n, .bytes _) :: args, _ :: regs, k => (n, .region k) :: env args regs (k + 1)
    | _, _, _ => []
  { code := t.code, contract := c, defs := t.defs, regions := regions, env := env t.args argRegs 0, place := t.place }

def main (args : List String) : IO UInt32 := do
  match args with
  | [tablePath, taskPath] =>
    let table ← match readTable (← IO.FS.readFile tablePath) with
      | .ok t => pure t
      | .error e => IO.println e; return 2
    let lines := ((← IO.FS.readFile taskPath).splitOn "\n").map fun l => (l.replace "\r" "")
    match lines.foldlM (Job.line table) {} with
    | .error e => IO.println e; return 2
    | .ok task =>
      match verdict task.ctx task.items with
      | none => IO.println "shown"; return 0
      | some why => IO.println why; return 1
  | _ => IO.println "odeverify TABLE TASK"; return 2
