import Machine
/-!
# What a specification says, and what a contract promises

A specification's definitions are expressions over whole numbers and runs of bytes; `evalSpec` is what
they mean, as a value or as nothing (a definition that does not come to an end, an index outside its run,
a difference below zero: the numbers of a specification are zero and up).
`Meets` is what it is for a function's code to meet a contract: the statement the verifier's yes stands for.

Here so far: definitions that are one expression (numbers, `if`, comparisons, `+ - *`, `a[i]`, `len`,
uses of definitions); contracts whose arguments are numbers and runs of `n` bytes that the function only
reads, with `returns` and `stack`. Not here yet: `requires`, `ensures` (memory written), `trace`, calls.
-/
namespace Ode

inductive SExpr where
  | num (n : Int)
  | name (x : String)
  | bin (op : String) (a b : SExpr)
  | ifx (c a b : SExpr)
  | index (a i : SExpr)
  | call (f : String) (args : SExpr)      -- the things a definition is used with: `cons a (cons b … nil)`
  | nil
  | cons (a rest : SExpr)
  deriving Repr, Inhabited

inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  | bytes (l : List Nat)
  deriving Repr, DecidableEq, Inhabited

structure Def where
  name : String
  params : List String
  body : SExpr
  deriving Repr, Inhabited

def binop (op : String) : Val → Val → Option Val
  | .int a, .int b =>
    if op == "+" then some (.int (a + b))
    else if op == "-" then (if b ≤ a then some (.int (a - b)) else none)     -- (no number is below zero)
    else if op == "*" then some (.int (a * b))
    else if op == "==" then some (.bool (a == b))
    else if op == "!=" then some (.bool (a != b))
    else if op == "<" then some (.bool (a < b))
    else if op == "<=" then some (.bool (a ≤ b))
    else if op == ">" then some (.bool (b < a))
    else if op == ">=" then some (.bool (b ≤ a))
    else none
  | _, _ => none

def findDef (defs : List Def) (f : String) : Option Def := defs.find? fun d => d.name == f

/-- The values of the things a definition is used with, each by `ev`. -/
def evalList (ev : SExpr → Option Val) : SExpr → Option (List Val)
  | .nil => some []
  | .cons a rest =>
    match ev a, evalList ev rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none
  | _ => none

/-- The value of an expression, where the names of `env` are these values; `none` where it has none within
`fuel` uses of definitions and operators nested. -/
def evalSpec (defs : List Def) : Nat → List (String × Val) → SExpr → Option Val
  | 0, _, _ => none
  | fuel + 1, env, e =>
    match e with
    | .num n => if 0 ≤ n then some (.int n) else none
    | .name x => env.lookup x
    | .bin op a b =>
      match evalSpec defs fuel env a, evalSpec defs fuel env b with
      | some x, some y => binop op x y
      | _, _ => none
    | .ifx c a b =>
      match evalSpec defs fuel env c with
      | some (.bool true) => evalSpec defs fuel env a
      | some (.bool false) => evalSpec defs fuel env b
      | _ => none
    | .index a i =>
      match evalSpec defs fuel env a, evalSpec defs fuel env i with
      | some (.bytes l), some (.int k) => if 0 ≤ k then (l[k.toNat]?).map fun b => .int b else none
      | _, _ => none
    | .call f args =>
      match evalList (evalSpec defs fuel env) args with
      | none => none
      | some vs =>
        if f == "len" then
          match vs with
          | [.bytes l] => some (.int l.length)
          | _ => none
        else
          match findDef defs f with
          | some d => if d.params.length == vs.length then evalSpec defs fuel (d.params.zip vs) d.body else none
          | none => none
    | .nil => none
    | .cons _ _ => none

/-- The expression has the value `v`. -/
def Value (defs : List Def) (env : List (String × Val)) (e : SExpr) (v : Val) : Prop :=
  ∃ fuel, evalSpec defs fuel env e = some v

inductive Kind where
  | number                      -- a whole number, in the argument's register
  | bytes (len : String)        -- the address, in the argument's register, of as many bytes as the number argument `len` says
  deriving Repr, Inhabited

structure Contract where
  args : List (String × Kind)
  returns : Option SExpr
  stack : Nat
  deriving Repr, Inhabited

/-- The registers arguments are in, in their order: rdi, rsi, rdx, rcx, r8, r9. -/
def argRegs : List Nat := [7, 6, 2, 1, 8, 9]

def calleeSaved : List Nat := [3, 5, 12, 13, 14, 15]

def regOfIn (name : String) : List (String × Kind) → List Nat → Option Nat
  | (n, _) :: args, r :: regs => if n == name then some r else regOfIn name args regs
  | _, _ => none

/-- The register of the argument of that name. -/
def Contract.regOf (c : Contract) (name : String) : Option Nat := regOfIn name c.args argRegs

def regionsIn (c : Contract) : List (String × Kind) → List Nat → List (Nat × Nat)
  | (_, .bytes len) :: args, r :: regs =>
    match c.regOf len with
    | some l => (r, l) :: regionsIn c args regs
    | none => regionsIn c args regs
  | (_, .number) :: args, _ :: regs => regionsIn c args regs
  | _, _ => []

/-- The runs of bytes the function is given: (the register with the address, the register with the length). -/
def Contract.regions (c : Contract) : List (Nat × Nat) := regionsIn c c.args argRegs

def envIn (c : Contract) (s : State) : List (String × Kind) → List Nat → List (String × Val)
  | (n, .number) :: args, r :: regs => (n, .int (s.reg r)) :: envIn c s args regs
  | (n, .bytes len) :: args, r :: regs =>
    match c.regOf len with
    | some l => (n, .bytes ((List.range (s.reg l)).map fun k => s.mem (s.reg r + k))) :: envIn c s args regs
    | none => envIn c s args regs
  | _, _ => []

/-- The names of the contract as values, in a state at entry: a number is its register; a run of bytes is
what memory holds there. -/
def Contract.env (c : Contract) (s : State) : List (String × Val) := envIn c s c.args argRegs

def Contract.inFrame (c : Contract) (s : State) (a : Nat) : Bool := s.reg RSP - c.stack ≤ a && a < s.reg RSP

/-- What the function may touch, `s` being the state at entry: it may read the runs of bytes it is given,
its own frame and the return address above it; it may write its own frame. -/
def Contract.perm (c : Contract) (s : State) : Perm where
  read a := (c.inFrame s a || s.reg RSP ≤ a && a < s.reg RSP + 8) || c.regions.any fun (r, l) => s.reg r ≤ a && a < s.reg r + s.reg l
  write a := c.inFrame s a

/-- What the caller sees to. -/
def Contract.pre (c : Contract) (p : Program) (s : State) : Prop :=
  s.rip = p.base ∧ (∀ r, s.reg r < M64) ∧ (∀ a, s.mem a < 256) ∧
  c.stack ≤ s.reg RSP ∧ s.reg RSP + 8 < M64 ∧
  ∀ r l, (r, l) ∈ c.regions →
    s.reg r + s.reg l ≤ M64 ∧ (s.reg r + s.reg l ≤ s.reg RSP - c.stack ∨ s.reg RSP + 8 ≤ s.reg r)

/-- What the function leaves, `s` being the state at entry: it has returned to its caller with the stack
pointer above the return address, the registers a callee keeps as they were, memory outside its own frame
as it was, and in rax the value the contract says. -/
def Contract.post (c : Contract) (defs : List Def) (s s' : State) : Prop :=
  s'.rip = load s.mem (s.reg RSP) 8 ∧ s'.reg RSP = s.reg RSP + 8 ∧
  (∀ r ∈ calleeSaved, s'.reg r = s.reg r) ∧
  (∀ a, c.inFrame s a = false → s'.mem a = s.mem a) ∧
  ∀ e, c.returns = some e → Value defs (c.env s) e (.int (s'.reg 0))

/-- The function's code meets the contract. -/
def Meets (c : Contract) (defs : List Def) (p : Program) : Prop :=
  ∀ s, c.pre p s → Runs (c.perm s) p (c.post defs s) s

end Ode
