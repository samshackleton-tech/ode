import Table
/-!
# The machine, as the table says it

What a row's EFFECT does to registers, two flags and memory, on whole numbers. This is the account a
contract's meaning is stated over (`Contract.lean`), and it is meant to say what `../core/conc.py` says,
which processors are compared with (`../core/cross.py`).

Here so far: the rows over the general registers, the two flags, and memory of 1, 4 and 8 bytes. A
row that uses anything else (a vector register, a call) has no meaning here yet, and a function that has
such a row is not verified.

Memory a function may not touch is said by `Perm`; touching it is a fault, as is an instruction with no row.
-/
namespace Ode

def M64 : Nat := 2 ^ 64

def regNames : List String :=
  ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]

def indexOf (name : String) : List String → Nat → Option Nat
  | [], _ => none
  | n :: ns, k => if n == name then some k else indexOf name ns (k + 1)

def regIndex (name : String) : Option Nat := indexOf name regNames 0

def RSP : Nat := 4

def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def readDigits (base : Nat) : List Char → Nat → Option Nat
  | [], n => some n
  | c :: cs, n => match hexDigit c with
    | some d => if d < base then readDigits base cs (n * base + d) else none
    | none => none

/-- A whole number as the decoder writes it: decimal, or `0x` and hexadecimal; `-` before it. -/
def readInt (text : String) : Option Int :=
  let nat : List Char → Option Nat
    | '0' :: 'x' :: d :: ds => readDigits 16 (d :: ds) 0
    | d :: ds => readDigits 10 (d :: ds) 0
    | [] => none
  match text.toList with
  | '-' :: cs => (nat cs).map fun n => -(n : Int)
  | cs => (nat cs).map fun n => (n : Int)

structure State where
  reg : Nat → Nat          -- the sixteen general registers, by number (rax 0, rcx 1, rdx 2, rbx 3, rsp 4, …)
  zf : Bool
  cf : Bool
  mem : Nat → Nat          -- the byte at an address
  rip : Nat

/-- The bytes a function may read, and may write. -/
structure Perm where
  read : Nat → Bool
  write : Nat → Bool

def allowed (p : Nat → Bool) (a : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => p a && allowed p (a + 1) n

/-- `n` bytes at `a` as one number, the lowest byte first. -/
def load (mem : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mem a % 256 + 256 * load mem (a + 1) n

def store (mem : Nat → Nat) (a v : Nat) : Nat → Nat → Nat
  | 0 => mem
  | n + 1 => store (fun x => if x = a then v % 256 else mem x) (a + 1) (v / 256) n

def memSize (f : String) : Option Nat :=
  if f == "mem8" then some 1 else if f == "mem32" then some 4 else if f == "mem64" then some 8 else none

/-- What each primitive means on numbers (conc.py's CONC). -/
def prim (f : String) (args : List Nat) : Option Nat :=
  match args with
  | [a] =>
    if f == "low32" then some (a % 2 ^ 32)
    else if f == "low8" then some (a % 256)
    else none
  | [a, b] =>
    if f == "add64" || f == "at" then some ((a + b) % M64)
    else if f == "sub64" then some ((a + (M64 - b % M64)) % M64)
    else if f == "and64" then some ((a &&& b) % M64)
    else if f == "or64" then some ((a ||| b) % M64)
    else if f == "shl64" then some ((a <<< b) % M64)
    else if f == "shr64" then some ((a % M64) >>> b)
    else if f == "equal" then some (if a % M64 = b % M64 then 1 else 0)
    else if f == "below" then some (if a % M64 < b % M64 then 1 else 0)
    else if f == "sub8" then some ((a + (256 - b % 256)) % 256)
    else if f == "setlow8" then some (a % M64 / 256 * 256 + b % 256)
    else none
  | _ => none

def isRegisterLetter (n : String) : Bool := n == "D" || n == "S" || n == "B" || n == "P"
def isNumberLetter (n : String) : Bool := n == "I" || n == "J" || n == "K" || n == "L" || n == "N"

/-- The register a name of an EFFECT stands for, in an instance. -/
def regOf (bind : Bind) (n : String) : Option Nat :=
  if isRegisterLetter n then (bind.lookup n).bind regIndex else regIndex n

def sumList : List Nat → Nat
  | [] => 0
  | v :: vs => v + sumList vs

mutual
  def value (perm : Perm) (bind : Bind) (s : State) : Expr → Option Nat
    | .number n => some n
    | .lane _ _ => none
    | .name n =>
      if isNumberLetter n then ((bind.lookup n).bind readInt).map fun i => (i % (M64 : Int)).toNat
      else (regOf bind n).map s.reg
    | .call f args =>
      match values perm bind s args with
      | none => none
      | some vs =>
        match memSize f with
        | some size =>
          let a := sumList vs % M64
          if allowed perm.read a size then some (load s.mem a size) else none
        | none => prim f vs
  def values (perm : Perm) (bind : Bind) (s : State) : List Expr → Option (List Nat)
    | [] => some []
    | e :: es =>
      match value perm bind s e, values perm bind s es with
      | some v, some vs => some (v :: vs)
      | _, _ => none
end

/-- `unknown`: the row says nothing of what it sets. -/
def isUnknown : Expr → Bool
  | .name n => n == "unknown"
  | _ => false

def setReg (s : State) (r v : Nat) : State := { s with reg := fun k => if k = r then v % M64 else s.reg k }

/-- One statement of an effect. `u` is what an `unknown` turns out to be this time. -/
def execStmt (perm : Perm) (bind : Bind) (base u : Nat) (s : State) : Stmt → Option State
  | .nothing => some s
  | .ret => none
  | .call _ => none
  | .jump target cond =>
    let taken := match cond with
      | none => true
      | some (flag, want) => (if flag == "zf" then s.zf else s.cf) == want
    if taken then (value perm bind s target).map fun t => { s with rip := base + t } else some s
  | .set place v =>
    match (if isUnknown v then some u else value perm bind s v), place with
    | some x, .name n =>
      if n == "zf" then some { s with zf := x != 0 }
      else if n == "cf" then some { s with cf := x != 0 }
      else (regOf bind n).map fun r => setReg s r x
    | some x, .call f args =>
      match memSize f, values perm bind s args with
      | some size, some vs =>
        let a := sumList vs % M64
        if allowed perm.write a size then some { s with mem := store s.mem a x size } else none
      | _, _ => none
    | _, _ => none

inductive Outcome where
  | next (s : State)          -- the instruction is done; the next is at `s.rip`
  | returned (s : State)      -- the function has returned to `s.rip`

/-- An effect's statements, left to right. A `return` takes the address at the stack pointer and moves it up. -/
def execAll (perm : Perm) (bind : Bind) (base : Nat) (u : Nat → Nat) : Nat → State → List Stmt → Option Outcome
  | _, s, [] => some (.next s)
  | _, s, .ret :: _ =>
    let sp := s.reg RSP
    if allowed perm.read sp 8 then some (.returned (setReg { s with rip := load s.mem sp 8 } RSP (sp + 8))) else none
  | k, s, st :: rest =>
    match execStmt perm bind base (u k) s st with
    | some s' => execAll perm bind base u (k + 1) s' rest
    | none => none

/-- A decoded instruction: its row's effect, what the row's placeholders are, and where the next one is
(counted from the function's start, as a jump's target is). -/
structure Instr where
  effect : List Stmt
  bind : Bind
  next : Nat
  deriving Inhabited

/-- A function's code: where it is in memory, and the instruction at each place in it. -/
structure Program where
  base : Nat
  code : List (Nat × Instr)

def Program.fetch (p : Program) (rip : Nat) : Option Instr :=
  if rip < p.base then none else p.code.lookup (rip - p.base)

def exec (perm : Perm) (p : Program) (i : Instr) (u : Nat → Nat) (s : State) : Option Outcome :=
  execAll perm i.bind p.base u 0 { s with rip := p.base + i.next } i.effect

/-- From `s`, whatever the unknowns turn out to be: the function runs on instructions it has, touches
only what it may, and returns after finitely many of them in a state of which `Q` holds. -/
inductive Runs (perm : Perm) (p : Program) (Q : State → Prop) : State → Prop where
  | step (s : State) (i : Instr) :
      p.fetch s.rip = some i →
      (∀ u, exec perm p i u s ≠ none) →
      (∀ u s', exec perm p i u s = some (.next s') → Runs perm p Q s') →
      (∀ u s', exec perm p i u s = some (.returned s') → Q s') →
      Runs perm p Q s

end Ode
