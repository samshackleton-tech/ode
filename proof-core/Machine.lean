import Table
/-!
# The machine, as the table says it

What a row's EFFECT does to registers, two flags and memory, on whole numbers. This is the account a
contract's meaning is stated over (`Contract.lean`), and it is meant to say what `../core/conc.py` says,
which processors are compared with (`../core/cross.py`).

The model covers general registers, two flags, calls by name, and vector operations on four or sixteen
32-bit lanes. It does not yet model mask registers. The read-only data of the function's file lies at an
address the state holds (`State.data`): the linker and the loader decide it, and no instruction changes it.

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

/-- What may depend on a secret: a mark (`true`) on each general register, on the two flags, and on each
byte of memory. (A vector register has no mark of its own: it is always taken as marked.) The marks do
nothing to what an instruction computes. They are moved as values are moved, so that a value that is not
marked has been computed from values not marked alone. -/
structure Marks where
  reg : Nat → Bool := fun _ => false
  zf : Bool := false
  cf : Bool := false
  mem : Nat → Bool := fun _ => false

structure State where
  reg : Nat → Nat          -- the sixteen general registers, by number (rax 0, rcx 1, rdx 2, rbx 3, rsp 4, …)
  zf : Bool
  cf : Bool
  mem : Nat → Nat          -- the byte at an address
  rip : Nat
  vec : Nat → Nat → Nat    -- the vector registers: a register's lanes of 32 bits, lane 0 the lowest
  data : Nat               -- where the read-only data of the function's file lies (no instruction changes it)
  marks : Marks := {}      -- what may depend on a secret
  trace : List (Nat × Nat) := []    -- what has been observed so far, the oldest first: (an instruction's address, 0); (an address touched, how many bytes)

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

def W32 : Nat := 2 ^ 32

/-- A word turned right by `n` bits: its low `n` bits go to the top. -/
def rotr (w n : Nat) : Nat := w / 2 ^ n + w % 2 ^ n * 2 ^ (32 - n)

/-- What each primitive on two lanes means (conc.py's CONC). -/
def prim32 (f : String) (a b : Nat) : Option Nat :=
  if f == "add32" then some ((a + b) % W32)
  else if f == "xor32" then some (a ^^^ b)
  else if f == "or32" then some (a ||| b)
  else if f == "ror32" then some (rotr a (b % 32))
  else if f == "shl32" then some ((a <<< b) % W32)
  else if f == "shr32" then some (a >>> b)
  else none

/-- Byte `j` (of sixteen, the lowest first) of four lanes. -/
def byteOf (lanes : List Nat) (j : Nat) : Nat := lanes.getD (j / 4) 0 / 256 ^ (j % 4) % 256

/-- Each byte of the result is the byte of `a` that the same byte of `b` names by its low four bits, or
zero where that byte of `b` has its top bit set. -/
def shuffleBytes (a b : List Nat) : List Nat :=
  (List.range 4).map fun k =>
    let out (j : Nat) : Nat := if 128 ≤ byteOf b j then 0 else byteOf a (byteOf b j % 16)
    out (4 * k) + 256 * out (4 * k + 1) + 65536 * out (4 * k + 2) + 16777216 * out (4 * k + 3)

/-- Half `h` (of eight halves of 16 bits, the lowest first) of four lanes. -/
def halfOf (lanes : List Nat) (h : Nat) : Nat := lanes.getD (h / 2) 0 / 65536 ^ (h % 2) % 65536

/-- Each half of 16 bits of the result is `b`'s where the bit of `i` for it is set, else `a`'s. -/
def blendHalves (a b : List Nat) (i : Nat) : List Nat :=
  (List.range 4).map fun k =>
    let pick (h : Nat) : Nat := halfOf (if i / 2 ^ h % 2 = 1 then b else a) h
    pick (2 * k) + 65536 * pick (2 * k + 1)

def isRegisterLetter (n : String) : Bool := n == "D" || n == "S" || n == "B" || n == "P"
def isVectorLetter (n : String) : Bool := n == "X" || n == "Y" || n == "Z"

/-- The vector register a letter of an EFFECT stands for, in an instance: its number. -/
def vecOf (bind : Bind) (n : String) : Option Nat := if isVectorLetter n then (bind.lookup n).bind String.toNat? else none
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
        | none =>
          if f == "data" then some ((s.data + sumList vs) % M64)       -- the address of a place in the file's data
          else prim f vs
  def values (perm : Perm) (bind : Bind) (s : State) : List Expr → Option (List Nat)
    | [] => some []
    | e :: es =>
      match value perm bind s e, values perm bind s es with
      | some v, some vs => some (v :: vs)
      | _, _ => none
end

/-- The four low lanes of the vector register a letter stands for. -/
def vecArg (bind : Bind) (s : State) : Expr → Option (List Nat)
  | .name n => (vecOf bind n).map fun r => (List.range 4).map (s.vec r)
  | _ => none

/-- One lane, as an EFFECT names it (`Y.2`). -/
def laneArg (bind : Bind) (s : State) : Expr → Option Nat
  | .lane n k => (vecOf bind n).map fun r => s.vec r k
  | _ => none

/-- Four lanes: what a vector register is set to, or what sixteen bytes of memory are (conc.py). -/
def lanesOf (perm : Perm) (bind : Bind) (s : State) : Expr → Option (List Nat)
  | .name n => vecArg bind s (.name n)
  | .call f args =>
    if f == "mem128" then
      match values perm bind s args with
      | some vs =>
        let a := sumList vs % M64
        if allowed perm.read a 16 then some ((List.range 4).map fun k => load s.mem (a + 4 * k) 4) else none
      | none => none
    else if f == "words" then
      match values perm bind s args with
      | some vs => if vs.length == 4 then some (vs.map (· % W32)) else none
      | none => none
    else if f == "lanes_of64" then
      match values perm bind s args with
      | some [a] => some [a % W32, a / W32 % W32, 0, 0]
      | _ => none
    else if f == "lanes" then
      if args.length == 4 then args.mapM (laneArg bind s) else none
    else if f == "each32" then
      match args with
      | [.name op, a, b] =>
        match vecArg bind s a with
        | some x =>
          match vecArg bind s b with
          | some y => (x.zip y).mapM fun (p, q) => prim32 op p q
          | none =>                                               -- (a number: the same for every lane)
            match value perm bind s b with
            | some n => x.mapM fun p => prim32 op p n
            | none => none
        | none => none
      | _ => none
    else
      match args with
      | [a, b] => if f == "shuffle_bytes" then (vecArg bind s a).bind fun x => (vecArg bind s b).map fun y => shuffleBytes x y else none
      | [a, b, i] =>
        match vecArg bind s a, vecArg bind s b, value perm bind s i with
        | some x, some y, some i =>
          if f == "pick4" then some [x.getD (i % 4) 0, x.getD (i / 4 % 4) 0, y.getD (i / 16 % 4) 0, y.getD (i / 64 % 4) 0]
          else if f == "blend4" then some ((List.range 4).map fun k => if i / 2 ^ k % 2 = 1 then y.getD k 0 else x.getD k 0)
          else if f == "blend_halves" then some (blendHalves x y i)
          else none
        | _, _, _ => none
      | _ => none
  | _ => none

/-- A vector register's four low lanes set; of its lanes above them the row says nothing: they are what
`u` makes them. -/
def setVec (s : State) (r : Nat) (lanes : List Nat) (u : Nat) : State :=
  { s with vec := fun x k => if x = r then (if k < 4 then lanes.getD k 0 else u / W32 ^ k % W32) else s.vec x k }

/-- `unknown`: the row says nothing of what it sets. -/
def isUnknown : Expr → Bool
  | .name n => n == "unknown"
  | _ => false

def setReg (s : State) (r v : Nat) : State := { s with reg := fun k => if k = r then v % M64 else s.reg k }

def vecOf512 (bind : Bind) (n : String) : Option Nat :=
  if n == "X512" then vecOf bind "X" else if n == "Y512" then vecOf bind "Y"
  else if n == "Z512" then vecOf bind "Z" else none

def vecArg512 (bind : Bind) (s : State) : Expr → Option (List Nat)
  | .name n => (vecOf512 bind n).map fun r => (List.range 16).map (s.vec r)
  | _ => none

/-- An aligned 512-bit memory operand faults unless the address is a multiple of 64. -/
def addr512 (perm : Perm) (bind : Bind) (s : State) (f : String) (args : List Expr) : Option Nat := do
  let vs ← values perm bind s args
  let a := sumList vs % M64
  if f == "mem512" || (f == "mem512a" && a % 64 == 0) then some a else none

/-- Pick four words independently in each quarter. Numbers 0 through 3 select from the first
register, and 4 through 7 select from the second. -/
def inQuarters (x y : List Nat) (pick : List Nat) : List Nat :=
  (List.range 4).flatMap fun q => pick.map fun i =>
    (if i < 4 then x else y).getD (4 * q + i % 4) 0

/-- Pick two quarters from the first register and two from the second. -/
def quarters (x y : List Nat) (i : Nat) : List Nat :=
  (List.range 16).map fun j =>
    let q := j / 4
    (if q < 2 then x else y).getD (4 * (i / 4 ^ q % 4) + j % 4) 0

def lanesOf512 (perm : Perm) (bind : Bind) (s : State) : Expr → Option (List Nat)
  | .name n => vecArg512 bind s (.name n)
  | .call f args =>
    if f == "mem512" || f == "mem512a" then do
      let a ← addr512 perm bind s f args
      if allowed perm.read a 64 then some ((List.range 16).map fun k => load s.mem (a + 4 * k) 4) else none
    else match f, args with
      | "spread16", [.call "lane32" [a]] => (value perm bind s a).map fun v => List.replicate 16 (v % W32)
      | "zeros16", [] => some (List.replicate 16 0)
      | "each32", [.name op, a, b] => do
        let x ← vecArg512 bind s a
        match vecArg512 bind s b with
        | some y => (x.zip y).mapM fun (p, q) => prim32 op p q
        | none => do
          let n ← value perm bind s b
          x.mapM fun p => prim32 op p n
      | "in_quarters", [a, b, .number p0, .number p1, .number p2, .number p3] => do
        let x ← vecArg512 bind s a
        let y ← vecArg512 bind s b
        if [p0, p1, p2, p3].all (· < 8) then some (inQuarters x y [p0, p1, p2, p3]) else none
      | "quarters", [a, b, i] => do
        let x ← vecArg512 bind s a
        let y ← vecArg512 bind s b
        let sel ← value perm bind s i
        some (quarters x y sel)
      | _, _ => none
  | _ => none

def storeWords (mem : Nat → Nat) (a : Nat) : List Nat → (Nat → Nat)
  | [] => mem
  | w :: ws => storeWords (store mem a w 4) (a + 4) ws

def setVec512 (s : State) (r : Nat) (lanes : List Nat) : State :=
  { s with vec := fun x k => if x = r then lanes.getD k 0 else s.vec x k }

def execVec512 (perm : Perm) (bind : Bind) (s : State) (place rhs : Expr) : Option State := do
  let lanes ← lanesOf512 perm bind s rhs
  if lanes.length != 16 then none else
  match place with
  | .name n => (vecOf512 bind n).map fun r => setVec512 s r lanes
  | .call f args => do
    let a ← addr512 perm bind s f args
    if allowed perm.write a 64 then some { s with mem := storeWords s.mem a lanes } else none
  | _ => none

/-! ## Marks and the trace

What follows changes no value. It says, of a statement run in the state `s`: which marks are set after
it, what was observed, and whether it used anything marked in a way that shows. -/

/-- How many bytes a memory operand is, by its name in an EFFECT. -/
def memWidth (f : String) : Option Nat :=
  if f == "mem8" then some 1 else if f == "mem32" then some 4 else if f == "mem64" then some 8
  else if f == "mem128" then some 16 else if f == "mem512" || f == "mem512a" then some 64 else none

/-- Is any of the `n` bytes at `a` marked? -/
def anyMarked (m : Nat → Bool) (a : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => m a || anyMarked m (a + 1) n

/-- The marks with the `n` bytes at `a` marked, or not marked. -/
def markBytes (m : Nat → Bool) (a n : Nat) (b : Bool) : Nat → Bool :=
  fun x => if a ≤ x ∧ x < a + n then b else m x

/-- Everything may be read and written. (An address is worked out under this: what may be touched is
another question.) -/
def Perm.all : Perm := ⟨fun _ => true, fun _ => true⟩

/-- The address the parts of a memory operand add up to. -/
def addrOf (bind : Bind) (s : State) (args : List Expr) : Option Nat :=
  (values Perm.all bind s args).map fun vs => sumList vs % M64

mutual
  /-- May what an expression stands for depend on a secret? A number of the instruction: no. A general
  register: its mark. A vector register, a lane of one, `unknown`: yes. Memory: yes if a byte read is
  marked, or anything its address is made of. Anything else: if anything it is made of may. -/
  def exprMark (bind : Bind) (s : State) : Expr → Bool
    | .number _ => false
    | .lane _ _ => true
    | .name n =>
      if isNumberLetter n then false
      else match regOf bind n with
        | some r => s.marks.reg r
        | none => true
    | .call f args =>
      exprMarks bind s args ||
        match memWidth f, addrOf bind s args with
        | some w, some a => anyMarked s.marks.mem a w
        | some _, none => true
        | none, _ => false
  def exprMarks (bind : Bind) (s : State) : List Expr → Bool
    | [] => false
    | e :: es => exprMark bind s e || exprMarks bind s es
end

mutual
  /-- No address in the expression is made of anything marked. -/
  def addrsQuiet (bind : Bind) (s : State) : Expr → Bool
    | .call f args => addrsQuietAll bind s args && ((memWidth f).isNone || !exprMarks bind s args)
    | _ => true
  def addrsQuietAll (bind : Bind) (s : State) : List Expr → Bool
    | [] => true
    | e :: es => addrsQuiet bind s e && addrsQuietAll bind s es
end

mutual
  /-- The memory an expression reads: each address with how many bytes. -/
  def touched (bind : Bind) (s : State) : Expr → List (Nat × Nat)
    | .call f args =>
      touchedAll bind s args ++
        match memWidth f, addrOf bind s args with
        | some w, some a => [(a, w)]
        | _, _ => []
    | _ => []
  def touchedAll (bind : Bind) (s : State) : List Expr → List (Nat × Nat)
    | [] => []
    | e :: es => touched bind s e ++ touchedAll bind s es
end

/-- How many bytes a statement's place is, where it is memory: by the operand's name for a general
store, sixteen for a vector's, sixty-four for a wide vector's. -/
def placeWidth : Stmt → Option Nat
  | .set (.call f _) _ => memSize f
  | .vset _ _ => some 16
  | .vset512 _ _ => some 64
  | _ => none

/-- The place a statement sets and what it sets it from. -/
def stmtParts : Stmt → Option (Expr × Expr)
  | .set place v => some (place, v)
  | .vset place v => some (place, v)
  | .vset512 place v => some (place, v)
  | _ => none

/-- A statement uses nothing marked in a way that shows: no address it touches is made of anything
marked; a jump is to a target not marked, and, where it is on a flag, on a flag not marked. -/
def quietStmt (bind : Bind) (s : State) (st : Stmt) : Bool :=
  match st with
  | .jump target cond =>
    addrsQuiet bind s target && !exprMark bind s target &&
      match cond with
      | none => true
      | some (flag, _) => !(if flag == "zf" then s.marks.zf else s.marks.cf)
  | _ =>
    match stmtParts st with
    | some (place, v) =>
      addrsQuiet bind s v &&
        match place with
        | .call _ args => addrsQuietAll bind s args && !exprMarks bind s args
        | _ => true
    | none => true

/-- The marks after a statement, `s` being the state before it: what is set is marked if what it is set
from may depend on a secret. A vector register has no mark; the memory a vector is stored to is marked. -/
def marksAfter (bind : Bind) (s : State) (st : Stmt) : Marks :=
  match stmtParts st with
  | none => s.marks
  | some (place, v) =>
    match place with
    | .call _ args =>
      match placeWidth st, addrOf bind s args with
      | some w, some a =>
        { s.marks with mem := markBytes s.marks.mem a w (match st with | .set _ _ => exprMark bind s v | _ => true) }
      | _, _ => s.marks
    | .name n =>
      match st with
      | .set _ _ =>
        if n == "zf" then { s.marks with zf := exprMark bind s v }
        else if n == "cf" then { s.marks with cf := exprMark bind s v }
        else match regOf bind n with
          | some r => { s.marks with reg := fun k => if k = r then exprMark bind s v else s.marks.reg k }
          | none => s.marks
      | _ => s.marks
    | _ => s.marks

/-- What a statement lets be observed: the memory it touches. -/
def observed (bind : Bind) (s : State) (st : Stmt) : List (Nat × Nat) :=
  match stmtParts st with
  | none => []
  | some (place, v) =>
    touched bind s v ++
      match place with
      | .call _ args =>
        touchedAll bind s args ++
          match placeWidth st, addrOf bind s args with
          | some w, some a => [(a, w)]
          | _, _ => []
      | _ => []

/-- The state `s'` a statement gave from `s`, with the marks and the trace brought up to date. -/
def noted (bind : Bind) (s : State) (st : Stmt) (s' : State) : State :=
  { s' with marks := marksAfter bind s st, trace := s.trace ++ observed bind s st }

/-- One statement of an effect. `u` is what an `unknown` turns out to be this time. -/
def execStmt (perm : Perm) (bind : Bind) (base u : Nat) (s : State) : Stmt → Option State
  | .nothing => some s
  | .ret => none
  | .call _ => none
  | .vset512 place v => execVec512 perm bind s place v
  | .vset place v =>
    match place with
    | .name n =>
      if n == "above128" then
        -- The high lanes of registers 0 through 15 are not specified by this row.
        if isUnknown v then some { s with vec := fun x k => if k < 4 ∨ 16 ≤ x then s.vec x k else u / W32 ^ (16 * x + k) % W32 } else none
      else
        match vecOf bind n, lanesOf perm bind s v with
        | some r, some l => some (setVec s r l u)
        | _, _ => none
    | .call _ args =>                                             -- (`mem128`: sixteen bytes, lane 0 lowest)
      match values perm bind s args, vecArg bind s v with
      | some vs, some l =>
        let a := sumList vs % M64
        if allowed perm.write a 16 then
          some { s with mem := store (store (store (store s.mem a (l.getD 0 0) 4) (a + 4) (l.getD 1 0) 4) (a + 8) (l.getD 2 0) 4) (a + 12) (l.getD 3 0) 4 }
        else none
      | _, _ => none
    | _ => none
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
    if allowed perm.read sp 8 then some (.returned (setReg { s with rip := load s.mem sp 8, trace := s.trace ++ [(sp, 8)] } RSP (sp + 8))) else none
  | k, s, st :: rest =>
    match execStmt perm bind base (u k) s st with
    | some s' => execAll perm bind base u (k + 1) (noted bind s st s') rest
    | none => none

/-- A return uses nothing marked in a way that shows: the stack pointer and the address to return to. -/
def quietRet (s : State) : Bool := !s.marks.reg RSP && !anyMarked s.marks.mem (s.reg RSP) 8

/-- As `execAll`, and the machine stops where a statement uses something marked in a way that shows. -/
def execAllQ (perm : Perm) (bind : Bind) (base : Nat) (u : Nat → Nat) : Nat → State → List Stmt → Option Outcome
  | _, s, [] => some (.next s)
  | _, s, .ret :: _ =>
    let sp := s.reg RSP
    if quietRet s && allowed perm.read sp 8 then some (.returned (setReg { s with rip := load s.mem sp 8, trace := s.trace ++ [(sp, 8)] } RSP (sp + 8))) else none
  | k, s, st :: rest =>
    if quietStmt bind s st then
      match execStmt perm bind base (u k) s st with
      | some s' => execAllQ perm bind base u (k + 1) (noted bind s st s') rest
      | none => none
    else none

/-- A decoded instruction: its row's effect, what the row's placeholders are, and where the next one is
(counted from the function's start, as a jump's target is). -/
structure Instr where
  effect : List Stmt
  bind : Bind
  next : Nat
  deriving Inhabited

/-- A function's code: its name, where it is in memory, and the instruction at each place in it. -/
structure Program where
  name : String
  base : Nat
  code : List (Nat × Instr)

def Program.fetch (p : Program) (rip : Nat) : Option Instr :=
  if rip < p.base then none else p.code.lookup (rip - p.base)

def exec (perm : Perm) (p : Program) (i : Instr) (u : Nat → Nat) (s : State) : Option Outcome :=
  execAll perm i.bind p.base u 0 { s with rip := p.base + i.next, trace := s.trace ++ [(s.rip, 0)] } i.effect

def execQ (perm : Perm) (p : Program) (i : Instr) (u : Nat → Nat) (s : State) : Option Outcome :=
  execAllQ perm i.bind p.base u 0 { s with rip := p.base + i.next, trace := s.trace ++ [(s.rip, 0)] } i.effect

/-- The function an instruction calls, by its name. -/
def callTarget (i : Instr) : Option String :=
  match i.effect with
  | [.call (.name n)] => i.bind.lookup n
  | _ => none

/-- The function of that name among the functions there are. -/
def findProgram (world : List Program) (name : String) : Option Program := world.find? fun q => q.name == name

/-- The state a called function starts in: the address to come back to is put just below the stack
pointer, the stack pointer points at it, and the next instruction is the called function's first. -/
def afterCall (p q : Program) (i : Instr) (s : State) : State :=
  { reg := fun k => if k = RSP then s.reg RSP - 8 else s.reg k, zf := s.zf, cf := s.cf,
    mem := store s.mem (s.reg RSP - 8) (p.base + i.next) 8, rip := q.base, vec := s.vec, data := s.data,
    marks := { s.marks with mem := markBytes s.marks.mem (s.reg RSP - 8) 8 false },      -- (the address to come back to is no secret)
    trace := s.trace ++ [(s.rip, 0), (s.reg RSP - 8, 8)] }

/-- The registers a called function gives back as it found them: rbx, rbp, r12 to r15. -/
def calleeSaved : List Nat := [3, 5, 12, 13, 14, 15]

/-- The state a caller goes on in when a called function has returned in `s'`, `s` being the state at the
call: the registers a callee keeps are marked as they were at the call. (They hold what they held then:
`Runs` and `Ends` ask that of a call. So if they did not depend on a secret before the call, they do not
after it, whatever the called function did with them in between.) -/
def backFrom (s s' : State) : State :=
  { s' with marks := { s'.marks with reg := fun r => if calleeSaved.contains r then s.marks.reg r else s'.marks.reg r } }

/-- From `s`, whatever the unknowns turn out to be: the function `p` runs on instructions it has, touches
only what `perm` lets it, uses nothing marked in a way that shows (in an address, at a jump, as the address a
return goes to), and returns after finitely many of them in a state of which `Q` holds.

At a call the address to come back to is written below the stack pointer, and the called function runs in
its turn, in the same way: on its own instructions, touching only what it is let (never more than its
caller is), until it returns; in every state it can return in, the registers a callee keeps hold what they
held at the call, and from that state the caller's run goes on. -/
inductive Runs (world : List Program) : Perm → Program → (State → Prop) → State → Prop where
  | step (perm : Perm) (p : Program) (Q : State → Prop) (s : State) (i : Instr) :
      p.fetch s.rip = some i →
      (∀ u, execQ perm p i u s ≠ none) →
      (∀ u s', execQ perm p i u s = some (.next s') → Runs world perm p Q s') →
      (∀ u s', execQ perm p i u s = some (.returned s') → Q s') →
      Runs world perm p Q s
  | call (perm : Perm) (p : Program) (Q : State → Prop) (s : State) (i : Instr)
      (name : String) (q : Program) (inner : Perm) (R : State → Prop) :
      p.fetch s.rip = some i → callTarget i = some name → findProgram world name = some q →
      8 ≤ s.reg RSP → allowed perm.write (s.reg RSP - 8) 8 = true → s.marks.reg RSP = false →
      (∀ a, inner.read a = true → perm.read a = true) → (∀ a, inner.write a = true → perm.write a = true) →
      Runs world inner q R (afterCall p q i s) →
      (∀ s', R s' → ∀ r ∈ calleeSaved, s'.reg r = s.reg r) →
      (∀ s', R s' → Runs world perm p Q (backFrom s s')) →
      Runs world perm p Q s

end Ode
