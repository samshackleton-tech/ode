import Table
/-!
# The machine, as the table says it

What a row's EFFECT does to registers, two flags and memory, on whole numbers. This is the account a
contract's meaning is stated over (`Contract.lean`), and it is meant to say what `../core/conc.py` says,
which processors are compared with (`../core/cross.py`).

The model covers general registers, two flags, calls by name, vector operations on four or sixteen 32-bit
lanes, and the mask registers where a row compares into one or sets a vector register under one. It is
one machine for the rows of two tables: x86-64's (`../core/x86.tab`) and a first one for AArch64
(`../arm64/arm64.tab`). They differ in the registers' names, and in where a call puts the address to come
back to: below the stack pointer, or in a register. The
read-only data of each object file of the program lies at an address the state holds (`State.data`, by the
file's number): the linker and the loader decide it, and no instruction changes it.

Memory a function may not touch is said by `Perm`; touching it is a fault, as is an instruction with no row.
-/
namespace Ode

def M64 : Nat := 2 ^ 64

def regNames : List String :=
  ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"]

def indexOf (name : String) : List String → Nat → Option Nat
  | [], _ => none
  | n :: ns, k => if n == name then some k else indexOf name ns (k + 1)

/-- AArch64's general registers x0 to x30 and its stack pointer. The stack pointer has the number that
x86-64's has (`RSP`), so x4 has the last number. -/
def regNamesArm : List String :=
  ["x0", "x1", "x2", "x3", "sp", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15",
   "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29", "x30", "x4"]

/-- A general register's number, by its name on either machine (no name is a name on both). -/
def regIndex (name : String) : Option Nat :=
  match indexOf name regNames 0 with
  | some r => some r
  | none => indexOf name regNamesArm 0

/-- The stack pointer's number: rsp, and AArch64's sp. -/
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
marked has been computed from values not marked alone.

A general register has a second mark, for its lowest byte (`low`). It is looked at only where the register
is marked: such a register may still have a lowest byte that is not (`mov al, 7` into a register that holds
a secret), and what is worked out of that byte alone is then not marked. -/
structure Marks where
  reg : Nat → Bool := fun _ => false
  zf : Bool := false
  cf : Bool := false
  mem : Nat → Bool := fun _ => false
  low : Nat → Bool := fun _ => false

/-- A byte: a number below 256. A cell of memory holds one. -/
abbrev Byte := Fin 256

structure State where
  reg : Nat → Nat          -- the general registers, by number: x86-64's sixteen (rax 0, rcx 1, rdx 2, rbx 3, rsp 4, …),
                           -- or AArch64's thirty-one and its stack pointer (`regNamesArm`)
  zf : Bool
  cf : Bool
  mem : Nat → Byte         -- memory: the byte at each address
  rip : Nat
  vec : Nat → Nat → Nat    -- the vector registers zmm0 to zmm31: a register's lanes of 32 bits, lane 0 the lowest;
                           -- after them, as registers 33 to 39, the mask registers k1 to k7 (`maskOf`): a
                           -- mask's sixteen bits, each a lane (0: the bit is not set; a compare writes 0 or 1)
  data : Nat → Nat         -- where the read-only data of each object file of the program lies, by the file's
                           -- number (no instruction changes it)
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
def load (mem : Nat → Byte) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (mem a).val + 256 * load mem (a + 1) n

/-- Memory with the `n` low bytes of `v` written at `a`, the lowest first. -/
def store (mem : Nat → Byte) (a v : Nat) : Nat → Nat → Byte
  | 0 => mem
  | n + 1 => store (fun x => if x = a then ⟨v % 256, Nat.mod_lt v (by decide)⟩ else mem x) (a + 1) (v / 256) n

def memSize (f : String) : Option Nat :=
  if f == "mem8" then some 1 else if f == "mem32" then some 4 else if f == "mem64" then some 8 else none

/-- What each primitive means on numbers (conc.py's CONC). -/
def prim (f : String) (args : List Nat) : Option Nat :=
  match args with
  | [a] =>
    if f == "low32" then some (a % 2 ^ 32)
    else if f == "low8" then some (a % 256)
    -- (AArch64's stack pointer as the base of a load or store: the processor faults where it is no multiple of 16)
    else if f == "on16" then (if a % 16 = 0 then some a else none)
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
  | [c, a, b] =>
    if f == "select" then some (if c != 0 then a else b) else none
  | _ => none

def W32 : Nat := 2 ^ 32

/-- A word turned right by `n` bits: its low `n` bits go to the top. -/
def rotr (w n : Nat) : Nat := w / 2 ^ n + w % 2 ^ n * 2 ^ (32 - n)

/-- What each primitive on two lanes means (conc.py's CONC). -/
def prim32 (f : String) (a b : Nat) : Option Nat :=
  if f == "add32" then some ((a + b) % W32)
  else if f == "xor32" then some (a ^^^ b)
  else if f == "and32" then some (a &&& b)
  else if f == "or32" then some (a ||| b)
  else if f == "ror32" then some (rotr a (b % 32))
  else if f == "shl32" then some ((a <<< b) % W32)
  else if f == "shr32" then some (a >>> b)
  else if f == "ult32" then some (if a < b then 1 else 0)        -- (is the one word below the other?)
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

/-- The vector register a letter of an EFFECT stands for, in an instance: its number, of the thirty-two. -/
def vecOf (bind : Bind) (n : String) : Option Nat :=
  if n == "xmm0" then some 0
  else if isVectorLetter n then ((bind.lookup n).bind String.toNat?).bind fun r => if r < 32 then some r else none
  else none

/-- The mask register the letter `M` of an EFFECT stands for, in an instance (k1 to k7): where its sixteen
bits are kept among the vector registers, after the thirty-two of them. (Not k0: where an instruction is
written under a mask, the processor takes k0 to say "no mask". No instruction that names k0 has a meaning
here.) -/
def maskOf (bind : Bind) (n : String) : Option Nat :=
  if n == "M" then ((bind.lookup n).bind String.toNat?).bind fun m => if 0 < m ∧ m < 8 then some (32 + m) else none else none
def isNumberLetter (n : String) : Bool := n == "I" || n == "J" || n == "K" || n == "L" || n == "N"

/-- The register a name of an EFFECT stands for, in an instance. -/
def regOf (bind : Bind) (n : String) : Option Nat :=
  if isRegisterLetter n then (bind.lookup n).bind regIndex else regIndex n

/-- Flag condition predicates read by conditional select (`cmov*`, `csel`). -/
def flagVal (s : State) (n : String) : Option Nat :=
  if n == "zf" then some (if s.zf then 1 else 0)
  else if n == "nzf" then some (if !s.zf then 1 else 0)
  else if n == "cf" then some (if s.cf then 1 else 0)
  else if n == "ncf" then some (if !s.cf then 1 else 0)
  else if n == "hi" then some (if !s.zf && !s.cf then 1 else 0)
  else if n == "nhi" then some (if s.zf || s.cf then 1 else 0)
  else none

/-- Whether a flag condition predicate may depend on values kept out of the trace. -/
def flagMark (m : Marks) (n : String) : Option Bool :=
  if n == "zf" || n == "nzf" then some m.zf
  else if n == "cf" || n == "ncf" then some m.cf
  else if n == "hi" || n == "nhi" then some (m.zf || m.cf)
  else none

def sumList : List Nat → Nat
  | [] => 0
  | v :: vs => v + sumList vs

/-- The object file in whose read-only data an instruction takes an address, by the file's number: the
reader of a statement writes it into each instruction of a function of that file (as `piece`). -/
def pieceOf (bind : Bind) : Option Nat := (bind.lookup "piece").bind String.toNat?

mutual
  def value (perm : Perm) (bind : Bind) (s : State) : Expr → Option Nat
    | .number n => some n
    | .lane _ _ => none
    | .name n =>
      if isNumberLetter n then ((bind.lookup n).bind readInt).map fun i => (i % (M64 : Int)).toNat
      else match flagVal s n with
        | some v => some v
        | none => (regOf bind n).map s.reg
    | .call f args =>
      match values perm bind s args with
      | none => none
      | some vs =>
        match memSize f with
        | some size =>
          let a := sumList vs % M64
          if allowed perm.read a size then some (load s.mem a size) else none
        | none =>
          if f == "data" then (pieceOf bind).map fun k => (s.data k + sumList vs) % M64     -- the address of a place in the file's data
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

/-- SHA-256 32-bit word primitives matching FIPS 180-4 and both x86-64 SHA-NI and AArch64 ARMv8.2 SHA2. -/
def sha256Ch (e f g : Nat) : Nat := g ^^^ (e &&& (f ^^^ g))
def sha256Maj (a b c : Nat) : Nat := (a &&& b) ^^^ ((a ^^^ b) &&& c)
def sha256S0 (a : Nat) : Nat := (rotr a 2 ^^^ rotr a 13) ^^^ rotr a 22
def sha256S1 (e : Nat) : Nat := (rotr e 6 ^^^ rotr e 11) ^^^ rotr e 25
def sha256s0 (x : Nat) : Nat := (rotr x 7 ^^^ rotr x 18) ^^^ (x >>> 3)
def sha256s1 (x : Nat) : Nat := (rotr x 17 ^^^ rotr x 19) ^^^ (x >>> 10)

def sha256Round (a b c d e f g h wk : Nat) : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let t1 := ((((h + sha256S1 e) % W32 + sha256Ch e f g) % W32) + wk) % W32
  let t2 := (sha256S0 a + sha256Maj a b c) % W32
  ((t1 + t2) % W32, a, b, c, (d + t1) % W32, e, f, g)

def sha256Msg1 (x y : List Nat) : List Nat :=
  [(x.getD 0 0 + sha256s0 (x.getD 1 0)) % W32,
   (x.getD 1 0 + sha256s0 (x.getD 2 0)) % W32,
   (x.getD 2 0 + sha256s0 (x.getD 3 0)) % W32,
   (x.getD 3 0 + sha256s0 (y.getD 0 0)) % W32]

def sha256Msg2 (x z : List Nat) : List Nat :=
  let r0 := (x.getD 0 0 + sha256s1 (z.getD 2 0)) % W32
  let r1 := (x.getD 1 0 + sha256s1 (z.getD 3 0)) % W32
  let r2 := (x.getD 2 0 + sha256s1 r0) % W32
  let r3 := (x.getD 3 0 + sha256s1 r1) % W32
  [r0, r1, r2, r3]

def sha256Su1 (x y z : List Nat) : List Nat :=
  sha256Msg2
    [(x.getD 0 0 + y.getD 1 0) % W32,
     (x.getD 1 0 + y.getD 2 0) % W32,
     (x.getD 2 0 + y.getD 3 0) % W32,
     (x.getD 3 0 + z.getD 0 0) % W32] z

def sha256Rnds2 (x z wk : List Nat) : List Nat :=
  let (a1, b1, c1, d1, e1, f1, g1, h1) :=
    sha256Round (z.getD 3 0) (z.getD 2 0) (x.getD 3 0) (x.getD 2 0)
                (z.getD 1 0) (z.getD 0 0) (x.getD 1 0) (x.getD 0 0) (wk.getD 0 0)
  let (a2, b2, _, _, e2, f2, _, _) :=
    sha256Round a1 b1 c1 d1 e1 f1 g1 h1 (wk.getD 1 0)
  [f2, e2, b2, a2]

def sha256H (x y wk : List Nat) : List Nat :=
  let (a1, b1, c1, d1, e1, f1, g1, h1) :=
    sha256Round (x.getD 0 0) (x.getD 1 0) (x.getD 2 0) (x.getD 3 0)
                (y.getD 0 0) (y.getD 1 0) (y.getD 2 0) (y.getD 3 0) (wk.getD 0 0)
  let (a2, b2, c2, d2, e2, f2, g2, h2) := sha256Round a1 b1 c1 d1 e1 f1 g1 h1 (wk.getD 1 0)
  let (a3, b3, c3, d3, e3, f3, g3, h3) := sha256Round a2 b2 c2 d2 e2 f2 g2 h2 (wk.getD 2 0)
  let (a4, b4, c4, d4, _, _, _, _) := sha256Round a3 b3 c3 d3 e3 f3 g3 h3 (wk.getD 3 0)
  [a4, b4, c4, d4]

def sha256H2 (x y wk : List Nat) : List Nat :=
  let (a1, b1, c1, d1, e1, f1, g1, h1) :=
    sha256Round (y.getD 0 0) (y.getD 1 0) (y.getD 2 0) (y.getD 3 0)
                (x.getD 0 0) (x.getD 1 0) (x.getD 2 0) (x.getD 3 0) (wk.getD 0 0)
  let (a2, b2, c2, d2, e2, f2, g2, h2) := sha256Round a1 b1 c1 d1 e1 f1 g1 h1 (wk.getD 1 0)
  let (a3, b3, c3, d3, e3, f3, g3, h3) := sha256Round a2 b2 c2 d2 e2 f2 g2 h2 (wk.getD 2 0)
  let (_, _, _, _, e4, f4, g4, h4) := sha256Round a3 b3 c3 d3 e3 f3 g3 h3 (wk.getD 3 0)
  [e4, f4, g4, h4]

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
      | [a, b] =>
        if f == "shuffle_bytes" then (vecArg bind s a).bind fun x => (vecArg bind s b).map fun y => shuffleBytes x y
        else if f == "sha256msg1" then (vecArg bind s a).bind fun x => (vecArg bind s b).map fun y => sha256Msg1 x y
        else if f == "sha256msg2" then (vecArg bind s a).bind fun x => (vecArg bind s b).map fun y => sha256Msg2 x y
        else none
      | [a, b, c] =>
        if f == "sha256su1" || f == "sha256rnds2" || f == "sha256h" || f == "sha256h2" then
          match vecArg bind s a, vecArg bind s b, vecArg bind s c with
          | some x, some y, some z =>
            if f == "sha256su1" then some (sha256Su1 x y z)
            else if f == "sha256rnds2" then some (sha256Rnds2 x y z)
            else if f == "sha256h" then some (sha256H x y z)
            else some (sha256H2 x y z)
          | _, _, _ => none
        else
          match vecArg bind s a, vecArg bind s b, value perm bind s c with
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

/-- The register a name of sixteen lanes stands for: a vector register whole, or a mask register. -/
def vecOf512 (bind : Bind) (n : String) : Option Nat :=
  if n == "X512" then vecOf bind "X" else if n == "Y512" then vecOf bind "Y"
  else if n == "Z512" then vecOf bind "Z" else maskOf bind n

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

/-- The sixteen words of a number of 512 bits, the lowest first (`words16(K)`: a constant of the file that
the decoder has put into the instruction; it writes such a number with its width after it, `0x…#512`). -/
def words16 (bind : Bind) : List Expr → Option (List Nat)
  | [.name k] =>
    if isNumberLetter k then
      ((bind.lookup k).bind fun text => readInt ((text.splitOn "#").headD text)).bind fun n =>
        if 0 ≤ n then some ((List.range 16).map fun i => n.toNat / W32 ^ i % W32) else none
    else none
  | _ => none

/-- Sixty-four bytes of memory as sixteen words: a wide memory operand, where it may be read. -/
def memLanes512 (perm : Perm) (bind : Bind) (s : State) (f : String) (args : List Expr) : Option (List Nat) := do
  let a ← addr512 perm bind s f args
  if allowed perm.read a 64 then some ((List.range 16).map fun k => load s.mem (a + 4 * k) 4) else none

def lanesOf512 (perm : Perm) (bind : Bind) (s : State) : Expr → Option (List Nat)
  | .name n => vecArg512 bind s (.name n)
  | .call f args =>
    if f == "mem512" || f == "mem512a" then memLanes512 perm bind s f args
    else match f, args with
      | "spread16", [.call "lane32" [a]] => (value perm bind s a).map fun v => List.replicate 16 (v % W32)
      | "zeros16", [] => some (List.replicate 16 0)
      | "each32", [.name op, a, b] => do
        let x ← vecArg512 bind s a
        match vecArg512 bind s b with
        | some y => (x.zip y).mapM fun (p, q) => prim32 op p q
        | none =>
          -- the second operand is no register: sixty-four bytes of memory (`vpaddd zmm, zmm, [mem]`), or one number
          match b with
          | .call g margs =>
            if g == "mem512" || g == "mem512a" then do
              let y ← memLanes512 perm bind s g margs
              (x.zip y).mapM fun (p, q) => prim32 op p q
            else if g == "words16" then do
              let y ← words16 bind margs
              (x.zip y).mapM fun (p, q) => prim32 op p q
            else do
              let n ← value perm bind s b
              x.mapM fun p => prim32 op p n
          | _ => do
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
      | "choose16", [m, .call "each32" [.name op, a, b], c] => do
        -- under a mask: in each lane the operation's result where the mask's bit is set, else what `c` holds
        let k ← vecArg512 bind s m
        let x ← vecArg512 bind s a
        let y ← vecArg512 bind s b
        let old ← vecArg512 bind s c
        let new ← (x.zip y).mapM fun (p, q) => prim32 op p q
        some ((k.zip (new.zip old)).map fun (bit, p, q) => if bit = 0 then q else p)
      | _, _ => none
  | _ => none

def storeWords (mem : Nat → Byte) (a : Nat) : List Nat → (Nat → Byte)
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

/-- The register whose lowest byte alone an expression is: `low8` of a general register. -/
def lowOnly (bind : Bind) (f : String) (args : List Expr) : Option Nat :=
  if f == "low8" then
    match args with
    | [.name n] => if isNumberLetter n then none else regOf bind n
    | _ => none
  else none

mutual
  /-- May what an expression stands for depend on a secret? A number of the instruction: no. A general
  register: its mark. The lowest byte of a general register: only if the register is marked and that byte
  is. A vector register, a lane of one, `unknown`: yes. Memory: yes if a byte read is
  marked, or anything its address is made of. Anything else: if anything it is made of may. -/
  def exprMark (bind : Bind) (s : State) : Expr → Bool
    | .number _ => false
    | .lane _ _ => true
    | .name n =>
      if isNumberLetter n then false
      else match flagMark s.marks n with
        | some b => b
        | none => match regOf bind n with
          | some r => s.marks.reg r
          | none => true
    | .call f args =>
      match lowOnly bind f args with
      | some r => s.marks.reg r && s.marks.low r
      | none =>
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

/-- Value of a jump condition flag (`"zf"`, `"cf"`, or `"hi"` = `!cf && !zf` for unsigned `>`). -/
def condFlag (s : State) (flag : String) : Bool :=
  if flag == "zf" then s.zf else if flag == "hi" then !s.cf && !s.zf else s.cf

/-- Whether a jump condition flag is marked (may depend on values kept out of the trace). -/
def condMark (m : Marks) (flag : String) : Bool :=
  if flag == "zf" then m.zf else if flag == "hi" then m.cf || m.zf else m.cf

/-- A statement uses nothing marked in a way that shows: no address it touches is made of anything
marked; a jump is to a target not marked, and, where it is on a flag, on a flag not marked. -/
def quietStmt (bind : Bind) (s : State) (st : Stmt) : Bool :=
  match st with
  | .jump target cond =>
    addrsQuiet bind s target && !exprMark bind s target &&
      match cond with
      | none => true
      | some (flag, _) => !condMark s.marks flag
  | _ =>
    match stmtParts st with
    | some (place, v) =>
      addrsQuiet bind s v &&
        match place with
        | .call _ args => addrsQuietAll bind s args && !exprMarks bind s args
        | _ => true
    | none => true

/-- May the lowest byte of what an expression stands for depend on a secret? Of `setlow8(x, w)`, whose
lowest byte is `w`'s: as `w` may. Of anything else: as the whole may. -/
def lowMark (bind : Bind) (s : State) : Expr → Bool
  | .call f [x, w] => if f == "setlow8" then exprMark bind s w else exprMark bind s (.call f [x, w])
  | e => exprMark bind s e

/-- The marks after a statement, `s` being the state before it: what is set is marked if what it is set
from may depend on a secret. A general register's lowest byte is marked by `lowMark`. A vector register has
no mark; the memory a vector is stored to is marked. -/
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
          | some r => { s.marks with reg := fun k => if k = r then exprMark bind s v else s.marks.reg k,
                                     low := fun k => if k = r then lowMark bind s v else s.marks.low k }
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
  | .retLink _ => none
  | .callLink _ _ => none
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
      | some (flag, want) => condFlag s flag == want
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

/-- An effect's statements, left to right. A `return` takes the address at the stack pointer and moves it up;
a `return` by a register goes to the address the register holds. -/
def execAll (perm : Perm) (bind : Bind) (base : Nat) (u : Nat → Nat) : Nat → State → List Stmt → Option Outcome
  | _, s, [] => some (.next s)
  | _, s, .ret :: _ =>
    let sp := s.reg RSP
    if allowed perm.read sp 8 then some (.returned (setReg { s with rip := load s.mem sp 8, trace := s.trace ++ [(sp, 8)] } RSP (sp + 8))) else none
  | _, s, .retLink r :: _ => (regIndex r).map fun k => .returned { s with rip := s.reg k }
  | k, s, st :: rest =>
    match execStmt perm bind base (u k) s st with
    | some s' => execAll perm bind base u (k + 1) (noted bind s st s') rest
    | none => none

/-- A return uses nothing marked in a way that shows: the stack pointer and the address to return to. -/
def quietRet (s : State) : Bool := !s.marks.reg RSP && !anyMarked s.marks.mem (s.reg RSP) 8

/-- As `execAll`, and the machine stops where a statement uses something marked in a way that shows. (A
return by a register: the register that holds the address to return to is not marked.) -/
def execAllQ (perm : Perm) (bind : Bind) (base : Nat) (u : Nat → Nat) : Nat → State → List Stmt → Option Outcome
  | _, s, [] => some (.next s)
  | _, s, .ret :: _ =>
    let sp := s.reg RSP
    if quietRet s && allowed perm.read sp 8 then some (.returned (setReg { s with rip := load s.mem sp 8, trace := s.trace ++ [(sp, 8)] } RSP (sp + 8))) else none
  | _, s, .retLink r :: _ => (regIndex r).bind fun k => if s.marks.reg k then none else some (.returned { s with rip := s.reg k })
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
  | [.callLink (.name n) r] => if (regIndex r).isSome then i.bind.lookup n else none
  | _ => none

/-- The register a call puts the address to come back to in. None: the call puts it below the stack pointer. -/
def callLink (i : Instr) : Option Nat :=
  match i.effect with
  | [.callLink _ r] => regIndex r
  | _ => none

/-- The function an instruction tail-calls (an unconditional jump whose target is a named function rather
than an integer offset inside this function). -/
def tailTarget (i : Instr) : Option String :=
  match i.effect with
  | [.jump (.name n) none] =>
    if isNumberLetter n then
      match i.bind.lookup n with
      | some name => if (readInt name).isNone then some name else none
      | none => none
    else none
  | _ => none

theorem tailTarget_not_call {i : Instr} {name : String} (h : tailTarget i = some name) : callTarget i = none := by
  unfold tailTarget at h
  cases heff : i.effect with
  | nil => simp [heff] at h
  | cons st more =>
    cases st <;> cases more <;> simp [heff] at h
    simp [callTarget, heff]

theorem exec_tail {p : Program} {i : Instr} {name : String} (h : tailTarget i = some name) (perm : Perm) (u : Nat → Nat)
    (s : State) : exec perm p i u s = none := by
  unfold tailTarget at h
  cases heff : i.effect with
  | nil => simp [heff] at h
  | cons st more =>
    cases st <;> cases more <;> simp [heff] at h
    rename_i tgt cond
    cases tgt <;> cases cond <;> simp at h
    rename_i n
    obtain ⟨hn, hlk⟩ := h
    cases hl : i.bind.lookup n with
    | none => simp [hl] at hlk
    | some nm =>
      simp only [hl] at hlk
      cases hr : readInt nm with
      | some _ => simp [hr] at hlk
      | none =>
        simp [exec, heff, execAll, execStmt, value, hn, hl, hr]

theorem execQ_tail {p : Program} {i : Instr} {name : String} (h : tailTarget i = some name) (perm : Perm) (u : Nat → Nat)
    (s : State) : execQ perm p i u s = none := by
  unfold tailTarget at h
  cases heff : i.effect with
  | nil => simp [heff] at h
  | cons st more =>
    cases st <;> cases more <;> simp [heff] at h
    rename_i tgt cond
    cases tgt <;> cases cond <;> simp at h
    rename_i n
    obtain ⟨hn, hlk⟩ := h
    cases hl : i.bind.lookup n with
    | none => simp [hl] at hlk
    | some nm =>
      simp only [hl] at hlk
      cases hr : readInt nm with
      | some _ => simp [hr] at hlk
      | none =>
        simp [execQ, heff, execAllQ, execStmt, value, hn, hl, hr]

/-- The state a tail-called function starts in: control jumps directly to `q.base` without touching the stack
or any register, recording the jump's own fetch in the trace. -/
def afterTail (q : Program) (s : State) : State :=
  { s with rip := q.base, trace := s.trace ++ [(s.rip, 0)] }

theorem afterTail_rip (q : Program) (s : State) : (afterTail q s).rip = q.base := rfl

theorem afterTail_data (q : Program) (s : State) : (afterTail q s).data = s.data := rfl

/-- The function of that name among the functions there are. -/
def findProgram (world : List Program) (name : String) : Option Program := world.find? fun q => q.name == name

/-- The state a called function starts in, and the next instruction is the called function's first. Where
the call puts the address to come back to below the stack pointer: it is put just below, and the stack
pointer points at it. Where the call puts it in a register: that register holds it, and nothing else
changes. -/
def afterCall (p q : Program) (i : Instr) (s : State) : State :=
  match callLink i with
  | none =>
    { reg := fun k => if k = RSP then s.reg RSP - 8 else s.reg k, zf := s.zf, cf := s.cf,
      mem := store s.mem (s.reg RSP - 8) (p.base + i.next) 8, rip := q.base, vec := s.vec, data := s.data,
      marks := { s.marks with mem := markBytes s.marks.mem (s.reg RSP - 8) 8 false },      -- (the address to come back to may show in the trace)
      trace := s.trace ++ [(s.rip, 0), (s.reg RSP - 8, 8)] }
  | some l =>
    { reg := fun k => if k = l then (p.base + i.next) % M64 else s.reg k, zf := s.zf, cf := s.cf,
      mem := s.mem, rip := q.base, vec := s.vec, data := s.data,
      marks := { s.marks with reg := fun k => if k = l then false else s.marks.reg k },     -- (the address to come back to may show in the trace)
      trace := s.trace ++ [(s.rip, 0)] }

/-- `afterCall` written out, where the call puts the address to come back to below the stack pointer. -/
theorem afterCall_stack {p q : Program} {i : Instr} {s : State} (h : callLink i = none) :
    afterCall p q i s =
      { reg := fun k => if k = RSP then s.reg RSP - 8 else s.reg k, zf := s.zf, cf := s.cf,
        mem := store s.mem (s.reg RSP - 8) (p.base + i.next) 8, rip := q.base, vec := s.vec, data := s.data,
        marks := { s.marks with mem := markBytes s.marks.mem (s.reg RSP - 8) 8 false },
        trace := s.trace ++ [(s.rip, 0), (s.reg RSP - 8, 8)] } := by
  simp only [afterCall, h]

/-- `afterCall` written out, where the call puts the address to come back to in the register `l`. -/
theorem afterCall_link {p q : Program} {i : Instr} {s : State} {l : Nat} (h : callLink i = some l) :
    afterCall p q i s =
      { reg := fun k => if k = l then (p.base + i.next) % M64 else s.reg k, zf := s.zf, cf := s.cf,
        mem := s.mem, rip := q.base, vec := s.vec, data := s.data,
        marks := { s.marks with reg := fun k => if k = l then false else s.marks.reg k },
        trace := s.trace ++ [(s.rip, 0)] } := by
  simp only [afterCall, h]

/-- A called function starts at its first instruction. -/
theorem afterCall_rip (p q : Program) (i : Instr) (s : State) : (afterCall p q i s).rip = q.base := by
  cases hl : callLink i with
  | none => rw [afterCall_stack hl]
  | some l => rw [afterCall_link hl]

/-- A call leaves the files' data where it is. -/
theorem afterCall_data (p q : Program) (i : Instr) (s : State) : (afterCall p q i s).data = s.data := by
  cases hl : callLink i with
  | none => rw [afterCall_stack hl]
  | some l => rw [afterCall_link hl]

/-- The registers a called function gives back as it found them, on x86-64: rbx, rbp, r12 to r15. -/
def calleeSavedX86 : List Nat := [3, 5, 12, 13, 14, 15]

/-- The same on AArch64: x19 to x29. -/
def calleeSavedArm : List Nat := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]

/-- The registers the function called at an instruction gives back as it found them: x86-64's where the
call puts the address to come back to below the stack pointer, AArch64's where it puts it in a register. -/
def keptAt (i : Instr) : List Nat := if (callLink i).isSome then calleeSavedArm else calleeSavedX86

/-- The state a caller goes on in when a called function has returned in `s'`, `s` being the state at the
call: the registers a callee keeps (`kept`) are marked as they were at the call. (They hold what they held
then: `Runs` and `Ends` ask that of a call. So if they were not marked before the call, they are not marked
after it, whatever the called function did with them in between.) -/
def backFrom (kept : List Nat) (s s' : State) : State :=
  { s' with marks := { s'.marks with reg := fun r => if kept.contains r then s.marks.reg r else s'.marks.reg r } }

/-- From `s`, whatever the unknowns turn out to be: the function `p` runs on instructions it has, touches
only what `perm` lets it, uses nothing marked in a way that shows (in an address, at a jump, as the address a
return goes to), and returns after finitely many of them in a state of which `Q` holds.

At a call the address to come back to is written below the stack pointer (or put in a register, by the
instruction), and the called function runs in its turn, in the same way: on its own instructions, touching
only what it is let (never more than its caller is), until it returns; in every state it can return in,
the registers a callee keeps hold what they held at the call, and from that state the caller's run goes
on. -/
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
      -- (where the address to come back to is written below the stack pointer: there is room, the function
      -- may write there, and the stack pointer is not marked)
      (callLink i = none → 8 ≤ s.reg RSP ∧ allowed perm.write (s.reg RSP - 8) 8 = true ∧ s.marks.reg RSP = false) →
      (∀ a, inner.read a = true → perm.read a = true) → (∀ a, inner.write a = true → perm.write a = true) →
      Runs world inner q R (afterCall p q i s) →
      (∀ s', R s' → ∀ r ∈ keptAt i, s'.reg r = s.reg r) →
      (∀ s', R s' → Runs world perm p Q (backFrom (keptAt i) s s')) →
      Runs world perm p Q s
  | tail (perm : Perm) (p : Program) (Q : State → Prop) (s : State) (i : Instr)
      (name : String) (q : Program) (inner : Perm) :
      p.fetch s.rip = some i → tailTarget i = some name → findProgram world name = some q →
      (∀ a, inner.read a = true → perm.read a = true) → (∀ a, inner.write a = true → perm.write a = true) →
      Runs world inner q Q (afterTail q s) →
      Runs world perm p Q s

/-- Functional execution without mark checks: from `s`, whatever the unknowns turn out to be, `p` runs on
instructions it has, touches only what `perm` lets it (`exec`), and returns after finitely many steps in a
state of which `Q` holds. -/
inductive RunsPlain (world : List Program) : Perm → Program → (State → Prop) → State → Prop where
  | step (perm : Perm) (p : Program) (Q : State → Prop) (s : State) (i : Instr) :
      p.fetch s.rip = some i →
      (∀ u, exec perm p i u s ≠ none) →
      (∀ u s', exec perm p i u s = some (.next s') → RunsPlain world perm p Q s') →
      (∀ u s', exec perm p i u s = some (.returned s') → Q s') →
      RunsPlain world perm p Q s
  | call (perm : Perm) (p : Program) (Q : State → Prop) (s : State) (i : Instr)
      (name : String) (q : Program) (inner : Perm) (R : State → Prop) (kept : List Nat) :
      p.fetch s.rip = some i → callTarget i = some name → findProgram world name = some q →
      (callLink i = none → 8 ≤ s.reg RSP ∧ allowed perm.write (s.reg RSP - 8) 8 = true) →
      (∀ a, inner.read a = true → perm.read a = true) → (∀ a, inner.write a = true → perm.write a = true) →
      RunsPlain world inner q R (afterCall p q i s) →
      (∀ s', R s' → ∀ r ∈ kept, s'.reg r = s.reg r) →
      (∀ s', R s' → RunsPlain world perm p Q (backFrom kept s s')) →
      RunsPlain world perm p Q s
  | tail (perm : Perm) (p : Program) (Q : State → Prop) (s : State) (i : Instr)
      (name : String) (q : Program) (inner : Perm) :
      p.fetch s.rip = some i → tailTarget i = some name → findProgram world name = some q →
      (∀ a, inner.read a = true → perm.read a = true) → (∀ a, inner.write a = true → perm.write a = true) →
      RunsPlain world inner q Q (afterTail q s) →
      RunsPlain world perm p Q s

end Ode
