import Machine
/-!
# What a specification says, and what a contract promises

A specification's definitions are expressions over whole numbers, words of 32 bits, counters of 64, lists
and records; `evalSpec` is what they mean, as a value or as nothing (a definition that does not come to an
end, an index outside its list, a difference below zero: the numbers of a specification are zero and up).
`Meets` is what it is for a function's code to meet a contract: the statement the verifier's yes stands for.

Here so far: definitions with `let` (numbers, `if`, comparisons, `+ - * / % |`, words with `+ ^ | >>>`,
`a[i]`, `a[i .. j]`, `len`, lists written out, joined, made thing by thing (`[e for x in a..b]`) and with
places replaced (`with`), records, `the least number`, `the greatest power of two`, uses of definitions; a
sequence is the definition it is, its place a last thing it is used with); contracts whose arguments are
numbers, runs of `n` bytes that the function only reads, runs of so many bytes that it may write and
does not read, and tables of addresses of blocks that it only reads; with `returns`, `stack`, a number that
is no less than another, and `ensures RUN[lo .. hi] = LIST`. Not here yet: other `requires` and `ensures`,
`trace`, `fails`.
-/
namespace Ode

inductive SExpr where
  | num (n : Int)
  | name (x : String)
  | bin (op : String) (a b : SExpr)
  | ifx (c a b : SExpr)
  | index (a i : SExpr)
  | call (f : String) (args : SExpr)      -- the things a definition is used with: `cons a (cons b … nil)`
  | list (items : SExpr)                  -- a list written out, `[a, b]`: its things as `cons a (cons b nil)`
  | nil
  | cons (a rest : SExpr)
  | letx (x : String) (e rest : SExpr)    -- `let x = e`, and then the rest of the definition
  | each (e : SExpr) (x : String) (a b : SExpr)       -- `[e for x in a..b]`
  | slice (a lo hi : SExpr)               -- `a[lo .. hi]`
  | withx (a puts : SExpr)                -- `a with [i: x, j: y]`: `puts` is `cons i (cons x (cons j (cons y nil)))`
  | record (names : List String) (items : SExpr)      -- `{h: a, length: b}`: the names, and their things
  | field (e : SExpr) (name : String)     -- `r.h`
  | theNumber (greatest : Bool) (x : String) (a b cond : SExpr)   -- `the least number x in a..b with cond` (or the greatest)
  | thePower (greatest : Bool) (x : String) (cond : SExpr)        -- `the greatest power of two x with cond` (or the least)
  deriving Repr, Inhabited, DecidableEq

inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  | word (w : Nat)                        -- 32 bits
  | counter (n : Nat)                     -- 64 bits
  | list (l : List Val)
  | record (fields : List (String × Val))
  deriving Repr, Inhabited, BEq

/-- A run of bytes, as the list of numbers it is. -/
def Val.bytes (l : List Nat) : Val := .list (l.map fun (b : Nat) => .int b)

structure Def where
  name : String
  params : List String
  body : SExpr
  deriving Repr, Inhabited

/-- `+`, `^`, `|` of two words: the sum's low 32 bits; bit by bit, one or the other; bit by bit, either. -/
def wordop (op : String) (a b : Nat) : Option Val :=
  if op == "+" then some (.word ((a + b) % W32))
  else if op == "^" then some (.word (a ^^^ b))
  else if op == "&" then some (.word (a &&& b))
  else if op == "|" then some (.word (a ||| b))
  else none

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
    else if op == "%" then (if 0 < b then some (.int (a % b)) else none)     -- (the remainder by a number above zero)
    else if op == "/" then (if 0 < b then some (.int (a / b)) else none)     -- (and the quotient, rounded down)
    else if op == "|" then (if 0 ≤ a ∧ 0 ≤ b then some (.int (a.toNat ||| b.toNat : Nat)) else none)   -- (bit by bit, either)
    else none
  | .word a, .word b => wordop op a b
  -- a number beside a word stands for the word of its low 32 bits; `w >>> n` turns the word right by n bits
  | .word a, .int b =>
    if op == ">>>" then (if 0 ≤ b ∧ b ≤ 32 then some (.word (rotr a b.toNat)) else none)
    else if op == ">>" then (if 0 ≤ b ∧ b < 32 then some (.word (a >>> b.toNat)) else none)
    else if 0 ≤ b then wordop op a (b.toNat % W32) else none
  | .int a, .word b => if 0 ≤ a then wordop op (a.toNat % W32) b else none
  | .counter c, .int n => if op == "+" ∧ 0 ≤ n then some (.counter ((c + n.toNat) % 2 ^ 64)) else none
  | .list a, .list b => if op == "++" then some (.list (a ++ b)) else none     -- (two lists joined)
  | _, _ => none

/-- Every four bytes a word, the lowest byte first. -/
def toWords : List Val → Option (List Val)
  | [] => some []
  | .int a :: .int b :: .int c :: .int d :: rest =>
    if 0 ≤ a ∧ a < 256 ∧ 0 ≤ b ∧ b < 256 ∧ 0 ≤ c ∧ c < 256 ∧ 0 ≤ d ∧ d < 256 then
      (toWords rest).map fun ws => .word (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat) :: ws
    else none
  | _ => none

/-- Each word's four bytes, the lowest first. (A word is 32 bits: of a number of 2^32 or more there are none.) -/
def ofWords : List Val → Option (List Val)
  | [] => some []
  | .word w :: rest =>
    if w < W32 then
      (ofWords rest).map fun bs =>
        .int (w % 256 : Nat) :: .int (w / 256 % 256 : Nat) :: .int (w / 65536 % 256 : Nat) :: .int (w / 16777216 % 256 : Nat) :: bs
    else none
  | _ => none

/-- The number that bytes are, the lowest first (as `load` of the machine reads them from memory). -/
def numberLE : List Val → Option Nat
  | [] => some 0
  | .int b :: rest => if 0 ≤ b ∧ b < 256 then (numberLE rest).map fun n => b.toNat + 256 * n else none
  | _ => none

/-- The language's own names, but `len`: a specification defines none of them. (`number.le` is no name a
specification can write: a statement uses it for a number that lies in a record in memory.) -/
def own : List String := ["word", "counter", "lo", "hi", "words", "bytes_of", "number.le"]

/-- What the language's own names mean. `word(n)`, `counter(n)`: the word of a number's low 32 bits, the
counter of its low 64; `lo(t)`, `hi(t)`: a counter's low and high word; `words(l)`, `bytes_of(l)`: every four
bytes a word, and back; `number.le(l)`: the number that bytes are, the lowest first. -/
def builtin (f : String) : List Val → Option Val
  | [.int n] =>
    if f == "word" then (if 0 ≤ n then some (.word (n.toNat % W32)) else none)
    else if f == "counter" then (if 0 ≤ n then some (.counter (n.toNat % 2 ^ 64)) else none)
    else none
  | [.word w] => if f == "word" then some (.word w) else none
  | [.counter t] =>
    if f == "counter" then some (.counter t)
    else if f == "lo" then some (.word (t % W32))
    else if f == "hi" then some (.word (t / W32))
    else none
  | [.list l] =>
    if f == "words" then (toWords l).map .list
    else if f == "bytes_of" then (ofWords l).map .list
    else if f == "number.le" then (numberLE l).map fun (n : Nat) => .int n
    else none
  | _ => none

def findDef (defs : List Def) (f : String) : Option Def := defs.find? fun d => d.name == f

/-- The values of the things a definition is used with, each by `ev`. -/
def evalList (ev : SExpr → Option Val) : SExpr → Option (List Val)
  | .nil => some []
  | .cons a rest =>
    match ev a, evalList ev rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none
  | _ => none

/-- `[e for x in a..b]`: the values `ev` gives of `count` numbers in turn, from `i` up. -/
def evalEach (ev : Int → Option Val) : Nat → Int → Option (List Val)
  | 0, _ => some []
  | count + 1, i =>
    match ev i, evalEach ev count (i + 1) with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- `l with [i: x, …]`: the list with those places replaced, one after another (`puts`: i, x, …). -/
def putAll : List Val → List Val → Option (List Val)
  | l, [] => some l
  | l, .int i :: x :: rest => if 0 ≤ i ∧ i.toNat < l.length then putAll (l.set i.toNat x) rest else none
  | _, _ => none

/-- The first of the numbers of which `ev` says true, every one before it being one of which it says false. -/
def firstWith (ev : Int → Option Val) : List Int → Option Val
  | [] => none
  | n :: rest =>
    match ev n with
    | some (.bool true) => some (.int n)
    | some (.bool false) => firstWith ev rest
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
      | some (.list l), some (.int k) => if 0 ≤ k then l[k.toNat]? else none
      | _, _ => none
    | .call f args =>
      match evalList (evalSpec defs fuel env) args with
      | none => none
      | some vs =>
        if f == "len" then
          match vs with
          | [.list l] => some (.int l.length)
          | _ => none
        else if own.contains f then builtin f vs
        else
          match findDef defs f with
          | some d => if d.params.length == vs.length then evalSpec defs fuel (d.params.zip vs) d.body else none
          | none => none
    | .list items => (evalList (evalSpec defs fuel env) items).map .list
    | .nil => none
    | .cons _ _ => none
    | .letx x e rest =>
      match evalSpec defs fuel env e with
      | some v => evalSpec defs fuel ((x, v) :: env) rest
      | none => none
    | .each e x a b =>
      match evalSpec defs fuel env a, evalSpec defs fuel env b with
      | some (.int lo), some (.int hi) =>
        (evalEach (fun i => evalSpec defs fuel ((x, .int i) :: env) e) (hi - lo).toNat lo).map .list
      | _, _ => none
    | .slice a lo hi =>
      match evalSpec defs fuel env a, evalSpec defs fuel env lo, evalSpec defs fuel env hi with
      | some (.list l), some (.int i), some (.int j) =>
        if 0 ≤ i ∧ i ≤ j ∧ j ≤ l.length then some (.list ((l.drop i.toNat).take (j - i).toNat)) else none
      | _, _, _ => none
    | .withx a puts =>
      match evalSpec defs fuel env a, evalList (evalSpec defs fuel env) puts with
      | some (.list l), some ps => (putAll l ps).map .list
      | _, _ => none
    | .record names items =>
      match evalList (evalSpec defs fuel env) items with
      | some vs => if names.length == vs.length then some (.record (names.zip vs)) else none
      | none => none
    | .field e x =>
      match evalSpec defs fuel env e with
      | some (.record fields) => fields.lookup x
      | _ => none
    | .theNumber greatest x a b cond =>
      match evalSpec defs fuel env a, evalSpec defs fuel env b with
      | some (.int lo), some (.int hi) =>
        let among := (List.range (hi - lo).toNat).map fun (k : Nat) => lo + (k : Int)
        firstWith (fun n => evalSpec defs fuel ((x, .int n) :: env) cond) (if greatest then among.reverse else among)
      | _, _ => none
    | .thePower greatest x cond =>
      let among := (List.range 64).map fun (k : Nat) => (2 : Int) ^ k
      firstWith (fun n => evalSpec defs fuel ((x, .int n) :: env) cond) (if greatest then among.reverse else among)

/-- The expression has the value `v`. -/
def Value (defs : List Def) (env : List (String × Val)) (e : SExpr) (v : Val) : Prop :=
  ∃ fuel, evalSpec defs fuel env e = some v

inductive Kind where
  | number                      -- a whole number, in the argument's register
  | bytes (len : String)        -- the address, in the argument's register, of as many bytes as the number argument `len` says
  | out (count : Nat)           -- the address of so many bytes that the function may write, and does not read
  | fixed (count : Nat)         -- the address of so many bytes that the function may read, and does not write
  | inout (count : Nat)         -- the address of so many bytes that the function may read and may write
  | valArray (len : String) (chunk elem : Nat) -- read-only array of `len / chunk` entries, each `elem` bytes (`chunk > 0`, `elem % 4 = 0`)
  deriving Repr, Inhabited

/-- Entry-value promise for a `valArray` argument: for each `i < len / chunk`, entry `i` holds the words of `expr`
with `idx := i`. -/
structure ValArraySpec where
  name : String
  idx  : String
  expr : SExpr
  deriving Repr, Inhabited

/-- `ensures RUN[lo .. hi] = value`: when the function has returned, those bytes of the run are that list. -/
structure Ensure where
  run : String
  lo : SExpr
  hi : SExpr
  value : SExpr
  deriving Repr, Inhabited

/-- `ensures RUN = value`: when the function has returned, the whole run holds that list of bytes. The value
is said of the state at entry, and may speak of the bytes that runs given to read (and this run) held then.
With `part`: so many bytes of the run, from a byte of it on, hold that list (`ensures RUN[i] = value` of one
of the chaining values a run is). -/
structure EnsureW where
  run : String
  value : SExpr
  part : Option (Nat × Nat) := none       -- (the first byte, how many bytes): the part of the run spoken of; none: the whole run
  deriving Repr, Inhabited

/-- The byte of the run where what an `ensures` speaks of begins. -/
def EnsureW.first (e : EnsureW) : Nat :=
  match e.part with
  | some (a, _) => a
  | none => 0

/-- How many bytes an `ensures` speaks of, in a run of `n` bytes. -/
def EnsureW.size (e : EnsureW) (n : Nat) : Nat :=
  match e.part with
  | some (_, m) => m
  | none => n

/-- A stack budget term `step * units((arg - sub) / div)`, where `units(q) = bitsNat q` (logarithmic,
`linear = false`) or `units(q) = q` (linear, `linear = true`). Together with `Contract.stack` (`base`),
the contract allows `base + step * units(...)` bytes. -/
structure StackBits where
  step   : Nat
  arg    : String
  sub    : Nat := 0
  div    : Nat := 1
  linear : Bool := false
  deriving Repr, Inhabited

/-- Number of bits needed to write `n`: `0` for `0`, and `floor(log2(n)) + 1` for `n > 0`. -/
def bitsNat : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.log2 (n + 1) + 1

def StackBits.units (sb : StackBits) (v : Nat) : Nat :=
  let q := (v - sb.sub) / sb.div
  if sb.linear then q else bitsNat q

structure Contract where
  args : List (String × Kind)
  returns : Option SExpr
  stack : Nat
  stackBits : Option StackBits := none    -- optional logarithmic stack budget term `step * bits((arg - sub) / div)`
  decreases : Option String := none       -- argument that strictly decreases on every direct recursive self-call
  preLines : List (Int × List (String × Int)) := []  -- (k, [(arg, a), ...]): linear entry precondition `0 ≤ k + Σ a * arg`
  valSpecs : List ValArraySpec := []      -- per-entry specification for each read-only `valArray` argument
  result : Option String := none      -- `returns r`, r no name of the specification's: the number returned, by that name in `ensures`
  ensures : List Ensure := []
  ensuresW : List EnsureW := []
  needs : List String := []           -- what the processor must have (`avx512`). The machine of Machine.lean has every row of
                                      -- the table, so this says nothing here; it is carried for the caller to see.
  bounds : List (String × Nat) := []  -- (an argument that is a number, n): the caller sees to it that the number is below n
  mbounds : List (String × Nat × Nat) := []   -- (a run of a fixed count given to read, a place in it, n): the eight bytes there,
                                      -- as one number (the lowest byte first), are below n; the caller sees to it
  needsIf : List (String × String × Nat) := []   -- (what, an argument that is a number, n): the processor must have `what`
                                      -- if that argument is n. (As `needs`, it says nothing of the machine here.)
  lanes : List (String × String) := []    -- (a run of a fixed count given to read, an argument that is a number): each eight
                                      -- bytes of the run are the address of that many blocks of 64 bytes, given to read
  atLeast : List (String × Nat) := []     -- (an argument that is a number, n): the caller sees to it that the number is no less than n
  aligns : List (String × Nat) := []      -- (a buffer argument, A): the caller sees to it that its address is a multiple of A (A > 0)
  lineDisjoint : List (String × String × Nat) := []  -- (argA, argB, L): cache-line disjoint at line size L (L > 0)
  hidden : List String := []              -- the runs given to read whose bytes may be marked, and the
                                          -- numbers given that may be: what can be observed of a run of the
                                          -- function must not depend on them
  traceExprs : List SExpr := []           -- computed values listed in `trace depends on`
  resultHidden : Option (List String) := none   -- where `result depends on` widens what a `returns r`
                                          -- result may depend on: the arguments still hidden from it
  arm64 : Bool := false                   -- the function is for AArch64: it is called as C calls a function there
                                          -- (`argRegsArm`, `calleeSavedArm`, the address to return to in x30).
                                          -- Else it is for x86-64, called as C calls a function there.
  customArgs : Option (List Nat) := none      -- custom Ode-to-Ode argument registers (when present)
  customRet : Option Nat := none              -- custom Ode-to-Ode return register (when present)
  customKeeps : Option (List Nat) := none     -- custom Ode-to-Ode callee-saved GPRs (when present)
  customKeepsVec : Option (List Nat) := none  -- custom Ode-to-Ode callee-saved vector registers (when present)
  deriving Repr, Inhabited

/-- The registers arguments are in, in their order, on x86-64: rdi, rsi, rdx, rcx, r8, r9. -/
def argRegsX86 : List Nat := [7, 6, 2, 1, 8, 9]

/-- The same on AArch64: x0 to x7 (x4 has the number 31: `regNamesArm`). -/
def argRegsArm : List Nat := [0, 1, 2, 3, 31, 5, 6, 7]

/-- Vector registers a callee must preserve under AArch64 AAPCS64: v8 through v15. -/
def calleeSavedVecArm : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]

/-- The register that holds the address to return to, on AArch64: x30. -/
def LINK : Nat := 30

/-- Decidable duplicate check for register lists. -/
def noDupB : List Nat → Bool
  | [] => true
  | r :: rs => !rs.contains r && noDupB rs

/-- Every register in `rs` is a valid general register of the machine, not `RSP`, not `LINK`, and distinct. -/
def validRegList (nreg : Nat) (rs : List Nat) : Bool :=
  rs.all (fun r => r < nreg && r != RSP && r != LINK) && noDupB rs

/-- How many general registers the function's machine has. -/
def Contract.regs (c : Contract) : Nat := if c.arm64 then 32 else 16

/-- Does the contract say that a number is returned? -/
def Contract.givesNumber (c : Contract) : Bool := c.returns.isSome || c.result.isSome

/-- The register carrying the returned number: custom `out` when valid (and not an abstract `returns r`
contract), else `0` (`rax` on x86-64, `x0` on AArch64). -/
def Contract.retReg (c : Contract) : Nat :=
  match c.customRet with
  | some r => if r < c.regs && r != RSP && r != LINK && !c.result.isSome then r else 0
  | none => 0

/-- The registers the function's arguments are in, in their order. -/
def Contract.argRegs (c : Contract) : List Nat :=
  match c.customArgs with
  | some rs => if validRegList c.regs rs then rs else if c.arm64 then argRegsArm else argRegsX86
  | none => if c.arm64 then argRegsArm else argRegsX86

/-- The general registers the function gives back as it found them. -/
def Contract.keeps (c : Contract) : List Nat :=
  let raw :=
    match c.customKeeps with
    | some rs => if validRegList c.regs rs then rs else if c.arm64 then calleeSavedArm else calleeSavedX86
    | none => if c.arm64 then calleeSavedArm else calleeSavedX86
  if c.givesNumber then raw.filter (· != c.retReg) else raw

/-- The vector registers the function gives back as it found them (AAPCS64 `v8..v15` by default on AArch64,
empty by default on x86-64). -/
def Contract.keepsVec (c : Contract) : List Nat :=
  match c.customKeepsVec with
  | some rs => if rs.all (· < 32) && noDupB rs then rs else if c.arm64 then calleeSavedVecArm else []
  | none => if c.arm64 then calleeSavedVecArm else []

/-- Are any custom calling-convention fields on `c` well-formed? Checked at verifier entry. -/
def Contract.callingOk (c : Contract) : Bool :=
  let rawKeeps := match c.customKeeps with
    | some rs => rs
    | none => if c.arm64 then calleeSavedArm else calleeSavedX86
  (match c.customArgs with | none => true | some rs => validRegList c.regs rs && decide (c.args.length ≤ rs.length)) &&
  (match c.customRet with | none => true | some r => r < c.regs && r != RSP && r != LINK && !c.result.isSome) &&
  (match c.customKeeps with | none => true | some rs => validRegList c.regs rs) &&
  !(c.givesNumber && rawKeeps.contains c.retReg) &&
  (match c.customKeepsVec with | none => true | some rs => rs.all (· < 32) && noDupB rs)

/-- How many bytes at the stack pointer hold the address to return to, at the function's entry: eight on
x86-64; none on AArch64, where a register holds it. -/
def Contract.slot (c : Contract) : Nat := if c.arm64 then 0 else 8

/-- The register that holds the address to return to at the function's entry, where one does. -/
def Contract.link (c : Contract) : Option Nat := if c.arm64 then some LINK else none

/-- The address the function returns to, `s` being the state at entry. -/
def Contract.backTo (c : Contract) (s : State) : Nat := if c.arm64 then s.reg LINK else load s.mem (s.reg RSP) 8

def regOfIn (name : String) : List (String × Kind) → List Nat → Option Nat
  | (n, _) :: args, r :: regs => if n == name then some r else regOfIn name args regs
  | _, _ => none

/-- The register of the argument of that name. -/
def Contract.regOf (c : Contract) (name : String) : Option Nat := regOfIn name c.args c.argRegs

def regionsIn (c : Contract) : List (String × Kind) → List Nat → List (Nat × Nat)
  | (_, .bytes len) :: args, r :: regs =>
    match c.regOf len with
    | some l => (r, l) :: regionsIn c args regs
    | none => regionsIn c args regs
  | (_, .number) :: args, _ :: regs => regionsIn c args regs
  | (_, .out _) :: args, _ :: regs => regionsIn c args regs
  | (_, .fixed _) :: args, _ :: regs => regionsIn c args regs
  | (_, .inout _) :: args, _ :: regs => regionsIn c args regs
  | (_, .valArray _ _ _) :: args, _ :: regs => regionsIn c args regs
  | _, _ => []

/-- The `(base, byte_length)` extent of a named buffer argument given register map `reg`. -/
def bufSpanIn (c : Contract) (reg : Nat → Nat) (name : String) : List (String × Kind) → List Nat → Option (Nat × Nat)
  | (n, k) :: args, r :: regs =>
    if n == name then
      match k with
      | .bytes len => (c.regOf len).map fun l => (reg r, reg l)
      | .out cnt | .fixed cnt | .inout cnt => some (reg r, cnt)
      | .valArray len ch el => (c.regOf len).map fun l => (reg r, el * (reg l / ch))
      | .number => none
    else bufSpanIn c reg name args regs
  | _, _ => none

def Contract.bufSpan (c : Contract) (s : State) (name : String) : Option (Nat × Nat) :=
  bufSpanIn c s.reg name c.args c.argRegs

/-- The runs of bytes the function is given to read: (the register with the address, the register with the length). -/
def Contract.regions (c : Contract) : List (Nat × Nat) := regionsIn c c.args c.argRegs

def outsIn : List (String × Kind) → List Nat → List (String × Nat × Nat)
  | (name, .out n) :: args, r :: regs => (name, r, n) :: outsIn args regs
  | (name, .inout n) :: args, r :: regs => (name, r, n) :: outsIn args regs
  | _ :: args, _ :: regs => outsIn args regs
  | _, _ => []

def fixedsIn : List (String × Kind) → List Nat → List (String × Nat × Nat)
  | (name, .fixed n) :: args, r :: regs => (name, r, n) :: fixedsIn args regs
  | _ :: args, _ :: regs => fixedsIn args regs
  | _, _ => []

def inoutsIn : List (String × Kind) → List Nat → List (String × Nat × Nat)
  | (name, .inout n) :: args, r :: regs => (name, r, n) :: inoutsIn args regs
  | _ :: args, _ :: regs => inoutsIn args regs
  | _, _ => []

/-- The runs of bytes the function may write: (the argument's name, the register with the address, how many
bytes). Those it may also read (`inout`) are among them. -/
def Contract.outs (c : Contract) : List (String × Nat × Nat) := outsIn c.args c.argRegs

/-- The runs of a fixed number of bytes the function may only read. -/
def Contract.fixeds (c : Contract) : List (String × Nat × Nat) := fixedsIn c.args c.argRegs

/-- The runs the function may read and may write. -/
def Contract.inouts (c : Contract) : List (String × Nat × Nat) := inoutsIn c.args c.argRegs

def valArraysIn (c : Contract) : List (String × Kind) → List Nat → List (String × Nat × Nat × Nat × Nat)
  | (x, .valArray len ch el) :: args, r :: regs =>
    match c.regOf len with
    | some l => if 0 < ch ∧ 0 < el ∧ el % 4 = 0 then (x, r, l, ch, el) :: valArraysIn c args regs else valArraysIn c args regs
    | none => valArraysIn c args regs
  | _ :: args, _ :: regs => valArraysIn c args regs
  | _, _ => []

/-- The read-only value arrays the function is given: `(name, ptrReg, lenReg, chunk, elem)`. -/
def Contract.valArrays (c : Contract) : List (String × Nat × Nat × Nat × Nat) :=
  valArraysIn c c.args c.argRegs

/-- The entry-value specification `(idx, expr)` attached to value-array argument `x`, if any. -/
def Contract.valSpecOf (c : Contract) (x : String) : Option (String × SExpr) :=
  c.valSpecs.findSome? fun vs => if vs.name == x then some (vs.idx, vs.expr) else none

/-- The address lies in a read-only value array given at entry state `s`. -/
def Contract.inValArray (c : Contract) (s : State) (a : Nat) : Bool :=
  c.valArrays.any fun (_, r, l, ch, el) => s.reg r ≤ a && a < s.reg r + el * (s.reg l / ch)

/-- The fixed run of number `j` is a table of addresses (`lanes` names it): the table's name, the register
with its address, how many addresses it holds (eight bytes each), and the register with the count of blocks. -/
def Contract.tableAt (c : Contract) (j : Nat) : Option (String × Nat × Nat × Nat) :=
  match c.fixeds[j]? with
  | some (x, r, n) =>
    match c.lanes.lookup x with
    | some y => (c.regOf y).map fun l => (x, r, n / 8, l)
    | none => none
  | none => none

/-- The tables of addresses, in the order of the runs they are. -/
def Contract.tables (c : Contract) : List (String × Nat × Nat × Nat) := (List.range c.fixeds.length).filterMap c.tableAt

/-- The address a table holds at its place `i`: eight bytes as one number, the lowest byte first. -/
def lanePtr (s : State) (r i : Nat) : Nat := load s.mem (s.reg r + 8 * i) 8

/-- The address is in the blocks a table of addresses points to, `s` being the state at entry. -/
def Contract.inLane (c : Contract) (s : State) (a : Nat) : Bool :=
  c.tables.any fun (_, r, count, l) => (List.range count).any fun i => lanePtr s r i ≤ a && a < lanePtr s r i + 64 * s.reg l

/-- A block as the specification has it: sixteen words, each four bytes, the lowest first. -/
def blockWords (mem : Nat → Byte) (a : Nat) : Val := .list ((List.range 16).map fun w => Val.word (load mem (a + 4 * w) 4))

/-- The blocks at an address, one after another: a list of `n` blocks. -/
def laneBlocks (mem : Nat → Byte) (p n : Nat) : Val := .list ((List.range n).map fun b => blockWords mem (p + 64 * b))

/-- A table's name as a value, in a state at entry: the list of its lanes, each the list of its blocks. -/
def Contract.lanesEnv (c : Contract) (s : State) : List (String × Val) :=
  c.tables.map fun (x, r, count, l) => (x, .list ((List.range count).map fun i => laneBlocks s.mem (lanePtr s r i) (s.reg l)))

/-- The address is in a run of a fixed number of bytes that the function may read, `s` being the state at entry. -/
def Contract.inFixed (c : Contract) (s : State) (a : Nat) : Bool :=
  (c.fixeds.any fun (_, r, n) => s.reg r ≤ a && a < s.reg r + n) || (c.inouts.any fun (_, r, n) => s.reg r ≤ a && a < s.reg r + n)

/-- The address is in a run the function may write, `s` being the state at entry. -/
def Contract.inOut (c : Contract) (s : State) (a : Nat) : Bool := c.outs.any fun (_, r, n) => s.reg r ≤ a && a < s.reg r + n

def envIn (c : Contract) (s : State) : List (String × Kind) → List Nat → List (String × Val)
  | (n, .number) :: args, r :: regs => (n, .int (s.reg r)) :: envIn c s args regs
  | (n, .bytes len) :: args, r :: regs =>
    match c.regOf len with
    | some l => (n, .bytes ((List.range (s.reg l)).map fun k => (s.mem (s.reg r + k)).val)) :: envIn c s args regs
    | none => envIn c s args regs
  | (_, .out _) :: args, _ :: regs => envIn c s args regs        -- (a run only written has no value at entry)
  | (_, .fixed _) :: args, _ :: regs => envIn c s args regs      -- (a run of a fixed count has its value in `envW`)
  | (_, .inout _) :: args, _ :: regs => envIn c s args regs
  | (_, .valArray _ _ _) :: args, _ :: regs => envIn c s args regs
  | _, _ => []

def envWIn (c : Contract) (s : State) : List (String × Kind) → List Nat → List (String × Val)
  | (n, .number) :: args, r :: regs => (n, .int (s.reg r)) :: envWIn c s args regs
  | (n, .bytes len) :: args, r :: regs =>
    match c.regOf len with
    | some l => (n, .bytes ((List.range (s.reg l)).map fun k => (s.mem (s.reg r + k)).val)) :: envWIn c s args regs
    | none => envWIn c s args regs
  | (_, .out _) :: args, _ :: regs => envWIn c s args regs
  | (n, .fixed count) :: args, r :: regs => (n, .bytes ((List.range count).map fun k => (s.mem (s.reg r + k)).val)) :: envWIn c s args regs
  | (n, .inout count) :: args, r :: regs => (n, .bytes ((List.range count).map fun k => (s.mem (s.reg r + k)).val)) :: envWIn c s args regs
  | (_, .valArray _ _ _) :: args, _ :: regs => envWIn c s args regs
  | _, _ => []

/-- The names of the contract as values, in a state at entry: a number is its register; a run of bytes is
what memory holds there. -/
def Contract.env (c : Contract) (s : State) : List (String × Val) := envIn c s c.args c.argRegs

/-- The same, with the runs of a fixed count as well (those only read, and those read and written): each is
the bytes memory holds there in the state at entry. An `EnsureW` is said by these names. A table of
addresses comes first, by its name: there the name is the list of its lanes (the first of a name counts). -/
def Contract.envW (c : Contract) (s : State) : List (String × Val) := c.lanesEnv s ++ envWIn c s c.args c.argRegs

/-- The stack budget at entry state `s`: `c.stack` plus `step * units(...)` if present.
When `c.stackBits = none`, this is `c.stack` by definition. -/
def Contract.stackAt (c : Contract) (s : State) : Nat :=
  c.stack + match c.stackBits with
  | none => 0
  | some sb =>
    match c.regOf sb.arg with
    | some r => sb.step * sb.units (s.reg r)
    | none => 0

theorem Contract.stack_le_stackAt (c : Contract) (s : State) : c.stack ≤ c.stackAt s :=
  Nat.le_add_right _ _

/-- Value of a linear entry precondition `(k, ts)` at entry state `s`. -/
def preLineVal (c : Contract) (s : State) (k : Int) (ts : List (String × Int)) : Int :=
  k + ts.foldl (fun acc (x, a) =>
    match c.regOf x with
    | some r => acc + a * (s.reg r : Int)
    | none => acc) 0

def Contract.inFrame (c : Contract) (s : State) (a : Nat) : Bool := s.reg RSP - c.stackAt s ≤ a && a < s.reg RSP

/-- The read-only data of an object file of the program: its bytes, and the boundary it lies on (where it
lies is a multiple of that). -/
structure Piece where
  bytes : List Nat
  align : Nat := 1
  deriving Repr, Inhabited

/-- The address is in the read-only data of an object file of the program (`pieces`: each file's, by the
file's number). -/
def inPieces (pieces : List Piece) (s : State) (a : Nat) : Bool :=
  pieces.zipIdx.any fun (pc, k) => s.data k ≤ a && a < s.data k + pc.bytes.length

/-- **The program is loaded.** The read-only data of each of its object files lies in memory, whole, at the
address the state holds for that file, which is a multiple of the file's boundary; it ends below 2^64; each
byte there is the file's, and none is marked (the program's own bytes may show in the trace). The addresses
themselves are any: a linker and a loader decide them. -/
def Loaded (pieces : List Piece) (s : State) : Prop :=
  ∀ k pc, pieces[k]? = some pc →
    s.data k + pc.bytes.length < M64 ∧ s.data k % pc.align = 0 ∧
    ∀ j (h : j < pc.bytes.length), (s.mem (s.data k + j)).val = pc.bytes[j]

/-- What the function may touch, `s` being the state at entry: it may read the runs of bytes it is given to
read, its own frame and the return address above it (where that is in memory: `slot`), the blocks a table
of addresses points to, and the read-only data of every object file of the program; it may write its own
frame and the runs given to write. -/
def Contract.perm (c : Contract) (pieces : List Piece) (s : State) : Perm where
  read a := (((((c.inFrame s a || s.reg RSP ≤ a && a < s.reg RSP + c.slot) || c.regions.any fun (r, l) => s.reg r ≤ a && a < s.reg r + s.reg l) || c.inFixed s a) || c.inLane s a) || c.inValArray s a) || inPieces pieces s a
  write a := c.inFrame s a || c.inOut s a

/-- The function's code lies in memory below 2^64. -/
def Program.fits (p : Program) : Prop := ∀ oi ∈ p.code, p.base + oi.2.next < M64

/-- What the caller sees to: the function is entered at its start; the registers hold numbers below 2^64;
`stack` bytes below the stack pointer and the bytes of the address to return to at it (`slot`: eight on
x86-64, none on AArch64) are in memory; each run of bytes given to read
lies in memory, apart from that frame and from the address to return to; each run given to
write lies in memory, apart from that frame, from the address to return to, from every run given to read
and from every other run given to write. A run of a fixed count given to read lies in memory likewise, apart
from the frame, the address to return to and every run given to write. A number the contract bounds is below its bound, in a register or in memory. The
blocks each address of a table points to lie in memory, apart from the frame, the address to return to and
every run given to write. A number the contract asks to be no less than another is so. On AArch64 the
stack pointer is a multiple of 16 (the processor faults at a load or store whose base is a stack pointer
that is not). -/
def Contract.pre (c : Contract) (p : Program) (s : State) : Prop :=
  s.rip = p.base ∧ (∀ r, s.reg r < M64) ∧
  c.stackAt s ≤ s.reg RSP ∧ s.reg RSP + c.slot < M64 ∧ p.fits ∧
  (∀ r l, (r, l) ∈ c.regions →
    s.reg r + s.reg l ≤ M64 ∧ (s.reg r + s.reg l ≤ s.reg RSP - c.stackAt s ∨ s.reg RSP + c.slot ≤ s.reg r)) ∧
  (∀ x r n, (x, r, n) ∈ c.outs →
    s.reg r + n ≤ M64 ∧ (s.reg r + n ≤ s.reg RSP - c.stackAt s ∨ s.reg RSP + c.slot ≤ s.reg r) ∧
    ∀ r' l, (r', l) ∈ c.regions → s.reg r + n ≤ s.reg r' ∨ s.reg r' + s.reg l ≤ s.reg r) ∧
  (c.outs.Pairwise fun (_, r, n) (_, r', n') => s.reg r + n ≤ s.reg r' ∨ s.reg r' + n' ≤ s.reg r) ∧
  (∀ x r n, (x, r, n) ∈ c.fixeds →
    s.reg r + n ≤ M64 ∧ (s.reg r + n ≤ s.reg RSP - c.stackAt s ∨ s.reg RSP + c.slot ≤ s.reg r) ∧
    ∀ x' r' n', (x', r', n') ∈ c.outs → s.reg r + n ≤ s.reg r' ∨ s.reg r' + n' ≤ s.reg r) ∧
  (∀ x b, (x, b) ∈ c.bounds → ∀ r, c.regOf x = some r → s.reg r < b) ∧
  (∀ x off b, (x, off, b) ∈ c.mbounds → ∀ r n, (x, r, n) ∈ c.fixeds → load s.mem (s.reg r + off) 8 < b) ∧
  (∀ j x r count l, c.tableAt j = some (x, r, count, l) → ∀ i, i < count →
    lanePtr s r i + 64 * s.reg l ≤ M64 ∧
    (lanePtr s r i + 64 * s.reg l ≤ s.reg RSP - c.stackAt s ∨ s.reg RSP + c.slot ≤ lanePtr s r i) ∧
    ∀ x' r' n', (x', r', n') ∈ c.outs → lanePtr s r i + 64 * s.reg l ≤ s.reg r' ∨ s.reg r' + n' ≤ lanePtr s r i) ∧
  (∀ x k, (x, k) ∈ c.atLeast → ∀ r, c.regOf x = some r → k ≤ s.reg r) ∧
  (c.arm64 = true → s.reg RSP % 16 = 0) ∧
  (∀ k ts, (k, ts) ∈ c.preLines → 0 ≤ preLineVal c s k ts) ∧
  (∀ x r l ch el, (x, r, l, ch, el) ∈ c.valArrays →
    s.reg r + el * (s.reg l / ch) < M64 ∧
    (s.reg r + el * (s.reg l / ch) ≤ s.reg RSP - c.stackAt s ∨ s.reg RSP + c.slot ≤ s.reg r) ∧
    ∀ x' r' n', (x', r', n') ∈ c.outs → s.reg r + el * (s.reg l / ch) ≤ s.reg r' ∨ s.reg r' + n' ≤ s.reg r) ∧
  (∀ x al, (x, al) ∈ c.aligns → 0 < al → ∀ r, c.regOf x = some r → s.reg r % al = 0) ∧
  (∀ x y L, (x, y, L) ∈ c.lineDisjoint → 0 < L →
    ∀ bx lx by_ ly, c.bufSpan s x = some (bx, lx) → c.bufSpan s y = some (by_, ly) →
      ∀ i < lx, ∀ j < ly, (bx + i) / L ≠ (by_ + j) / L)

/-- Entry-value promises for every read-only `valArray` argument: for each `i < len / chunk`,
the `elem` bytes at `r + elem * i` are the `elem / 4` words of `expr` with `idx := i`.
Vacuously `True` when `c.valArrays = []`. -/
def Contract.preVals (c : Contract) (defs : List Def) (s : State) : Prop :=
  ∀ x r l ch el, (x, r, l, ch, el) ∈ c.valArrays →
    ∀ idx expr, c.valSpecOf x = some (idx, expr) →
      ∀ i, i < s.reg l / ch →
        Value defs ((idx, .int i) :: c.envW s) expr
          (.list ((List.range (el / 4)).map fun k => Val.word (load s.mem (s.reg r + el * i + 4 * k) 4)))

/-- A byte of the program as it is loaded, which no function writes: a byte of the read-only data of one of
its object files, or a byte of an instruction of one of its functions. -/
def Fixed (world : List Program) (pieces : List Piece) (s : State) (a : Nat) : Prop :=
  inPieces pieces s a = true ∨ ∃ q ∈ world, ∃ oi ∈ q.code, q.base + oi.1 ≤ a ∧ a < q.base + oi.2.next

/-- What the caller sees to about the program as it is loaded: no byte the function may write (its frame,
the runs given to write) and no byte of the address to return to is a byte of the program's read-only data
or of its code. (A run given only to read may lie over read-only data: both are only read.) -/
def Contract.clear (c : Contract) (world : List Program) (pieces : List Piece) (s : State) : Prop :=
  ∀ a, Fixed world pieces s a → c.inFrame s a = false ∧ c.inOut s a = false ∧ ¬(s.reg RSP ≤ a ∧ a < s.reg RSP + c.slot)

/-- The names of the contract as values when the function has returned: those at entry, and the number
returned by the name `returns` gives it, where it gives it one. -/
def Contract.envAfter (c : Contract) (s s' : State) : List (String × Val) :=
  match c.result with
  | some name => (name, .int (s'.reg c.retReg)) :: c.env s
  | none => c.env s

/-- `ensures RUN[lo .. hi] = value` holds, `s` being the state at entry and `s'` the state at the return:
the list has `hi - lo` things, the places lie in the run, and each byte there is the list's thing. -/
def Ensure.holds (e : Ensure) (c : Contract) (defs : List Def) (s s' : State) : Prop :=
  ∃ r n a b l, (e.run, r, n) ∈ c.outs ∧
    Value defs (c.envAfter s s') e.lo (.int a) ∧ Value defs (c.envAfter s s') e.hi (.int b) ∧
    Value defs (c.envAfter s s') e.value (.bytes l) ∧
    0 ≤ a ∧ a + l.length = b ∧ b ≤ n ∧
    ∀ k (h : k < l.length), (s'.mem (s.reg r + a.toNat + k)).val = l[k]

/-- `ensures RUN = value` holds, `s` being the state at entry and `s'` the state at the return: the run is one
given to write, the value is a list of as many bytes as the run has (as the part spoken of has, which lies
within the run), and each byte of the run (of that part) is the list's. -/
def EnsureW.holds (e : EnsureW) (c : Contract) (defs : List Def) (s s' : State) : Prop :=
  ∃ r n l, (e.run, r, n) ∈ c.outs ∧ Value defs (c.envW s) e.value (.bytes l) ∧ l.length = e.size n ∧ e.first + e.size n ≤ n ∧
    ∀ k (h : k < l.length), (s'.mem (s.reg r + e.first + k)).val = l[k]

/-- Of a whole run that is: the value is a list of as many bytes as the run has, and each byte of the run is
the list's. -/
theorem EnsureW.holds_whole {e : EnsureW} (hp : e.part = none) {c : Contract} {defs : List Def} {s s' : State} :
    e.holds c defs s s' ↔ ∃ r n l, (e.run, r, n) ∈ c.outs ∧ Value defs (c.envW s) e.value (.bytes l) ∧ l.length = n ∧
      ∀ k (h : k < l.length), (s'.mem (s.reg r + k)).val = l[k] := by
  simp only [EnsureW.holds, EnsureW.first, EnsureW.size, hp, Nat.zero_add, Nat.add_zero, Nat.le_refl, true_and]

/-- What the function leaves, `s` being the state at entry: it has returned to its caller (`backTo`) with the
stack pointer above the return address (on AArch64: where it was), the registers a callee keeps as they
were, memory outside its own frame and the runs given to write as it was, in rax (on AArch64: x0) the value
the contract says, numbers below 2^64 in the registers, and in the runs given to write what each `ensures`
says. -/
def Contract.post (c : Contract) (defs : List Def) (s s' : State) : Prop :=
  s'.rip = c.backTo s ∧ s'.reg RSP = s.reg RSP + c.slot ∧
  (∀ r ∈ c.keeps, s'.reg r = s.reg r) ∧
  (∀ a, c.inFrame s a = false → c.inOut s a = false → s'.mem a = s.mem a) ∧
  (∀ e, c.returns = some e → Value defs (c.env s) e (.int (s'.reg c.retReg))) ∧
  (∀ r, s'.reg r < M64) ∧
  (c.preVals defs s → (∀ e ∈ c.ensures, e.holds c defs s s') ∧ ∀ e ∈ c.ensuresW, e.holds c defs s s') ∧
  (∀ r ∈ c.keepsVec, s'.vec r = s.vec r)

/-- The registers of the arguments that hold nothing hidden: each argument's register, but for a number the
contract says is hidden. (An address is never hidden: the function reads or writes there, so it shows.) -/
def cleanIn (c : Contract) : List (String × Kind) → List Nat → List Nat
  | (x, k) :: args, r :: regs =>
    (match k with
     | .number => if c.hidden.contains x then [] else [r]
     | _ => [r]) ++ cleanIn c args regs
  | _, _ => []

/-- The general registers that are not marked at the function's entry: the stack pointer, and what
`cleanIn` gives. Any other register may be marked: a number the contract says is hidden, and whatever a
caller left in a register that holds no argument. -/
def Contract.cleanAtEntry (c : Contract) : List Nat := RSP :: cleanIn c c.args c.argRegs

/-- The address to return to is not marked: its eight bytes at the stack pointer; on AArch64, the register
that holds it. -/
def Contract.backQuiet (c : Contract) (s : State) : Prop :=
  if c.arm64 then s.marks.reg LINK = false else ∀ k, k < 8 → s.marks.mem (s.reg RSP + k) = false

/-- Does the contract's returned number follow its `trace depends on` line by default?
True only for `returns r` with no `result depends on` line (a contract with `returns E` specifies the
value directly; one with `result depends on` checks the returned number against `resultHidden`). -/
def Contract.resultFollowsTrace (c : Contract) : Bool := c.result.isSome && c.resultHidden.isNone

/-- The contract used for the second pass when `result depends on` is present: `hidden` is narrowed to `rh`
and `resultHidden` is cleared so `resultFollowsTrace` holds and the return register is checked. -/
def Contract.forResult (c : Contract) (rh : List String) : Contract :=
  { c with hidden := rh, resultHidden := none }

/-- Is `x` bound as a readable argument (`.number` or `.bytes` with a length register) in `c.env`? -/
def envArgIn (c : Contract) (x : String) : List (String × Kind) → List Nat → Bool
  | (n, .number) :: args, _ :: regs => if n == x then true else envArgIn c x args regs
  | (n, .bytes len) :: args, _ :: regs => if n == x then (c.regOf len).isSome else envArgIn c x args regs
  | _ :: args, _ :: regs => envArgIn c x args regs
  | _, _ => false

def Contract.envArg (c : Contract) (x : String) : Bool := envArgIn c x c.args c.argRegs

def isExpr : SExpr → Bool
  | .nil => false
  | .cons _ _ => false
  | _ => true

/-- Is `e` computed only from constants, bound variables, readable arguments not in `c.hidden`, and
top-level computed values listed in `c.traceExprs`? -/
def traceCleanWith (c : Contract) (bound : List String) (e : SExpr) : Bool :=
  if isExpr e && bound.isEmpty && c.traceExprs.any (· == e) then true
  else match e with
    | .num _ => true
    | .nil => true
    | .name x => bound.contains x || (c.envArg x && !c.hidden.contains x)
    | .bin _ a b => traceCleanWith c bound a && traceCleanWith c bound b
    | .ifx cond a b => traceCleanWith c bound cond && traceCleanWith c bound a && traceCleanWith c bound b
    | .index a i => traceCleanWith c bound a && traceCleanWith c bound i
    | .call _ args => traceCleanWith c bound args
    | .list items => traceCleanWith c bound items
    | .cons a rest => traceCleanWith c bound a && traceCleanWith c bound rest
    | .letx x rhs body => traceCleanWith c bound rhs && traceCleanWith c (x :: bound) body
    | .each body x a b => traceCleanWith c bound a && traceCleanWith c bound b && traceCleanWith c (x :: bound) body
    | .slice a lo hi => traceCleanWith c bound a && traceCleanWith c bound lo && traceCleanWith c bound hi
    | .withx a puts => traceCleanWith c bound a && traceCleanWith c bound puts
    | .record _ items => traceCleanWith c bound items
    | .field e _ => traceCleanWith c bound e
    | .theNumber _ x a b cond => traceCleanWith c bound a && traceCleanWith c bound b && traceCleanWith c (x :: bound) cond
    | .thePower _ x cond => traceCleanWith c (x :: bound) cond
termination_by e

def Contract.traceClean (c : Contract) (e : SExpr) : Bool := traceCleanWith c [] e

/-- Is the run whose address is in the register `r` one the contract says is hidden? -/
def Contract.hiddenAt (c : Contract) (r : Nat) : Bool := c.hidden.any fun x => c.regOf x == some r

/-- Two entry states agree on everything the contract's `trace depends on` line lists:
same addresses (code position, read-only data, stack pointer, return address, argument pointers),
same values for every argument not in `c.hidden` (numbers, read-only byte runs and their lengths,
and fixed-size read-only runs), and the same value under `defs` for every computed expression listed
in `c.traceExprs`. -/
def Contract.traceAgree (c : Contract) (defs : List Def) (a b : State) : Prop :=
  a.rip = b.rip ∧ a.data = b.data ∧ a.trace = b.trace ∧ a.reg RSP = b.reg RSP ∧
  c.backTo a = c.backTo b ∧
  (∀ r ∈ c.cleanAtEntry, a.reg r = b.reg r) ∧
  (∀ r l, (r, l) ∈ c.regions → c.hiddenAt r = false →
    a.reg l = b.reg l ∧ ∀ k, k < a.reg l → a.mem (a.reg r + k) = b.mem (b.reg r + k)) ∧
  (∀ x r n, (x, r, n) ∈ c.fixeds → x ∉ c.hidden → ∀ k, k < n → a.mem (a.reg r + k) = b.mem (b.reg r + k)) ∧
  (∀ e ∈ c.traceExprs, ∀ v, Value defs (c.env a) e v ↔ Value defs (c.env b) e v)

/-- What the caller sees to about marks: the stack pointer is not marked,
nor is the register of an argument, but for a number the contract says is hidden (of any other general
register nothing is asked: it may be marked); the address to return to is not marked; no byte of a run
given to read is marked, but for the runs the contract says are hidden. -/
def Contract.quietAt (c : Contract) (s : State) : Prop :=
  (∀ r ∈ c.cleanAtEntry, s.marks.reg r = false) ∧
  c.backQuiet s ∧
  (∀ r l, (r, l) ∈ c.regions → c.hiddenAt r = false → ∀ k, k < s.reg l → s.marks.mem (s.reg r + k) = false) ∧
  ∀ x r n, (x, r, n) ∈ c.fixeds → x ∉ c.hidden → ∀ k, k < n → s.marks.mem (s.reg r + k) = false

/-- What the function leaves of the marks, `s` being the state at entry: the stack pointer is not marked;
the number returned, where `resultFollowsTrace` asks for it, is not marked; and outside the function's
own frame and the runs given to write every byte of memory is marked as it was. -/
def Contract.quietAfter (c : Contract) (s s' : State) : Prop :=
  s'.marks.reg RSP = false ∧
  (c.resultFollowsTrace = true → s'.marks.reg 0 = false) ∧
  ∀ a, c.inFrame s a = false → c.inOut s a = false → s'.marks.mem a = s.marks.mem a

/-- What the function leaves: what `post` says, and what `quietAfter` says of the marks. -/
def Contract.left (c : Contract) (defs : List Def) (s s' : State) : Prop := c.post defs s s' ∧ c.quietAfter s s'

/-- The function's code meets the contract, among the functions of `world` (those it may call), `pieces`
being the read-only data of the program's object files: from every state at entry in which the program is
loaded (`Loaded`), in which nothing the function may write is of the program's own bytes (`clear`), and of
which the caller has seen to what the contract asks (`pre`), it runs to its return, touching only what it
is let (`perm`), and leaves what the contract says (`post`). -/
def Meets (world : List Program) (pieces : List Piece) (c : Contract) (defs : List Def) (p : Program) : Prop :=
  ∀ s, Loaded pieces s → c.clear world pieces s → c.pre p s → RunsPlain world (c.perm pieces s) p (c.post defs s) s

end Ode
