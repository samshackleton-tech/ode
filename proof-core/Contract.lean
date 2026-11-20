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
  deriving Repr, Inhabited

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
  deriving Repr, Inhabited

/-- `ensures RUN[lo .. hi] = value`: when the function has returned, those bytes of the run are that list. -/
structure Ensure where
  run : String
  lo : SExpr
  hi : SExpr
  value : SExpr
  deriving Repr, Inhabited

/-- `ensures RUN = value`: when the function has returned, the whole run holds that list of bytes. The value
is said of the state at entry, and may speak of the bytes that runs given to read (and this run) held then. -/
structure EnsureW where
  run : String
  value : SExpr
  deriving Repr, Inhabited

structure Contract where
  args : List (String × Kind)
  returns : Option SExpr
  stack : Nat
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
  hidden : List String := []              -- the runs given to read whose bytes may be marked (secret): what
                                          -- can be observed of a run of the function must not depend on them
  data : List Nat := []                   -- the bytes of the file's read-only data, where the function takes that
                                          -- data's address: it may read them (they lie at `State.data`)
  deriving Repr, Inhabited

/-- The registers arguments are in, in their order: rdi, rsi, rdx, rcx, r8, r9. -/
def argRegs : List Nat := [7, 6, 2, 1, 8, 9]

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
  | (_, .out _) :: args, _ :: regs => regionsIn c args regs
  | (_, .fixed _) :: args, _ :: regs => regionsIn c args regs
  | (_, .inout _) :: args, _ :: regs => regionsIn c args regs
  | _, _ => []

/-- The runs of bytes the function is given to read: (the register with the address, the register with the length). -/
def Contract.regions (c : Contract) : List (Nat × Nat) := regionsIn c c.args argRegs

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
def Contract.outs (c : Contract) : List (String × Nat × Nat) := outsIn c.args argRegs

/-- The runs of a fixed number of bytes the function may only read. -/
def Contract.fixeds (c : Contract) : List (String × Nat × Nat) := fixedsIn c.args argRegs

/-- The runs the function may read and may write. -/
def Contract.inouts (c : Contract) : List (String × Nat × Nat) := inoutsIn c.args argRegs

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
  | _, _ => []

/-- The names of the contract as values, in a state at entry: a number is its register; a run of bytes is
what memory holds there. -/
def Contract.env (c : Contract) (s : State) : List (String × Val) := envIn c s c.args argRegs

/-- The same, with the runs of a fixed count as well (those only read, and those read and written): each is
the bytes memory holds there in the state at entry. An `EnsureW` is said by these names. A table of
addresses comes first, by its name: there the name is the list of its lanes (the first of a name counts). -/
def Contract.envW (c : Contract) (s : State) : List (String × Val) := c.lanesEnv s ++ envWIn c s c.args argRegs

def Contract.inFrame (c : Contract) (s : State) (a : Nat) : Bool := s.reg RSP - c.stack ≤ a && a < s.reg RSP

/-- The address is in the file's read-only data, `s` being the state at entry. -/
def Contract.inData (c : Contract) (s : State) (a : Nat) : Bool := s.data ≤ a && a < s.data + c.data.length

/-- What the caller sees to about the file's read-only data, where the function takes its address: the data
lies in memory at `s.data`, whole, and ends below 2^64; each byte there is the file's; it lies apart from
the function's frame and from the address to return to, and apart from every run given to write. (A run
given to read may lie over it: both are only read.) -/
def Contract.dataAt (c : Contract) (s : State) : Prop :=
  c.data ≠ [] →
    s.data + c.data.length < M64 ∧
    (s.data + c.data.length ≤ s.reg RSP - c.stack ∨ s.reg RSP + 8 ≤ s.data) ∧
    (∀ k (h : k < c.data.length), (s.mem (s.data + k)).val = c.data[k]) ∧
    ∀ x r n, (x, r, n) ∈ c.outs → s.data + c.data.length ≤ s.reg r ∨ s.reg r + n ≤ s.data

/-- What the function may touch, `s` being the state at entry: it may read the runs of bytes it is given to
read, its own frame and the return address above it, the blocks a table of addresses points to, and the
file's read-only data; it may write its own frame and the runs given to write. -/
def Contract.perm (c : Contract) (s : State) : Perm where
  read a := ((((c.inFrame s a || s.reg RSP ≤ a && a < s.reg RSP + 8) || c.regions.any fun (r, l) => s.reg r ≤ a && a < s.reg r + s.reg l) || c.inFixed s a) || c.inLane s a) || c.inData s a
  write a := c.inFrame s a || c.inOut s a

/-- The function's code lies in memory below 2^64. -/
def Program.fits (p : Program) : Prop := ∀ oi ∈ p.code, p.base + oi.2.next < M64

/-- What the caller sees to: the function is entered at its start; the registers hold numbers below 2^64;
`stack` bytes below the stack pointer and the eight at it are in memory; each run of bytes given to read
lies in memory, apart from that frame and from the address to return to; each run given to
write lies in memory, apart from that frame, from the address to return to, from every run given to read
and from every other run given to write. A run of a fixed count given to read lies in memory likewise, apart
from the frame, the address to return to and every run given to write. A number the contract bounds is below its bound, in a register or in memory. The
blocks each address of a table points to lie in memory, apart from the frame, the address to return to and
every run given to write. A number the contract asks to be no less than another is so.
The file's read-only data is where the function expects it (`dataAt`). -/
def Contract.pre (c : Contract) (p : Program) (s : State) : Prop :=
  s.rip = p.base ∧ (∀ r, s.reg r < M64) ∧
  c.stack ≤ s.reg RSP ∧ s.reg RSP + 8 < M64 ∧ p.fits ∧
  (∀ r l, (r, l) ∈ c.regions →
    s.reg r + s.reg l ≤ M64 ∧ (s.reg r + s.reg l ≤ s.reg RSP - c.stack ∨ s.reg RSP + 8 ≤ s.reg r)) ∧
  (∀ x r n, (x, r, n) ∈ c.outs →
    s.reg r + n ≤ M64 ∧ (s.reg r + n ≤ s.reg RSP - c.stack ∨ s.reg RSP + 8 ≤ s.reg r) ∧
    ∀ r' l, (r', l) ∈ c.regions → s.reg r + n ≤ s.reg r' ∨ s.reg r' + s.reg l ≤ s.reg r) ∧
  (c.outs.Pairwise fun (_, r, n) (_, r', n') => s.reg r + n ≤ s.reg r' ∨ s.reg r' + n' ≤ s.reg r) ∧
  (∀ x r n, (x, r, n) ∈ c.fixeds →
    s.reg r + n ≤ M64 ∧ (s.reg r + n ≤ s.reg RSP - c.stack ∨ s.reg RSP + 8 ≤ s.reg r) ∧
    ∀ x' r' n', (x', r', n') ∈ c.outs → s.reg r + n ≤ s.reg r' ∨ s.reg r' + n' ≤ s.reg r) ∧
  (∀ x b, (x, b) ∈ c.bounds → ∀ r, c.regOf x = some r → s.reg r < b) ∧
  (∀ x off b, (x, off, b) ∈ c.mbounds → ∀ r n, (x, r, n) ∈ c.fixeds → load s.mem (s.reg r + off) 8 < b) ∧
  (∀ j x r count l, c.tableAt j = some (x, r, count, l) → ∀ i, i < count →
    lanePtr s r i + 64 * s.reg l ≤ M64 ∧
    (lanePtr s r i + 64 * s.reg l ≤ s.reg RSP - c.stack ∨ s.reg RSP + 8 ≤ lanePtr s r i) ∧
    ∀ x' r' n', (x', r', n') ∈ c.outs → lanePtr s r i + 64 * s.reg l ≤ s.reg r' ∨ s.reg r' + n' ≤ lanePtr s r i) ∧
  (∀ x k, (x, k) ∈ c.atLeast → ∀ r, c.regOf x = some r → k ≤ s.reg r) ∧
  c.dataAt s

/-- The names of the contract as values when the function has returned: those at entry, and the number
returned by the name `returns` gives it, where it gives it one. -/
def Contract.envAfter (c : Contract) (s s' : State) : List (String × Val) :=
  match c.result with
  | some name => (name, .int (s'.reg 0)) :: c.env s
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
given to write, the value is a list of as many bytes as the run has, and each byte of the run is the list's. -/
def EnsureW.holds (e : EnsureW) (c : Contract) (defs : List Def) (s s' : State) : Prop :=
  ∃ r n l, (e.run, r, n) ∈ c.outs ∧ Value defs (c.envW s) e.value (.bytes l) ∧ l.length = n ∧
    ∀ k (h : k < l.length), (s'.mem (s.reg r + k)).val = l[k]

/-- What the function leaves, `s` being the state at entry: it has returned to its caller with the stack
pointer above the return address, the registers a callee keeps as they were, memory outside its own frame
and the runs given to write as it was, in rax the value the contract says, numbers below 2^64 in the
registers, and in the runs given to write what each `ensures` says. -/
def Contract.post (c : Contract) (defs : List Def) (s s' : State) : Prop :=
  s'.rip = load s.mem (s.reg RSP) 8 ∧ s'.reg RSP = s.reg RSP + 8 ∧
  (∀ r ∈ calleeSaved, s'.reg r = s.reg r) ∧
  (∀ a, c.inFrame s a = false → c.inOut s a = false → s'.mem a = s.mem a) ∧
  (∀ e, c.returns = some e → Value defs (c.env s) e (.int (s'.reg 0))) ∧
  (∀ r, s'.reg r < M64) ∧
  (∀ e ∈ c.ensures, e.holds c defs s s') ∧
  ∀ e ∈ c.ensuresW, e.holds c defs s s'

/-- The general registers that are not marked at a call and at a return: all but those a callee keeps
(rax, rcx, rdx, rsp, rsi, rdi, r8 to r11). A register a callee keeps may be marked: it is given back as it
was found. -/
def quietRegs : List Nat := [0, 1, 2, 4, 6, 7, 8, 9, 10, 11]

/-- Is the run whose address is in the register `r` one the contract says is hidden? -/
def Contract.hiddenAt (c : Contract) (r : Nat) : Bool := c.hidden.any fun x => c.regOf x == some r

/-- What the caller sees to about marks (what may depend on a secret): no general register is marked but
those a callee keeps; the address to return to is not marked; no byte of a run given to read is marked,
but for the runs the contract says are hidden; no byte of the file's read-only data is marked. -/
def Contract.quietAt (c : Contract) (s : State) : Prop :=
  (∀ r ∈ quietRegs, s.marks.reg r = false) ∧
  (∀ k, k < 8 → s.marks.mem (s.reg RSP + k) = false) ∧
  (∀ r l, (r, l) ∈ c.regions → c.hiddenAt r = false → ∀ k, k < s.reg l → s.marks.mem (s.reg r + k) = false) ∧
  (∀ x r n, (x, r, n) ∈ c.fixeds → x ∉ c.hidden → ∀ k, k < n → s.marks.mem (s.reg r + k) = false) ∧
  ∀ k, k < c.data.length → s.marks.mem (s.data + k) = false

/-- What the function leaves of the marks, `s` being the state at entry: no general register is marked
but those a callee keeps, and outside its own frame and the runs given to write every byte of memory is marked as it was. -/
def Contract.quietAfter (c : Contract) (s s' : State) : Prop :=
  (∀ r ∈ quietRegs, s'.marks.reg r = false) ∧
  ∀ a, c.inFrame s a = false → c.inOut s a = false → s'.marks.mem a = s.marks.mem a

/-- What the function leaves: what `post` says, and what `quietAfter` says of the marks. -/
def Contract.left (c : Contract) (defs : List Def) (s s' : State) : Prop := c.post defs s s' ∧ c.quietAfter s s'

/-- The function's code meets the contract, among the functions of `world` (those it may call): from every
state at entry of which the caller has seen to what the contract asks, it runs to its return, touching
only what it is let, using nothing marked in a way that shows, and leaves what the contract says. -/
def Meets (world : List Program) (c : Contract) (defs : List Def) (p : Program) : Prop :=
  ∀ s, c.pre p s → c.quietAt s → Runs world (c.perm s) p (c.left defs s) s

end Ode
