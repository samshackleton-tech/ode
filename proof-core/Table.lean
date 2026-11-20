/-!
# The table of instructions, read

`../core/x86.tab` is the one account of the machine: a row is `NAME | ASM | ROW | EFFECT`. This file reads
its rows (the lines that say how a row's instances are written in bytes are left to the reader of code),
and says which row a decoded instruction is an instance of. It follows `../core/table.py` line for line.
-/
namespace Ode

/-- Nested lists of words: how a decoded instruction, and a row's ROW, are written. -/
inductive Sexp where
  | atom (s : String)
  | list (l : List Sexp)
  deriving Repr, Inhabited

def blank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Words and brackets. -/
def sexpTokens (text : String) : List String :=
  let flush (word : List Char) (out : List String) := if word.isEmpty then out else String.ofList word.reverse :: out
  let rec go : List Char → List Char → List String → List String
    | [], word, out => (flush word out).reverse
    | c :: cs, word, out =>
      if c == '(' || c == ')' then go cs [] (String.singleton c :: flush word out)
      else if blank c then go cs [] (flush word out)
      else go cs (c :: word) out
  go text.toList [] []

def parseSexp (text : String) : Option (List Sexp) :=
  let step (st : Option (List (List Sexp))) (t : String) : Option (List (List Sexp)) :=
    match st with
    | none => none
    | some stack =>
      if t == "(" then some ([] :: stack)
      else if t == ")" then
        match stack with
        | done :: top :: rest => some ((Sexp.list done.reverse :: top) :: rest)
        | _ => none
      else match stack with
        | top :: rest => some ((Sexp.atom t :: top) :: rest)
        | [] => none
  match (sexpTokens text).foldl step (some [[]]) with
  | some [top] => some top.reverse
  | _ => none

/-- An EFFECT's expression. -/
inductive Expr where
  | number (n : Nat)
  | name (s : String)
  | lane (s : String) (k : Nat)
  | call (f : String) (args : List Expr)
  deriving Repr, Inhabited

/-- An EFFECT's statement. -/
inductive Stmt where
  | set (place value : Expr)
  | vset (place value : Expr)             -- a 128-bit vector or its memory operand
  | vset512 (place value : Expr)          -- a 512-bit vector or its memory operand
  | jump (target : Expr) (cond : Option (String × Bool))
  | call (target : Expr)
  | ret
  | nothing
  deriving Repr, Inhabited

structure TRow where
  name : String
  pattern : List Sexp
  effect : List Stmt
  deriving Repr, Inhabited

def wordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Names, numbers, and the signs `( ) . , =`. -/
def effectTokens (text : String) : List String :=
  let flush (word : List Char) (out : List String) := if word.isEmpty then out else String.ofList word.reverse :: out
  let rec go : List Char → List Char → List String → List String
    | [], word, out => (flush word out).reverse
    | c :: cs, word, out =>
      if wordChar c then go cs (c :: word) out
      else if c == '(' || c == ')' || c == '.' || c == ',' || c == '=' then go cs [] (String.singleton c :: flush word out)
      else go cs [] (flush word out)
  go text.toList [] []

mutual
  partial def parseExpr : List String → Option (Expr × List String)
    | [] => none
    | t :: rest =>
      match t.toNat? with
      | some n => some (.number n, rest)
      | none =>
        match rest with
        | "(" :: rest => (parseArgs rest []).map fun (args, rest) => (.call t args, rest)
        | "." :: k :: rest => k.toNat?.map fun k => (.lane t k, rest)
        | _ => some (.name t, rest)
  partial def parseArgs : List String → List Expr → Option (List Expr × List String)
    | ")" :: rest, args => some (args.reverse, rest)
    | "," :: rest, args => parseArgs rest args
    | tokens, args => (parseExpr tokens).bind fun (e, rest) => parseArgs rest (e :: args)
end

def wholeExpr (tokens : List String) : Option Expr :=
  match parseExpr tokens with
  | some (e, []) => some e
  | _ => none

def splitAt (sign : String) : List String → Option (List String × List String)
  | [] => none
  | t :: rest => if t == sign then some ([], rest) else (splitAt sign rest).map fun (a, b) => (t :: a, b)

/-- What a statement sets is a vector register (`X`, `Y`, `Z`), the vector registers' bits above the low
128 (`above128`), or sixteen bytes of memory (`mem128`). -/
def isVectorPlace : Expr → Bool
  | .name n => n == "X" || n == "Y" || n == "Z" || n == "above128"
  | .call f _ => f == "mem128"
  | _ => false

def isWidePlace : Expr → Bool
  | .name n => n == "X512" || n == "Y512" || n == "Z512" || n == "M"
  | .call f _ => f == "mem512" || f == "mem512a"
  | _ => false

def parseStmt (text : String) : Option Stmt :=
  let t := effectTokens text
  match splitAt "=" t with
  | some (place, value) => do
    let p ← wholeExpr place
    let v ← wholeExpr value
    some (if isVectorPlace p then .vset p v else if isWidePlace p then .vset512 p v else .set p v)
  | none =>
    match t with
    | ["return"] => some .ret
    | ["nothing"] => some .nothing
    | "call" :: target => (wholeExpr target).map .call
    | "jump" :: rest =>
      match splitAt "if" rest with
      | none => (wholeExpr rest).map (.jump · none)
      | some (target, ["not", flag]) => if flag == "zf" || flag == "cf" then (wholeExpr target).map (.jump · (some (flag, false))) else none
      | some (target, [flag]) => if flag == "zf" || flag == "cf" then (wholeExpr target).map (.jump · (some (flag, true))) else none
      | _ => none
    | _ => none

def trim (s : String) : String :=
  String.ofList ((s.toList.dropWhile blank).reverse.dropWhile blank).reverse

/-- The rows of the table, in its order. -/
def readTable (text : String) : Except String (Array TRow) := do
  let mut rows : Array TRow := #[]
  for raw in text.splitOn "\n" do
    let line := trim ((raw.splitOn "#").headD "")
    if line.isEmpty || line.startsWith "=" then continue
    match (line.splitOn "|").map trim with
    | [name, _, row, effect] =>
      let some pattern := parseSexp row | throw s!"the table: cannot read the row of {name}"
      let some stmts := ((effect.splitOn ";").mapM parseStmt) | throw s!"the table: cannot read the effect of {name}"
      rows := rows.push ⟨name, pattern, stmts⟩
    | _ => throw s!"the table: not NAME | ASM | ROW | EFFECT: {line}"
  return rows

/-- What each placeholder of a row is, in an instance: a register's name, or a number as the decoder wrote it. -/
abbrev Bind := List (String × String)

def unifyAtom (p ins : String) (bind : Bind) : Option Bind :=
  let put (key val : String) : Option Bind :=
    match bind.lookup key with
    | some old => if old == val then some bind else none
    | none => some ((key, val) :: bind)
  if p == ".D" || p == ".S" || p == ".B" || p == ".P" then
    match ins.toList with
    | '.' :: name => if p == ".P" && ins == ".rsp" then none else put (String.ofList (p.toList.drop 1)) (String.ofList name)
    | _ => none
  else if p == "X" || p == "Y" || p == "Z" || p == "M" then
    if ins.toList.all Char.isDigit && !ins.isEmpty then put p ins else none
  else if p == "I" || p == "J" || p == "K" || p == "L" || p == "N" then put p ins
  else if p == ins then some bind else none

mutual
  partial def unify : Sexp → Sexp → Bind → Option Bind
    | .atom p, .atom i, b => unifyAtom p i b
    | .list ps, .list is, b => unifyList ps is b
    | _, _, _ => none
  partial def unifyList : List Sexp → List Sexp → Bind → Option Bind
    | [], [], b => some b
    | p :: ps, i :: is, b => (unify p i b).bind (unifyList ps is)
    | _, _, _ => none
end

/-- The first row of the table that the decoded instruction is an instance of, and what its placeholders are. -/
def findRow (table : Array TRow) (ins : List Sexp) : Option (TRow × Bind) :=
  table.toList.findSome? fun row => (unifyList row.pattern ins []).map fun b => (row, b)

end Ode
