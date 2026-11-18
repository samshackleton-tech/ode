import Reader
/-!
The meaning of definitions as a program:  `odespec DEFINITIONS CASES`

For the comparison of `evalSpec` (Contract.lean) with `../kcheck/ode.py` (test_spec.py). DEFINITIONS holds
`def` lines as a statement has them. A line of CASES is an expression and what its names are:

    NAME=i:NUMBER NAME=b:HEXBYTES … | EXPRESSION

The answer is a line: `int N`, `bool 0` or `bool 1`, `bytes HEX` (a list of numbers all below 256), `list N N …`
(a list of numbers, one of them 256 or more), `val V` for any other value (a word `wN`, a counter `cN`, a list
`[V V]`, a record `{NAME=V NAME=V}`, a number `N`, `true`, `false`), or `none` where the expression has no value.
-/
open Ode

def hexBytes (s : String) : List Nat :=
  let cs := s.toList.toArray
  (List.range (cs.size / 2)).map fun i => (hexDigit cs[2 * i]!).getD 0 * 16 + (hexDigit cs[2 * i + 1]!).getD 0

def hex2 (n : Nat) : String :=
  let d := "0123456789abcdef".toList.toArray
  String.ofList [d[n / 16 % 16]!, d[n % 16]!]

def readBinding (text : String) : Option (String × Val) :=
  match text.splitOn "=" with
  | [name, v] =>
    if v.startsWith "i:" then (readInt (v.drop 2).toString).map fun n => (name, Val.int n)
    else if v.startsWith "b:" then some (name, Val.bytes (hexBytes (v.drop 2).toString))
    else none
  | _ => none

/-- The numbers of a list, where they are all numbers. -/
def numbersOf : List Val → Option (List Int)
  | [] => some []
  | .int n :: rest => (numbersOf rest).map (n :: ·)
  | _ => none

partial def showAny : Val → String
  | .int n => toString n
  | .bool b => if b then "true" else "false"
  | .word w => s!"w{w}"
  | .counter n => s!"c{n}"
  | .list l => "[" ++ " ".intercalate (l.map showAny) ++ "]"
  | .record fields => "{" ++ " ".intercalate (fields.map fun (n, v) => n ++ "=" ++ showAny v) ++ "}"

def showVal : Option Val → String
  | some (.int n) => s!"int {n}"
  | some (.bool b) => if b then "bool 1" else "bool 0"
  | some (.list l) =>
    match numbersOf l with
    | some ns =>
      if ns.all (fun n => 0 ≤ n && n < 256) then "bytes " ++ String.join (ns.map fun n => hex2 n.toNat)
      else "list " ++ " ".intercalate (ns.map toString)
    | none => "val " ++ showAny (.list l)
  | some v => "val " ++ showAny v
  | none => "none"

def runCase (defs : List Def) (line : String) : String :=
  match line.splitOn " | " with
  | [bindings, text] =>
    match ((bindings.splitOn " ").filter (· ≠ "")).mapM readBinding, readSExpr text with
    | some env, .ok e => showVal (evalSpec defs 4000 env e)
    | _, _ => "unreadable"
  | _ => "unreadable"

def main (args : List String) : IO UInt32 := do
  match args with
  | [defsPath, casesPath] =>
    let lines (path : String) : IO (List String) := do
      pure ((((← IO.FS.readFile path).splitOn "\n").map fun l => (l.replace "\r" "")).filter (· ≠ ""))
    match (← lines defsPath).foldlM (Job.line #[] false) {} with
    | .error e => IO.println e; return 2
    | .ok job =>
      for l in ← lines casesPath do IO.println (runCase job.defs l)
      return 0
  | _ => IO.println "odespec DEFINITIONS CASES"; return 2
