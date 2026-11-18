import Reader
/-!
The meaning of definitions as a program:  `odespec DEFINITIONS CASES`

For the comparison of `evalSpec` (Contract.lean) with `../kcheck/ode.py` (test_spec.py). DEFINITIONS holds
`def` lines as a statement has them. A line of CASES is an expression and what its names are:

    NAME=i:NUMBER NAME=b:HEXBYTES … | EXPRESSION

The answer is a line: `int N`, `bool 0` or `bool 1`, `bytes HEX` (a list of numbers all below 256), `list N N …`
(a list with a number of 256 or more), or `none` where the expression has no value.
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

def showVal : Option Val → String
  | some (.int n) => s!"int {n}"
  | some (.bool b) => if b then "bool 1" else "bool 0"
  | some (.bytes l) =>
    if l.all (· < 256) then "bytes " ++ String.join (l.map hex2) else "list " ++ " ".intercalate (l.map toString)
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
