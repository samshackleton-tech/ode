import Reader
/-!
The verifier as a program:  `odeverify TABLE STATEMENT PROOF`

TABLE is `../core/x86.tab`. STATEMENT says what is to be shown, and is made by the one who asks
(statement.py makes it from a file's bytes and a specification's text). A line a thing:

    i START END ROW…          an instruction of the function, as the reader of code writes it
    arg NAME number           the contract's arguments, in order
    arg NAME bytes LEN
    returns EXPRESSION
    stack N
    def NAME PARAMETER… = EXPRESSION      a definition of the specification
    callee NAME               a function this one calls, then its contract, by which the call is taken:
    carg NAME number  /  carg NAME bytes LEN  /  creturns EXPRESSION  /  cstack N

PROOF is the maker's, and may be anything: no line of it adds to what is to be shown, and a line of the
statement's kinds in it is refused.

    place PC                  a place, then what holds there
    name NAME REGISTER
    keep REGISTER…
    fact EXPRESSION
    decreases EXPRESSION
    t NAME [N]                what the verifier asks for, in the order it asks
    r … / s … / q             a proof of arithmetic (as ArithMain.lean reads it)

An EXPRESSION is written with brackets: (num 1) (name x) (bin + A B) (ifx C A B) (index A I) (call f A…).
It answers `shown`, or what it needs or why it refuses, and ends with 0 only for `shown`.
Reading this text is not covered by any theorem.
-/
open Ode Ode.Arithmetic

def main (args : List String) : IO UInt32 := do
  match args with
  | [tablePath, statementPath, proofPath] =>
    let table ← match readTable (← IO.FS.readFile tablePath) with
      | .ok t => pure t
      | .error e => IO.println e; return 2
    let lines (path : String) : IO (List String) := do
      pure (((← IO.FS.readFile path).splitOn "\n").map fun l => (l.replace "\r" ""))
    match (← lines statementPath).foldlM (Job.line table false) {} with
    | .error e => IO.println e; return 2
    | .ok job =>
      match (← lines proofPath).foldlM (Job.line table true) job with
      | .error e => IO.println e; return 2
      | .ok job =>
        match verdict job.ctx job.items with
        | none => IO.println "shown"; return 0
        | some why => IO.println why; return 1
  | _ => IO.println "odeverify TABLE STATEMENT PROOF"; return 2
