import Arithmetic
/-!
The arithmetic rule as a program: proofs on standard input, a letter a proof on standard output.

    r CONSTANT C0 C1 …     a row the proof starts from: C0·x0 + C1·x1 + … + CONSTANT ≥ 0
    s I A J B D            a step: (A · row I + B · row J) / D
    q                      the proof ends: `y` if its rows cannot all hold by its steps, else `n`

Numbers are whole numbers in decimal. A line that is none of these makes its proof's answer `n`.
This reading of text is not covered by `Ode.Arithmetic.refutes_sound`.
-/
open Ode.Arithmetic

structure Reading where
  starts : Array Row := #[]
  steps : Array Step := #[]
  bad : Bool := false
  said : String := ""

def Reading.line (r : Reading) (text : String) : Reading :=
  match (text.splitOn " ").filter (· ≠ "") with
  | [] => r
  | "r" :: numbers => match numbers.mapM String.toInt? with
    | some (k :: cs) => { r with starts := r.starts.push ⟨cs, k⟩ }
    | _ => { r with bad := true }
  | "s" :: numbers => match numbers.mapM String.toNat? with
    | some [i, a, j, b, d] => { r with steps := r.steps.push ⟨i, a, j, b, d⟩ }
    | _ => { r with bad := true }
  | ["q"] =>
    let yes := !r.bad && refutes r.starts.toList r.starts.toList r.steps.toList
    { said := r.said ++ (if yes then "y\n" else "n\n") }
  | _ => { r with bad := true }

partial def read (input : IO.FS.Stream) (r : Reading) : IO Reading := do
  let text ← input.getLine
  if text.isEmpty then return r else read input (r.line ((text.replace "\n" "").replace "\r" ""))

def main : IO Unit := do
  let r ← read (← IO.getStdin) {}
  IO.print r.said
