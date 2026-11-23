import Reader
import Advice
/-!
The verifier as the PROVER's helper:  `odeprove TABLE STATEMENT HEAD NAME`

Nobody relies on this program. It says what `odeverify` would say of a proof that is still being written,
without going through the proof from its first line each time a line is added. A finished proof is given
to `odeverify`, which alone says `shown` to a reader.

HEAD holds the proof's lines before those to be found: the parts of the functions before NAME, then
`for NAME`, its places, and as many lines of its part as the prover likes to begin from. The further lines
of NAME's part come on standard input, as the prover finds them.

The verifier (Core.lean) takes the proof's lines by number. Here, when it comes to a line that has not
come yet, the process makes a copy of itself (`fork`). The copy goes on as if the proof ended there and
prints what the verifier then says, as `odeverify` would for that much of the proof. The original waits,
having done all the work up to that line, for one of:

    lines N        and N lines: a copy goes on with them, and the original waits for that copy to end
    back           the process prints `.back` and ends; the one that made it waits again

So the processes that wait are the stages of the proof so far, the newest last, and going back to an
earlier stage costs nothing. After what the verifier says comes one line: `.more` where a process now
waits at the end of the lines given, `.end` where none does (the verifier refused, or needed something no
further line can give). Each command is answered before the next is sent: a copy takes a copy of the
input already read, so two commands sent at once would be read twice.
-/
open Ode Ode.Arithmetic

@[extern "fork"] opaque cFork : UInt64 → UInt32
@[extern "waitpid"] opaque cWaitpid : UInt32 → USize → UInt32 → UInt32

initialize known : IO.Ref (Array Item) ← IO.mkRef #[]        -- the lines of NAME's part that have come
initialize ended : IO.Ref Bool ← IO.mkRef false              -- this copy goes on as if the proof ended
initialize forks : IO.Ref UInt64 ← IO.mkRef 0
initialize reader : IO.Ref (List String → Except String (List Item)) ← IO.mkRef (fun _ => .ok [])

def say (text : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStr text
  out.flush

def forkNow : IO UInt32 := do
  (← IO.getStdout).flush
  let n ← forks.modifyGet fun n => (n, n + 1)
  let pid := cFork n
  if pid == 0xFFFFFFFF then throw (IO.userError "fork failed")
  if pid == 0 then forks.set (n + 1000003)
  pure pid

def waitFor (pid : UInt32) : IO Unit := do
  if cWaitpid pid 0 0 == 0xFFFFFFFF then throw (IO.userError "waitpid failed")

partial def lineIO (n : Nat) : IO (Option Item) := do
  let have_ ← known.get
  if h : n < have_.size then return some have_[n]
  if ← ended.get then return none
  let copy ← forkNow
  if copy == 0 then ended.set true; return none
  waitFor copy
  let stdin ← IO.getStdin
  let rec wait : IO (Option Item) := do
    let command := (← stdin.getLine).replace "\n" ""
    match (command.splitOn " ").filter (· ≠ "") with
    | ["lines", count] =>
      let mut lines : List String := []
      for _ in [0:count.toNat!] do lines := lines ++ [(← stdin.getLine).replace "\n" ""]
      match (← reader.get) lines with
      | .error why => say s!"{why}\n.end\n"; wait
      | .ok [] => say "refused: no line of a proof among those given\n.end\n"; wait
      | .ok items =>
        let copy ← forkNow
        if copy == 0 then
          known.modify (· ++ items.toArray)
          lineIO n
        else
          waitFor copy
          wait
    | ["back"] => say ".back\n"; IO.Process.exit 0
    | _ => IO.Process.exit 0            -- the input has ended
  wait

unsafe def lineUnsafe (n : Nat) : Option Item :=
  match unsafeIO (lineIO n) with
  | .ok item => item
  | .error _ => none

@[implemented_by lineUnsafe] def lineAsItComes (_ : Nat) : Option Item := none

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--locate", tablePath, statementPath, proofPath] =>
    let table ← match readTable (← IO.FS.readFile tablePath) with
      | .ok t => pure t
      | .error e => IO.println e; return 2
    let lines (path : String) : IO (List String) := do
      pure (((← IO.FS.readFile path).splitOn "\n").map fun l => (l.replace "\r" ""))
    let job ← match (← lines statementPath).foldlM (Job.line table false) {} with
      | .error e => IO.println e; return 2
      | .ok job => pure job
    let job ← match (← lines proofPath).foldlM (Job.line table true) job with
      | .error e => IO.println e; return 2
      | .ok job => pure job
    let mut done : List (String × Contract) := []
    for f in job.fns do
      if done.any (fun d => d.1 == f.name) then
        IO.println s!"refused: two functions are named {f.name}\nin {f.name}"; return 1
      let ctx : Ctx := { code := f.code, contract := f.contract, defs := job.defs, places := f.places, callees := done,
                         pieces := job.pieces, piece := f.piece }
      match locateRefusal ctx f.proof with
      | some why => IO.println s!"{why}\nin {f.name}"; return 1
      | none => done := (f.name, f.contract) :: done
    IO.println "shown"
    return 0
  | [tablePath, statementPath, headPath, name] =>
    let table ← match readTable (← IO.FS.readFile tablePath) with
      | .ok t => pure t
      | .error e => say s!"{e}\n.end\n"; return 2
    let lines (path : String) : IO (List String) := do
      pure (((← IO.FS.readFile path).splitOn "\n").map fun l => (l.replace "\r" ""))
    let job ← match (← lines statementPath).foldlM (Job.line table false) {} with
      | .error e => say s!"{e}\n.end\n"; return 2
      | .ok job => pure job
    let job ← match (← lines headPath).foldlM (Job.line table true) job with
      | .error e => say s!"{e}\n.end\n"; return 2
      | .ok job => pure job
    if !job.fns.any (fun f => f.name == name) then say s!"refused: {name} is no function of the statement\n.end\n"; return 2
    known.set ((job.fns.find? (fun f => f.name == name)).map (·.proof.toArray) |>.getD #[])
    -- lines that come later are read as lines of NAME's part, each batch by itself
    let base : Job := { job with cur := some name, starts := [], steps := [],
                                 fns := job.fns.map fun f => if f.name == name then { f with proof := [] } else f }
    reader.set fun ls => do
      let j ← ls.foldlM (Job.line table true) base
      match j.fns.find? (fun f => f.name == name) with
      | some f => pure f.proof
      | none => pure []
    -- as verdictFrom (Core.lean) goes: the functions in the statement's order, each by the contracts of those before
    let mut done : List (String × Contract) := []
    let mut said : Option String := none
    for f in job.fns do
      if said.isSome then break
      if done.any (fun d => d.1 == f.name) then said := some s!"refused: two functions are named {f.name}"
      else
        let ctx : Ctx := { code := f.code, contract := f.contract, defs := job.defs, places := f.places, callees := done,
                           pieces := job.pieces, piece := f.piece }
        let why ←
          if f.name == name then do
            -- (with the advice: where the lines have run out before an `ensures` of words or a call, the rows to try are printed)
            match verify { ctx with advice := adviceFor ctx } { line := lineAsItComes } with
            | .error why => pure (some why)
            | .ok _ =>
              match ctx.contract.resultHidden with
              | none => pure none
              | some rh =>
                if !rh.all ctx.contract.hidden.contains then
                  pure (some "result depends on: arguments kept out of the result must be a subset of those kept out of the trace")
                else
                  let items ← known.get
                  match verdictOne { ctx with contract := ctx.contract.forResult rh, resultPass := true } items.toList with
                  | none => pure none
                  | some why => pure (some s!"for `result depends on`: {why}")
          else pure (verdict ctx f.proof)
        match why with
        | some why => said := some s!"{why}\nin {f.name}"
        | none => done := (f.name, f.contract) :: done
    say ((said.getD "shown") ++ "\n" ++ (if ← ended.get then ".more\n" else ".end\n"))
    return 0
  | _ => say "odeprove TABLE STATEMENT HEAD NAME | odeprove --locate TABLE STATEMENT PROOF\n.end\n"; return 2
