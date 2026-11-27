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

Instead of POSIX `fork()` (which copies process page tables on every query), this driver runs `Core`'s
exact pure functions step-by-step on an explicit continuation stack and keeps an in-memory array of pure
checkpoints `(next, jdone, stack)`. A checkpoint is committed only when `next` strictly advances and stays
strictly below the current proof length (`next < items.size`), guaranteeing that every `items.line` read
before that checkpoint hit an already-present item and never observed end-of-proof. Rolling back (`back`)
shrinks two arrays in O(1) time with zero syscalls.
-/
open Ode Ode.Arithmetic

def say (text : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStr text
  out.flush

/-- What to do after establishing all `facts` of a place `p`. -/
inductive PlaceCont where
  | arriveJoin (p : Place)
  | genJoin (fuel : Nat) (base : Sym) (seen : List Seen) (jstack : List Nat) (p : Place) (first : Sym)
  | arriveLoop (p : Place) (d : Row)
  | genLoop (fuel : Nat) (seen : List Seen) (p : Place) (origNext : Sym)

/-- One pure continuation frame of the incremental verifier driver. -/
inductive StepTask where
  | instr (fuel : Nat) (base : Sym) (seen : List Seen) (jstack : List Nat) (s : Sym) (pc : Nat)
  | afterClears (fuel : Nat) (base : Sym) (seen : List Seen) (jstack : List Nat) (s : Sym) (pc : Nat) (i : Instr)
  | onward (fuel : Nat) (base : Sym) (seen : List Seen) (jstack : List Nat) (next : Sym × Next)
  | placeFacts (p : Place) (env : List (String × SVal)) (s : Sym) (rem : List SExpr) (cont : PlaceCont)
  | specFacts (p : Place) (env : List (String × SVal)) (s : Sym) (remFacts : List SFact) (remExprs : List SExpr) (cont : PlaceCont)
  | specOne (fuel : Nat) (s : Sym) (goal : SFact) (p : Place) (env : List (String × SVal)) (remFacts : List SFact) (remExprs : List SExpr) (cont : PlaceCont)
  | filledBytes (env : List (String × SVal)) (x : String) (b : SExpr) (w : Nat) (lo : Row) (k : Nat) (count : Nat) (s : Sym) (after : Sym → StepTask)
  | finishPlace (p : Place) (s : Sym) (cont : PlaceCont)
  | afterRange (p : Place) (s : Sym) (cont : PlaceCont)
  | pushJoin (p : Place) (first : Sym)
  | restoreJdone (saved : List JoinEntry)
  | checkFinished

structure DriverState where
  next : Nat
  jdone : List JoinEntry
  stack : List StepTask

instance : Inhabited DriverState := ⟨{ next := 0, jdone := [], stack := [] }⟩

inductive StepOut where
  | next (st : DriverState)
  | done
  | err (msg : String)

def itemsAt (arr : Array Item) (pos : Nat) : Items :=
  { line := fun n => if h : n < arr.size then some arr[n] else none, next := pos }

/-- Finish a place check after all `p.facts` have been established: check lanes/cells, then run
`rangeShown` (byte-by-byte via `filledBytes` so each output byte checkpoints independently). -/
def stepFinishPlace (ctx : Ctx) (st : DriverState) (arr : Array Item) (p : Place) (s : Sym) (cont : PlaceCont)
    (tail : List StepTask) : StepOut :=
  let laneErr := match cont with
    | .arriveJoin _ | .genJoin .. => s!"at the join place {p.pc} the vector registers are not shown to hold what the place says"
    | .arriveLoop .. => s!"at the place {p.pc} the vector registers are not shown to hold what the place says, on coming there again"
    | .genLoop .. => s!"at the place {p.pc} the vector registers are not shown to hold what the place says"
  let cellErr := match cont with
    | .arriveJoin _ | .genJoin .. => s!"at the join place {p.pc} a cell of the frame is not shown to hold what the place says"
    | .arriveLoop .. => s!"at the place {p.pc} a cell of the frame is not shown to hold what the place says, on coming there again"
    | .genLoop .. => s!"at the place {p.pc} a cell of the frame is not shown to hold what the place says"
  if !(p.lanes.all (lanesShown ctx p s)) then .err laneErr
  else if !(p.cells.all (cellShown ctx p s)) then .err cellErr
  else
    match p.wrote with
    | none => .next { st with stack := .afterRange p s cont :: tail }
    | some (run, loExpr, f, argsExpr, fromStart) =>
      match findOutNamed run ctx.contract.outs 0 with
      | none => .err "a place says what is written of what is no run given to write"
      | some (w, n) =>
        let env := placeEnv ctx p s.reg
        let prep : V (List (String × SVal) × String × SExpr × Row × Nat × Sym) := do
          let (lo0, s1) ← seval ctx env s loExpr
          let (lo, s2) ← numberV (opener ctx DEEP) s1 lo0
          let (vs0, s3) ← seval ctx env s2 argsExpr
          match vs0 with
          | .list vs =>
            match eachOf ctx f vs.length with
            | none => refuse "a place says what is written by what is no list made thing by thing from 0 on"
            | some (params, x, b, hi) =>
              if n < hi then refuse "a place says more is written than the run has places"
              else do
                entail s3.facts lo
                let base := rangeBase s3 w f vs hi fromStart
                let diff := if fromStart then Lin.sub lo base else Lin.sub base lo
                let start := if fromStart then base else lo
                match Lin.isConst diff with
                | some k =>
                  if k < 0 || GROW < k then refuse "a place: what is written does not reach from where the place says"
                  else pure (params.zip vs, x, b, start, k.toNat, s3)
                | none => refuse "a place: where the written places begin is not known by a number from where they began before"
          | _ => refuse "a place: a definition used with what is no list of things"
        match prep (itemsAt arr st.next) with
        | .error msg => .err msg
        | .ok ((fenv, x, b, start, cnt, s3), it') =>
          .next { st with
            next := it'.next
            stack := .filledBytes fenv x b w start 0 cnt s3 (fun s' => .afterRange p s' cont) :: tail }

/-- Execute one pure step of the verifier driver, calling `Core` functions directly. -/
def stepOnce (ctx : Ctx) (st : DriverState) (arr : Array Item) (withPc : Bool := false) : StepOut :=
  match st.stack with
  | [] => .done
  | task :: tail =>
    let it := itemsAt arr st.next
    match task with
    | .checkFinished =>
      match finished it with
      | .error msg => .err msg
      | .ok (true, it') => .next { st with next := it'.next, stack := tail }
      | .ok (false, _) => .err "the proof says more than is asked of it"
    | .pushJoin p first =>
      .next { st with jdone := ⟨p, first⟩ :: st.jdone, stack := tail }
    | .restoreJdone saved =>
      .next { st with jdone := saved, stack := tail }
    | .instr fuel base seen jstack s pc =>
      if fuel == 0 then .err "a path longer than the verifier goes"
      else match ctx.code.lookup pc with
      | none => .err s!"no instruction at {pc}"
      | some i =>
        match symClears ctx pc CLEARS s it with
        | .error msg => .err msg
        | .ok (s', it') =>
          .next { st with next := it'.next, stack := .afterClears (fuel - 1) base seen jstack s' pc i :: tail }
    | .afterClears fuel base seen jstack s pc i =>
      match symNext ctx s i it with
      | .error msg => .err (if withPc && msg.startsWith "need entail\n" then s!"{msg}at {pc}\n" else msg)
      | .ok (nexts, it') =>
        let tasks := nexts.map fun nx => StepTask.onward fuel base seen jstack nx
        .next { st with next := it'.next, stack := tasks ++ tail }
    | .onward fuel base seen jstack next =>
      match next.2 with
      | .returned => .next { st with stack := tail }
      | .at pc' =>
        match ctx.places.find? (fun p => p.pc == pc') with
        | none => .next { st with stack := .instr fuel base seen jstack next.1 pc' :: tail }
        | some p =>
          if p.isJoin then
            if jstack.contains pc' then
              .err s!"at the join place {pc'} a path returns to it (add `decreases` for a loop)"
            else match st.jdone.find? (fun e => e.place.pc == pc') with
            | some e =>
              let s := next.1
              match e.place.keep.find? fun r => s.reg r != e.first.reg r with
              | some r => .err s!"at the join place {e.place.pc} register {r} does not hold what it held on first coming there"
              | none =>
              if !(e.first.q.regq.all s.q.regq.contains) then
                .err s!"at the join place {e.place.pc} register {(e.first.q.regq.find? fun r => !s.q.regq.contains r).getD 0} may depend on values kept out of the trace, which it did not on first coming there"
              else if !(e.first.q.fq.all s.q.fq.contains) then
                .err s!"at the join place {e.place.pc} stack slot {(e.first.q.fq.find? fun c => !s.q.fq.contains c).getD 0} may depend on values kept out of the trace, which it did not on first coming there"
              else if !(e.first.frame.all fun cell => s.frame.contains cell) then
                .err "at the join place the frame does not hold what it held on first coming there"
              else if !(e.first.vecIntact.all s.vecIntact.contains) then
                .err "at the join place a callee-saved vector register was modified"
              else
                .next { st with stack := .placeFacts e.place (placeEnv ctx e.place s.reg) s e.place.facts (.arriveJoin e.place) :: tail }
            | none =>
              match joinFirst ctx base next.1 p with
              | none =>
                .err (match p.keep.find? fun r => !(decide (r < ctx.nreg) && decide ((next.1.reg r).coeff.length ≤ base.nvars)) with
                  | some r => s!"at the join place {pc'} register {r} depends on a value not in scope"
                  | none => s!"at the join place {pc'} a kept register depends on a value not in scope")
              | some first =>
                let s := next.1
                match p.keep.find? fun r => s.reg r != first.reg r with
                | some r => .err s!"at the join place {p.pc} register {r} does not hold what it held on first coming there"
                | none =>
                if !(first.q.regq.all s.q.regq.contains) then
                  .err s!"at the join place {p.pc} register {(first.q.regq.find? fun r => !s.q.regq.contains r).getD 0} may depend on values kept out of the trace, which it did not on first coming there"
                else if !(first.q.fq.all s.q.fq.contains) then
                  .err s!"at the join place {p.pc} stack slot {(first.q.fq.find? fun c => !s.q.fq.contains c).getD 0} may depend on values kept out of the trace, which it did not on first coming there"
                else if !(first.frame.all fun cell => s.frame.contains cell) then
                  .err "at the join place the frame does not hold what it held on first coming there"
                else if !(first.vecIntact.all s.vecIntact.contains) then
                  .err "at the join place a callee-saved vector register was modified"
                else
                  .next { st with stack := .placeFacts p (placeEnv ctx p s.reg) s p.facts (.genJoin fuel base seen jstack p first) :: tail }
          else
            match seen.find? (fun e => e.place.pc == pc') with
            | some e =>
              let s := next.1
              match e.place.keep.find? fun r => s.reg r != e.first.reg r with
              | some r => .err s!"at the place {e.place.pc} register {r} does not hold what it held on first coming there"
              | none =>
              if !(e.first.q.regq.all s.q.regq.contains) then
                .err s!"at the place {e.place.pc} register {(e.first.q.regq.find? fun r => !s.q.regq.contains r).getD 0} may depend on values kept out of the trace, which it did not on first coming there"
              else if !(e.first.q.fq.all s.q.fq.contains) then
                .err s!"at the place {e.place.pc} stack slot {(e.first.q.fq.find? fun c => !s.q.fq.contains c).getD 0} may depend on values kept out of the trace, which it did not on first coming there"
              else if !(e.first.frame.all fun cell => s.frame.contains cell) then
                .err "at the place the frame does not hold what it held on first coming there"
              else if !(e.first.vecIntact.all s.vecIntact.contains) then
                .err "at the place a callee-saved vector register was modified in the loop"
              else
                .next { st with stack := .placeFacts e.place (placeEnv ctx e.place s.reg) s e.place.facts (.arriveLoop e.place e.d) :: tail }
            | none =>
              if !p.keep.contains RSP || p.names.any (fun (_, r) => decide (ctx.nreg ≤ r)) || (!p.cells.isEmpty && !ctx.contract.valArrays.isEmpty) then
                .err "a place must keep the stack pointer, and name registers"
              else
                let s := next.1
                .next { st with stack := .placeFacts p (placeEnv ctx p s.reg) s p.facts (.genLoop fuel seen p s) :: tail }
    | .placeFacts p env s rem cont =>
      match rem with
      | [] => .next { st with stack := .finishPlace p s cont :: tail }
      | e :: rest =>
        let stepA : V (List SFact × Sym) := do
          let (rows, facts, s1) ← assertion ctx env s e
          each (entail s1.facts) rows
          pure (facts, s1)
        match stepA it with
        | .error msg => .err msg
        | .ok ((facts, s1), it') =>
          .next { st with next := it'.next, stack := .specFacts p env s1 facts rest cont :: tail }
    | .specFacts p env s remFacts remExprs cont =>
      match remFacts with
      | [] => .next { st with stack := .placeFacts p env s remExprs cont :: tail }
      | g :: more =>
        .next { st with stack := .specOne 32 s g p env more remExprs cont :: tail }
    | .specOne fuel s goal p env remFacts remExprs cont =>
      if fuel == 0 then .err "too many definitions opened for one fact"
      else if holdsSpec s.spec goal then
        .next { st with stack := .specFacts p env s remFacts remExprs cont :: tail }
      else
        match pop it with
        | .error msg => .err msg
        | .ok (some (.tag name n), it1) =>
          if name == "open" then
            match (callsOf s.spec goal)[n]? with
            | some c =>
              match openCall ctx s c it1 with
              | .error msg => .err msg
              | .ok (s', it2) =>
                .next { st with next := it2.next, stack := .specOne (fuel - 1) s' goal p env remFacts remExprs cont :: tail }
            | none => .err "no such use of a definition to open"
          else if name == "carry" then
            match carry s goal n it1 with
            | .error msg => .err msg
            | .ok ((), it2) =>
              .next { st with next := it2.next, stack := .specFacts p env s remFacts remExprs cont :: tail }
          else if name == "same" then
            let calls := callsOf s.spec goal
            match calls[n / 256]?, calls[n % 256]? with
            | some ci, some cj =>
              match sameUse s ci cj it1 with
              | .error msg => .err msg
              | .ok ((), it2) =>
                .next { st with next := it2.next, stack := .specOne (fuel - 1) { s with spec := .same ci cj :: s.spec } goal p env remFacts remExprs cont :: tail }
            | _, _ => .err "no such pair of uses of a definition"
          else .err "open, carry, or same is expected"
        | .ok (some _, _) => .err "open, carry, or same is expected"
        | .ok (none, _) =>
          let calls := callsOf s.spec goal
          let ps := samePairs s.spec calls
          let pline := if ps.isEmpty then "" else s!"p {ps}\n"
          let ys := match goal with
            | .value c _ => (heldValues s.spec).zipIdx.filterMap fun ((c', _), k) =>
                if c'.f == c.f then some (toString k) else none
            | _ => []
          let mline := ctx.advice.specMeta s goal calls
          .err s!"need spec\nc {calls.length}\no {31 - (fuel - 1)}\nh {(heldValues s.spec).length}\ny {String.intercalate " " ys}\n{pline}{mline}"
    | .filledBytes env x b w lo k count s after =>
      if count == 0 then
        .next { st with stack := after s :: tail }
      else
        let here := Lin.add lo (Lin.const (k : Int))
        match wroteAt w here s.wrote with
        | none => .err "a place: a byte of the run is not known written"
        | some byte =>
          let oneByte : V Sym := do
            let (v, s1) ← seval ctx ((x, .lin here) :: env) s b
            match v with
            | .val (.lin v) => do
              entail s1.facts (Lin.sub v byte)
              entail s1.facts (Lin.sub byte v)
              pure s1
            | _ => refuse "a place: a thing of the list is no number"
          match oneByte it with
          | .error msg => .err msg
          | .ok (s1, it') =>
            .next { st with next := it'.next, stack := .filledBytes env x b w lo (k + 1) (count - 1) s1 after :: tail }
    | .finishPlace p s cont =>
      stepFinishPlace ctx st arr p s cont tail
    | .afterRange _p s cont =>
      match cont with
      | .arriveJoin _ => .next { st with stack := tail }
      | .genJoin fuel base seen jstack p' first =>
        match generalizeJoin ctx p' first it with
        | .error msg => .err msg
        | .ok (g, it') =>
          .next { st with
            next := it'.next
            stack := .instr fuel base seen (p'.pc :: jstack) { g with q := { regq := first.q.regq, fq := first.q.fq } } p'.pc
                     :: .pushJoin p' first :: tail }
      | .arriveLoop p' d =>
        let fin : V Unit := do
          let (d', s2) ← seval ctx (placeEnv ctx p' s.reg) s p'.decreases
          match d' with
          | .val (.lin d') => entail s2.facts (Lin.sub (Lin.sub d d') (Lin.const 1))
          | _ => refuse "a place's number that decreases is no number"
        match fin it with
        | .error msg => .err msg
        | .ok ((), it') => .next { st with next := it'.next, stack := tail }
      | .genLoop fuel seen p' origNext =>
        let fin : V (Sym × Row) := do
          let g ← fold (suppose ctx (placeEnv ctx p' (s.general ctx.nreg p').reg)) (s.general ctx.nreg p') p'.facts
          let g ← fold (supposeLanes ctx p') g p'.lanes
          let g ← fold (supposeCell ctx p') g p'.cells
          let g ← supposeRange ctx p' g
          let (d, g) ← seval ctx (placeEnv ctx p' (s.general ctx.nreg p').reg) g p'.decreases
          match d with
          | .val (.lin d) => do
            entail g.facts d
            pure (g, d)
          | _ => refuse "a place's number that decreases is no number"
        match fin it with
        | .error msg => .err msg
        | .ok ((g, d), it') =>
          let q0 : SMarks := { regq := placeQuiet ctx p' origNext.q.regq, fq := origNext.q.fq }
          let g0 := { g with q := q0 }
          let savedJdone := st.jdone
          .next { next := it'.next, jdone := [],
                  stack := .instr fuel g0 (⟨p', d, { s with q := q0 }⟩ :: seen) [] g0 p'.pc
                           :: .restoreJdone savedJdone :: tail }

/-- Advance from the latest checkpoint as far as `.next` steps succeed, committing a checkpoint whenever
`next` strictly advances while staying strictly below `arr.size` (so no committed step ever saw EOF). -/
partial def advance (ctx : Ctx) (arr : Array Item) (ckpts : Array DriverState) (withPc : Bool := false) : Except String Unit × Array DriverState :=
  let rec go (cur : DriverState) (cs : Array DriverState) : Except String Unit × Array DriverState :=
    match stepOnce ctx cur arr withPc with
    | .done => (.ok (), cs)
    | .err msg => (.error msg, cs)
    | .next cur' =>
      let cs' :=
        if cur'.next > cs.back!.next && cur'.next < arr.size then cs.push cur'
        else cs
      go cur' cs'
  go ckpts.back! ckpts

/-- After `name` passes `verify`, check optional `result depends on` and any subsequent functions. -/
def finishRest (ctx : Ctx) (items : Array Item) (afterFns : List Fn) (doneAfter : List (String × Contract))
    (runsAfter : List String) (onlyTarget : Bool) : String :=
  let resWhy : Option String :=
    match ctx.contract.resultHidden with
    | none => none
    | some rh =>
      if !rh.all ctx.contract.hidden.contains then
        some "result depends on: arguments kept out of the result must be a subset of those kept out of the trace"
      else
        match verdictOne { ctx with contract := ctx.contract.forResult rh, resultPass := true } items.toList with
        | none => none
        | some why => some s!"for `result depends on`: {why}"
  match resWhy with
  | some why => s!"{why}\nin {ctx.selfName.getD ""}"
  | none =>
    if onlyTarget then "shown"
    else
      let rec checkTail (fns : List Fn) (done : List (String × Contract)) (runsOk : List String) : String :=
        match fns with
        | [] => "shown"
        | f :: more =>
          if done.any (fun d => d.1 == f.name) then s!"refused: two functions are named {f.name}\nin {f.name}"
          else
            let callees := if f.contract.decreases.isSome then (f.name, f.contract) :: done else done
            let selfName := if f.contract.decreases.isSome then some f.name else none
            let fctx : Ctx := {
              ctx with
              code := f.code, contract := f.contract, places := f.places,
              callees := callees, selfName := selfName, piece := f.piece,
              runsCallees := runsOk, advice := {}
            }
            match verdict fctx f.proof with
            | some why => s!"{why}\nin {f.name}"
            | none =>
              let runs' := if fnRunsCapable f then f.name :: runsOk else runsOk
              checkTail more ((f.name, f.contract) :: done) runs'
      checkTail afterFns doneAfter runsAfter

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
    let mut runsOk : List String := []
    for f in job.fns do
      if done.any (fun d => d.1 == f.name) then
        IO.println s!"refused: two functions are named {f.name}\nin {f.name}"; return 1
      let callees := if f.contract.decreases.isSome then (f.name, f.contract) :: done else done
      let selfName := if f.contract.decreases.isSome then some f.name else none
      let baseCtx : Ctx := { code := f.code, contract := f.contract, defs := job.defs, places := f.places, callees := callees,
                             selfName := selfName, pieces := job.pieces, piece := f.piece, runsCallees := runsOk }
      let ctx : Ctx := { baseCtx with advice := { specMeta := specMetaFor baseCtx } }
      match locateRefusal ctx f.proof with
      | some why => IO.println s!"{why}\nin {f.name}"; return 1
      | none =>
        if fnRunsCapable f then runsOk := f.name :: runsOk
        done := (f.name, f.contract) :: done
    IO.println "shown"
    return 0
  | ["--only", "--with-pc", tablePath, statementPath, headPath, name]
  | ["--with-pc", "--only", tablePath, statementPath, headPath, name]
  | ["--with-pc", tablePath, statementPath, headPath, name]
  | ["--only", tablePath, statementPath, headPath, name]
  | [tablePath, statementPath, headPath, name] =>
    let onlyTarget := args.contains "--only"
    let withPc := args.contains "--with-pc"
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

    -- Parse any incoming batch of proof lines for `name` using a clean base `Job`.
    let baseJob : Job := { job with cur := some name, starts := [], steps := [],
                                    fns := job.fns.map fun f => if f.name == name then { f with proof := [] } else f }
    let parseBatch (ls : List String) : Except String (List Item) := do
      let j ← ls.foldlM (Job.line table true) baseJob
      match j.fns.find? (fun f => f.name == name) with
      | some f => pure f.proof
      | none => pure []

    -- Verify any functions before `name` (unless `--only`), and capture `name`'s context + trailing functions.
    let mut done : List (String × Contract) := []
    let mut runsOk : List String := []
    let mut targetCtx : Option Ctx := none
    let mut targetFn : Option Fn := none
    let mut afterFns : List Fn := []
    let mut foundTarget := false
    for f in job.fns do
      if foundTarget then
        afterFns := afterFns ++ [f]
      else
        if done.any (fun d => d.1 == f.name) then
          say s!"refused: two functions are named {f.name}\nin {f.name}\n.end\n"; return 0
        let callees := if f.contract.decreases.isSome then (f.name, f.contract) :: done else done
        let selfName := if f.contract.decreases.isSome then some f.name else none
        let ctx : Ctx := { code := f.code, contract := f.contract, defs := job.defs, places := f.places, callees := callees,
                           selfName := selfName, pieces := job.pieces, piece := f.piece, runsCallees := runsOk }
        if f.name == name then
          if !ctx.contract.callingOk then
            say s!"refused: invalid custom calling convention (register out of range, duplicate, RSP/LINK, or return register preserved)\nin {name}\n.end\n"; return 0
          if !ctx.contract.stackBitsOk then
            say s!"refused: stack bits argument must be a parameter listed in `trace depends on` with a positive divisor\nin {name}\n.end\n"; return 0
          if !ctx.contract.decreasesOk then
            say s!"refused: `decreases` argument must be a parameter listed in `trace depends on`\nin {name}\n.end\n"; return 0
          if hasSelect ctx.code && !ctx.contract.traceExprs.isEmpty then
            say s!"refused: conditional select cannot be combined with computed `trace depends on` values\nin {name}\n.end\n"; return 0
          targetCtx := some { ctx with advice := adviceFor ctx }
          targetFn := some f
          foundTarget := true
        else
          if !onlyTarget then
            match verdict ctx f.proof with
            | some why => say s!"{why}\nin {f.name}\n.end\n"; return 0
            | none => pure ()
          if fnRunsCapable f then runsOk := f.name :: runsOk
          done := (f.name, f.contract) :: done

    let some ctx := targetCtx | return 2
    let some tf := targetFn | return 2
    let doneAfter := (tf.name, tf.contract) :: done
    let runsAfter := if fnRunsCapable tf then tf.name :: runsOk else runsOk

    let s0 := entrySym ctx
    let initState : DriverState := { next := 0, jdone := [], stack := [.instr PATH s0 [] [] s0 0, .checkFinished] }
    let mut items : Array Item := tf.proof.toArray
    let mut ckpts : Array DriverState := #[initState]
    let mut batches : Array (Nat × Nat) := #[]

    let evalCurrent (curItems : Array Item) (curCkpts : Array DriverState) : (String × Bool × Array DriverState) :=
      let (res, ckpts') := advance ctx curItems curCkpts withPc
      match res with
      | .error why => (s!"{why}\nin {name}", true, ckpts')
      | .ok () =>
        let restMsg :=
          let raw := finishRest ctx curItems afterFns doneAfter runsAfter onlyTarget
          if raw.endsWith "\nin " then s!"{raw}{name}" else raw
        (restMsg, false, ckpts')

    let (firstMsg, firstMore, ckpts0) := evalCurrent items ckpts
    ckpts := ckpts0
    say (firstMsg ++ "\n" ++ (if firstMore then ".more\n" else ".end\n"))
    if !firstMore then return 0

    let stdin ← IO.getStdin
    while true do
      let line ← stdin.getLine
      if line.isEmpty then break
      let command := line.replace "\n" ""
      match (command.splitOn " ").filter (· ≠ "") with
      | ["lines", count] =>
        let mut ls : List String := []
        for _ in [0:count.toNat!] do
          ls := ls ++ [(← stdin.getLine).replace "\n" ""]
        match parseBatch ls with
        | .error why => say s!"{why}\n.end\n"
        | .ok [] => say "refused: no line of a proof among those given\n.end\n"
        | .ok newItems =>
          let prevItemsLen := items.size
          let prevCkptsLen := ckpts.size
          let items' := items ++ newItems.toArray
          let (msg, more, ckpts') := evalCurrent items' ckpts
          if more then
            batches := batches.push (prevItemsLen, prevCkptsLen)
            items := items'
            ckpts := ckpts'
            say (msg ++ "\n.more\n")
          else
            -- Do not retain this batch when `.end` is reported (`session.py` does not push it).
            say (msg ++ "\n.end\n")
      | ["back"] =>
        if h : 0 < batches.size then
          let (prevItemsLen, prevCkptsLen) := batches[batches.size - 1]
          batches := batches.pop
          items := items.shrink prevItemsLen
          ckpts := ckpts.shrink prevCkptsLen
        say ".back\n"
      | _ => break
    return 0
  | _ => say "odeprove TABLE STATEMENT HEAD NAME | odeprove --locate TABLE STATEMENT PROOF\n.end\n"; return 2
