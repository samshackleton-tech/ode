import Core
/-!
Advice for a PROVER's helper. Nobody relies on this file, and `odeverify` is built without it.

Before an `ensures` of a run of words, and before a call, the proof file may give rows for the verifier
to show from the facts and then keep among them (`know` items; `symKnow` in Core.lean). Which rows are
worth giving is found here, for `odeprove` to print where a proof that is still being written has run
out at such a point (`need know`): the prover then tries to show one of them.

- Before an `ensures` of a run of words: the first comparison of two numbers that stops the working out
  of the specification's words, because no one fact says how the two compare (`wask`, which goes the way
  `weval` goes). Two rows are proposed: the first number is below the second, or it is not.
- Before a call: the bounds of the parts of runs handed over that the call's rules will look for among
  the facts and that no one fact says (`callNeeds`).
-/
namespace Ode
open Arithmetic (Row Step)

/-- Among numbers gone through in order, of each of which something is worked out: where it is not
followed of one of them (and, with `first`, was not followed and true of one before): that number; or,
with `middle`, the middle one of the run of numbers from there on of which it is not followed.
(Where the thing is a comparison that turns once along the numbers, as `1024 * k < len` does along the
powers of two, a row about the middle one says it of half the run at once: six rows for sixty-four
powers. Where it does not turn once, the row about the middle one may be one that cannot be shown,
though a search from the first would have ended before it: the prover then finds no proof.) -/
def askAt (first middle : Bool) (followed : Int → Option WVal) (l : List Int) : Option Int :=
  let rest := l.dropWhile fun n =>
    match followed n with
    | some (.bool true) => !first
    | some _ => true
    | none => false
  match rest with
  | [] => none
  | n :: more =>
    if (followed n).isSome then none
    else if !middle then some n
    else
      let run := n :: more.takeWhile fun m => (followed m).isNone
      run[run.length / 2]?

mutual
  /-- Where `weval` does not follow the expression because two numbers are compared (or one taken from
  the other, or a part of a run of bytes is to end within it) and the facts do not say at once how they
  compare: those two numbers, the first such in `weval`'s order. -/
  def wask (ctx : Ctx) (look : Node → Option Nat) (s : Sym) : Nat → List (String × WVal) → SExpr → Option (Row × Row)
    | 0, _, _ => none
    | fuel + 1, env, e =>
      if (weval ctx look s (fuel + 1) env e).isSome then none
      else
        match e with
        | .bin op a b =>
          match weval ctx look s fuel env a, weval ctx look s fuel env b with
          | some x, some y =>
            let pair := fun (p q : Row) =>
              -- (only where `wnum` turns on how the two compare)
              if !(op == "-" || op == "==" || op == "<" || op == ">=" || op == "<=" || op == ">") then none
              -- `==`, where the first is known to be no less than the second: is the second below the first?
              else if op == "==" && plain s.facts (Lin.sub p q) then some (q, p)
              else if op == "<=" || op == ">" then some (q, p)
              else some (p, q)
            (match x, y with
             | .num p, .num q => pair p q
             | .num p, .int m => pair p (Lin.const m)
             | .int m, .num q => pair (Lin.const m) q
             | _, _ => none)
          | none, _ => wask ctx look s fuel env a
          | some _, none => wask ctx look s fuel env b
        | .ifx c a b =>
          match weval ctx look s fuel env c with
          | some (.bool true) => wask ctx look s fuel env a
          | some (.bool false) => wask ctx look s fuel env b
          | some _ => none
          | none => wask ctx look s fuel env c
        | .index a i => (wask ctx look s fuel env a).orElse fun _ => wask ctx look s fuel env i
        | .call f args =>
          match wevalList (weval ctx look s fuel env) args with
          | none => waskList ctx look s fuel env args
          | some vs =>
            if f == "len" || own.contains f then none
            else
              match findDef ctx.defs f with
              | some d => if d.params.length == vs.length then wask ctx look s fuel (d.params.zip vs) d.body else none
              | none => none
        | .list items => waskList ctx look s fuel env items
        | .letx x e1 rest =>
          match weval ctx look s fuel env e1 with
          | some v => wask ctx look s fuel ((x, v) :: env) rest
          | none => wask ctx look s fuel env e1
        | .each e1 x a b =>
          match weval ctx look s fuel env a, weval ctx look s fuel env b with
          | some (.int lo), some (.int hi) =>
            match askAt false false (fun n => weval ctx look s fuel ((x, .int n) :: env) e1) ((List.range (hi - lo).toNat).map fun (k : Nat) => lo + (k : Int)) with
            | some n => wask ctx look s fuel ((x, .int n) :: env) e1
            | none => none
          | none, _ => wask ctx look s fuel env a
          | _, _ => wask ctx look s fuel env b
        | .withx a puts => (wask ctx look s fuel env a).orElse fun _ => waskList ctx look s fuel env puts
        | .slice a lo hi =>
          match weval ctx look s fuel env a, weval ctx look s fuel env lo, weval ctx look s fuel env hi with
          | some (.region _ l), some (.int i), some (.int j) =>
            if 0 ≤ i ∧ i ≤ j then some (Lin.var l, Lin.const j) else none        -- is the run shorter than the part's end?
          | some (.region _ l), some (.int i), some (.num j) =>
            if 0 ≤ i then (if plain s.facts (Lin.sub j (Lin.const i)) then some (Lin.var l, j) else some (j, Lin.const i)) else none
          | none, _, _ => wask ctx look s fuel env a
          | some _, none, _ => wask ctx look s fuel env lo
          | some _, some _, none => wask ctx look s fuel env hi
          | _, _, _ => none
        | .record _ items => waskList ctx look s fuel env items
        | .field e1 _ => wask ctx look s fuel env e1
        | .theNumber greatest x a b cond =>
          match weval ctx look s fuel env a, weval ctx look s fuel env b with
          | some (.int lo), some (.int hi) =>
            let among := (List.range (hi - lo).toNat).map fun (k : Nat) => lo + (k : Int)
            match askAt true false (fun n => weval ctx look s fuel ((x, .int n) :: env) cond) (if greatest then among.reverse else among) with
            | some n => wask ctx look s fuel ((x, .int n) :: env) cond
            | none => none
          | none, _ => wask ctx look s fuel env a
          | _, _ => wask ctx look s fuel env b
        | .thePower greatest x cond =>
          let among := (List.range 64).map fun (k : Nat) => (2 : Int) ^ k
          match askAt true true (fun n => weval ctx look s fuel ((x, .int n) :: env) cond) (if greatest then among.reverse else among) with
          | some n => wask ctx look s fuel ((x, .int n) :: env) cond
          | none => none
        | _ => none
  /-- The first of the things of a list that `weval` does not follow: what is proposed there. -/
  def waskList (ctx : Ctx) (look : Node → Option Nat) (s : Sym) : Nat → List (String × WVal) → SExpr → Option (Row × Row)
    | fuel, env, .cons a rest =>
      if (weval ctx look s fuel env a).isSome then waskList ctx look s fuel env rest else wask ctx look s fuel env a
    | _, _, _ => none
end

/-- Before an `ensures` of a run of words: where a comparison stops the working out of the
specification's words, the two rows of which one is to be shown: the first number is below the second;
or it is not. (None where a number speaks of an unknown that is not in use.) -/
def ensureRows (ctx : Ctx) (s : Sym) (e : EnsureW) : List Row :=
  match e.value with
  | .call _ (.cons x .nil) =>
    match wask ctx s.tab.find s WFUEL (wenv ctx.contract) x with
    | some (a, b) =>
      if a.coeff.length ≤ s.nvars ∧ b.coeff.length ≤ s.nvars then [Lin.sub (Lin.sub b a) (Lin.const 1), Lin.sub a b] else []
    | none => []
  | _ => []

/-- The rows a call's rules look for among the facts: that each part of a run of bytes with a length
that the called function is given ends within the run, and does not begin before it. -/
def callNeeds (ctx : Ctx) (s : Sym) (c : Contract) : List (String × Kind) → List Nat → List Row
  | (_, .fixed n) :: args, r :: regs =>
    (match findOut (s.reg r) ctx.contract.fixeds 0 with
     | some _ => []
     | none =>
       match findRegion (s.reg r) ctx.contract.regions 0 with
       | some (.region k off) =>
         match Lin.isConst off, ctx.contract.regions[k]? with
         | some c0, some (_, l) => [Lin.sub (Lin.var l) (Lin.const (c0 + n))]
         | _, _ => []
       | _ => []) ++ callNeeds ctx s c args regs
  | (_, .bytes len) :: args, r :: regs =>
    (match c.regOf len with
     | some l =>
       match findRegion (s.reg r) ctx.contract.regions 0 with
       | some (.region k off) =>
         match ctx.contract.regions[k]? with
         | some (_, lb) => [off, Lin.sub (Lin.var lb) (Lin.add off (s.reg l))]
         | none => []
       | _ => []
     | none => []) ++ callNeeds ctx s c args regs
  | _ :: args, _ :: regs => callNeeds ctx s c args regs
  | _, _ => []

/-- Before a call: the rows its rules will look for that no one fact says (region bounds, lane region bounds,
and conditional `needsIf` equalities). -/
def laneRegionNeeds (ctx : Ctx) (s : Sym) (ct : Int) (nb : Nat) : Nat → Nat → List Row
  | 0, _ => []
  | count + 1, i =>
    (match s.frame.find? (fun cell => cell.1 == ct + 8 * (i : Int)) with
     | some (_, a) =>
       match findRegion a ctx.contract.regions 0 with
       | some (.region k off) =>
         match Lin.isConst off, ctx.contract.regions[k]? with
         | some c0, some (_, l) => [Lin.sub (Lin.var l) (Lin.const (c0 + 64 * (nb : Int)))]
         | _, _ => []
       | _ => []
     | none => []) ++ laneRegionNeeds ctx s ct nb count (i + 1)

def callRows (ctx : Ctx) (s : Sym) (c : Contract) : List Row :=
  let laneRows := match c.tables with
    | [(_, tr, count, l)] =>
      match Lin.isConst (s.reg l), frameAt s tr with
      | some nb, some ct => if 0 ≤ nb then laneRegionNeeds ctx s ct nb.toNat count 0 else []
      | _, _ => []
    | _ => []
  let needRows := (c.needs.map fun what =>
    if ctx.contract.needs.contains what then []
    else (ctx.contract.needsIf.filter fun x => x.1 == what).flatMap fun (_, arg0, k0) =>
      match ctx.contract.regOf arg0 with
      | some r0 => [Lin.sub (Lin.var r0) (Lin.const k0), Lin.sub (Lin.const k0) (Lin.var r0)]
      | none => []).flatten
  (callNeeds ctx s c c.args c.argRegs ++ laneRows ++ needRows).filter fun g =>
    decide (g.coeff.length ≤ s.nvars) && !plain s.facts g

/-- True if specification expression `e` invokes definition `fnName`. -/
def exprCallsFn (fnName : String) : SExpr → Bool
  | .num _ | .name _ | .nil => false
  | .bin _ a b => exprCallsFn fnName a || exprCallsFn fnName b
  | .ifx c a b => exprCallsFn fnName c || exprCallsFn fnName a || exprCallsFn fnName b
  | .index a i => exprCallsFn fnName a || exprCallsFn fnName i
  | .call f args => f == fnName || exprCallsFn fnName args
  | .list xs => exprCallsFn fnName xs
  | .cons a rest => exprCallsFn fnName a || exprCallsFn fnName rest
  | .letx _ e rest => exprCallsFn fnName e || exprCallsFn fnName rest
  | .each e _ a b => exprCallsFn fnName e || exprCallsFn fnName a || exprCallsFn fnName b
  | .slice a lo hi => exprCallsFn fnName a || exprCallsFn fnName lo || exprCallsFn fnName hi
  | .withx a puts => exprCallsFn fnName a || exprCallsFn fnName puts
  | .record _ items => exprCallsFn fnName items
  | .field e _ => exprCallsFn fnName e
  | .theNumber _ _ a b cond => exprCallsFn fnName a || exprCallsFn fnName b || exprCallsFn fnName cond
  | .thePower _ _ cond => exprCallsFn fnName cond

/-- Structural call-graph metadata emitted by `odeprove` on `need spec` so `prove.py` can prioritize
frontier calls in the goal's connected component and report exact specification names on refusal.
Never called by `odeverify` (Bob's reliance set is unchanged). -/
def specMetaFor (ctx : Ctx) (s : Sym) (goal : SFact) (calls : List SCall) : String :=
  let goalComp := reach s.spec (s.spec.length + 1) (callsIn goal)
  let idxOf (c : SCall) : Int :=
    match calls.zipIdx.find? (fun (c', _) => c' == c) with
    | some (_, i) => i
    | none => -1
  let goalLine := match goal with
    | .value c _ => s!"m goal value {c.f} {idxOf c}\n"
    | .same a b => s!"m goal same {a.f} {idxOf a} {b.f} {idxOf b}\n"
    | .neq _ => ""
  let callLines := calls.zipIdx.map fun (c, idx) =>
    let inGoal := if goalComp.contains c then 1 else 0
    let hasVal := if s.spec.any (fun | .value c' _ => c' == c | _ => false) then 1 else 0
    let deg := s.spec.foldl (fun acc f => match f with
      | .same a b => acc + (if a == c || b == c then 1 else 0)
      | _ => acc) 0
    let isRec := match findDef ctx.defs c.f with
      | some d => if exprCallsFn c.f d.body then 1 else 0
      | none => 0
    s!"d {idx} {c.f} {inGoal} {hasVal} {deg} {isRec}\n"
  goalLine ++ String.join callLines

/-- The advice `odeprove` gives the verifier's rules to print. -/
def adviceFor (ctx : Ctx) : Advice :=
  { ensures := ensureRows ctx, call := callRows ctx,
    sameByte := fun s r o =>
      !o.coeff.isEmpty && s.bytes.any fun (_, r', o') =>
        r' == r && !o'.coeff.isEmpty && !Lin.sameCoeff o.coeff o'.coeff,
    specMeta := specMetaFor ctx }

private def tagPc (pc : Nat) (m : V α) : V α := fun st =>
  match m st with
  | .ok v => .ok v
  | .error why =>
    if why.startsWith "at +" then .error why
    else .error s!"at +{pc}\n{why}"

/-- Mirror of `Core.onward` that records the exact `pc` of any refusal and reports a loop with no `place`
as soon as a path returns to an instruction it already visited without passing a `place`.
`visited` records `(pc, liveCountAtEntry)` along the current active path so completed sibling
branches never count toward a later loop's budget. -/
def onwardAt (ctx : Ctx) (livePrefix : Array Nat) (base : Sym) (seen : List Seen) (jstack : List Nat)
    (visited : List (Nat × Nat))
    (go : Sym → List Seen → List Nat → List JoinEntry → List (Nat × Nat) → Sym → Nat → V (List JoinEntry))
    (jdone : List JoinEntry) (next : Sym × Next) : V (List JoinEntry) :=
  match next.2 with
  | .returned => pure jdone
  | .at pc' =>
    match ctx.places.find? (fun p => p.pc == pc') with
    | none => fun st =>
      let curLives := livePrefix.getD st.next (livePrefix.getD (livePrefix.size - 1) 0)
      let hits := visited.filter (·.1 == pc')
      let vc := hits.length
      let firstLives := match hits.getLast? with | some (_, l) => l | none => curLives
      let loopLives := curLives - firstLives
      if vc ≥ 65 ∨ (vc ≥ 4 ∧ loopLives ≥ 150) then
        .error s!"at +{pc'}\nrefused: path returned to +{pc'} with no place"
      else go base seen jstack jdone ((pc', curLives) :: visited) next.1 pc' st
    | some p =>
      if p.isJoin then
        if jstack.contains pc' then
          tagPc pc' (refuse s!"at the join place {pc'} a path returns to it (add `decreases` for a loop)")
        else
          match jdone.find? (fun e => e.place.pc == pc') with
          | some e => do tagPc pc' (arriveJoin ctx e.place e.first next.1); pure jdone
          | none =>
            match joinFirst ctx base next.1 p with
            | none =>
              match p.keep.find? fun r => !(decide (r < ctx.nreg) && decide ((next.1.reg r).coeff.length ≤ base.nvars)) with
              | some r => tagPc pc' (refuse s!"at the join place {pc'} register {r} depends on a value not in scope")
              | none => tagPc pc' (refuse s!"at the join place {pc'} a kept register depends on a value not in scope")
            | some first => do
              tagPc pc' (arriveJoin ctx p first next.1)
              let g ← tagPc pc' (generalizeJoin ctx p first)
              let jdone' ← go base seen (pc' :: jstack) jdone [(pc', 0)] { g with q := { regq := first.q.regq, fq := first.q.fq } } pc'
              pure (⟨p, first⟩ :: jdone')
      else
        match seen.find? (fun e => e.place.pc == pc') with
        | some e => do tagPc pc' (arrive ctx e.place e.first e.d next.1); pure jdone
        | none => do
          let (g, d, first) ← tagPc pc' (generalize ctx p next.1)
          let q0 : SMarks := { regq := placeQuiet ctx p next.1.q.regq, fq := next.1.q.fq }
          let g' := { g with q := q0 }
          let _ ← go g' (⟨p, d, { first with q := q0 }⟩ :: seen)
                       [] [] [(pc', 0)] g' pc'
          pure jdone

def exploreAt (ctx : Ctx) (livePrefix : Array Nat) : Nat → Sym → List Seen → List Nat → List JoinEntry → List (Nat × Nat) → Sym → Nat → V (List JoinEntry)
  | 0, _, _, _, _, _, _, pc => fun _ => .error s!"at +{pc}\nrefused: a path longer than the verifier goes"
  | fuel + 1, base, seen, jstack, jdone, visited, s, pc =>
    match ctx.code.lookup pc with
    | none => fun _ => .error s!"at +{pc}\nrefused: no instruction at {pc}"
    | some i => do
      let s ← tagPc pc (symClears ctx pc CLEARS s)
      let nexts ← tagPc pc (symNext ctx s i)
      eachState (onwardAt ctx livePrefix base seen jstack visited (exploreAt ctx livePrefix fuel)) jdone nexts

/-- Diagnostic run of `verify` on one function: `none` if shown, else `at +PC\nWHY`. -/
def locateRefusal (ctx : Ctx) (proof : List Item) : Option String :=
  let livePrefix := Id.run do
    let mut arr := Array.mkEmpty (proof.length + 1)
    let mut acc : Nat := 0
    arr := arr.push 0
    for it in proof do
      if let .tag "live" _ := it then acc := acc + 1
      arr := arr.push acc
    pure arr
  let run (c : Ctx) : Option String :=
    let s0 := entrySym c
    let act : V Unit := do
      let _ ← exploreAt c livePrefix PATH s0 [] [] [] [(0, 0)] s0 0
      if ← finished then pure () else refuse "the proof says more than is asked of it"
    match act (Items.ofList proof) with
    | .ok _ => none
    | .error why => some why
  match run ctx with
  | some why => some why
  | none =>
    match ctx.contract.resultHidden with
    | none => none
    | some rh =>
      if !rh.all ctx.contract.hidden.contains then
        some "at +0\nrefused: result depends on: arguments kept out of the result must be a subset of those kept out of the trace"
      else
        run { ctx with contract := ctx.contract.forResult rh, resultPass := true }

end Ode
