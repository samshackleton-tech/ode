/-
The marks change no value, and nothing need be forbidden.

`State.plain` is a state with its marks erased. The plain machine (`execP`) is the machine of Machine.lean
without marks: it sets no mark, reads none, and never stops for one. Here:

- what the machine with marks does, the plain machine does on the plain states (`runs_plain`);
- what the machine does where it may touch only some memory, it does where it may touch all of it
  (`exec_all`), so a run that touches only what it is let is a run of the plain machine on which nothing
  is forbidden (`runs_free`);
- two runs of that machine, from two states alike in everything not marked, from each of which the machine
  with marks runs the function without stopping, let the same things be observed (`runs_trace`).
-/
import Trace

namespace Ode

/-- The state with no mark. -/
def State.plain (s : State) : State := { s with marks := {} }

mutual
  theorem value_plain (perm : Perm) (bind : Bind) (s : State) : ∀ (e : Expr), value perm bind s.plain e = value perm bind s e
    | .number _ => rfl
    | .lane _ _ => rfl
    | .name _ => rfl
    | .call f args => by
      simp only [value, values_plain perm bind s args]
      rfl
  theorem values_plain (perm : Perm) (bind : Bind) (s : State) : ∀ (es : List Expr), values perm bind s.plain es = values perm bind s es
    | [] => rfl
    | e :: es => by simp only [values, value_plain perm bind s e, values_plain perm bind s es]
end

theorem vecArg_plain (bind : Bind) (s : State) (e : Expr) : vecArg bind s.plain e = vecArg bind s e := by
  cases e <;> rfl

theorem laneArg_plain (bind : Bind) (s : State) : laneArg bind s.plain = laneArg bind s := by
  funext e; cases e <;> rfl

theorem vecArg512_plain (bind : Bind) (s : State) (e : Expr) : vecArg512 bind s.plain e = vecArg512 bind s e := by
  cases e <;> rfl

theorem addr512_plain (perm : Perm) (bind : Bind) (s : State) (f : String) (args : List Expr) :
    addr512 perm bind s.plain f args = addr512 perm bind s f args := by
  simp only [addr512, values_plain]

theorem lanesOf_plain (perm : Perm) (bind : Bind) (s : State) (e : Expr) : lanesOf perm bind s.plain e = lanesOf perm bind s e := by
  cases e with
  | number _ => rfl
  | lane _ _ => rfl
  | name n => exact vecArg_plain bind s (.name n)
  | call f args =>
    simp only [lanesOf, values_plain, value_plain, vecArg_plain, laneArg_plain]
    rfl

theorem memLanes512_plain (perm : Perm) (bind : Bind) (s : State) (f : String) (args : List Expr) :
    memLanes512 perm bind s.plain f args = memLanes512 perm bind s f args := by
  simp only [memLanes512, addr512_plain]
  rfl

theorem lanesOf512_plain (perm : Perm) (bind : Bind) (s : State) (e : Expr) : lanesOf512 perm bind s.plain e = lanesOf512 perm bind s e := by
  cases e with
  | number _ => rfl
  | lane _ _ => rfl
  | name n => exact vecArg512_plain bind s (.name n)
  | call f args =>
    simp only [lanesOf512, memLanes512_plain, value_plain, vecArg512_plain]

theorem execVec512_plain (perm : Perm) (bind : Bind) (s : State) (place v : Expr) :
    execVec512 perm bind s.plain place v = (execVec512 perm bind s place v).map State.plain := by
  simp only [execVec512, lanesOf512_plain, addr512_plain]
  cases lanesOf512 perm bind s v with
  | none => rfl
  | some lanes =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · rfl
    · cases place with
      | name n => simp only; cases vecOf512 bind n <;> rfl
      | call f args =>
        simp only
        cases addr512 perm bind s f args with
        | none => rfl
        | some a => simp only [Option.bind_some]; split <;> rfl
      | number _ => rfl
      | lane _ _ => rfl

/-- A statement does to the values of a plain state what it does to the values of the state with marks. -/
theorem execStmt_plain (perm : Perm) (bind : Bind) (base u : Nat) (s : State) (st : Stmt) :
    execStmt perm bind base u s.plain st = (execStmt perm bind base u s st).map State.plain := by
  cases st with
  | nothing => rfl
  | ret => rfl
  | call _ => rfl
  | retLink _ => rfl
  | callLink _ _ => rfl
  | vset512 place v => exact execVec512_plain perm bind s place v
  | jump target cond =>
    have hv := value_plain perm bind s target
    cases cond with
    | none =>
      show (value perm bind s.plain target).map _ = ((value perm bind s target).map _).map State.plain
      rw [hv]; cases value perm bind s target <;> rfl
    | some fw =>
      obtain ⟨flag, want⟩ := fw
      show (if (condFlag s.plain flag == want) = true then (value perm bind s.plain target).map _ else some s.plain)
        = (if (condFlag s flag == want) = true then (value perm bind s target).map _ else some s).map State.plain
      have hcf : condFlag s.plain flag = condFlag s flag := by unfold condFlag; rfl
      rw [hv, hcf]
      generalize (condFlag s flag == want) = c
      cases c
      · rfl
      · cases value perm bind s target <;> rfl
  | set place v =>
    simp only [execStmt, value_plain, values_plain]
    cases (if isUnknown v = true then some u else value perm bind s v) with
    | none => rfl
    | some x =>
      cases place with
      | number _ => rfl
      | lane _ _ => rfl
      | name n =>
        simp only
        split
        · rfl
        · split
          · rfl
          · cases regOf bind n <;> rfl
      | call f args =>
        simp only
        cases memSize f with
        | none => rfl
        | some size =>
          cases values perm bind s args with
          | none => rfl
          | some vs => simp only; split <;> rfl
  | vset place v =>
    cases place with
    | number _ => rfl
    | lane _ _ => rfl
    | name n =>
      simp only [execStmt, lanesOf_plain]
      split
      · split <;> rfl
      · cases vecOf bind n with
        | none => rfl
        | some r => cases lanesOf perm bind s v <;> rfl
    | call f args =>
      simp only [execStmt, values_plain, vecArg_plain]
      cases values perm bind s args with
      | none => rfl
      | some vs =>
        cases vecArg bind s v with
        | none => rfl
        | some l => simp only; split <;> rfl

/-! ## What is observed reads no mark -/

theorem addrOf_plain (bind : Bind) (s : State) (args : List Expr) : addrOf bind s.plain args = addrOf bind s args := by
  simp only [addrOf, values_plain]

mutual
  theorem touched_plain (bind : Bind) (s : State) : ∀ (e : Expr), touched bind s.plain e = touched bind s e
    | .number _ => rfl
    | .lane _ _ => rfl
    | .name _ => rfl
    | .call f args => by simp only [touched, touchedAll_plain bind s args, addrOf_plain]
  theorem touchedAll_plain (bind : Bind) (s : State) : ∀ (es : List Expr), touchedAll bind s.plain es = touchedAll bind s es
    | [] => rfl
    | e :: es => by simp only [touchedAll, touched_plain bind s e, touchedAll_plain bind s es]
end

theorem observed_plain (bind : Bind) (s : State) (st : Stmt) : observed bind s.plain st = observed bind s st := by
  simp only [observed, touched_plain, touchedAll_plain, addrOf_plain]

/-! ## The plain machine

The machine of Machine.lean with every word about marks left out: it sets none, reads none and never stops
for one. It keeps the trace. -/

/-- The state `s'` a statement gave from `s`, with the trace brought up to date. -/
def notedP (bind : Bind) (s : State) (st : Stmt) (s' : State) : State :=
  { s' with marks := {}, trace := s.trace ++ observed bind s st }

def execAllP (perm : Perm) (bind : Bind) (base : Nat) (u : Nat → Nat) : Nat → State → List Stmt → Option Outcome
  | _, s, [] => some (.next s)
  | _, s, .ret :: _ =>
    let sp := s.reg RSP
    if allowed perm.read sp 8 then some (.returned (setReg { s with rip := load s.mem sp 8, trace := s.trace ++ [(sp, 8)] } RSP (sp + 8))) else none
  | _, s, .retLink r :: _ => (regIndex r).map fun k => .returned { s with rip := s.reg k }
  | k, s, st :: rest =>
    match execStmt perm bind base (u k) s st with
    | some s' => execAllP perm bind base u (k + 1) (notedP bind s st s') rest
    | none => none

def execP (perm : Perm) (p : Program) (i : Instr) (u : Nat → Nat) (s : State) : Option Outcome :=
  execAllP perm i.bind p.base u 0 { s with rip := p.base + i.next, trace := s.trace ++ [(s.rip, 0)] } i.effect

/-- The state a called function starts in, on the plain machine: the address to come back to is written
just below the stack pointer, or put in a register, as the call instruction says. -/
def afterCallP (p q : Program) (i : Instr) (s : State) : State :=
  match callLink i with
  | none =>
    { reg := fun k => if k = RSP then s.reg RSP - 8 else s.reg k, zf := s.zf, cf := s.cf,
      mem := store s.mem (s.reg RSP - 8) (p.base + i.next) 8, rip := q.base, vec := s.vec, data := s.data,
      marks := {}, trace := s.trace ++ [(s.rip, 0), (s.reg RSP - 8, 8)] }
  | some l =>
    { reg := fun k => if k = l then (p.base + i.next) % M64 else s.reg k, zf := s.zf, cf := s.cf,
      mem := s.mem, rip := q.base, vec := s.vec, data := s.data,
      marks := {}, trace := s.trace ++ [(s.rip, 0)] }

/-- The plain machine's state after a call is the state of the machine with marks after it, without its marks. -/
theorem afterCallP_plain (p q : Program) (i : Instr) (s : State) : afterCallP p q i s.plain = (afterCall p q i s).plain := by
  cases hl : callLink i with
  | none => rw [afterCall_stack hl]; simp only [afterCallP, hl]; rfl
  | some l => rw [afterCall_link hl]; simp only [afterCallP, hl]; rfl

/-- `Runs` on the plain machine: no word about marks. -/
inductive RunsP (world : List Program) : Perm → Program → (State → Prop) → State → Prop where
  | step (perm : Perm) (p : Program) (Q : State → Prop) (s : State) (i : Instr) :
      p.fetch s.rip = some i →
      (∀ u, execP perm p i u s ≠ none) →
      (∀ u s', execP perm p i u s = some (.next s') → RunsP world perm p Q s') →
      (∀ u s', execP perm p i u s = some (.returned s') → Q s') →
      RunsP world perm p Q s
  | call (perm : Perm) (p : Program) (Q : State → Prop) (s : State) (i : Instr)
      (name : String) (q : Program) (inner : Perm) (R : State → Prop) :
      p.fetch s.rip = some i → callTarget i = some name → findProgram world name = some q →
      (callLink i = none → 8 ≤ s.reg RSP ∧ allowed perm.write (s.reg RSP - 8) 8 = true) →
      (∀ a, inner.read a = true → perm.read a = true) → (∀ a, inner.write a = true → perm.write a = true) →
      RunsP world inner q R (afterCallP p q i s) →
      (∀ s', R s' → ∀ r ∈ keptAt i, s'.reg r = s.reg r) →
      (∀ s', R s' → RunsP world perm p Q s') →
      RunsP world perm p Q s
  | tail (perm : Perm) (p : Program) (Q : State → Prop) (s : State) (i : Instr)
      (name : String) (q : Program) (inner : Perm) :
      p.fetch s.rip = some i → tailTarget i = some name → findProgram world name = some q →
      (∀ a, inner.read a = true → perm.read a = true) → (∀ a, inner.write a = true → perm.write a = true) →
      RunsP world inner q Q (afterTail q s) →
      RunsP world perm p Q s

def Outcome.plain : Outcome → Outcome
  | .next s => .next s.plain
  | .returned s => .returned s.plain

theorem execAll_plain {perm : Perm} {bind : Bind} {base : Nat} {u : Nat → Nat} :
    ∀ (stmts : List Stmt) (k : Nat) (s : State),
    execAllP perm bind base u k s.plain stmts = (execAll perm bind base u k s stmts).map Outcome.plain
  | [], _, _ => rfl
  | st :: rest, k, s => by
    have go : st ≠ .ret → (∀ r, st ≠ .retLink r) → execAllP perm bind base u k s.plain (st :: rest) =
        (match execStmt perm bind base (u k) s st with
          | some s' => execAll perm bind base u (k + 1) (noted bind s st s') rest
          | none => none).map Outcome.plain := by
      intro hr hl
      have e := execStmt_plain perm bind base (u k) s st
      cases h : execStmt perm bind base (u k) s st with
      | none =>
        rw [h] at e
        cases st <;> first | exact absurd rfl hr | exact absurd rfl (hl _) | rfl | (simp only [execAllP, e]; rfl)
      | some s' =>
        rw [h] at e
        have r := execAll_plain (perm := perm) (bind := bind) (base := base) (u := u) rest (k + 1) (noted bind s st s')
        have n : notedP bind s.plain st s'.plain = (noted bind s st s').plain := by
          have o := observed_plain bind s st
          simp only [notedP, noted]
          rw [o]; rfl
        cases st <;> first | (cases h; done) | (simp only [execAllP, e, Option.map_some]; rw [n]; exact r)
    cases st with
    | ret =>
      show (if allowed perm.read (s.reg RSP) 8 = true then _ else _) = Option.map _ (if allowed perm.read (s.reg RSP) 8 = true then _ else _)
      split <;> rfl
    | retLink r =>
      simp only [execAllP, execAll]
      cases regIndex r <;> rfl
    | callLink _ _ => exact go (by intro x; cases x) (by intro r x; cases x)
    | nothing => exact go (by intro x; cases x) (by intro r x; cases x)
    | call _ => exact go (by intro x; cases x) (by intro r x; cases x)
    | jump _ _ => exact go (by intro x; cases x) (by intro r x; cases x)
    | set _ _ => exact go (by intro x; cases x) (by intro r x; cases x)
    | vset _ _ => exact go (by intro x; cases x) (by intro r x; cases x)
    | vset512 _ _ => exact go (by intro x; cases x) (by intro r x; cases x)

theorem exec_plain (perm : Perm) (p : Program) (i : Instr) (u : Nat → Nat) (s : State) :
    execP perm p i u s.plain = (exec perm p i u s).map Outcome.plain :=
  execAll_plain i.effect 0 { s with rip := p.base + i.next, trace := s.trace ++ [(s.rip, 0)] }

theorem outcome_next {o : Outcome} {t : State} (h : o.plain = .next t) : ∃ s', o = .next s' ∧ t = s'.plain := by
  cases o with
  | next s' => exact ⟨s', rfl, by cases h; rfl⟩
  | returned _ => cases h

theorem outcome_returned {o : Outcome} {t : State} (h : o.plain = .returned t) : ∃ s', o = .returned s' ∧ t = s'.plain := by
  cases o with
  | returned s' => exact ⟨s', rfl, by cases h; rfl⟩
  | next _ => cases h

/-- **The marks change no value.** A run of the machine with marks, to states of which `Q` holds, is a
run of the plain machine from the same state without its marks, to those states without theirs. -/
theorem runs_plain {world : List Program} {perm : Perm} {p : Program} {Q : State → Prop} {s : State}
    (h : Runs world perm p Q s) : RunsP world perm p (fun t => ∃ s', Q s' ∧ t = s'.plain) s.plain := by
  induction h with
  | step perm p Q s i hf hn _ hr ih =>
    have both : ∀ u, ∃ o, execQ perm p i u s = some o ∧ execP perm p i u s.plain = some o.plain := by
      intro u
      cases e : execQ perm p i u s with
      | none => exact absurd e (hn u)
      | some o => exact ⟨o, rfl, by rw [exec_plain, execQ_exec e]; rfl⟩
    refine RunsP.step perm p _ s.plain i hf ?_ ?_ ?_
    · intro u e
      obtain ⟨o, _, e'⟩ := both u
      rw [e] at e'; cases e'
    · intro u t e
      obtain ⟨o, eq, e'⟩ := both u
      rw [e] at e'
      obtain ⟨s', rfl, rfl⟩ := outcome_next (Option.some.inj e').symm
      exact ih u s' eq
    · intro u t e
      obtain ⟨o, eq, e'⟩ := both u
      rw [e] at e'
      obtain ⟨s', rfl, rfl⟩ := outcome_returned (Option.some.inj e').symm
      exact ⟨s', hr u s' eq, rfl⟩
  | call perm p Q s i name q inner R hf hc hw hstack hir hiw _ hk _ ihq ihp =>
    rw [← afterCallP_plain] at ihq
    refine RunsP.call perm p _ s.plain i name q inner _ hf hc hw (fun hl => ⟨(hstack hl).1, (hstack hl).2.1⟩) hir hiw ihq ?_ ?_
    · rintro t ⟨s', hs', rfl⟩ r hr
      exact hk s' hs' r hr
    · rintro t ⟨s', hs', rfl⟩
      exact ihp s' hs'
  | tail perm p Q s i name q inner hf ht hw hir hiw _ ihq =>
    exact RunsP.tail perm p _ s.plain i name q inner hf ht hw hir hiw ihq


/-! ## Nothing forbidden

What a statement does where only some memory may be touched, it does where all of it may. So a run that
touches only what it is let is a run of the machine on which nothing is forbidden. -/

theorem lanesOf_all {perm : Perm} {bind : Bind} {s : State} : ∀ (e : Expr) {l : List Nat},
    lanesOf perm bind s e = some l → lanesOf Perm.all bind s e = some l
  | .name _, _, h => h
  | .number _, _, h => h
  | .lane _ _, _, h => h
  | .call f args, l, h => by
    simp only [lanesOf] at h ⊢
    by_cases h1 : (f == "mem128") = true
    · rw [if_pos h1] at h ⊢
      cases hv : values perm bind s args with
      | none => rw [hv] at h; cases h
      | some vs =>
        rw [hv] at h; rw [values_all args hv]
        simp only at h ⊢
        split at h
        · rw [if_pos (allowed_all _ _).1]; exact h
        · cases h
    · rw [if_neg h1] at h ⊢
      by_cases h2 : (f == "words") = true
      · rw [if_pos h2] at h ⊢
        cases hv : values perm bind s args with
        | none => rw [hv] at h; cases h
        | some vs => rw [hv] at h; rw [values_all args hv]; exact h
      · rw [if_neg h2] at h ⊢
        by_cases h3 : (f == "lanes_of64") = true
        · rw [if_pos h3] at h ⊢
          cases hv : values perm bind s args with
          | none => rw [hv] at h; cases h
          | some vs => rw [hv] at h; rw [values_all args hv]; exact h
        · rw [if_neg h3] at h ⊢
          by_cases h4 : (f == "lanes") = true
          · rw [if_pos h4] at h ⊢; exact h
          · rw [if_neg h4] at h ⊢
            by_cases h5 : (f == "each32") = true
            · rw [if_pos h5] at h ⊢
              match args, h with
              | [.name op, a, b], h =>
                simp only at h ⊢
                cases hx : vecArg bind s a with
                | none => rw [hx] at h; cases h
                | some x =>
                  rw [hx] at h
                  simp only at h ⊢
                  cases hy : vecArg bind s b with
                  | some y => rw [hy] at h; exact h
                  | none =>
                    rw [hy] at h
                    simp only at h ⊢
                    cases hn : value perm bind s b with
                    | none => rw [hn] at h; cases h
                    | some n => rw [hn] at h; rw [value_all b hn]; exact h
            · rw [if_neg h5] at h ⊢
              match args, h with
              | [a, b], h => exact h
              | [a, b, i], h =>
                simp only at h ⊢
                by_cases hs : (f == "sha256su1" || f == "sha256rnds2" || f == "sha256h" || f == "sha256h2") = true
                · simp only [hs, ite_true] at h ⊢; exact h
                · simp only [hs, ite_false] at h ⊢
                  cases hi : value perm bind s i with
                  | none => rw [hi] at h; cases hx : vecArg bind s a <;> cases hy : vecArg bind s b <;> simp [hx, hy] at h
                  | some iv => rw [hi] at h; rw [value_all i hi]; exact h


theorem addr512_all {perm : Perm} {bind : Bind} {s : State} {f : String} {args : List Expr} {a : Nat}
    (h : addr512 perm bind s f args = some a) : addr512 Perm.all bind s f args = some a := by
  unfold addr512 at h ⊢
  cases hv : values perm bind s args with
  | none => rw [hv] at h; simp at h
  | some vs => rw [hv] at h; rw [values_all args hv]; exact h

theorem memLanes512_all {perm : Perm} {bind : Bind} {s : State} {f : String} {args : List Expr} {l : List Nat}
    (h : memLanes512 perm bind s f args = some l) : memLanes512 Perm.all bind s f args = some l := by
  unfold memLanes512 at h ⊢
  cases ha : addr512 perm bind s f args with
  | none => rw [ha] at h; simp at h
  | some a =>
    rw [ha] at h; rw [addr512_all ha]
    simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
    split at h
    · rw [if_pos (allowed_all _ _).1]; exact h
    · cases h

theorem lanesOf512_all {perm : Perm} {bind : Bind} {s : State} : ∀ (e : Expr) {l : List Nat},
    lanesOf512 perm bind s e = some l → lanesOf512 Perm.all bind s e = some l
  | .name _, _, h => h
  | .number _, _, h => h
  | .lane _ _, _, h => h
  | .call f args, l, h => by
    simp only [lanesOf512] at h ⊢
    by_cases h1 : (f == "mem512" || f == "mem512a") = true
    · rw [if_pos h1] at h ⊢; exact memLanes512_all h
    · rw [if_neg h1] at h ⊢
      split at h
      next a =>
        cases hv : value perm bind s a with
        | none => rw [hv] at h; simp at h
        | some v => rw [hv] at h; simp only [value_all a hv]; exact h
      next => exact h
      next op a b =>
        cases hx : vecArg512 bind s a with
        | none => rw [hx] at h; simp at h
        | some x =>
          rw [hx] at h
          simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
          cases hy : vecArg512 bind s b with
          | some y => rw [hy] at h; exact h
          | none =>
            rw [hy] at h
            simp only at h ⊢
            split at h
            next g margs =>
              split at h
              next hg =>
                rw [if_pos hg]
                cases hm : memLanes512 perm bind s g margs with
                | none => rw [hm] at h; simp at h
                | some y => rw [hm] at h; rw [memLanes512_all hm]; exact h
              next hg =>
                rw [if_neg hg]
                split at h
                next hw => rw [if_pos hw]; exact h
                next hw =>
                  rw [if_neg hw]
                  cases hn : value perm bind s (.call g margs) with
                  | none => rw [hn] at h; simp at h
                  | some n => rw [hn] at h; rw [value_all _ hn]; exact h
            next =>
              cases hn : value perm bind s b with
              | none => rw [hn] at h; simp at h
              | some n => rw [hn] at h; rw [value_all _ hn]; exact h
      next => exact h
      next a b i =>
        cases hx : vecArg512 bind s a with
        | none => rw [hx] at h; simp at h
        | some x =>
          rw [hx] at h
          cases hy : vecArg512 bind s b with
          | none => rw [hy] at h; simp at h
          | some y =>
            rw [hy] at h
            cases hi : value perm bind s i with
            | none => rw [hi] at h; simp at h
            | some iv => rw [hi] at h; rw [value_all i hi]; exact h
      next => exact h
      next => cases h

theorem execVec512_all {perm : Perm} {bind : Bind} {s s' : State} {place v : Expr}
    (h : execVec512 perm bind s place v = some s') : execVec512 Perm.all bind s place v = some s' := by
  unfold execVec512 at h ⊢
  cases hl : lanesOf512 perm bind s v with
  | none => rw [hl] at h; simp at h
  | some lanes =>
    rw [hl] at h; rw [lanesOf512_all v hl]
    simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
    split at h
    · cases h
    next hlen =>
      rw [if_neg hlen]
      cases place with
      | name n => exact h
      | number _ => exact h
      | lane _ _ => exact h
      | call f args =>
        simp only at h ⊢
        cases ha : addr512 perm bind s f args with
        | none => rw [ha] at h; simp at h
        | some a =>
          rw [ha] at h; rw [addr512_all ha]
          simp only [Option.bind_some] at h ⊢
          split at h
          · rw [if_pos (allowed_all _ _).2]; exact h
          · cases h

theorem execStmt_all {perm : Perm} {bind : Bind} {base u : Nat} {s : State} : ∀ (st : Stmt) {s' : State},
    execStmt perm bind base u s st = some s' → execStmt Perm.all bind base u s st = some s'
  | .nothing, _, h => h
  | .ret, _, h => h
  | .call _, _, h => h
  | .retLink _, _, h => h
  | .callLink _ _, _, h => h
  | .vset512 _ _, _, h => execVec512_all h
  | .jump target cond, s', h => by
    have hv : ∀ {r : State}, (value perm bind s target).map (fun t => { s with rip := base + t }) = some r →
        (value Perm.all bind s target).map (fun t => { s with rip := base + t }) = some r := by
      intro r hr
      cases hv : value perm bind s target with
      | none => rw [hv] at hr; simp at hr
      | some x => rw [hv] at hr; rw [value_all target hv]; exact hr
    cases cond with
    | none =>
      simp only [execStmt] at h ⊢
      exact hv h
    | some fw =>
      obtain ⟨flag, want⟩ := fw
      simp only [execStmt] at h ⊢
      by_cases ht : (condFlag s flag == want) = true
      · rw [if_pos ht] at h ⊢; exact hv h
      · rw [if_neg ht] at h ⊢; exact h
  | .set place v, s', h => by
    simp only [execStmt] at h ⊢
    have hx : ∀ x, (if isUnknown v = true then some u else value perm bind s v) = some x →
        (if isUnknown v = true then some u else value Perm.all bind s v) = some x := by
      intro x hx
      split at hx
      next hu => rw [if_pos hu]; exact hx
      next hu => rw [if_neg hu]; exact value_all v hx
    cases hc : (if isUnknown v = true then some u else value perm bind s v) with
    | none => rw [hc] at h; simp at h
    | some x =>
      rw [hc] at h; rw [hx x hc]
      cases place with
      | name n => exact h
      | number _ => exact h
      | lane _ _ => exact h
      | call f args =>
        simp only at h ⊢
        cases hm : memSize f with
        | none => rw [hm] at h; simp at h
        | some size =>
          rw [hm] at h
          cases hv : values perm bind s args with
          | none => rw [hv] at h; simp at h
          | some vs =>
            rw [hv] at h; rw [values_all args hv]
            simp only at h ⊢
            split at h
            · rw [if_pos (allowed_all _ _).2]; exact h
            · cases h
  | .vset place v, s', h => by
    cases place with
    | number _ => exact h
    | lane _ _ => exact h
    | name n =>
      simp only [execStmt] at h ⊢
      split at h
      next hn => rw [if_pos hn]; exact h
      next hn =>
        rw [if_neg hn]
        cases hr : vecOf bind n with
        | none => rw [hr] at h; simp at h
        | some r =>
          rw [hr] at h
          cases hl : lanesOf perm bind s v with
          | none => rw [hl] at h; simp at h
          | some l => rw [hl] at h; rw [lanesOf_all v hl]; exact h
    | call f args =>
      simp only [execStmt] at h ⊢
      cases hv : values perm bind s args with
      | none => rw [hv] at h; simp at h
      | some vs =>
        rw [hv] at h; rw [values_all args hv]
        cases hl : vecArg bind s v with
        | none => rw [hl] at h; simp at h
        | some l =>
          rw [hl] at h
          simp only at h ⊢
          split at h
          · rw [if_pos (allowed_all _ _).2]; exact h
          · cases h

theorem execAll_all {perm : Perm} {bind : Bind} {base : Nat} {u : Nat → Nat} :
    ∀ (stmts : List Stmt) (k : Nat) (s : State) {o : Outcome},
    execAll perm bind base u k s stmts = some o → execAll Perm.all bind base u k s stmts = some o
  | [], _, _, _, h => h
  | st :: rest, k, s, o, h => by
    have go : st ≠ .ret → (∀ r, st ≠ .retLink r) → execAll Perm.all bind base u k s (st :: rest) = some o := by
      intro hr hl
      have unf : ∀ pm, execAll pm bind base u k s (st :: rest) =
          (match execStmt pm bind base (u k) s st with
            | some s' => execAll pm bind base u (k + 1) (noted bind s st s') rest
            | none => none) := by
        intro pm; cases st <;> first | exact absurd rfl hr | exact absurd rfl (hl _) | rfl
      rw [unf] at h ⊢
      cases he : execStmt perm bind base (u k) s st with
      | none => rw [he] at h; cases h
      | some s' =>
        rw [he] at h; rw [execStmt_all st he]
        exact execAll_all rest (k + 1) _ h
    cases st with
    | ret =>
      simp only [execAll] at h ⊢
      split at h
      · rw [if_pos (allowed_all _ _).1]; exact h
      · cases h
    | retLink r =>
      simp only [execAll] at h ⊢
      exact h
    | callLink _ _ => exact go (by intro x; cases x) (by intro r x; cases x)
    | nothing => exact go (by intro x; cases x) (by intro r x; cases x)
    | call _ => exact go (by intro x; cases x) (by intro r x; cases x)
    | jump _ _ => exact go (by intro x; cases x) (by intro r x; cases x)
    | set _ _ => exact go (by intro x; cases x) (by intro r x; cases x)
    | vset _ _ => exact go (by intro x; cases x) (by intro r x; cases x)
    | vset512 _ _ => exact go (by intro x; cases x) (by intro r x; cases x)

/-- What an instruction does where only some memory may be touched, it does where all of it may. -/
theorem exec_all {perm : Perm} {p : Program} {i : Instr} {u : Nat → Nat} {s : State} {o : Outcome}
    (h : exec perm p i u s = some o) : exec Perm.all p i u s = some o :=
  execAll_all i.effect 0 _ h

/-- A call is not run as an instruction of the function it is in. -/
theorem exec_call {p : Program} {i : Instr} {name : String} (h : callTarget i = some name) (perm : Perm) (u : Nat → Nat)
    (s : State) : exec perm p i u s = none := by
  unfold callTarget at h
  split at h
  next n heff => simp [exec, heff, execAll, execStmt]
  next n r heff => simp [exec, heff, execAll, execStmt]
  next => cases h

/-- **Nothing forbidden.** A run of the machine with marks that touches only what it is let, to states of
which `Q` holds, is a run of the plain machine on which nothing is forbidden, from the same state without
its marks, to those states without theirs. (So what is shown of a function on the machine that faults
where it touches what it is not let is so of it on a machine that lets it touch anything.) -/
theorem runs_free {world : List Program} {perm : Perm} {p : Program} {Q : State → Prop} {s : State}
    (h : Runs world perm p Q s) : RunsP world Perm.all p (fun t => ∃ s', Q s' ∧ t = s'.plain) s.plain := by
  induction h with
  | step perm p Q s i hf hn _ hr ih =>
    have both : ∀ u, ∃ o, execQ perm p i u s = some o ∧ execP Perm.all p i u s.plain = some o.plain := by
      intro u
      cases e : execQ perm p i u s with
      | none => exact absurd e (hn u)
      | some o => exact ⟨o, rfl, by rw [exec_plain, exec_all (execQ_exec e)]; rfl⟩
    refine RunsP.step Perm.all p _ s.plain i hf ?_ ?_ ?_
    · intro u e
      obtain ⟨o, _, e'⟩ := both u
      rw [e] at e'; cases e'
    · intro u t e
      obtain ⟨o, eq, e'⟩ := both u
      rw [e] at e'
      obtain ⟨s', rfl, rfl⟩ := outcome_next (Option.some.inj e').symm
      exact ih u s' eq
    · intro u t e
      obtain ⟨o, eq, e'⟩ := both u
      rw [e] at e'
      obtain ⟨s', rfl, rfl⟩ := outcome_returned (Option.some.inj e').symm
      exact ⟨s', hr u s' eq, rfl⟩
  | call perm p Q s i name q inner R hf hc hw hstack hir hiw _ hk _ ihq ihp =>
    rw [← afterCallP_plain] at ihq
    refine RunsP.call Perm.all p _ s.plain i name q Perm.all _ hf hc hw (fun hl => ⟨(hstack hl).1, (allowed_all _ _).2⟩) (fun _ h => h) (fun _ h => h) ihq ?_ ?_
    · rintro t ⟨s', hs', rfl⟩ r hr
      exact hk s' hs' r hr
    · rintro t ⟨s', hs', rfl⟩
      exact ihp s' hs'
  | tail perm p Q s i name q inner hf ht hw _ _ _ ihq =>
    exact RunsP.tail Perm.all p _ s.plain i name q Perm.all hf ht hw (fun _ h => h) (fun _ h => h) ihq

/-! ## Two runs of the plain machine -/

/-- The function `p`, started in the state `s`, has returned in the state `s'`: by instructions of the
plain machine, on which there is no mark and nothing is forbidden, whatever the unknowns turned out to be
at each; a called function running to its return in its turn. -/
inductive EndsP (world : List Program) : Program → State → State → Prop where
  | ret (p : Program) (s : State) (i : Instr) (u : Nat → Nat) (s' : State) :
      p.fetch s.rip = some i → execP Perm.all p i u s = some (.returned s') → EndsP world p s s'
  | step (p : Program) (s : State) (i : Instr) (u : Nat → Nat) (s1 s' : State) :
      p.fetch s.rip = some i → execP Perm.all p i u s = some (.next s1) → EndsP world p s1 s' → EndsP world p s s'
  | call (p : Program) (s : State) (i : Instr) (name : String) (q : Program) (s1 s' : State) :
      p.fetch s.rip = some i → callTarget i = some name → findProgram world name = some q →
      EndsP world q (afterCallP p q i s) s1 → EndsP world p s1 s' → EndsP world p s s'
  | tail (p : Program) (s : State) (i : Instr) (name : String) (q : Program) (s' : State) :
      p.fetch s.rip = some i → tailTarget i = some name → findProgram world name = some q →
      EndsP world q (afterTail q s) s' → EndsP world p s s'

/-- Where the machine with marks runs a function from `s` (to states of which `Q` holds, touching only what
it is let, stopping nowhere), every run of the plain machine from `s` without its marks is that machine's
run: it ends in a state the machine with marks ends in, without its marks. -/
theorem runs_endsP {world : List Program} {perm : Perm} {p : Program} {Q : State → Prop} {s : State}
    (h : Runs world perm p Q s) : ∀ {t : State}, EndsP world p s.plain t → ∃ s', Ends world p s s' ∧ Q s' ∧ t = s'.plain := by
  induction h with
  | step perm p Q s i hf hn _ hr ih =>
    intro t E
    have both : ∀ u, ∃ o, execQ perm p i u s = some o ∧ execP Perm.all p i u s.plain = some o.plain := by
      intro u
      cases e : execQ perm p i u s with
      | none => exact absurd e (hn u)
      | some o => exact ⟨o, rfl, by rw [exec_plain, exec_all (execQ_exec e)]; rfl⟩
    cases E with
    | ret _ _ i2 u s' hf2 hx =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      obtain ⟨o, eq, e'⟩ := both u
      rw [hx] at e'
      obtain ⟨s2, rfl, rfl⟩ := outcome_returned (Option.some.inj e').symm
      exact ⟨s2, Ends.ret p s i2 perm u s2 hf eq, hr u s2 eq, rfl⟩
    | step _ _ i2 u s1 _ hf2 hx E1 =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      obtain ⟨o, eq, e'⟩ := both u
      rw [hx] at e'
      obtain ⟨s2, rfl, rfl⟩ := outcome_next (Option.some.inj e').symm
      obtain ⟨s3, e3, q3, rfl⟩ := ih u s2 eq E1
      exact ⟨s3, Ends.step p s i2 perm u s2 s3 hf eq e3, q3, rfl⟩
    | call _ _ i2 name q s1 _ hf2 hc _ _ _ =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      exact absurd (execQ_call hc perm (fun _ => 0) s) (hn _)
    | tail _ _ i2 name q _ hf2 ht _ _ =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      exact absurd (execQ_tail ht perm (fun _ => 0) s) (hn _)
  | call perm p Q s i name q inner R hf hc hw hstack hir hiw _ hk _ ihq ihp =>
    intro t E
    have no : ∀ u, execP Perm.all p i u s.plain = none := by
      intro u; rw [exec_plain, exec_call hc]; rfl
    cases E with
    | ret _ _ i2 u s' hf2 hx =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      rw [no u] at hx; cases hx
    | step _ _ i2 u s1 _ hf2 hx _ =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      rw [no u] at hx; cases hx
    | call _ _ i2 name2 q2 s1 _ hf2 hc2 hw2 Ein Eout =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      rw [hc] at hc2; injection hc2 with e; subst e
      rw [hw] at hw2; injection hw2 with e; subst e
      rw [afterCallP_plain] at Ein
      obtain ⟨s1', e1, r1, rfl⟩ := ihq Ein
      obtain ⟨s2', e2, q2, rfl⟩ := ihp s1' r1 Eout
      exact ⟨s2', Ends.call p s i2 name q s1' s2' hf hc hw (fun hl => (hstack hl).2.2) e1 (hk s1' r1) e2, q2, rfl⟩
    | tail _ _ i2 name2 q2 _ hf2 ht2 _ _ =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      rw [tailTarget_not_call ht2] at hc; cases hc
  | tail perm p Q s i name q inner hf ht hw _ _ _ ihq =>
    intro t E
    have no : ∀ u, execP Perm.all p i u s.plain = none := by
      intro u; rw [exec_plain, exec_tail ht]; rfl
    cases E with
    | ret _ _ i2 u s' hf2 hx =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      rw [no u] at hx; cases hx
    | step _ _ i2 u s1 _ hf2 hx _ =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      rw [no u] at hx; cases hx
    | call _ _ i2 name2 q2 s1 _ hf2 hc2 _ _ _ =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      rw [tailTarget_not_call ht] at hc2; cases hc2
    | tail _ _ i2 name2 q2 _ hf2 ht2 hw2 Ein =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      rw [ht] at ht2; injection ht2 with e; subst e
      rw [hw] at hw2; injection hw2 with e; subst e
      obtain ⟨s', e', q', rfl⟩ := ihq Ein
      exact ⟨s', Ends.tail p s i2 name q s' hf ht hw e', q', rfl⟩

/-- **TWO RUNS OF THE PLAIN MACHINE.** Two states alike in everything not marked, from each of which the
machine with marks runs the function without stopping; two runs of the plain machine, from the one state
without its marks and from the other without its marks, each to the function's return. The two runs let
the same things be observed: the same instructions at the same addresses, touching the same memory. -/
theorem runs_trace {world : List Program} {p : Program} {pa pb : Perm} {Qa Qb : State → Prop} {a b a' b' : State}
    (A : Alike a b) (Ra : Runs world pa p Qa a) (Rb : Runs world pb p Qb b)
    (Ea : EndsP world p a.plain a') (Eb : EndsP world p b.plain b') : a'.trace = b'.trace := by
  obtain ⟨sa, ea, _, rfl⟩ := runs_endsP Ra Ea
  obtain ⟨sb, eb, _, rfl⟩ := runs_endsP Rb Eb
  show sa.trace = sb.trace
  exact ends_trace A ea eb

end Ode
