/-
The marks change no value.

`State.plain` is a state with its marks erased. The plain machine (`execP`) is the machine of Machine.lean
without marks: it sets no mark, reads none, and never stops for one. Here: what the machine with marks
does, the plain machine does on the plain states.
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

theorem lanesOf512_plain (perm : Perm) (bind : Bind) (s : State) (e : Expr) : lanesOf512 perm bind s.plain e = lanesOf512 perm bind s e := by
  cases e with
  | number _ => rfl
  | lane _ _ => rfl
  | name n => exact vecArg512_plain bind s (.name n)
  | call f args =>
    simp only [lanesOf512, addr512_plain, value_plain, vecArg512_plain]
    rfl

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
  | vset512 place v => exact execVec512_plain perm bind s place v
  | jump target cond =>
    have hv := value_plain perm bind s target
    cases cond with
    | none =>
      show (value perm bind s.plain target).map _ = ((value perm bind s target).map _).map State.plain
      rw [hv]; cases value perm bind s target <;> rfl
    | some fw =>
      obtain ⟨flag, want⟩ := fw
      show (if ((if flag == "zf" then s.zf else s.cf) == want) = true then (value perm bind s.plain target).map _ else some s.plain)
        = (if ((if flag == "zf" then s.zf else s.cf) == want) = true then (value perm bind s target).map _ else some s).map State.plain
      rw [hv]
      generalize ((if flag == "zf" then s.zf else s.cf) == want) = c
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
  | k, s, st :: rest =>
    match execStmt perm bind base (u k) s st with
    | some s' => execAllP perm bind base u (k + 1) (notedP bind s st s') rest
    | none => none

def execP (perm : Perm) (p : Program) (i : Instr) (u : Nat → Nat) (s : State) : Option Outcome :=
  execAllP perm i.bind p.base u 0 { s with rip := p.base + i.next, trace := s.trace ++ [(s.rip, 0)] } i.effect

/-- The state a called function starts in, on the plain machine. -/
def afterCallP (p q : Program) (i : Instr) (s : State) : State :=
  { reg := fun k => if k = RSP then s.reg RSP - 8 else s.reg k, zf := s.zf, cf := s.cf,
    mem := store s.mem (s.reg RSP - 8) (p.base + i.next) 8, rip := q.base, vec := s.vec,
    marks := {}, trace := s.trace ++ [(s.rip, 0), (s.reg RSP - 8, 8)] }

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
      8 ≤ s.reg RSP → allowed perm.write (s.reg RSP - 8) 8 = true →
      (∀ a, inner.read a = true → perm.read a = true) → (∀ a, inner.write a = true → perm.write a = true) →
      RunsP world inner q R (afterCallP p q i s) →
      (∀ s', R s' → ∀ r ∈ calleeSaved, s'.reg r = s.reg r) →
      (∀ s', R s' → RunsP world perm p Q s') →
      RunsP world perm p Q s

def Outcome.plain : Outcome → Outcome
  | .next s => .next s.plain
  | .returned s => .returned s.plain

theorem execAll_plain {perm : Perm} {bind : Bind} {base : Nat} {u : Nat → Nat} :
    ∀ (stmts : List Stmt) (k : Nat) (s : State),
    execAllP perm bind base u k s.plain stmts = (execAll perm bind base u k s stmts).map Outcome.plain
  | [], _, _ => rfl
  | st :: rest, k, s => by
    have go : st ≠ .ret → execAllP perm bind base u k s.plain (st :: rest) =
        (match execStmt perm bind base (u k) s st with
          | some s' => execAll perm bind base u (k + 1) (noted bind s st s') rest
          | none => none).map Outcome.plain := by
      intro hr
      have e := execStmt_plain perm bind base (u k) s st
      cases h : execStmt perm bind base (u k) s st with
      | none =>
        rw [h] at e
        cases st <;> first | exact absurd rfl hr | rfl | (simp only [execAllP, e]; rfl)
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
    | nothing => exact go (by intro x; cases x)
    | call _ => exact go (by intro x; cases x)
    | jump _ _ => exact go (by intro x; cases x)
    | set _ _ => exact go (by intro x; cases x)
    | vset _ _ => exact go (by intro x; cases x)
    | vset512 _ _ => exact go (by intro x; cases x)

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
  | call perm p Q s i name q inner R hf hc hw h8 ha _ hir hiw _ hk _ ihq ihp =>
    refine RunsP.call perm p _ s.plain i name q inner _ hf hc hw h8 ha hir hiw ihq ?_ ?_
    · rintro t ⟨s', hs', rfl⟩ r hr
      exact hk s' hs' r hr
    · rintro t ⟨s', hs', rfl⟩
      exact ihp s' hs'

end Ode
