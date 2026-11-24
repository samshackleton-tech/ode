import SoundMarks
import Plain
/-!
# Two-run trace and result soundness helpers

Supporting lemmas for `verify_all_trace` and `verify_all_result` in `SoundTop.lean`:
- `RunsPlain` relates directly to `EndsP` (plain execution without marks);
- `traceClean_same`: every expression allowed by `Contract.traceClean` evaluates to the same `Value`
  in any two entry states satisfying `Contract.traceAgree`;
- `callExprClean_same` & `callQuiet_traceAgree`: at a call approved by `callQuiet`, the callee's
  entry states satisfy `c.traceAgree`, and every expression approved by `callExprClean` takes the
  same `Value` in both runs;
- `initMarks`: constructs shared entry marks from `traceAgree` so the exported trace theorem needs
  no mention of `Marks`, `Alike`, or `quietAt`;
- `unmarkReg_alike`: clearing a register whose value agrees in both runs preserves `Alike`;
- `FlagEq` & `symStmtQ_flagEq`: an unmarked flag computed by `equal` or `below` has identical
  operands in both runs, so both runs always follow the same symbolic branch in `flagWays`.
-/
namespace Ode
open Arithmetic

/-! ## Plain-machine lemmas (`RunsPlain` and `EndsP`) -/

theorem str_beq_comm (a b : String) : (a == b) = (b == a) := by
  cases h : (b == a) with
  | true => simp [beq_iff_eq.mp h]
  | false =>
    cases h2 : (a == b) with
    | false => rfl
    | true => rw [beq_iff_eq.mp h2] at h; simp at h

theorem noted_data (bind : Bind) (s : State) (st : Stmt) (s1 : State) : (noted bind s st s1).data = s1.data := rfl

theorem execAll_data {perm : Perm} {bind : Bind} {base : Nat} {u : Nat → Nat} :
    ∀ (stmts : List Stmt) (k : Nat) {s : State} {o : Outcome},
    execAll perm bind base u k s stmts = some o → o.data = s.data
  | [], _, _, _, h => by simp only [execAll, Option.some.injEq] at h; subst h; rfl
  | st :: more, k, s, o, h => by
    cases st with
    | ret =>
      simp only [execAll] at h
      split at h
      · injection h with h; subst h; rfl
      · cases h
    | retLink r =>
      simp only [execAll] at h
      cases hr : regIndex r with
      | none => rw [hr] at h; cases h
      | some idx => rw [hr] at h; injection h with h; subst h; rfl
    | nothing | set _ _ | vset _ _ | vset512 _ _ | jump _ _ | call _ | callLink _ _ =>
      simp only [execAll] at h
      cases hx : execStmt perm bind base (u k) s _ with
      | none => rw [hx] at h; cases h
      | some s1 =>
        rw [hx] at h
        exact (execAll_data more (k + 1) h).trans ((noted_data _ _ _ _).trans (execStmt_data _ hx))

theorem exec_data {perm : Perm} {p : Program} {i : Instr} {u : Nat → Nat} {s : State} {o : Outcome}
    (h : exec perm p i u s = some o) : o.data = s.data :=
  execAll_data (s := { s with rip := p.base + i.next, trace := s.trace ++ [(s.rip, 0)] }) i.effect 0 h

theorem runsPlain_mono {world : List Program} {perm : Perm} {p : Program} {Q R : State → Prop}
    (imp : ∀ s, Q s → R s) {s : State} (h : RunsPlain world perm p Q s) : RunsPlain world perm p R s := by
  induction h with
  | step perm p Q s i hf hn _ hr ih =>
    exact RunsPlain.step perm p R s i hf hn (fun u s' hx => ih u s' hx imp) (fun u s' hx => imp s' (hr u s' hx))
  | call perm p Q s i name q inner M hf hc hw hstack hir hiw hq hk _ _ ihp =>
    exact RunsPlain.call perm p R s i name q inner M hf hc hw hstack hir hiw hq hk (fun s' h' => ihp s' h' imp)

theorem runsPlain_data {world : List Program} {perm : Perm} {p : Program} {Q : State → Prop} {s : State}
    (h : RunsPlain world perm p Q s) : RunsPlain world perm p (fun s' => Q s' ∧ s'.data = s.data) s := by
  induction h with
  | step perm p Q s i hf hn _ hr ih =>
    refine RunsPlain.step perm p _ s i hf hn (fun u s' hx => ?_) (fun u s' hx => ⟨hr u s' hx, exec_data hx⟩)
    have h1 := ih u s' hx
    have hd : s'.data = s.data := exec_data hx
    simpa [hd] using h1
  | call perm p Q s i name q inner R hf hc hw hstack hir hiw _ hk _ ihq ihp =>
    refine RunsPlain.call perm p _ s i name q inner (fun s1 => R s1 ∧ s1.data = s.data) hf hc hw hstack hir hiw ?_
      (fun s1 h1 r hr => hk s1 h1.1 r hr) (fun s1 h1 => ?_)
    · have h1 := ihq
      rw [afterCall_data] at h1
      exact h1
    · have h2 := ihp s1 h1.1
      have hd : (backFrom (keptAt i) s s1).data = s.data := h1.2
      simpa [hd] using h2

theorem plain_eq_fields {s1 s2 : State} (h : s1.plain = s2.plain) :
    s1.rip = s2.rip ∧ s1.reg = s2.reg ∧ s1.zf = s2.zf ∧ s1.cf = s2.cf ∧
    s1.mem = s2.mem ∧ s1.vec = s2.vec ∧ s1.data = s2.data ∧ s1.trace = s2.trace :=
  ⟨show s1.plain.rip = s2.plain.rip from congrArg State.rip h,
   show s1.plain.reg = s2.plain.reg from congrArg State.reg h,
   show s1.plain.zf = s2.plain.zf from congrArg State.zf h,
   show s1.plain.cf = s2.plain.cf from congrArg State.cf h,
   show s1.plain.mem = s2.plain.mem from congrArg State.mem h,
   show s1.plain.vec = s2.plain.vec from congrArg State.vec h,
   show s1.plain.data = s2.plain.data from congrArg State.data h,
   show s1.plain.trace = s2.plain.trace from congrArg State.trace h⟩

theorem exec_eq_plain {perm : Perm} {p : Program} {i : Instr} {u : Nat → Nat} {s1 s2 : State}
    (hp : s1.plain = s2.plain) {o1 : Outcome} (h : exec perm p i u s1 = some o1) :
    ∃ o2, exec perm p i u s2 = some o2 ∧ o1.plain = o2.plain := by
  have h1 : (exec perm p i u s1).map Outcome.plain = (exec perm p i u s2).map Outcome.plain := by
    rw [← exec_plain, hp, exec_plain]
  rw [h] at h1
  cases h2 : exec perm p i u s2 with
  | none => rw [h2] at h1; cases h1
  | some o2 => rw [h2] at h1; exact ⟨o2, rfl, Option.some.inj h1⟩

theorem runsPlain_of_plain_aux {world : List Program} {perm : Perm} {p : Program} {Q : State → Prop} {s1 : State}
    (h : RunsPlain world perm p Q s1) :
    ∀ s2, s1.plain = s2.plain → RunsPlain world perm p (fun t => ∃ t0, Q t0 ∧ t0.plain = t.plain) s2 := by
  induction h with
  | step perm p Q s i hf hn _ hr ih =>
    intro s2 hp
    have hrip : s2.rip = s.rip := (plain_eq_fields hp).1.symm
    refine RunsPlain.step perm p _ s2 i (by rw [hrip]; exact hf) ?_ ?_ ?_
    · intro u he
      cases e1 : exec perm p i u s with
      | none => exact absurd e1 (hn u)
      | some o1 =>
        obtain ⟨o2, e2, _⟩ := exec_eq_plain hp e1
        rw [he] at e2; cases e2
    · intro u t2 e2
      cases e1 : exec perm p i u s with
      | none => exact absurd e1 (hn u)
      | some o1 =>
        obtain ⟨o2, e2', ho⟩ := exec_eq_plain hp e1
        rw [e2] at e2'; injection e2' with e2'; subst e2'
        obtain ⟨t1, rfl, ht⟩ := outcome_next (show o1.plain = .next t2.plain from ho)
        exact ih u t1 e1 t2 ht.symm
    · intro u t2 e2
      cases e1 : exec perm p i u s with
      | none => exact absurd e1 (hn u)
      | some o1 =>
        obtain ⟨o2, e2', ho⟩ := exec_eq_plain hp e1
        rw [e2] at e2'; injection e2' with e2'; subst e2'
        obtain ⟨t1, rfl, ht⟩ := outcome_returned (show o1.plain = .returned t2.plain from ho)
        exact ⟨t1, hr u t1 e1, ht.symm⟩
  | call perm p Q s i name q inner R hf hc hw hstack hir hiw _ hk _ ihq ihp =>
    intro s2 hp
    have ⟨hrip, hreg, _, _, _, _, _, _⟩ := plain_eq_fields hp
    have hac : (afterCall p q i s).plain = (afterCall p q i s2).plain := by
      rw [← afterCallP_plain, hp, afterCallP_plain]
    refine RunsPlain.call perm p _ s2 i name q inner (fun t => ∃ t0, R t0 ∧ t0.plain = t.plain)
      (by rw [← hrip]; exact hf) hc hw
      (fun hl => by rw [← hreg]; exact hstack hl) hir hiw
      (ihq (afterCall p q i s2) hac)
      (fun s' ⟨t0, ht0, hpt⟩ r hr => by
        rw [← hreg, ← (plain_eq_fields hpt).2.1]
        exact hk t0 ht0 r hr)
      (fun s' ⟨t0, ht0, hpt⟩ => ihp t0 ht0 (backFrom (keptAt i) s2 s') (by
        have ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := plain_eq_fields hpt
        simp only [backFrom, State.plain, hreg, r1, r2, r3, r4, r5, r6, r7, r8]))

theorem runsPlain_of_plain {world : List Program} {perm : Perm} {p : Program} {Q : State → Prop}
    (hQ : ∀ s1 s2, s1.plain = s2.plain → Q s1 → Q s2) {s1 : State}
    (h : RunsPlain world perm p Q s1) : ∀ s2, s1.plain = s2.plain → RunsPlain world perm p Q s2 :=
  fun s2 hp => runsPlain_mono (fun _ ⟨t0, ht0, hpt⟩ => hQ t0 _ hpt ht0) (runsPlain_of_plain_aux h s2 hp)

/-- Every `EndsP` run from `s.plain` is covered by `RunsPlain` from `s`, ending in a state satisfying `Q`. -/
theorem runsPlain_endsP {world : List Program} {perm : Perm} {p : Program} {Q : State → Prop} {s : State}
    (h : RunsPlain world perm p Q s) : ∀ {t : State}, EndsP world p s.plain t → ∃ s', Q s' ∧ t = s'.plain := by
  induction h with
  | step perm p Q s i hf hn _ hr ih =>
    intro t E
    have both : ∀ u, ∃ o, exec perm p i u s = some o ∧ execP Perm.all p i u s.plain = some o.plain := by
      intro u
      cases e : exec perm p i u s with
      | none => exact absurd e (hn u)
      | some o => exact ⟨o, rfl, by rw [exec_plain, exec_all e]; rfl⟩
    cases E with
    | ret _ _ i2 u s' hf2 hx =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      obtain ⟨o, eq, e'⟩ := both u
      rw [hx] at e'
      obtain ⟨s2, rfl, rfl⟩ := outcome_returned (Option.some.inj e').symm
      exact ⟨s2, hr u s2 eq, rfl⟩
    | step _ _ i2 u s1 _ hf2 hx E1 =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      obtain ⟨o, eq, e'⟩ := both u
      rw [hx] at e'
      obtain ⟨s2, rfl, rfl⟩ := outcome_next (Option.some.inj e').symm
      exact ih u s2 eq E1
    | call _ _ i2 name q s1 _ hf2 hc _ _ _ =>
      have e : i2 = i := by have := hf2; rw [show s.plain.rip = s.rip from rfl, hf] at this; exact (Option.some.inj this).symm
      subst e
      exact absurd (exec_call hc perm (fun _ => 0) s) (hn _)
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
      obtain ⟨s1', r1, rfl⟩ := ihq Ein
      exact ihp s1' r1 Eout

/-! ## Little-endian byte uniqueness for `load` -/

theorem load_eq_bytes {m1 m2 : Nat → Byte} :
    ∀ (n a : Nat), load m1 a n = load m2 a n → ∀ k, k < n → m1 (a + k) = m2 (a + k)
  | 0, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, a, h, k, hk => by
    simp only [load] at h
    have b1 := (m1 a).isLt
    have b2 := (m2 a).isLt
    have h0 : (m1 a).val = (m2 a).val := by omega
    have hr : load m1 (a + 1) n = load m2 (a + 1) n := by omega
    cases k with
    | zero => exact Fin.ext h0
    | succ k =>
      have := load_eq_bytes n (a + 1) hr k (by omega)
      rwa [show a + (k + 1) = a + 1 + k by omega]

/-! ## Specification evaluation helpers -/

theorem lookup_append_mem {α : Type} {x : String} {l1 l2 : List (String × α)} (h : (l1.map Prod.fst).contains x = true) :
    (l1 ++ l2).lookup x = l1.lookup x := by
  induction l1 with
  | nil => simp at h
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
    simp only [List.cons_append, List.lookup_cons]
    cases hpx : (x == a) with
    | true => rfl
    | false =>
      rcases h with h1 | h2
      · rw [h1] at hpx; simp at hpx
      · exact ih h2

theorem lookup_append_not_mem {α : Type} {x : String} {l1 l2 : List (String × α)} (h : (l1.map Prod.fst).contains x = false) :
    (l1 ++ l2).lookup x = l2.lookup x := by
  induction l1 with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    simp only [List.cons_append, List.lookup_cons, beq_false_of_ne h.1]
    exact ih h.2

/-- Lift a single-direction `Value` implication across `evalEach`, picking a common sufficient fuel. -/
theorem evalEach_lift {defs : List Def} {env1 env2 : List (String × Val)} {x : String} {body1 body2 : SExpr} {f1 : Nat} :
    ∀ (n : Nat) (lo : Int) {vs : List Val},
    evalEach (fun i => evalSpec defs f1 ((x, .int i) :: env1) body1) n lo = some vs →
    (∀ i v, evalSpec defs f1 ((x, .int i) :: env1) body1 = some v → Value defs ((x, .int i) :: env2) body2 v) →
    ∃ f2, evalEach (fun i => evalSpec defs f2 ((x, .int i) :: env2) body2) n lo = some vs
  | 0, _, _, h, _ => by
    simp only [evalEach, Option.some.injEq] at h; subst h; exact ⟨0, rfl⟩
  | n + 1, lo, vs, h, himp => by
    simp only [evalEach] at h
    cases ha : evalSpec defs f1 ((x, .int lo) :: env1) body1 with
    | none => simp [ha] at h
    | some v =>
      rw [ha] at h
      cases hr : evalEach (fun i => evalSpec defs f1 ((x, .int i) :: env1) body1) n (lo + 1) with
      | none => simp [hr] at h
      | some ws =>
        rw [hr] at h; injection h with h; subst h
        obtain ⟨fa, hva⟩ := himp lo v ha
        obtain ⟨fr, hvr⟩ := evalEach_lift n (lo + 1) hr himp
        refine ⟨max fa fr, ?_⟩
        simp only [evalEach]
        rw [evalSpec_mono defs fa hva (max fa fr) (Nat.le_max_left fa fr)]
        rw [evalEach_mono (fun _ _ hv => evalSpec_mono defs fr hv (max fa fr) (Nat.le_max_right fa fr)) n (lo + 1) hvr]

theorem firstWith_lift {defs : List Def} {env1 env2 : List (String × Val)} {x : String} {cond1 cond2 : SExpr} {f1 : Nat} :
    ∀ (xs : List Int) {v : Val},
    firstWith (fun i => evalSpec defs f1 ((x, .int i) :: env1) cond1) xs = some v →
    (∀ i w, evalSpec defs f1 ((x, .int i) :: env1) cond1 = some w → Value defs ((x, .int i) :: env2) cond2 w) →
    ∃ f2, firstWith (fun i => evalSpec defs f2 ((x, .int i) :: env2) cond2) xs = some v
  | [], _, h, _ => by cases h
  | k :: ks, v, h, himp => by
    simp only [firstWith] at h
    cases hk : evalSpec defs f1 ((x, .int k) :: env1) cond1 with
    | none => simp [hk] at h
    | some w =>
      rw [hk] at h
      cases w with
      | int _ | list _ | record _ | word _ | counter _ => cases h
      | bool b =>
        cases b with
        | true =>
          injection h with h; subst h
          obtain ⟨fk, hvk⟩ := himp k (.bool true) hk
          exact ⟨fk, by simp [firstWith, hvk]⟩
        | false =>
          obtain ⟨fk, hvk⟩ := himp k (.bool false) hk
          obtain ⟨fr, hvr⟩ := firstWith_lift ks h himp
          refine ⟨max fk fr, ?_⟩
          simp only [firstWith]
          rw [evalSpec_mono defs fk hvk (max fk fr) (Nat.le_max_left fk fr)]
          exact firstWith_mono (fun _ _ hv => evalSpec_mono defs fr hv (max fk fr) (Nat.le_max_right fk fr)) ks hvr

/-- Combined value & argument-list transfer relation between `(env1, e1)` and `(env2, e2)`. -/
def ExprImp (defs : List Def) (env1 env2 : List (String × Val)) (e1 e2 : SExpr) : Prop :=
  (∀ v, Value defs env1 e1 v → Value defs env2 e2 v) ∧
  (∀ f1 vs, evalList (evalSpec defs f1 env1) e1 = some vs →
    ∃ f2, evalList (evalSpec defs f2 env2) e2 = some vs)

theorem ExprImp.of_val {defs : List Def} {env1 env2 : List (String × Val)} {e1 e2 : SExpr}
    (hne1 : isExpr e1 = true) (hv : ∀ v, Value defs env1 e1 v → Value defs env2 e2 v) :
    ExprImp defs env1 env2 e1 e2 :=
  ⟨hv, fun _ _ hl => by cases e1 <;> simp [isExpr, evalList] at hne1 hl⟩

theorem ExprImp.bin {defs : List Def} {env1 env2 : List (String × Val)} {op : String} {a1 b1 a2 b2 : SExpr}
    (ha : ExprImp defs env1 env2 a1 a2) (hb : ExprImp defs env1 env2 b1 b2) :
    ExprImp defs env1 env2 (.bin op a1 b1) (.bin op a2 b2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases h1 : evalSpec defs f env1 a1 with
      | none => simp [h1] at hf
      | some v1 =>
        rw [h1] at hf
        cases h2 : evalSpec defs f env1 b1 with
        | none => simp [h2] at hf
        | some v2 =>
          rw [h2] at hf
          obtain ⟨f1, hf1⟩ := ha.1 v1 ⟨f, h1⟩
          obtain ⟨f2, hf2⟩ := hb.1 v2 ⟨f, h2⟩
          refine ⟨max f1 f2 + 1, ?_⟩
          simp only [evalSpec, evalSpec_mono defs f1 hf1 (max f1 f2) (Nat.le_max_left f1 f2),
            evalSpec_mono defs f2 hf2 (max f1 f2) (Nat.le_max_right f1 f2)]
          exact hf

theorem ExprImp.ifx {defs : List Def} {env1 env2 : List (String × Val)} {c1 a1 b1 c2 a2 b2 : SExpr}
    (hc : ExprImp defs env1 env2 c1 c2) (ha : ExprImp defs env1 env2 a1 a2) (hb : ExprImp defs env1 env2 b1 b2) :
    ExprImp defs env1 env2 (.ifx c1 a1 b1) (.ifx c2 a2 b2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases h0 : evalSpec defs f env1 c1 with
      | none => simp [h0] at hf
      | some vc =>
        rw [h0] at hf
        cases vc with
        | int _ | list _ | record _ | word _ | counter _ => simp at hf
        | bool tb =>
          obtain ⟨fc, hfc⟩ := hc.1 (.bool tb) ⟨f, h0⟩
          cases tb with
          | true =>
            obtain ⟨ft, hft⟩ := ha.1 v ⟨f, hf⟩
            exact ⟨max fc ft + 1, by simp only [evalSpec, evalSpec_mono defs fc hfc (max fc ft) (Nat.le_max_left fc ft), evalSpec_mono defs ft hft (max fc ft) (Nat.le_max_right fc ft)]⟩
          | false =>
            obtain ⟨ft, hft⟩ := hb.1 v ⟨f, hf⟩
            exact ⟨max fc ft + 1, by simp only [evalSpec, evalSpec_mono defs fc hfc (max fc ft) (Nat.le_max_left fc ft), evalSpec_mono defs ft hft (max fc ft) (Nat.le_max_right fc ft)]⟩

theorem ExprImp.index {defs : List Def} {env1 env2 : List (String × Val)} {a1 i1 a2 i2 : SExpr}
    (ha : ExprImp defs env1 env2 a1 a2) (hi : ExprImp defs env1 env2 i1 i2) :
    ExprImp defs env1 env2 (.index a1 i1) (.index a2 i2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases h1 : evalSpec defs f env1 a1 with
      | none => simp [h1] at hf
      | some v1 =>
        rw [h1] at hf
        cases h2 : evalSpec defs f env1 i1 with
        | none => simp [h2] at hf
        | some v2 =>
          rw [h2] at hf
          obtain ⟨f1, hf1⟩ := ha.1 v1 ⟨f, h1⟩
          obtain ⟨f2, hf2⟩ := hi.1 v2 ⟨f, h2⟩
          refine ⟨max f1 f2 + 1, ?_⟩
          simp only [evalSpec, evalSpec_mono defs f1 hf1 (max f1 f2) (Nat.le_max_left f1 f2),
            evalSpec_mono defs f2 hf2 (max f1 f2) (Nat.le_max_right f1 f2)]
          exact hf

theorem ExprImp.call {defs : List Def} {env1 env2 : List (String × Val)} {fn : String} {args1 args2 : SExpr}
    (ha : ExprImp defs env1 env2 args1 args2) :
    ExprImp defs env1 env2 (.call fn args1) (.call fn args2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases hl : evalList (evalSpec defs f env1) args1 with
      | none => simp [hl] at hf
      | some vs =>
        simp only [hl] at hf
        obtain ⟨f2, hf2⟩ := ha.2 f vs hl
        refine ⟨max f f2 + 1, ?_⟩
        simp only [evalSpec, evalList_mono (fun _ _ hv => evalSpec_mono defs f2 hv (max f f2) (Nat.le_max_right f f2)) args2 hf2]
        by_cases hlen : (fn == "len") = true
        · simp only [hlen, ite_true] at hf ⊢; exact hf
        · simp only [hlen, ite_false] at hf ⊢
          by_cases hown : own.contains fn = true
          · simp only [hown, ite_true] at hf ⊢; exact hf
          · simp only [hown, ite_false] at hf ⊢
            cases hd : findDef defs fn with
            | none => simp [hd] at hf
            | some d =>
              simp only [hd] at hf ⊢
              by_cases hpl : (d.params.length == vs.length) = true
              · simp only [hpl, ite_true] at hf ⊢
                exact evalSpec_mono defs f hf (max f f2) (Nat.le_max_left f f2)
              · simp [hpl] at hf

theorem ExprImp.list {defs : List Def} {env1 env2 : List (String × Val)} {items1 items2 : SExpr}
    (hi : ExprImp defs env1 env2 items1 items2) :
    ExprImp defs env1 env2 (.list items1) (.list items2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases hl : evalList (evalSpec defs f env1) items1 with
      | none => simp [hl] at hf
      | some vs =>
        rw [hl] at hf
        obtain ⟨f2, hf2⟩ := hi.2 f vs hl
        exact ⟨f2 + 1, by simp only [evalSpec, hf2]; exact hf⟩

theorem ExprImp.cons {defs : List Def} {env1 env2 : List (String × Val)} {a1 r1 a2 r2 : SExpr}
    (ha : ExprImp defs env1 env2 a1 a2) (hr : ExprImp defs env1 env2 r1 r2) :
    ExprImp defs env1 env2 (.cons a1 r1) (.cons a2 r2) :=
  ⟨fun _ ⟨f, hf⟩ => by cases f <;> simp [evalSpec] at hf,
   fun f1 vs hl => by
     simp only [evalList] at hl
     cases h1 : evalSpec defs f1 env1 a1 with
     | none => simp [h1] at hl
     | some v =>
       rw [h1] at hl
       cases h2 : evalList (evalSpec defs f1 env1) r1 with
       | none => simp [h2] at hl
       | some ws =>
         rw [h2] at hl; injection hl with hl; subst hl
         obtain ⟨fa, hfa⟩ := ha.1 v ⟨f1, h1⟩
         obtain ⟨fr, hfr⟩ := hr.2 f1 ws h2
         refine ⟨max fa fr, ?_⟩
         simp only [evalList, evalSpec_mono defs fa hfa (max fa fr) (Nat.le_max_left fa fr),
           evalList_mono (fun _ _ hv => evalSpec_mono defs fr hv (max fa fr) (Nat.le_max_right fa fr)) r2 hfr]⟩

theorem ExprImp.letx {defs : List Def} {env1 env2 : List (String × Val)} {x : String} {r1 b1 r2 b2 : SExpr}
    (hr : ExprImp defs env1 env2 r1 r2)
    (hb : ∀ w, ExprImp defs ((x, w) :: env1) ((x, w) :: env2) b1 b2) :
    ExprImp defs env1 env2 (.letx x r1 b1) (.letx x r2 b2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases h1 : evalSpec defs f env1 r1 with
      | none => simp [h1] at hf
      | some w =>
        rw [h1] at hf
        obtain ⟨fr, hfr⟩ := hr.1 w ⟨f, h1⟩
        obtain ⟨fb, hfb⟩ := (hb w).1 v ⟨f, hf⟩
        exact ⟨max fr fb + 1, by
          simp only [evalSpec, evalSpec_mono defs fr hfr (max fr fb) (Nat.le_max_left fr fb),
            evalSpec_mono defs fb hfb (max fr fb) (Nat.le_max_right fr fb)]⟩

theorem ExprImp.each {defs : List Def} {env1 env2 : List (String × Val)} {x : String} {body1 a1 b1 body2 a2 b2 : SExpr}
    (ha : ExprImp defs env1 env2 a1 a2) (hb : ExprImp defs env1 env2 b1 b2)
    (hbody : ∀ i : Int, ExprImp defs ((x, .int i) :: env1) ((x, .int i) :: env2) body1 body2) :
    ExprImp defs env1 env2 (.each body1 x a1 b1) (.each body2 x a2 b2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases h1 : evalSpec defs f env1 a1 with
      | none => simp [h1] at hf
      | some v1 =>
        rw [h1] at hf
        cases h2 : evalSpec defs f env1 b1 with
        | none => simp [h2] at hf
        | some v2 =>
          rw [h2] at hf
          cases v1 with
          | bool _ | list _ | record _ | word _ | counter _ => simp at hf
          | int lo =>
            cases v2 with
            | bool _ | list _ | record _ | word _ | counter _ => simp at hf
            | int hi =>
              simp only at hf
              cases he : evalEach (fun i => evalSpec defs f ((x, .int i) :: env1) body1) (hi - lo).toNat lo with
              | none => simp [he] at hf
              | some vs =>
                simp only [he, Option.map_some, Option.some.injEq] at hf; subst hf
                obtain ⟨f1, hf1⟩ := ha.1 (.int lo) ⟨f, h1⟩
                obtain ⟨f2, hf2⟩ := hb.1 (.int hi) ⟨f, h2⟩
                obtain ⟨fe, hfe⟩ := evalEach_lift (hi - lo).toNat lo he (fun i w hw => (hbody i).1 w ⟨f, hw⟩)
                let F := max (max f1 f2) fe
                refine ⟨F + 1, ?_⟩
                simp only [evalSpec]
                rw [evalSpec_mono defs f1 hf1 F (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)),
                    evalSpec_mono defs f2 hf2 F (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))]
                simp only [evalEach_mono (fun _ _ hw => evalSpec_mono defs fe hw F (Nat.le_max_right _ _)) (hi - lo).toNat lo hfe]
                rfl

theorem ExprImp.slice {defs : List Def} {env1 env2 : List (String × Val)} {a1 lo1 hi1 a2 lo2 hi2 : SExpr}
    (ha : ExprImp defs env1 env2 a1 a2) (hlo : ExprImp defs env1 env2 lo1 lo2) (hhi : ExprImp defs env1 env2 hi1 hi2) :
    ExprImp defs env1 env2 (.slice a1 lo1 hi1) (.slice a2 lo2 hi2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases h1 : evalSpec defs f env1 a1 with
      | none => simp [h1] at hf
      | some v1 =>
        rw [h1] at hf
        cases h2 : evalSpec defs f env1 lo1 with
        | none => simp [h2] at hf
        | some v2 =>
          rw [h2] at hf
          cases h3 : evalSpec defs f env1 hi1 with
          | none => simp [h3] at hf
          | some v3 =>
            rw [h3] at hf
            obtain ⟨f1, hf1⟩ := ha.1 v1 ⟨f, h1⟩
            obtain ⟨f2, hf2⟩ := hlo.1 v2 ⟨f, h2⟩
            obtain ⟨f3, hf3⟩ := hhi.1 v3 ⟨f, h3⟩
            let F := max (max f1 f2) f3
            refine ⟨F + 1, ?_⟩
            simp only [evalSpec,
              evalSpec_mono defs f1 hf1 F (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)),
              evalSpec_mono defs f2 hf2 F (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)),
              evalSpec_mono defs f3 hf3 F (Nat.le_max_right _ _)]
            exact hf

theorem ExprImp.withx {defs : List Def} {env1 env2 : List (String × Val)} {a1 p1 a2 p2 : SExpr}
    (ha : ExprImp defs env1 env2 a1 a2) (hp : ExprImp defs env1 env2 p1 p2) :
    ExprImp defs env1 env2 (.withx a1 p1) (.withx a2 p2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases h1 : evalSpec defs f env1 a1 with
      | none => simp [h1] at hf
      | some v1 =>
        rw [h1] at hf
        cases h2 : evalList (evalSpec defs f env1) p1 with
        | none => simp [h2] at hf
        | some ps =>
          rw [h2] at hf
          obtain ⟨f1, hf1⟩ := ha.1 v1 ⟨f, h1⟩
          obtain ⟨f2, hf2⟩ := hp.2 f ps h2
          refine ⟨max f1 f2 + 1, ?_⟩
          simp only [evalSpec, evalSpec_mono defs f1 hf1 (max f1 f2) (Nat.le_max_left f1 f2),
            evalList_mono (fun _ _ hv => evalSpec_mono defs f2 hv (max f1 f2) (Nat.le_max_right f1 f2)) p2 hf2]
          exact hf

theorem ExprImp.record {defs : List Def} {env1 env2 : List (String × Val)} {ns : List String} {items1 items2 : SExpr}
    (hi : ExprImp defs env1 env2 items1 items2) :
    ExprImp defs env1 env2 (.record ns items1) (.record ns items2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases hl : evalList (evalSpec defs f env1) items1 with
      | none => simp [hl] at hf
      | some vs =>
        rw [hl] at hf
        obtain ⟨f2, hf2⟩ := hi.2 f vs hl
        exact ⟨f2 + 1, by simp only [evalSpec, hf2]; exact hf⟩

theorem ExprImp.field {defs : List Def} {env1 env2 : List (String × Val)} {e1 e2 : SExpr} {fn : String}
    (he : ExprImp defs env1 env2 e1 e2) :
    ExprImp defs env1 env2 (.field e1 fn) (.field e2 fn) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases h1 : evalSpec defs f env1 e1 with
      | none => simp [h1] at hf
      | some v1 =>
        rw [h1] at hf
        obtain ⟨f1, hf1⟩ := he.1 v1 ⟨f, h1⟩
        exact ⟨f1 + 1, by simp only [evalSpec, hf1]; exact hf⟩

theorem ExprImp.theNumber {defs : List Def} {env1 env2 : List (String × Val)} {g : Bool} {x : String} {a1 b1 c1 a2 b2 c2 : SExpr}
    (ha : ExprImp defs env1 env2 a1 a2) (hb : ExprImp defs env1 env2 b1 b2)
    (hc : ∀ i : Int, ExprImp defs ((x, .int i) :: env1) ((x, .int i) :: env2) c1 c2) :
    ExprImp defs env1 env2 (.theNumber g x a1 b1 c1) (.theNumber g x a2 b2 c2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      cases h1 : evalSpec defs f env1 a1 with
      | none => simp [h1] at hf
      | some v1 =>
        rw [h1] at hf
        cases h2 : evalSpec defs f env1 b1 with
        | none => simp [h2] at hf
        | some v2 =>
          rw [h2] at hf
          cases v1 with
          | bool _ | list _ | record _ | word _ | counter _ => simp at hf
          | int lo =>
            cases v2 with
            | bool _ | list _ | record _ | word _ | counter _ => simp at hf
            | int hi =>
              obtain ⟨f1, hf1⟩ := ha.1 (.int lo) ⟨f, h1⟩
              obtain ⟨f2, hf2⟩ := hb.1 (.int hi) ⟨f, h2⟩
              obtain ⟨fc, hfc⟩ := firstWith_lift _ hf (fun i w hw => (hc i).1 w ⟨f, hw⟩)
              let F := max (max f1 f2) fc
              refine ⟨F + 1, ?_⟩
              simp only [evalSpec]
              rw [evalSpec_mono defs f1 hf1 F (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)),
                  evalSpec_mono defs f2 hf2 F (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))]
              exact firstWith_mono (fun _ _ hw => evalSpec_mono defs fc hw F (Nat.le_max_right _ _)) _ hfc

theorem ExprImp.thePower {defs : List Def} {env1 env2 : List (String × Val)} {g : Bool} {x : String} {c1 c2 : SExpr}
    (hc : ∀ i : Int, ExprImp defs ((x, .int i) :: env1) ((x, .int i) :: env2) c1 c2) :
    ExprImp defs env1 env2 (.thePower g x c1) (.thePower g x c2) :=
  ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
    cases f with
    | zero => cases hf
    | succ f =>
      simp only [evalSpec] at hf
      obtain ⟨fc, hfc⟩ := firstWith_lift _ hf (fun i w hw => (hc i).1 w ⟨f, hw⟩)
      exact ⟨fc + 1, by simp only [evalSpec]; exact hfc⟩

/-! ## Agreement on `envIn` and `traceClean` -/

theorem argRegs_nodup (c : Contract) : c.argRegs.Nodup := by
  unfold Contract.argRegs
  cases c.arm64 <;> decide

theorem regOfIn_eq_head {x y : String} {k : Kind} {args : List (String × Kind)} {r : Nat} {regs : List Nat}
    (hnd : (r :: regs).Nodup) (h : regOfIn y ((x, k) :: args) (r :: regs) = some r) : y = x := by
  simp only [regOfIn] at h
  cases hxy : (x == y) with
  | true => exact (beq_iff_eq.mp hxy).symm
  | false =>
    simp only [hxy, Bool.false_eq_true, ite_false] at h
    have hmem : r ∈ regs := regOfIn_mem y args regs r h
    exact absurd hmem (List.nodup_cons.mp hnd).1

theorem regOfIn_tail_ne {y : String} {x : String} {k : Kind} {args : List (String × Kind)} {r r' : Nat} {regs : List Nat}
    (hnd : (r :: regs).Nodup) (hne : r' ≠ r) (h : regOfIn y ((x, k) :: args) (r :: regs) = some r') :
    regOfIn y args regs = some r' := by
  simp only [regOfIn] at h
  cases hxy : (x == y) with
  | true => simp only [hxy, ite_true, Option.some.injEq] at h; exact absurd h.symm hne
  | false => simp only [hxy, Bool.false_eq_true, ite_false] at h; exact h

theorem envIn_lookup_agree {c : Contract} {defs : List Def} {a b : State} (ta : c.traceAgree defs a b) :
    ∀ (args : List (String × Kind)) (regs : List Nat) (x : String),
    regs.Nodup →
    (∀ r ∈ cleanIn c args regs, r ∈ c.cleanAtEntry) →
    (∀ r l, (r, l) ∈ regionsIn c args regs → (r, l) ∈ c.regions) →
    (∀ y r, r ∈ regs → c.regOf y = some r → regOfIn y args regs = some r) →
    envArgIn c x args regs = true → x ∉ c.hidden →
    (envIn c a args regs).lookup x = (envIn c b args regs).lookup x
  | [], _, _, _, _, _, _, he, _ => by simp [envArgIn] at he
  | _ :: _, [], _, _, _, _, _, he, _ => by simp [envArgIn] at he
  | (n, k) :: args, r :: regs, x, hnd, hcl, hreg, hro, he, hnh => by
    have hnd' : regs.Nodup := (List.nodup_cons.mp hnd).2
    have hnr : r ∉ regs := (List.nodup_cons.mp hnd).1
    have hcl' : ∀ r' ∈ cleanIn c args regs, r' ∈ c.cleanAtEntry := fun r' hm =>
      hcl r' (by simp only [cleanIn, List.mem_append]; exact Or.inr hm)
    have hreg' : ∀ r' l', (r', l') ∈ regionsIn c args regs → (r', l') ∈ c.regions := fun r' l' hm =>
      hreg r' l' (regionsIn_tail c (n, k) r hm)
    have hro' : ∀ y r', r' ∈ regs → c.regOf y = some r' → regOfIn y args regs = some r' := fun y r' hm hr =>
      regOfIn_tail_ne hnd (fun e => hnr (e ▸ hm)) (hro y r' (List.mem_cons_of_mem _ hm) hr)
    cases k with
    | number =>
      simp only [envIn, List.lookup_cons]
      cases hxn : (x == n) with
      | true =>
        have e : x = n := beq_iff_eq.mp hxn
        subst e
        have hr : r ∈ c.cleanAtEntry := hcl r (by simp [cleanIn, hnh])
        simp only
        rw [ta.2.2.2.2.2.1 r hr]
      | false =>
        simp only [envArgIn, str_beq_comm n x, hxn, Bool.false_eq_true, ite_false] at he
        exact envIn_lookup_agree ta args regs x hnd' hcl' hreg' hro' he hnh
    | bytes len =>
      cases hl : c.regOf len with
      | none =>
        simp only [envIn, hl]
        simp only [envArgIn, hl] at he
        cases hxn : (n == x) with
        | true => simp [hxn] at he
        | false => simp only [hxn, Bool.false_eq_true, ite_false] at he; exact envIn_lookup_agree ta args regs x hnd' hcl' hreg' hro' he hnh
      | some l =>
        simp only [envIn, hl, List.lookup_cons]
        cases hxn : (x == n) with
        | true =>
          have e : x = n := beq_iff_eq.mp hxn
          subst e
          have hrl : (r, l) ∈ c.regions := hreg r l (by simp [regionsIn, hl])
          have hnhr : c.hiddenAt r = false := by
            unfold Contract.hiddenAt
            rw [List.any_eq_false]
            intro y hy
            cases hry : c.regOf y with
            | none => simp [hry]
            | some r' =>
              simp only [hry, beq_iff_eq]
              intro er
              injection er with er
              subst r'
              have h1 := hro y r (List.mem_cons_self ..) hry
              have h2 := regOfIn_eq_head hnd h1
              rw [h2] at hy
              exact hnh hy
          obtain ⟨hlen, hbytes⟩ := ta.2.2.2.2.2.2.1 r l hrl hnhr
          simp only [hxn]
          congr 2
          rw [hlen]
          apply List.map_congr_left
          intro k hk
          have hk' : k < a.reg l := by rw [hlen]; exact List.mem_range.mp hk
          rw [hbytes k hk']
        | false =>
          simp only [envArgIn, str_beq_comm n x, hxn, Bool.false_eq_true, ite_false] at he
          exact envIn_lookup_agree ta args regs x hnd' hcl' hreg' hro' he hnh
    | out _ | fixed _ | inout _ | valArray _ _ =>
      simp only [envIn]
      simp only [envArgIn] at he
      exact envIn_lookup_agree ta args regs x hnd' hcl' hreg' hro' he hnh

theorem env_lookup_agree {c : Contract} {defs : List Def} {a b : State} (ta : c.traceAgree defs a b)
    {x : String} (he : c.envArg x = true) (hnh : x ∉ c.hidden) :
    (c.env a).lookup x = (c.env b).lookup x :=
  envIn_lookup_agree ta c.args c.argRegs x (argRegs_nodup c)
    (fun _ hr => List.mem_cons_of_mem _ hr) (fun _ _ hr => hr) (fun _ _ _ h => h) he hnh

theorem traceAgree_symm {c : Contract} {defs : List Def} {a b : State} (ta : c.traceAgree defs a b) :
    c.traceAgree defs b a := by
  obtain ⟨hrip, hdata, htr, hrsp, hback, hclean, hreg, hfix, hexpr⟩ := ta
  refine ⟨hrip.symm, hdata.symm, htr.symm, hrsp.symm, hback.symm, fun r hr => (hclean r hr).symm,
    fun r l hm hnh => ?_, fun x r n hm hnh k hk => (hfix x r n hm hnh k hk).symm,
    fun e he v => (hexpr e he v).symm⟩
  obtain ⟨hl, hb⟩ := hreg r l hm hnh
  exact ⟨hl.symm, fun k hk => (hb k (hl ▸ hk)).symm⟩

theorem traceClean_imp {c : Contract} {defs : List Def} {a b : State} (ta : c.traceAgree defs a b) :
    ∀ (e : SExpr) (ext : List (String × Val)),
    traceCleanWith c (ext.map Prod.fst) e = true →
    ExprImp defs (ext ++ c.env a) (ext ++ c.env b) e e := by
  intro e
  induction e with
  | num n =>
    intro ext _
    exact ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
      cases f with | zero => cases hf | succ f => exact ⟨1, by simpa [evalSpec] using hf⟩
  | nil =>
    intro ext _
    exact ⟨fun _ ⟨f, hf⟩ => by cases f <;> simp [evalSpec] at hf,
      fun _ _ hl => by simp only [evalList, Option.some.injEq] at hl; subst hl; exact ⟨0, rfl⟩⟩
  | cons a1 r1 iha ihr =>
    intro ext htc
    unfold traceCleanWith at htc
    simp only [isExpr, Bool.false_and, Bool.false_eq_true, if_false, Bool.and_eq_true] at htc
    exact ExprImp.cons (iha ext htc.1) (ihr ext htc.2)
  | name x =>
    intro ext htc
    unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next =>
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at htc
      exact ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
        cases f with
        | zero => cases hf
        | succ f =>
          simp only [evalSpec] at hf
          rcases htc with hbd | ⟨he, hnh⟩
          · rw [lookup_append_mem hbd] at hf
            exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
          · cases hbd : (ext.map Prod.fst).contains x with
            | true =>
              rw [lookup_append_mem hbd] at hf
              exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
            | false =>
              rw [lookup_append_not_mem hbd] at hf
              have hnot : x ∉ c.hidden := fun hm => by
                have := List.contains_iff_mem.mpr hm
                simp_all
              rw [env_lookup_agree ta he hnot] at hf
              exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hbd]; exact hf⟩
  | bin op a1 b1 iha ihb =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next =>
      simp only [Bool.and_eq_true] at htc
      exact ExprImp.bin (iha ext htc.1) (ihb ext htc.2)
  | ifx cond a1 b1 ihc iha ihb =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next =>
      simp only [Bool.and_eq_true] at htc
      exact ExprImp.ifx (ihc ext htc.1.1) (iha ext htc.1.2) (ihb ext htc.2)
  | index a1 i1 iha ihi =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next =>
      simp only [Bool.and_eq_true] at htc
      exact ExprImp.index (iha ext htc.1) (ihi ext htc.2)
  | call fn args iha =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next => exact ExprImp.call (iha ext htc)
  | list items ihi =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next => exact ExprImp.list (ihi ext htc)
  | letx x r1 b1 ihr ihb =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next =>
      simp only [Bool.and_eq_true] at htc
      exact ExprImp.letx (ihr ext htc.1) (fun w => ihb ((x, w) :: ext) htc.2)
  | each body x a1 b1 ihb iha ihhi =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next =>
      simp only [Bool.and_eq_true] at htc
      exact ExprImp.each (iha ext htc.1.1) (ihhi ext htc.1.2) (fun i => ihb ((x, .int i) :: ext) htc.2)
  | slice a1 lo1 hi1 iha ihlo ihhi =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next =>
      simp only [Bool.and_eq_true] at htc
      exact ExprImp.slice (iha ext htc.1.1) (ihlo ext htc.1.2) (ihhi ext htc.2)
  | withx a1 p1 iha ihp =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next =>
      simp only [Bool.and_eq_true] at htc
      exact ExprImp.withx (iha ext htc.1) (ihp ext htc.2)
  | record ns items ihi =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next => exact ExprImp.record (ihi ext htc)
  | field e1 fn ihe =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next => exact ExprImp.field (ihe ext htc)
  | theNumber g x a1 b1 cond iha ihb ihc =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next =>
      simp only [Bool.and_eq_true] at htc
      exact ExprImp.theNumber (iha ext htc.1.1) (ihb ext htc.1.2) (fun i => ihc ((x, .int i) :: ext) htc.2)
  | thePower g x cond ihc =>
    intro ext htc; unfold traceCleanWith at htc
    split at htc
    next htop =>
      simp only [isExpr, Bool.true_and, Bool.and_eq_true, List.isEmpty_iff, List.map_eq_nil_iff, List.any_eq_true, beq_iff_eq] at htop
      obtain ⟨rfl, e', he', heq⟩ := htop; subst heq
      exact ExprImp.of_val rfl fun v hv => (ta.2.2.2.2.2.2.2.2 _ he' v).mp hv
    next => exact ExprImp.thePower (fun i => ihc ((x, .int i) :: ext) htc)

/-- Any expression allowed by `Contract.traceClean` takes the exact same `Value` in any two entry
states satisfying `Contract.traceAgree`. -/
theorem traceClean_same {c : Contract} {defs : List Def} {a b : State} (ta : c.traceAgree defs a b)
    {e : SExpr} (htc : c.traceClean e = true) (v : Val) :
    Value defs (c.env a) e v ↔ Value defs (c.env b) e v :=
  ⟨(traceClean_imp ta e [] htc).1 v, (traceClean_imp (traceAgree_symm ta) e [] htc).1 v⟩

/-! ## Callee expression agreement (`callExprClean` and `callQuiet_traceAgree`) -/

/-- A byte of a read-only region of `ctx.contract` is left unchanged by `afterCall` and by the caller's execution. -/
theorem afterCall_region_byte {ctx : Ctx} {p q : Program} {s0 st : State} (E : Setting ctx p s0)
    {ρ : Nat → Int} {s : Sym} (H : Holds ctx s0 ρ s st) {c : Contract} {i : Instr}
    (hl : callLink i = c.link) (h8 : c.slot ≤ st.reg RSP)
    (hw : allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true)
    {b0 l0 k : Nat} (hm : (b0, l0) ∈ ctx.contract.regions) (hk : k < s0.reg l0) :
    (afterCall p q i st).mem (s0.reg b0 + k) = s0.mem (s0.reg b0 + k) := by
  obtain ⟨_, r2⟩ := E.regionAt hm
  have hnf : ctx.contract.inFrame s0 (s0.reg b0 + k) = false := notFrame (by omega)
  have hno : ctx.contract.inOut s0 (s0.reg b0 + k) = false := E.region_notOut hm (by omega) (by omega)
  have hnot : s0.reg b0 + k < st.reg RSP - c.slot ∨ st.reg RSP ≤ s0.reg b0 + k := by
    by_cases h1 : s0.reg b0 + k < st.reg RSP - c.slot
    · exact Or.inl h1
    · by_cases h2 : st.reg RSP ≤ s0.reg b0 + k
      · exact Or.inr h2
      · exfalso
        have := allowed_at hw (s0.reg b0 + k) (by omega) (by omega)
        simp [Contract.perm, hnf, hno] at this
  rw [afterCall_mem hl h8 hnot, H.mem _ hnf hno]

theorem callArgClean_agree {ctx : Ctx} {p q : Program} {a0 b0 sta stb : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0)
    {ρa ρb : Nat → Int} {s : Sym}
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb)
    (Ma : MarksOk ctx a0 s.q sta) (A : Alike sta stb)
    {c : Contract} {i : Instr} (Fa : Fits ctx sta i c) (Fb : Fits ctx stb i c)
    (h8a : c.slot ≤ sta.reg RSP) (h8b : c.slot ≤ stb.reg RSP)
    (hwa : allowed (ctx.contract.perm ctx.pieces a0).write (sta.reg RSP - c.slot) c.slot = true)
    (hwb : allowed (ctx.contract.perm ctx.pieces b0).write (stb.reg RSP - c.slot) c.slot = true) :
    ∀ (args : List (String × Kind)) (regs : List Nat) (x : String),
    (∀ r ∈ regs, r ∈ c.argRegs) →
    callArgClean.go ctx s c x args regs = true →
    (envIn c (afterCall p q i sta) args regs).lookup x = (envIn c (afterCall p q i stb) args regs).lookup x
  | [], _, _, _, h => by simp [callArgClean.go] at h
  | _ :: _, [], _, _, h => by simp [callArgClean.go] at h
  | (n, k) :: args, r :: regs, x, hregs, h => by
    have hr_in : r ∈ c.argRegs := hregs r (List.mem_cons_self ..)
    have hregs' : ∀ r' ∈ regs, r' ∈ c.argRegs := fun r' hm => hregs r' (List.mem_cons_of_mem _ hm)
    obtain ⟨ra16, rak⟩ := Fa.arg hr_in
    obtain ⟨rb16, rbk⟩ := Fb.arg hr_in
    cases k with
    | number =>
      simp only [envIn, List.lookup_cons]
      cases hxn : (x == n) with
      | true =>
        simp only [callArgClean.go, str_beq_comm n x, hxn, ite_true] at h
        have hmk : sta.marks.reg r = false := Ma.reg r (List.contains_iff_mem.mp h)
        simp only [hxn]
        rw [afterCall_reg Fa.link rak, afterCall_reg Fb.link rbk, A.reg r hmk]
      | false =>
        simp only [callArgClean.go, str_beq_comm n x, hxn, Bool.false_eq_true, ite_false] at h
        exact callArgClean_agree Ea Eb ta Ha Hb Ma A Fa Fb h8a h8b hwa hwb args regs x hregs' h
    | bytes len =>
      cases hl : c.regOf len with
      | none =>
        simp only [envIn, hl]
        simp only [callArgClean.go] at h
        cases hnx : (n == x) with
        | true => simp [hnx, hl] at h
        | false => simp only [hnx, Bool.false_eq_true, ite_false] at h; exact callArgClean_agree Ea Eb ta Ha Hb Ma A Fa Fb h8a h8b hwa hwb args regs x hregs' h
      | some l =>
        simp only [envIn, hl, List.lookup_cons]
        cases hxn : (x == n) with
        | true =>
          simp only [callArgClean.go, str_beq_comm n x, hxn, ite_true, hl, Bool.and_eq_true] at h
          obtain ⟨hlq, hfind⟩ := h
          cases hf : findRun s r l ctx.contract.regions 0 with
          | none => simp [hf] at hfind
          | some j =>
            obtain ⟨b0r, l0r, _, hget, er, el⟩ := findRun_spec hf
            have hnh0 : ctx.contract.hiddenAt b0r = false := by
              rw [hf] at hfind; simp only at hfind
              have hget' : ctx.contract.regions[j]? = some (b0r, l0r) := by simpa using hget
              rw [hget'] at hfind; simpa using hfind
            have hmem : (b0r, l0r) ∈ ctx.contract.regions := List.mem_of_getElem? hget
            obtain ⟨hb0, hl0⟩ := regions_lt hmem
            have hl_in : l ∈ c.argRegs := regOfIn_mem len c.args c.argRegs l hl
            obtain ⟨la16, lak⟩ := Fa.arg hl_in
            obtain ⟨lb16, lbk⟩ := Fb.arg hl_in
            have vra : sta.reg r = a0.reg b0r := by have := Ha.reg r ra16; rw [er, ev_var, Ha.entry b0r hb0] at this; omega
            have vla : sta.reg l = a0.reg l0r := by have := Ha.reg l la16; rw [el, ev_var, Ha.entry l0r hl0] at this; omega
            have vrb : stb.reg r = b0.reg b0r := by have := Hb.reg r rb16; rw [er, ev_var, Hb.entry b0r hb0] at this; omega
            have vlb : stb.reg l = b0.reg l0r := by have := Hb.reg l lb16; rw [el, ev_var, Hb.entry l0r hl0] at this; omega
            obtain ⟨hlen, hbytes⟩ := ta.2.2.2.2.2.2.1 b0r l0r hmem hnh0
            simp only [hxn]
            congr 2
            rw [afterCall_reg Fa.link lak, afterCall_reg Fb.link lbk, vla, vlb, hlen]
            apply List.map_congr_left
            intro k hk
            have hk' : k < a0.reg l0r := by rw [hlen]; exact List.mem_range.mp hk
            rw [afterCall_reg Fa.link rak, afterCall_reg Fb.link rbk, vra, vrb]
            rw [afterCall_region_byte Ea Ha Fa.link h8a hwa hmem hk',
                afterCall_region_byte Eb Hb Fb.link h8b hwb hmem (hlen ▸ hk'), hbytes k hk']
        | false =>
          simp only [callArgClean.go, str_beq_comm n x, hxn, Bool.false_eq_true, ite_false] at h
          exact callArgClean_agree Ea Eb ta Ha Hb Ma A Fa Fb h8a h8b hwa hwb args regs x hregs' h
    | out _ | fixed _ | inout _ | valArray _ _ =>
      simp only [envIn]
      simp only [callArgClean.go] at h
      exact callArgClean_agree Ea Eb ta Ha Hb Ma A Fa Fb h8a h8b hwa hwb args regs x hregs' h

theorem callAllClean_imp {ctx : Ctx} {p q : Program} {a0 b0 sta stb : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0)
    {ρa ρb : Nat → Int} {s : Sym}
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb)
    (Ma : MarksOk ctx a0 s.q sta) (A : Alike sta stb)
    {c : Contract} {i : Instr} (Fa : Fits ctx sta i c) (Fb : Fits ctx stb i c)
    (h8a : c.slot ≤ sta.reg RSP) (h8b : c.slot ≤ stb.reg RSP)
    (hwa : allowed (ctx.contract.perm ctx.pieces a0).write (sta.reg RSP - c.slot) c.slot = true)
    (hwb : allowed (ctx.contract.perm ctx.pieces b0).write (stb.reg RSP - c.slot) c.slot = true) :
    ∀ (e : SExpr) (ext : List (String × Val)),
    callAllClean ctx s c (ext.map Prod.fst) e = true →
    ExprImp ctx.defs (ext ++ c.env (afterCall p q i sta)) (ext ++ c.env (afterCall p q i stb)) e e := by
  intro e
  induction e with
  | num _ =>
    intro ext _
    exact ExprImp.of_val rfl fun v ⟨f, hf⟩ => by cases f with | zero => cases hf | succ f => exact ⟨1, by simpa [evalSpec] using hf⟩
  | nil =>
    intro ext _
    exact ⟨fun _ ⟨f, hf⟩ => by cases f <;> simp [evalSpec] at hf,
      fun _ _ hl => by simp only [evalList, Option.some.injEq] at hl; subst hl; exact ⟨0, rfl⟩⟩
  | cons a1 r1 iha ihr =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.cons (iha ext h.1) (ihr ext h.2)
  | name x =>
    intro ext h
    simp only [callAllClean, Bool.or_eq_true] at h
    exact ExprImp.of_val rfl fun v ⟨f, hf⟩ => by
      cases f with
      | zero => cases hf
      | succ f =>
        simp only [evalSpec] at hf
        rcases h with hbd | hcl
        · rw [lookup_append_mem hbd] at hf
          exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
        · cases hbd : (ext.map Prod.fst).contains x with
          | true =>
            rw [lookup_append_mem hbd] at hf
            exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
          | false =>
            rw [lookup_append_not_mem hbd] at hf
            unfold Contract.env at hf
            rw [callArgClean_agree Ea Eb ta Ha Hb Ma A Fa Fb h8a h8b hwa hwb c.args c.argRegs x (fun _ hm => hm) hcl] at hf
            exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hbd, Contract.env]; exact hf⟩
  | bin op a1 b1 iha ihb =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.bin (iha ext h.1) (ihb ext h.2)
  | ifx cond a1 b1 ihc iha ihb =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.ifx (ihc ext h.1.1) (iha ext h.1.2) (ihb ext h.2)
  | index a1 i1 iha ihi =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.index (iha ext h.1) (ihi ext h.2)
  | call fn args iha =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.call (iha ext h)
  | list items ihi =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.list (ihi ext h)
  | letx x r1 b1 ihr ihb =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.letx (ihr ext h.1) (fun w => ihb ((x, w) :: ext) h.2)
  | each body x a1 b1 ihb iha ihhi =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.each (iha ext h.1.1) (ihhi ext h.1.2) (fun i => ihb ((x, .int i) :: ext) h.2)
  | slice a1 lo1 hi1 iha ihlo ihhi =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.slice (iha ext h.1.1) (ihlo ext h.1.2) (ihhi ext h.2)
  | withx a1 p1 iha ihp =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.withx (iha ext h.1) (ihp ext h.2)
  | record ns items ihi =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.record (ihi ext h)
  | field e1 fn ihe =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.field (ihe ext h)
  | theNumber g x a1 b1 cond iha ihb ihc =>
    intro ext h; simp only [callAllClean, Bool.and_eq_true] at h
    exact ExprImp.theNumber (iha ext h.1.1) (ihb ext h.1.2) (fun i => ihc ((x, .int i) :: ext) h.2)
  | thePower g x cond ihc =>
    intro ext h; simp only [callAllClean] at h
    exact ExprImp.thePower (fun i => ihc ((x, .int i) :: ext) h)

/-- Helper: `callerNumName.go` returns a name not in `seen` whose lookup in `envIn` is `.int (s0.reg r0)`. -/
theorem callerNumName_spec {c : Contract} {s0 : State} {r0 : Nat} :
    ∀ (seen : List String) (args : List (String × Kind)) (regs : List Nat) (y : String),
    callerNumName.go r0 seen args regs = some y →
    seen.contains y = false ∧ (envIn c s0 args regs).lookup y = some (.int (s0.reg r0))
  | _, [], _, _, h => by simp [callerNumName.go] at h
  | _, _ :: _, [], _, h => by simp [callerNumName.go] at h
  | seen, (x, k) :: args, r :: regs, y, h => by
    cases k with
    | number =>
      simp only [callerNumName.go] at h
      split at h
      next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
        injection h with h; subst h
        exact ⟨hc.2, by simp [envIn, hc.1]⟩
      next hc =>
        obtain ⟨hs, hl⟩ := callerNumName_spec (x :: seen) args regs y h
        simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
        exact ⟨hs.2, by simp only [envIn, List.lookup_cons, beq_false_of_ne hs.1]; exact hl⟩
    | bytes len =>
      simp only [callerNumName.go] at h
      obtain ⟨hs, hl⟩ := callerNumName_spec (x :: seen) args regs y h
      simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
      refine ⟨hs.2, ?_⟩
      simp only [envIn]
      cases c.regOf len with
      | none => exact hl
      | some _ => simp only [List.lookup_cons, beq_false_of_ne hs.1]; exact hl
    | out _ | fixed _ | inout _ | valArray _ _ =>
      simp only [callerNumName.go] at h
      obtain ⟨hs, hl⟩ := callerNumName_spec (x :: seen) args regs y h
      simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
      exact ⟨hs.2, by simp only [envIn]; exact hl⟩

/-- Helper: `callerRegionName.go` returns a name not in `seen` whose lookup in `envIn` matches `regionsIn[j - k]?`. -/
theorem callerRegionName_spec {c : Contract} {s0 : State} {j : Nat} :
    ∀ (seen : List String) (args : List (String × Kind)) (regs : List Nat) (k : Nat) (y : String),
    callerRegionName.go c j seen args regs k = some y →
    seen.contains y = false ∧
    ∃ b0 l0, (regionsIn c args regs)[j - k]? = some (b0, l0) ∧ k ≤ j ∧
      (envIn c s0 args regs).lookup y = some (.bytes ((List.range (s0.reg l0)).map fun t => (s0.mem (s0.reg b0 + t)).val))
  | _, [], _, _, _, h => by simp [callerRegionName.go] at h
  | _, _ :: _, [], _, _, h => by simp [callerRegionName.go] at h
  | seen, (x, kind) :: args, r :: regs, k, y, h => by
    cases kind with
    | bytes len =>
      simp only [callerRegionName.go] at h
      cases hrl : c.regOf len with
      | none =>
        rw [hrl] at h
        obtain ⟨hs, b0, l0, hget, hle, hl⟩ := callerRegionName_spec (x :: seen) args regs k y h
        simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
        exact ⟨hs.2, b0, l0, by simpa [regionsIn, hrl] using hget, hle, by simpa [envIn, hrl] using hl⟩
      | some l =>
        simp only [hrl] at h
        split at h
        next hc =>
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
          injection h with h; subst h
          have hjk : j - k = 0 := by omega
          refine ⟨hc.2, r, l, ?_, by omega, by simp [envIn, hrl]⟩
          simp [regionsIn, hrl, hjk]
        next hc =>
          obtain ⟨hs, b0, l0, hget, hle, hl⟩ := callerRegionName_spec (x :: seen) args regs (k + 1) y h
          simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
          refine ⟨hs.2, b0, l0, ?_, by omega, ?_⟩
          · have hsub : j - k = (j - (k + 1)) + 1 := by omega
            simp only [regionsIn, hrl, hsub, List.getElem?_cons_succ]
            exact hget
          · simp only [envIn, hrl, List.lookup_cons, beq_false_of_ne hs.1]
            exact hl
    | number =>
      simp only [callerRegionName.go] at h
      obtain ⟨hs, b0, l0, hget, hle, hl⟩ := callerRegionName_spec (x :: seen) args regs k y h
      simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
      exact ⟨hs.2, b0, l0, by simpa [regionsIn] using hget, hle,
        by simp only [envIn, List.lookup_cons, beq_false_of_ne hs.1]; exact hl⟩
    | out _ | fixed _ | inout _ | valArray _ _ =>
      simp only [callerRegionName.go] at h
      obtain ⟨hs, b0, l0, hget, hle, hl⟩ := callerRegionName_spec (x :: seen) args regs k y h
      simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
      exact ⟨hs.2, b0, l0, by simpa [regionsIn] using hget, hle, by simpa [envIn] using hl⟩

theorem findSome?_range_some {n : Nat} {α : Type} {f : Nat → Option α} {v : α}
    (h : (List.range n).findSome? f = some v) : ∃ r0, r0 < n ∧ f r0 = some v := by
  obtain ⟨r0, hr, hf⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨r0, List.mem_range.mp hr, hf⟩

theorem callArgExpr_spec {ctx : Ctx} {p q : Program} {s0 st : State} (E : Setting ctx p s0)
    {ρ : Nat → Int} {s : Sym} (H : Holds ctx s0 ρ s st)
    {c : Contract} {i : Instr} (F : Fits ctx st i c) (h8 : c.slot ≤ st.reg RSP)
    (hw : allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true) :
    ∀ (args : List (String × Kind)) (regs : List Nat) (x : String) (e' : SExpr),
    (∀ r ∈ regs, r ∈ c.argRegs) →
    callArgExpr.go ctx s c x args regs = some e' →
    ∃ v, (envIn c (afterCall p q i st) args regs).lookup x = some v ∧
      ((∃ k, e' = .num k ∧ 0 ≤ k ∧ v = .int k) ∨
       (∃ y, e' = .name y ∧ (ctx.contract.env s0).lookup y = some v))
  | [], _, _, _, _, h => by simp [callArgExpr.go] at h
  | _ :: _, [], _, _, _, h => by simp [callArgExpr.go] at h
  | (n, k) :: args, r :: regs, x, e', hregs, h => by
    have hr_in : r ∈ c.argRegs := hregs r (List.mem_cons_self ..)
    have hregs' : ∀ r' ∈ regs, r' ∈ c.argRegs := fun r' hm => hregs r' (List.mem_cons_of_mem _ hm)
    obtain ⟨r16, rk⟩ := F.arg hr_in
    cases k with
    | number =>
      simp only [envIn, List.lookup_cons]
      cases hxn : (x == n) with
      | true =>
        simp only [callArgExpr.go, str_beq_comm n x, hxn, ite_true] at h
        cases hc : Lin.isConst (s.reg r) with
        | some k =>
          simp only [hc] at h
          split at h
          next hk =>
            injection h with h; subst h
            have ev := ev_isConst (ρ := ρ) hc
            have vr := H.reg r r16
            have hval : ((afterCall p q i st).reg r : Int) = k := by rw [afterCall_reg F.link rk]; omega
            exact ⟨.int ((afterCall p q i st).reg r), by simp [hxn], Or.inl ⟨k, rfl, hk, by rw [hval]⟩⟩
          next => cases h
        | none =>
          simp only [hc] at h
          obtain ⟨r0, hr0, hf⟩ := findSome?_range_some h
          split at hf
          next heq =>
            have heq : s.reg r = Lin.var r0 := beq_iff_eq.mp heq
            cases hn : callerNumName ctx.contract r0 with
            | none => simp [hn] at hf
            | some y =>
              simp only [hn, Option.map_some, Option.some.injEq] at hf
              subst hf
              obtain ⟨_, hl⟩ := callerNumName_spec [] ctx.contract.args ctx.contract.argRegs y hn
              have vr : (afterCall p q i st).reg r = s0.reg r0 := by
                rw [afterCall_reg F.link rk]
                have h1 := H.reg r r16
                rw [heq, ev_var, H.entry r0 hr0] at h1
                omega
              exact ⟨.int ((afterCall p q i st).reg r), by simp [hxn], Or.inr ⟨y, rfl, by rw [vr]; exact hl⟩⟩
          next => cases hf
      | false =>
        simp only [callArgExpr.go, str_beq_comm n x, hxn, Bool.false_eq_true, ite_false] at h
        exact callArgExpr_spec E H F h8 hw args regs x e' hregs' h
    | bytes len =>
      cases hrl : c.regOf len with
      | none =>
        simp only [envIn, hrl]
        simp only [callArgExpr.go] at h
        cases hnx : (n == x) with
        | true => simp [hnx, hrl] at h
        | false => simp only [hnx, Bool.false_eq_true, ite_false] at h; exact callArgExpr_spec E H F h8 hw args regs x e' hregs' h
      | some l =>
        simp only [envIn, hrl, List.lookup_cons]
        cases hxn : (x == n) with
        | true =>
          simp only [callArgExpr.go, str_beq_comm n x, hxn, ite_true, hrl] at h
          cases hf : findRun s r l ctx.contract.regions 0 with
          | none => simp [hf] at h
          | some j =>
            rw [hf] at h
            obtain ⟨b0, l0, _, hget, er, el⟩ := findRun_spec hf
            cases hn : callerRegionName ctx.contract j with
            | none => simp [hn] at h
            | some y =>
              simp only [hn, Option.map_some, Option.some.injEq] at h
              subst h
              obtain ⟨_, b0', l0', hget', _, hl⟩ := callerRegionName_spec [] ctx.contract.args ctx.contract.argRegs 0 y hn
              have hget0 : ctx.contract.regions[j]? = some (b0', l0') := by simpa [Contract.regions] using hget'
              have heq_bl : (b0, l0) = (b0', l0') := by
                have h1 : ctx.contract.regions[j]? = some (b0, l0) := by simpa using hget
                rw [h1] at hget0; exact Option.some.inj hget0
              injection heq_bl with eb0 el0
              subst eb0 el0
              have hmem : (b0, l0) ∈ ctx.contract.regions := List.mem_of_getElem? hget
              obtain ⟨hb0, hl0⟩ := regions_lt hmem
              have hl_in : l ∈ c.argRegs := regOfIn_mem len c.args c.argRegs l hrl
              obtain ⟨l16, lk⟩ := F.arg hl_in
              have vr : (afterCall p q i st).reg r = s0.reg b0 := by
                rw [afterCall_reg F.link rk]; have := H.reg r r16; rw [er, ev_var, H.entry b0 hb0] at this; omega
              have vl : (afterCall p q i st).reg l = s0.reg l0 := by
                rw [afterCall_reg F.link lk]; have := H.reg l l16; rw [el, ev_var, H.entry l0 hl0] at this; omega
              have hbytes : ((List.range ((afterCall p q i st).reg l)).map fun t => ((afterCall p q i st).mem ((afterCall p q i st).reg r + t)).val) =
                  (List.range (s0.reg l0)).map fun t => (s0.mem (s0.reg b0 + t)).val := by
                rw [vr, vl]
                apply List.map_congr_left
                intro t ht
                rw [afterCall_region_byte E H F.link h8 hw hmem (List.mem_range.mp ht)]
              exact ⟨.bytes ((List.range ((afterCall p q i st).reg l)).map fun t => ((afterCall p q i st).mem ((afterCall p q i st).reg r + t)).val),
                by simp [hxn], Or.inr ⟨y, rfl, by rw [hbytes]; exact hl⟩⟩
        | false =>
          simp only [callArgExpr.go, str_beq_comm n x, hxn, Bool.false_eq_true, ite_false] at h
          exact callArgExpr_spec E H F h8 hw args regs x e' hregs' h
    | out _ | fixed _ | inout _ | valArray _ _ =>
      simp only [envIn]
      simp only [callArgExpr.go] at h
      exact callArgExpr_spec E H F h8 hw args regs x e' hregs' h

/-- Substitution by `substCallExpr` preserves `Value` in BOTH directions between the callee's entry
environment and the caller's entry environment. -/
theorem substCallExpr_equiv {ctx : Ctx} {p q : Program} {s0 st : State} (E : Setting ctx p s0)
    {ρ : Nat → Int} {s : Sym} (H : Holds ctx s0 ρ s st)
    {c : Contract} {i : Instr} (F : Fits ctx st i c) (h8 : c.slot ≤ st.reg RSP)
    (hw : allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true) :
    ∀ (e : SExpr) (ext : List (String × Val)) {e' : SExpr},
    substCallExpr ctx s c (ext.map Prod.fst) e = some e' →
    ExprImp ctx.defs (ext ++ c.env (afterCall p q i st)) (ext ++ ctx.contract.env s0) e e' ∧
    ExprImp ctx.defs (ext ++ ctx.contract.env s0) (ext ++ c.env (afterCall p q i st)) e' e := by
  intro e
  induction e with
  | num n =>
    intro ext e' h; simp only [substCallExpr, Option.some.injEq] at h; subst h
    refine ⟨ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_, ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_⟩
    · cases f with | zero => cases hf | succ f => exact ⟨1, by simpa [evalSpec] using hf⟩
    · cases f with | zero => cases hf | succ f => exact ⟨1, by simpa [evalSpec] using hf⟩
  | nil =>
    intro ext e' h; simp only [substCallExpr, Option.some.injEq] at h; subst h
    refine ⟨⟨fun _ ⟨f, hf⟩ => by cases f <;> simp [evalSpec] at hf,
             fun _ _ hl => ⟨0, by simpa [evalList] using hl⟩⟩,
            ⟨fun _ ⟨f, hf⟩ => by cases f <;> simp [evalSpec] at hf,
             fun _ _ hl => ⟨0, by simpa [evalList] using hl⟩⟩⟩
  | cons a1 r1 iha ihr =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, r2, hr, rfl⟩ := h
    obtain ⟨ha1, ha2⟩ := iha ext ha
    obtain ⟨hr1, hr2⟩ := ihr ext hr
    exact ⟨ExprImp.cons ha1 hr1, ExprImp.cons ha2 hr2⟩
  | name x =>
    intro ext e' h
    simp only [substCallExpr] at h
    cases hbd : (ext.map Prod.fst).contains x with
    | true =>
      simp only [hbd, ite_true, Option.some.injEq] at h; subst h
      refine ⟨ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_, ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_⟩
      · cases f with | zero => cases hf | succ f =>
        simp only [evalSpec, lookup_append_mem hbd] at hf
        exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
      · cases f with | zero => cases hf | succ f =>
        simp only [evalSpec, lookup_append_mem hbd] at hf
        exact ⟨1, by simp only [evalSpec, lookup_append_mem hbd]; exact hf⟩
    | false =>
      simp only [hbd, Bool.false_eq_true, ite_false] at h
      cases harg : callArgExpr ctx s c x with
      | none => simp [harg] at h
      | some ex =>
        simp only [harg] at h
        obtain ⟨v0, hv0, hcase⟩ := callArgExpr_spec (q := q) E H F h8 hw c.args c.argRegs x ex (fun _ hm => hm) harg
        rcases hcase with ⟨k, rfl, hk, rfl⟩ | ⟨y, rfl, hy⟩
        · injection h with h; subst h
          refine ⟨ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_, ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_⟩
          · cases f with | zero => cases hf | succ f =>
            simp only [evalSpec, lookup_append_not_mem hbd, Contract.env, hv0, Option.some.injEq] at hf
            subst hf; exact ⟨1, by simp [evalSpec, hk]⟩
          · cases f with | zero => cases hf | succ f =>
            simp only [evalSpec, hk, ite_true, Option.some.injEq] at hf
            subst hf; exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hbd, Contract.env, hv0]⟩
        · simp only at h
          cases hby : (ext.map Prod.fst).contains y with
          | true => simp only [hby, ite_true] at h; cases h
          | false =>
            simp only [hby, Bool.false_eq_true, ite_false, Option.some.injEq] at h; subst h
            refine ⟨ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_, ExprImp.of_val rfl fun v ⟨f, hf⟩ => ?_⟩
            · cases f with | zero => cases hf | succ f =>
              simp only [evalSpec, lookup_append_not_mem hbd, Contract.env, hv0, Option.some.injEq] at hf
              subst hf; exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hby, hy]⟩
            · cases f with | zero => cases hf | succ f =>
              simp only [evalSpec, lookup_append_not_mem hby, hy, Option.some.injEq] at hf
              subst hf; exact ⟨1, by simp only [evalSpec, lookup_append_not_mem hbd, Contract.env, hv0]⟩
  | bin op a1 b1 iha ihb =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, b2, hb, rfl⟩ := h
    exact ⟨ExprImp.bin (iha ext ha).1 (ihb ext hb).1, ExprImp.bin (iha ext ha).2 (ihb ext hb).2⟩
  | ifx c1 a1 b1 ihc iha ihb =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨c2, hc, a2, ha, b2, hb, rfl⟩ := h
    exact ⟨ExprImp.ifx (ihc ext hc).1 (iha ext ha).1 (ihb ext hb).1, ExprImp.ifx (ihc ext hc).2 (iha ext ha).2 (ihb ext hb).2⟩
  | index a1 i1 iha ihi =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, i2, hi, rfl⟩ := h
    exact ⟨ExprImp.index (iha ext ha).1 (ihi ext hi).1, ExprImp.index (iha ext ha).2 (ihi ext hi).2⟩
  | call fn args iha =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, rfl⟩ := h
    exact ⟨ExprImp.call (iha ext ha).1, ExprImp.call (iha ext ha).2⟩
  | list items ihi =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨i2, hi, rfl⟩ := h
    exact ⟨ExprImp.list (ihi ext hi).1, ExprImp.list (ihi ext hi).2⟩
  | letx x r1 b1 ihr ihb =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨r2, hr, b2, hb, rfl⟩ := h
    exact ⟨ExprImp.letx (ihr ext hr).1 (fun w => (ihb ((x, w) :: ext) hb).1),
           ExprImp.letx (ihr ext hr).2 (fun w => (ihb ((x, w) :: ext) hb).2)⟩
  | each body x a1 b1 ihb iha ihhi =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨body2, hbd, a2, ha, b2, hb, rfl⟩ := h
    exact ⟨ExprImp.each (iha ext ha).1 (ihhi ext hb).1 (fun i => (ihb ((x, .int i) :: ext) hbd).1),
           ExprImp.each (iha ext ha).2 (ihhi ext hb).2 (fun i => (ihb ((x, .int i) :: ext) hbd).2)⟩
  | slice a1 lo1 hi1 iha ihlo ihhi =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, lo2, hlo, hi2, hhi, rfl⟩ := h
    exact ⟨ExprImp.slice (iha ext ha).1 (ihlo ext hlo).1 (ihhi ext hhi).1,
           ExprImp.slice (iha ext ha).2 (ihlo ext hlo).2 (ihhi ext hhi).2⟩
  | withx a1 p1 iha ihp =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, p2, hp, rfl⟩ := h
    exact ⟨ExprImp.withx (iha ext ha).1 (ihp ext hp).1, ExprImp.withx (iha ext ha).2 (ihp ext hp).2⟩
  | record ns items ihi =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨i2, hi, rfl⟩ := h
    exact ⟨ExprImp.record (ihi ext hi).1, ExprImp.record (ihi ext hi).2⟩
  | field e1 fn ihe =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨e2, he, rfl⟩ := h
    exact ⟨ExprImp.field (ihe ext he).1, ExprImp.field (ihe ext he).2⟩
  | theNumber g x a1 b1 cond iha ihb ihc =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨a2, ha, b2, hb, c2, hc, rfl⟩ := h
    exact ⟨ExprImp.theNumber (iha ext ha).1 (ihb ext hb).1 (fun i => (ihc ((x, .int i) :: ext) hc).1),
           ExprImp.theNumber (iha ext ha).2 (ihb ext hb).2 (fun i => (ihc ((x, .int i) :: ext) hc).2)⟩
  | thePower g x cond ihc =>
    intro ext e' h
    simp only [substCallExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨c2, hc, rfl⟩ := h
    exact ⟨ExprImp.thePower (fun i => (ihc ((x, .int i) :: ext) hc).1),
           ExprImp.thePower (fun i => (ihc ((x, .int i) :: ext) hc).2)⟩

/-- Any callee expression approved by `callExprClean` takes the exact same `Value` at the call in both runs. -/
theorem callExprClean_same {ctx : Ctx} {p q : Program} {a0 b0 sta stb : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0)
    {ρa ρb : Nat → Int} {s : Sym}
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb)
    (Ma : MarksOk ctx a0 s.q sta) (Mb : MarksOk ctx b0 s.q stb) (A : Alike sta stb)
    {c : Contract} {i : Instr} (Fa : Fits ctx sta i c) (Fb : Fits ctx stb i c)
    (h8a : c.slot ≤ sta.reg RSP) (h8b : c.slot ≤ stb.reg RSP)
    (hwa : allowed (ctx.contract.perm ctx.pieces a0).write (sta.reg RSP - c.slot) c.slot = true)
    (hwb : allowed (ctx.contract.perm ctx.pieces b0).write (stb.reg RSP - c.slot) c.slot = true)
    {e : SExpr} (he : callExprClean ctx s c e = true) (v : Val) :
    Value ctx.defs (c.env (afterCall p q i sta)) e v ↔ Value ctx.defs (c.env (afterCall p q i stb)) e v := by
  simp only [callExprClean, Bool.or_eq_true] at he
  rcases he with hall | hsub
  · have As : Alike stb sta := ⟨A.marks.symm, A.rip.symm, A.data.symm, A.trace.symm,
      fun r hr => (A.reg r (A.marks ▸ hr)).symm, fun h => (A.zf (A.marks ▸ h)).symm,
      fun h => (A.cf (A.marks ▸ h)).symm, fun a ha => (A.mem a (A.marks ▸ ha)).symm,
      fun r hr => (A.low r (A.marks ▸ hr)).symm⟩
    exact ⟨(callAllClean_imp Ea Eb ta Ha Hb Ma A Fa Fb h8a h8b hwa hwb e [] hall).1 v,
           (callAllClean_imp Eb Ea (traceAgree_symm ta) Hb Ha Mb As Fb Fa h8b h8a hwb hwa e [] hall).1 v⟩
  · cases hs : substCallExpr ctx s c [] e with
    | none => rw [hs] at hsub; cases hsub
    | some e' =>
      rw [hs] at hsub
      obtain ⟨ea1, ea2⟩ := substCallExpr_equiv Ea Ha Fa h8a hwa e [] hs
      obtain ⟨eb1, eb2⟩ := substCallExpr_equiv Eb Hb Fb h8b hwb e [] hs
      have hsame := traceClean_same ta hsub v
      exact ⟨fun h => eb2.1 v (hsame.mp (ea1.1 v h)), fun h => ea2.1 v (hsame.mpr (eb1.1 v h))⟩

/-- At a call approved by `callQuiet`, the callee's entry states satisfy `c.traceAgree`. -/
theorem callQuiet_traceAgree {ctx : Ctx} {p q : Program} {a0 b0 sta stb : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0)
    {ρa ρb : Nat → Int} {s : Sym}
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb)
    (Ma : MarksOk ctx a0 s.q sta) (Mb : MarksOk ctx b0 s.q stb) (A : Alike sta stb)
    {c : Contract} {i : Instr} (Fa : Fits ctx sta i c) (Fb : Fits ctx stb i c)
    (h8a : c.slot ≤ sta.reg RSP) (h8b : c.slot ≤ stb.reg RSP)
    (hwa : allowed (ctx.contract.perm ctx.pieces a0).write (sta.reg RSP - c.slot) c.slot = true)
    (hwb : allowed (ctx.contract.perm ctx.pieces b0).write (stb.reg RSP - c.slot) c.slot = true)
    (hwritea : ∀ a, (c.perm ctx.pieces (afterCall p q i sta)).write a = true → (ctx.contract.perm ctx.pieces a0).write a = true)
    (hq : callQuiet ctx s c = true) :
    c.traceAgree ctx.defs (afterCall p q i sta) (afterCall p q i stb) := by
  obtain ⟨hrsp, hqa, _⟩ := callQuiet_sound Ea Ma Ha hq q i Fa hwa hwritea
  have Ac : Alike (afterCall p q i sta) (afterCall p q i stb) :=
    afterCall_alike A (fun _ => hrsp)
  simp only [callQuiet, Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, hrun⟩, htexpr⟩ := hq
  refine ⟨Ac.rip, Ac.data, Ac.trace, Ac.reg RSP (hqa.1 RSP (List.mem_cons_self ..)), ?_,
    fun r hr => Ac.reg r (hqa.1 r hr), fun r l hm hnh => ?_, fun x r n hm hnh k hk => ?_,
    fun e he v => callExprClean_same Ea Eb ta Ha Hb Ma Mb A Fa Fb h8a h8b hwa hwb (List.all_eq_true.mp htexpr e he) v⟩
  · -- `c.backTo`: either LINK register (arm64) or 8 bytes at RSP (x86-64)
    have hbq := hqa.2.1
    unfold Contract.backQuiet at hbq
    unfold Contract.backTo
    cases ha : c.arm64 with
    | true => simp only [ha, ite_true] at hbq ⊢; exact Ac.reg LINK hbq
    | false =>
      simp only [ha, Bool.false_eq_true, ite_false] at hbq ⊢
      rw [Ac.reg RSP (hqa.1 RSP (List.mem_cons_self ..))]
      apply load_same
      intro x hx1 hx2
      have hk : x - (afterCall p q i sta).reg RSP < 8 := by
        rw [Ac.reg RSP (hqa.1 RSP (List.mem_cons_self ..))]; omega
      have hmx := hbq (x - (afterCall p q i sta).reg RSP) hk
      have heq : (afterCall p q i sta).reg RSP + (x - (afterCall p q i sta).reg RSP) = x := by
        rw [Ac.reg RSP (hqa.1 RSP (List.mem_cons_self ..))]; omega
      rw [heq] at hmx
      exact Ac.mem x hmx
  · -- non-hidden read-only region `(r, l)`
    have hfound := List.all_eq_true.mp hrun (r, l) hm
    simp only [hnh, Bool.false_or, Bool.and_eq_true] at hfound
    have hlq : sta.marks.reg l = false := Ma.reg l (List.contains_iff_mem.mp hfound.1)
    have hlen : (afterCall p q i sta).reg l = (afterCall p q i stb).reg l :=
      Ac.reg l (afterCall_marks_reg hlq)
    have hbase : (afterCall p q i sta).reg r = (afterCall p q i stb).reg r :=
      Ac.reg r (hqa.1 r (by
        -- Every region base `r` is in `c.cleanAtEntry`
        have hmem := regions_args hm
        exact List.mem_cons_of_mem _ (by
          -- Direct from `regionsIn` -> `cleanIn`
          clear hfound hlen hlq hrun htexpr hqa Ac hrsp hwa hwb h8a h8b Fa Fb Ma Mb Ha Hb ta Ea Eb
          suffices ∀ args regs, (r, l) ∈ regionsIn c args regs → r ∈ cleanIn c args regs from this c.args c.argRegs hm
          intro args
          induction args with
          | nil => intro regs h; simp [regionsIn] at h
          | cons ak more ih =>
            intro regs h
            cases regs with
            | nil => simp [regionsIn] at h
            | cons r0 rs =>
              obtain ⟨nm, kd⟩ := ak
              cases kd with
              | bytes ln =>
                simp only [regionsIn] at h
                cases hrl : c.regOf ln with
                | none => rw [hrl] at h; exact List.mem_append_right _ (ih rs h)
                | some l0 =>
                  rw [hrl] at h
                  rcases List.mem_cons.mp h with he | ht
                  · injection he with er _; subst er; exact List.mem_append_left _ (List.mem_cons_self ..)
                  · exact List.mem_append_right _ (ih rs ht)
              | number | out _ | fixed _ | inout _ | valArray _ _ =>
                simp only [regionsIn] at h
                exact List.mem_append_right _ (ih rs h))))
    refine ⟨hlen, fun k hk => ?_⟩
    rw [← hbase]
    exact Ac.mem _ (hqa.2.2.1 r l hm hnh k hk)
  · -- non-hidden fixed read-only run `(x, r, n)`
    have hbase : (afterCall p q i sta).reg r = (afterCall p q i stb).reg r :=
      Ac.reg r (hqa.1 r (List.mem_cons_of_mem _ (by
        clear hrun htexpr hqa Ac hrsp hwa hwb h8a h8b Fa Fb Ma Mb Ha Hb ta Ea Eb
        suffices ∀ args regs, (x, r, n) ∈ fixedsIn args regs → r ∈ cleanIn c args regs from this c.args c.argRegs hm
        intro args
        induction args with
        | nil => intro regs h; simp [fixedsIn] at h
        | cons ak more ih =>
          intro regs h
          cases regs with
          | nil => simp [fixedsIn] at h
          | cons r0 rs =>
            obtain ⟨nm, kd⟩ := ak
            cases kd with
            | fixed cnt =>
              simp only [fixedsIn] at h
              rcases List.mem_cons.mp h with he | ht
              · injection he with _ he2; injection he2 with er _; subst er
                exact List.mem_append_left _ (List.mem_cons_self ..)
              · exact List.mem_append_right _ (ih rs ht)
            | number | bytes _ | out _ | inout _ | valArray _ _ =>
              simp only [fixedsIn] at h
              exact List.mem_append_right _ (ih rs h))))
    rw [← hbase]
    exact Ac.mem _ (hqa.2.2.2 x r n hm hnh k hk)

/-! ## Constructing shared entry marks from `traceAgree` (`initMarks`), post-call marks, and `clear` -/

/-- Shared entry marks constructed purely from `c`, `pieces`, and `a0`:
unmarks `cleanAtEntry`, the link register (arm64), read-only `pieces`, the x86-64 return slot,
and all non-hidden read-only regions and fixed runs. -/
def initMarks (c : Contract) (pieces : List Piece) (a0 : State) : Marks where
  reg r := !(c.cleanAtEntry.contains r || (c.link == some r))
  low _ := true
  zf := true
  cf := true
  mem a := !(inPieces pieces a0 a ||
    (!c.arm64 && decide (a0.reg RSP ≤ a) && decide (a < a0.reg RSP + 8)) ||
    c.regions.any (fun (r, l) => !c.hiddenAt r && decide (a0.reg r ≤ a) && decide (a < a0.reg r + a0.reg l)) ||
    c.fixeds.any (fun (x, r, n) => !c.hidden.contains x && decide (a0.reg r ≤ a) && decide (a < a0.reg r + n)))

theorem initMarks_alike {c : Contract} {pieces : List Piece} {defs : List Def} {a0 b0 : State}
    (la : Loaded pieces a0) (lb : Loaded pieces b0) (ta : c.traceAgree defs a0 b0) :
    Alike { a0 with marks := initMarks c pieces a0 } { b0 with marks := initMarks c pieces a0 } := by
  obtain ⟨hrip, hdata, htr, hrsp, hback, hclean, hreg, hfix, _⟩ := ta
  refine ⟨rfl, hrip, hdata, htr, fun r hr => ?_, fun h => by simp [initMarks] at h,
    fun h => by simp [initMarks] at h, fun a ha => ?_, fun _ h => by simp [initMarks] at h⟩
  · simp only [initMarks, Bool.not_eq_false', Bool.or_eq_true, beq_iff_eq] at hr
    rcases hr with hc | hl
    · exact hclean r (List.contains_iff_mem.mp hc)
    · unfold Contract.link at hl
      cases ha : c.arm64 with
      | false => simp [ha] at hl
      | true =>
        simp only [ha, ite_true, Option.some.injEq] at hl; subst hl
        simp only [Contract.backTo, ha, ite_true] at hback
        exact hback
  · simp only [initMarks, Bool.not_eq_false', Bool.or_eq_true] at ha
    rcases ha with ((hp | hslot) | hrg) | hfx
    · obtain ⟨k, pc, hpk, h1, h2⟩ := inPieces_iff.mp hp
      have hk : a - a0.data k < pc.bytes.length := by omega
      have ha1 := (la k pc hpk).2.2 (a - a0.data k) hk
      have hb1 := (lb k pc hpk).2.2 (a - a0.data k) hk
      have heq : a0.data k + (a - a0.data k) = a := by omega
      have hb2 : b0.data k + (a - a0.data k) = a := by rw [← hdata]; exact heq
      rw [heq] at ha1; rw [hb2] at hb1
      exact Fin.ext (ha1.trans hb1.symm)
    · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hslot
      obtain ⟨⟨ha, h1⟩, h2⟩ := hslot
      simp only [Contract.backTo, ha, Bool.false_eq_true, ite_false, hrsp] at hback
      have hbytes := load_eq_bytes 8 (b0.reg RSP) hback (a - b0.reg RSP) (by omega)
      have heq : b0.reg RSP + (a - b0.reg RSP) = a := by omega
      rwa [heq] at hbytes
    · obtain ⟨⟨r, l⟩, hm, hb⟩ := List.any_eq_true.mp hrg
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
      obtain ⟨⟨hnh, h1⟩, h2⟩ := hb
      have hbase : a0.reg r = b0.reg r := hclean r (List.mem_cons_of_mem _ (by
        suffices ∀ args regs, (r, l) ∈ regionsIn c args regs → r ∈ cleanIn c args regs from this c.args c.argRegs hm
        intro args; induction args with
        | nil => intro regs h; simp [regionsIn] at h
        | cons ak more ih =>
          intro regs h; cases regs with | nil => simp [regionsIn] at h | cons r0 rs =>
          obtain ⟨nm, kd⟩ := ak; cases kd with
          | bytes ln =>
            simp only [regionsIn] at h; cases hrl : c.regOf ln with
            | none => rw [hrl] at h; exact List.mem_append_right _ (ih rs h)
            | some l0 =>
              rw [hrl] at h; rcases List.mem_cons.mp h with he | ht
              · injection he with er _; subst er; exact List.mem_append_left _ (List.mem_cons_self ..)
              · exact List.mem_append_right _ (ih rs ht)
          | number | out _ | fixed _ | inout _ | valArray _ _ => simp only [regionsIn] at h; exact List.mem_append_right _ (ih rs h)))
      have hk := (hreg r l hm hnh).2 (a - a0.reg r) (by omega)
      have heq : a0.reg r + (a - a0.reg r) = a := by omega
      rw [← hbase, heq] at hk; exact hk
    · obtain ⟨⟨x, r, n⟩, hm, hb⟩ := List.any_eq_true.mp hfx
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
      obtain ⟨⟨hnh, h1⟩, h2⟩ := hb
      have hnot : x ∉ c.hidden := fun hmem => by
        have : c.hidden.contains x = true := List.contains_iff_mem.mpr hmem
        simp_all
      have hbase : a0.reg r = b0.reg r := hclean r (List.mem_cons_of_mem _ (by
        suffices ∀ args regs, (x, r, n) ∈ fixedsIn args regs → r ∈ cleanIn c args regs from this c.args c.argRegs hm
        intro args; induction args with
        | nil => intro regs h; simp [fixedsIn] at h
        | cons ak more ih =>
          intro regs h; cases regs with | nil => simp [fixedsIn] at h | cons r0 rs =>
          obtain ⟨nm, kd⟩ := ak; cases kd with
          | fixed cnt =>
            simp only [fixedsIn] at h; rcases List.mem_cons.mp h with he | ht
            · injection he with _ he2; injection he2 with er _; subst er; exact List.mem_append_left _ (List.mem_cons_self ..)
            · exact List.mem_append_right _ (ih rs ht)
          | number | bytes _ | out _ | inout _ | valArray _ _ => simp only [fixedsIn] at h; exact List.mem_append_right _ (ih rs h)))
      have hk := hfix x r n hm hnot (a - a0.reg r) (by omega)
      have heq : a0.reg r + (a - a0.reg r) = a := by omega
      rw [← hbase, heq] at hk; exact hk

theorem initMarks_quiet {c : Contract} {pieces : List Piece} {defs : List Def} {a0 b0 : State}
    (ta : c.traceAgree defs a0 b0) :
    c.quietAt { a0 with marks := initMarks c pieces a0 } ∧
    c.quietAt { b0 with marks := initMarks c pieces a0 } := by
  obtain ⟨_, _, _, hrsp, _, hclean, hreg, _, _⟩ := ta
  have q_a : c.quietAt { a0 with marks := initMarks c pieces a0 } := by
    refine ⟨fun r hr => by simp [initMarks, hr], ?_, fun r l hm hnh k hk => ?_, fun x r n hm hnot k hk => ?_⟩
    · unfold Contract.backQuiet
      cases ha : c.arm64 with
      | true => simp [initMarks, Contract.link, ha]
      | false =>
        simp only [ha, Bool.false_eq_true, ite_false]
        intro k hk
        simp only [initMarks, ha, Bool.not_false, Bool.true_and, Bool.not_eq_false', Bool.or_eq_true]
        left; left; right
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩
    · simp only [initMarks, Bool.not_eq_false', Bool.or_eq_true]
      left; right
      exact List.any_eq_true.mpr ⟨(r, l), hm, by
        dsimp only
        simp only [hnh, Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩⟩
    · simp only [initMarks, Bool.not_eq_false', Bool.or_eq_true]
      right
      have hnc : c.hidden.contains x = false := by
        cases hc : c.hidden.contains x with | false => rfl | true => exact absurd (List.contains_iff_mem.mp hc) hnot
      exact List.any_eq_true.mpr ⟨(x, r, n), hm, by
        dsimp only
        simp only [hnc, Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩⟩
  refine ⟨q_a, ⟨q_a.1, ?_, fun r l hm hnh k hk => ?_, fun x r n hm hnot k hk => ?_⟩⟩
  · have hq := q_a.2.1
    unfold Contract.backQuiet at hq ⊢
    cases ha : c.arm64 with
    | true => simpa [ha] using hq
    | false =>
      simp only [ha, Bool.false_eq_true, ite_false] at hq ⊢
      intro k hk; rw [← hrsp]; exact hq k hk
  · have hbase : a0.reg r = b0.reg r := hclean r (List.mem_cons_of_mem _ (by
      suffices ∀ args regs, (r, l) ∈ regionsIn c args regs → r ∈ cleanIn c args regs from this c.args c.argRegs hm
      intro args; induction args with
      | nil => intro regs h; simp [regionsIn] at h
      | cons ak more ih =>
        intro regs h; cases regs with | nil => simp [regionsIn] at h | cons r0 rs =>
        obtain ⟨nm, kd⟩ := ak; cases kd with
        | bytes ln =>
          simp only [regionsIn] at h; cases hrl : c.regOf ln with
          | none => rw [hrl] at h; exact List.mem_append_right _ (ih rs h)
          | some l0 =>
            rw [hrl] at h; rcases List.mem_cons.mp h with he | ht
            · injection he with er _; subst er; exact List.mem_append_left _ (List.mem_cons_self ..)
            · exact List.mem_append_right _ (ih rs ht)
        | number | out _ | fixed _ | inout _ | valArray _ _ => simp only [regionsIn] at h; exact List.mem_append_right _ (ih rs h)))
    have hlen : a0.reg l = b0.reg l := (hreg r l hm hnh).1
    have hka : k < a0.reg l := hlen ▸ hk
    rw [← hbase]; exact q_a.2.2.1 r l hm hnh k hka
  · have hbase : a0.reg r = b0.reg r := hclean r (List.mem_cons_of_mem _ (by
      suffices ∀ args regs, (x, r, n) ∈ fixedsIn args regs → r ∈ cleanIn c args regs from this c.args c.argRegs hm
      intro args; induction args with
      | nil => intro regs h; simp [fixedsIn] at h
      | cons ak more ih =>
        intro regs h; cases regs with | nil => simp [fixedsIn] at h | cons r0 rs =>
        obtain ⟨nm, kd⟩ := ak; cases kd with
        | fixed cnt =>
          simp only [fixedsIn] at h; rcases List.mem_cons.mp h with he | ht
          · injection he with _ he2; injection he2 with er _; subst er; exact List.mem_append_left _ (List.mem_cons_self ..)
          · exact List.mem_append_right _ (ih rs ht)
        | number | bytes _ | out _ | inout _ | valArray _ _ => simp only [fixedsIn] at h; exact List.mem_append_right _ (ih rs h)))
    rw [← hbase]; exact q_a.2.2.2 x r n hm hnot k hk

theorem initMarks_dataQuiet {c : Contract} {pieces : List Piece} {a0 : State} :
    ∀ k pc, pieces[k]? = some pc → ∀ j, j < pc.bytes.length → (initMarks c pieces a0).mem (a0.data k + j) = false := by
  intro k pc hpk j hj
  simp only [initMarks, Bool.not_eq_false', Bool.or_eq_true]
  left; left; left
  exact inPieces_iff.mpr ⟨k, pc, hpk, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩

/-- Post-call marks placed on both returned callee states `s2_a` and `s2_b`: identical on both runs,
unmarking `RSP`, `0` (when `cleanRet = true`), and every memory byte outside callee's frame and outs
that was unmarked at call entry. -/
def postCallMarks (c : Contract) (cleanRet : Bool) (call_a : State) : Marks where
  reg r := !(r == RSP || (cleanRet && r == 0))
  low _ := true
  zf := true
  cf := true
  mem addr := if c.inFrame call_a addr || c.inOut call_a addr then true else call_a.marks.mem addr

/-- Clearing the mark on register `r` in a state. -/
def unmarkReg (st : State) (r : Nat) : State :=
  { st with marks := { st.marks with reg := fun k => if k = r then false else st.marks.reg k } }

theorem unmarkReg_plain (st : State) (r : Nat) : (unmarkReg st r).plain = st.plain := rfl

theorem unmarkReg_alike {a b : State} (A : Alike a b) {r : Nat} (heq : a.reg r = b.reg r) :
    Alike (unmarkReg a r) (unmarkReg b r) := by
  refine ⟨?_, A.rip, A.data, A.trace, fun k hk => ?_, A.zf, A.cf, A.mem, A.low⟩
  · simp only [unmarkReg, A.marks]
  · show a.reg k = b.reg k
    by_cases hkr : k = r
    · subst hkr; exact heq
    · simp only [unmarkReg, hkr, ite_false] at hk
      exact A.reg k hk

/-! ## Unmarked flags have equal operands in both runs (`FlagEq`) -/

def FlagValEq (ρa ρb : Nat → Int) : Flag → Prop
  | .unknown => True
  | .equal x y => ev ρa x = ev ρb x ∧ ev ρa y = ev ρb y
  | .below x y => ev ρa x = ev ρb x ∧ ev ρa y = ev ρb y

structure FlagEq (ρa ρb : Nat → Int) (s : Sym) : Prop where
  zf : s.q.zq = true → FlagValEq ρa ρb s.zf
  cf : s.q.cq = true → FlagValEq ρa ρb s.cf

theorem FlagEq.mono {ρa ρa' ρb ρb' : Nat → Int} {s : Sym} (F : FlagEq ρa ρb s) (wf : WF ctx s)
    (aa : Agree s.nvars ρa ρa') (ab : Agree s.nvars ρb ρb') : FlagEq ρa' ρb' s := by
  refine ⟨fun hz => ?_, fun hc => ?_⟩
  · have h := F.zf hz; have hw := wf.zf
    cases hf : s.zf with
    | unknown => trivial
    | equal x y =>
      rw [hf] at h hw
      exact ⟨by rw [← ev_agree hw.1 aa, ← ev_agree hw.1 ab]; exact h.1,
             by rw [← ev_agree hw.2 aa, ← ev_agree hw.2 ab]; exact h.2⟩
    | below x y =>
      rw [hf] at h hw
      exact ⟨by rw [← ev_agree hw.1 aa, ← ev_agree hw.1 ab]; exact h.1,
             by rw [← ev_agree hw.2 aa, ← ev_agree hw.2 ab]; exact h.2⟩
  · have h := F.cf hc; have hw := wf.cf
    cases hf : s.cf with
    | unknown => trivial
    | equal x y =>
      rw [hf] at h hw
      exact ⟨by rw [← ev_agree hw.1 aa, ← ev_agree hw.1 ab]; exact h.1,
             by rw [← ev_agree hw.2 aa, ← ev_agree hw.2 ab]; exact h.2⟩
    | below x y =>
      rw [hf] at h hw
      exact ⟨by rw [← ev_agree hw.1 aa, ← ev_agree hw.1 ab]; exact h.1,
             by rw [← ev_agree hw.2 aa, ← ev_agree hw.2 ab]; exact h.2⟩

theorem symDivide_flags (s : Sym) (x : Row) (m : Int) :
    (symDivide s x m).2.2.zf = s.zf ∧ (symDivide s x m).2.2.cf = s.cf := by
  unfold symDivide
  cases divided s x m with
  | some _ => exact ⟨rfl, rfl⟩
  | none => exact ⟨rfl, rfl⟩

theorem symLow_flags (s : Sym) (x : Row) (m : Int) :
    (symLow s x m).2.zf = s.zf ∧ (symLow s x m).2.cf = s.cf := by
  unfold symLow
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · exact symDivide_flags s x m

theorem symQuot_flags (s : Sym) (x : Row) (m : Int) :
    (symQuot s x m).2.zf = s.zf ∧ (symQuot s x m).2.cf = s.cf := by
  unfold symQuot
  split
  · exact ⟨rfl, rfl⟩
  · exact symDivide_flags s x m

theorem readByte_flags {ctx : Ctx} {s s1 : Sym} {r : Nat} {o v : Row} {items rest : Items}
    (h : readByte ctx s r o items = .ok ((v, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold readByte at h
  cases hreg : ctx.contract.regions[r]? with
  | none => simp only [hreg] at h; exact (refuse_ok h).elim
  | some _ =>
    simp only [hreg] at h
    obtain ⟨_, _, _, h⟩ := V.bind_ok h
    obtain ⟨_, _, _, h⟩ := V.bind_ok h
    cases hl : lookupByte r o s.bytes with
    | some _ => simp only [hl] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
    | none => simp only [hl] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩

theorem symData_lin {ctx : Ctx} {bind : Bind} {s s1 : Sym} {x : Row} {val : EV} {items rest : Items}
    (h : symData ctx bind s x items = .ok ((val, s1), rest)) : (∃ r, val = .lin r) ∧ s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symData at h
  by_cases hp : pieceOf bind = ctx.piece
  · simp only [hp, ite_true] at h
    cases hc : Lin.isConst x with
    | none => simp only [hc] at h; exact (refuse_ok h).elim
    | some c =>
      simp only [hc] at h
      by_cases hr : 0 ≤ c ∧ c < ctx.data.length
      · simp only [hr, ite_true] at h
        have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩
      · simp only [hr, ite_false] at h; exact (refuse_ok h).elim
  · simp only [hp, ite_false] at h; exact (refuse_ok h).elim

theorem symOn16_lin {ctx : Ctx} {s s1 : Sym} {x : Row} {val : EV} {items rest : Items}
    (h : symOn16 ctx s x items = .ok ((val, s1), rest)) : (∃ r, val = .lin r) ∧ s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symOn16 at h
  cases hc : Lin.isConst (Lin.sub x (Lin.var RSP)) with
  | none => simp only [hc] at h; exact (refuse_ok h).elim
  | some c =>
    simp only [hc] at h
    by_cases ha : (ctx.contract.arm64 && decide (c % 16 = 0)) = true
    · simp only [ha, ite_true] at h
      have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩
    · rw [if_neg ha] at h; exact (refuse_ok h).elim

theorem symPrim1_lin {f : String} {s s1 : Sym} {x : Row} {val : EV} {items rest : Items}
    (h : symPrim1 f s x items = .ok ((val, s1), rest)) : (∃ r, val = .lin r) ∧ s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symPrim1 at h
  by_cases h1 : (f == "low32") = true
  · simp only [h1, ite_true] at h
    have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, symLow_flags s x _⟩
  · rw [if_neg h1] at h
    by_cases h2 : (f == "low8") = true
    · simp only [h2, ite_true] at h
      have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, symLow_flags s x _⟩
    · rw [if_neg h2] at h; exact (refuse_ok h).elim

theorem symLoadFixed_lin {ctx : Ctx} {s s1 : Sym} {addr : Row} {sz : Nat} {val : EV} {items rest : Items}
    (h : symLoadFixed ctx s addr sz items = .ok ((val, s1), rest)) : (∃ r, val = .lin r) ∧ s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symLoadFixed at h
  cases hf : findOut addr ctx.contract.fixeds 0 with
  | none => simp only [hf] at h; exact (refuse_ok h).elim
  | some loc =>
    simp only [hf] at h
    cases loc with
    | frame _ | region _ _ | data _ => exact (refuse_ok h).elim
    | out j off =>
      cases hc : Lin.isConst off with
      | none => simp only [hc] at h; exact (refuse_ok h).elim
      | some c =>
        cases hg : ctx.contract.fixeds[j]? with
        | none => simp only [hc, hg] at h; exact (refuse_ok h).elim
        | some p =>
          obtain ⟨name, _, count⟩ := p
          simp only [hc, hg] at h
          by_cases hsz : sz = 8 ∧ 0 ≤ c ∧ c + 8 ≤ count
          · simp only [hsz, ite_true] at h
            cases hk : knownLoad j c.toNat s.known with
            | some v => simp only [hk] at h; have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩
            | none => simp only [hk] at h; have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩
          · simp only [hsz, ite_false] at h; exact (refuse_ok h).elim

theorem symLoad_lin {ctx : Ctx} {s s1 : Sym} {addr : Row} {sz : Nat} {val : EV} {items rest : Items}
    (h : symLoad ctx s addr sz items = .ok ((val, s1), rest)) : (∃ r, val = .lin r) ∧ s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symLoad at h
  cases hl : locate ctx addr with
  | none => simp only [hl] at h; exact symLoadFixed_lin h
  | some loc =>
    simp only [hl] at h
    cases loc with
    | frame c =>
      dsimp only at h
      by_cases hfr : sz = 8 ∧ inFrame ctx s c = true
      · simp only [hfr, ite_true] at h
        cases hlu : s.frame.lookup c with
        | none => simp only [hlu] at h; exact (refuse_ok (items := items) h).elim
        | some v => simp only [hlu] at h; have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩
      · rw [if_neg hfr] at h; exact (refuse_ok h).elim
    | region r o =>
      dsimp only at h
      by_cases hsz : sz = 1
      · simp only [hsz, ite_true] at h
        obtain ⟨⟨v, s'⟩, _, hr, hp⟩ := V.bind_ok h
        have := V.pure_ok hp; injection this with h _; injection h with h1 h2; subst h1 h2
        exact ⟨⟨_, rfl⟩, readByte_flags hr⟩
      · rw [if_neg hsz] at h; exact (refuse_ok h).elim
    | out _ _ => dsimp only at h; exact (refuse_ok h).elim
    | data c =>
      dsimp only at h
      by_cases hd : (sz = 1 ∨ sz = 4 ∨ sz = 8) ∧ 0 ≤ c ∧ c + sz ≤ ctx.data.length
      · simp only [hd, ite_true] at h
        have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩
      · rw [if_neg hd] at h; exact (refuse_ok h).elim

theorem symOrKnown_lin {s s1 : Sym} {x y : Row} {val : EV} {items rest : Items}
    (h : symOrKnown s x y items = .ok ((val, s1), rest)) : (∃ r, val = .lin r) ∧ s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symOrKnown at h
  cases hk : knownOr x y s.known with
  | some _ => simp only [hk] at h; have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩
  | none => simp only [hk] at h; have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩

theorem symOrSmall_lin {s s1 : Sym} {x : Row} {k : Int} {j : Nat} {val : EV} {items rest : Items}
    (h : symOrSmall s x k j items = .ok ((val, s1), rest)) : (∃ r, val = .lin r) ∧ s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symOrSmall at h
  by_cases hm : k % 2 ^ j = 0
  · simp only [hm, ite_true] at h
    have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩
  · simp only [hm, ite_false] at h
    obtain ⟨⟨u, s'⟩, _, ho, hp⟩ := V.bind_ok h
    have ⟨_, hsf⟩ := symOrKnown_lin ho
    cases u with
    | lin ur => have := V.pure_ok hp; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, hsf⟩
    | equal _ _ | below _ _ => exact (refuse_ok hp).elim

theorem symOr_lin {s s1 : Sym} {x y : Row} {val : EV} {items rest : Items}
    (h : symOr s x y items = .ok ((val, s1), rest)) : (∃ r, val = .lin r) ∧ s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symOr at h
  by_cases hy0 : Lin.isConst y = some 0
  · simp only [hy0, ite_true] at h
    have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩
  · simp only [hy0, ite_false] at h
    by_cases hx0 : Lin.isConst x = some 0
    · simp only [hx0, ite_true] at h
      have := V.pure_ok h; injection this with h _; injection h with h1 h2; subst h1 h2; exact ⟨⟨_, rfl⟩, rfl, rfl⟩
    · simp only [hx0, ite_false] at h
      cases hp1 : orParts s.facts x y with
      | some p => simp only [hp1] at h; exact symOrSmall_lin h
      | none =>
        simp only [hp1] at h
        cases hp2 : orParts s.facts y x with
        | some p => simp only [hp2] at h; exact symOrSmall_lin h
        | none => simp only [hp2] at h; exact symOrKnown_lin h

theorem symPrim_flags {f : String} {s s1 : Sym} {x y : Row} {val : EV} {items rest : Items}
    (h : symPrim f s x y items = .ok ((val, s1), rest)) :
    s1.zf = s.zf ∧ s1.cf = s.cf ∧
    (∀ a b, val = .equal a b → f = "equal" ∧ a = x ∧ b = y ∧ s1 = s) ∧
    (∀ a b, val = .below a b → f = "below" ∧ a = x ∧ b = y ∧ s1 = s) := by
  have ofLin : ∀ (it : Items) (r : Row) (s' : Sym), (pure (EV.lin r, s') : V (EV × Sym)) it = .ok ((val, s1), rest) → s'.zf = s.zf → s'.cf = s.cf →
      s1.zf = s.zf ∧ s1.cf = s.cf ∧
      (∀ a b, val = .equal a b → f = "equal" ∧ a = x ∧ b = y ∧ s1 = s) ∧
      (∀ a b, val = .below a b → f = "below" ∧ a = x ∧ b = y ∧ s1 = s) := by
    intro it r s' hp hz hc
    have := V.pure_ok hp; injection this with hp _; injection hp with h1 h2
    refine ⟨(by rw [h2]; exact hz), (by rw [h2]; exact hc), (fun _ _ he => by rw [h1] at he; cases he), (fun _ _ he => by rw [h1] at he; cases he)⟩
  unfold symPrim at h
  by_cases h1 : (f == "add64" || f == "at") = true
  · simp only [h1, ite_true] at h; obtain ⟨_, _, _, h⟩ := V.bind_ok h; exact ofLin _ _ _ h rfl rfl
  · simp only [h1, ite_false] at h
    by_cases h2 : (f == "sub64") = true
    · simp only [h2, ite_true] at h; obtain ⟨_, _, _, h⟩ := V.bind_ok h; exact ofLin _ _ _ h rfl rfl
    · simp only [h2, ite_false] at h
      by_cases h3 : (f == "equal") = true
      · simp only [h3, ite_true] at h
        have := V.pure_ok h; injection this with hp _; injection hp with hv hs
        refine ⟨(by rw [hs]), (by rw [hs]), (fun a b he => ?_), (fun _ _ he => by rw [hv] at he; cases he)⟩
        rw [hv] at he; injection he with ha hb; exact ⟨beq_iff_eq.mp h3, ha.symm, hb.symm, hs⟩
      · simp only [h3, ite_false] at h
        by_cases h4 : (f == "below") = true
        · simp only [h4, ite_true] at h
          have := V.pure_ok h; injection this with hp _; injection hp with hv hs
          refine ⟨(by rw [hs]), (by rw [hs]), (fun _ _ he => by rw [hv] at he; cases he), (fun a b he => ?_)⟩
          rw [hv] at he; injection he with ha hb; exact ⟨beq_iff_eq.mp h4, ha.symm, hb.symm, hs⟩
        · simp only [h4, ite_false] at h
          by_cases h5 : (f == "shl64") = true
          · simp only [h5, ite_true] at h
            cases hc : Lin.isConst y with
            | none => simp only [hc] at h; exact (refuse_ok (items := items) h).elim
            | some k =>
              simp only [hc] at h
              by_cases hk : 0 ≤ k ∧ k < 64
              · simp only [hk, ite_true] at h
                obtain ⟨kept, _, _, h⟩ := V.bind_ok h
                cases kept with
                | true => simp only [ite_true] at h; exact ofLin _ _ _ h rfl rfl
                | false => simp only [Bool.false_eq_true, ite_false] at h; exact ofLin _ _ _ h (symLow_flags s x _).1 (symLow_flags s x _).2
              · simp only [hk, ite_false] at h; exact (refuse_ok (items := items) h).elim
          · simp only [h5, ite_false] at h
            by_cases h6 : (f == "shr64") = true
            · simp only [h6, ite_true] at h
              cases hc : Lin.isConst y with
              | none => simp only [hc] at h; exact (refuse_ok (items := items) h).elim
              | some k =>
                simp only [hc] at h
                by_cases hk : 0 ≤ k ∧ k < 64
                · simp only [hk, ite_true] at h; exact ofLin _ _ _ h (symDivide_flags s x _).1 (symDivide_flags s x _).2
                · simp only [hk, ite_false] at h; exact (refuse_ok (items := items) h).elim
            · simp only [h6, ite_false] at h
              by_cases h7 : (f == "and64") = true
              · simp only [h7, ite_true] at h
                cases hc : Lin.isConst y with
                | none => simp only [hc] at h; exact (refuse_ok (items := items) h).elim
                | some m =>
                  simp only [hc] at h
                  by_cases hm64 : (m == 2 ^ 64 - 64) = true
                  · simp only [hm64, ite_true] at h; exact ofLin _ _ _ h (symDivide_flags s x 64).1 (symDivide_flags s x 64).2
                  · simp only [hm64, ite_false] at h
                    cases hf : (List.range 65).find? (fun k => (2 : Int) ^ k - 1 == m) with
                    | none => simp only [hf] at h; exact (refuse_ok (items := items) h).elim
                    | some k => simp only [hf] at h; exact ofLin _ _ _ h (symDivide_flags s x _).1 (symDivide_flags s x _).2
              · simp only [h7, ite_false] at h
                by_cases h8 : (f == "sub8") = true
                · simp only [h8, ite_true] at h
                  have f1 := symLow_flags s y 256
                  have f2 := symLow_flags (symLow s y 256).2 (Lin.sub (Lin.add x (Lin.const 256)) (symLow s y 256).1) 256
                  exact ofLin _ _ _ h (f2.1.trans f1.1) (f2.2.trans f1.2)
                · simp only [h8, ite_false] at h
                  by_cases h9 : (f == "setlow8") = true
                  · simp only [h9, ite_true] at h
                    have f1 := symQuot_flags s x 256
                    have f2 := symLow_flags (symQuot s x 256).2 y 256
                    exact ofLin _ _ _ h (f2.1.trans f1.1) (f2.2.trans f1.2)
                  · simp only [h9, ite_false] at h; exact (refuse_ok (items := items) h).elim

theorem symValue_flags {ctx : Ctx} (bind : Bind) :
    ∀ (v : Expr) {s s1 : Sym} {val : EV} {items rest : Items},
    symValue ctx bind s v items = .ok ((val, s1), rest) → s1.zf = s.zf ∧ s1.cf = s.cf
  | .number _, s, s1, _, _, _, h => by
    simp only [symValue] at h
    split at h
    · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
    · exact (refuse_ok h).elim
  | .lane _ _, _, _, _, _, _, h => by simp only [symValue] at h; exact (refuse_ok h).elim
  | .name n, s, s1, _, _, _, h => by
    simp only [symValue] at h
    split at h
    · cases h1 : (bind.lookup n).bind readInt with
      | none => simp only [h1] at h; exact (refuse_ok h).elim
      | some _ => simp only [h1] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
    · cases h1 : ctx.regOf bind n with
      | none => simp only [h1] at h; exact (refuse_ok h).elim
      | some _ => simp only [h1] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
  | .call _ [], _, _, _, _, _, h => by simp only [symValue] at h; exact (refuse_ok h).elim
  | .call f [e1], s, s1, _, _, _, h => by
    simp only [symValue] at h
    obtain ⟨⟨ev1, sa⟩, _, h1, h2⟩ := V.bind_ok h
    have ih1 := symValue_flags bind e1 h1
    cases ev1 with
    | equal _ _ | below _ _ => exact (refuse_ok h2).elim
    | lin _ =>
      have h2f : s1.zf = sa.zf ∧ s1.cf = sa.cf := by
        by_cases hd : (f == "data") = true
        · simp only [hd, ite_true] at h2; exact (symData_lin h2).2
        · simp only [hd, ite_false] at h2
          by_cases ho : (f == "on16") = true
          · simp only [ho, ite_true] at h2; exact (symOn16_lin h2).2
          · simp only [ho, ite_false] at h2; exact (symPrim1_lin h2).2
      exact ⟨h2f.1.trans ih1.1, h2f.2.trans ih1.2⟩
  | .call f [e1, e2], s, s1, _, _, _, h => by
    simp only [symValue] at h
    obtain ⟨⟨ev1, sa1⟩, _, h1, h⟩ := V.bind_ok h
    obtain ⟨⟨ev2, sa2⟩, _, h2, h⟩ := V.bind_ok h
    have ih1 := symValue_flags bind e1 h1
    have ih2 := symValue_flags bind e2 h2
    cases ev1 with
    | equal _ _ | below _ _ => exact (refuse_ok h).elim
    | lin x1 =>
      cases ev2 with
      | equal _ _ | below _ _ => exact (refuse_ok h).elim
      | lin x2 =>
        have h3f : s1.zf = sa2.zf ∧ s1.cf = sa2.cf := by
          cases hms : memSize f with
          | some sz => simp only [hms] at h; exact (symLoad_lin h).2
          | none =>
            simp only [hms] at h
            by_cases hor : (f == "or64") = true
            · simp only [hor, ite_true] at h; exact (symOr_lin h).2
            · simp only [hor, ite_false] at h; have := symPrim_flags h; exact ⟨this.1, this.2.1⟩
        exact ⟨h3f.1.trans (ih2.1.trans ih1.1), h3f.2.trans (ih2.2.trans ih1.2)⟩
  | .call _ (_ :: _ :: _ :: _), _, _, _, _, _, h => by simp only [symValue] at h; exact (refuse_ok h).elim

theorem symValue_flag_operands {ctx : Ctx} {p : Program} {a0 b0 sta stb : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (bind : Bind) {s s1 : Sym} {v : Expr} {val : EV} {items rest : Items}
    {ρa ρb : Nat → Int}
    (hsv : symValue ctx bind s v items = .ok ((val, s1), rest))
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb) (wf : WF ctx s)
    (Ma : MarksOk ctx a0 s.q sta) (A : Alike sta stb)
    (hm : markOf ctx bind s s1 v = some false) :
    ∀ {x y : Row}, (val = .equal x y ∨ val = .below x y) →
    ∃ ρa' ρb' xa xb,
      Carried ctx a0 ρa s ρa' s1 sta ∧ Carried ctx b0 ρb s ρb' s1 stb ∧
      value (ctx.contract.perm ctx.pieces a0) bind sta v = some xa ∧
      value (ctx.contract.perm ctx.pieces b0) bind stb v = some xb ∧
      EV.sem ρa' s1.nvars xa val ∧ EV.sem ρb' s1.nvars xb val ∧
      ev ρa' x = ev ρb' x ∧ ev ρa' y = ev ρb' y := by
  intro x y he
  have notLin : (∃ r, val = .lin r) → False := fun ⟨r, hr⟩ => by
    rcases he with h1 | h1 <;> rw [hr] at h1 <;> cases h1
  cases v with
  | number _ =>
    simp only [symValue] at hsv
    split at hsv
    · have := V.pure_ok hsv; injection this with h _; injection h with h _; exact (notLin ⟨_, h⟩).elim
    · exact (refuse_ok hsv).elim
  | lane _ _ => simp only [symValue] at hsv; exact (refuse_ok hsv).elim
  | name n =>
    simp only [symValue] at hsv
    split at hsv
    · cases h1 : (bind.lookup n).bind readInt with
      | none => simp only [h1] at hsv; exact (refuse_ok hsv).elim
      | some _ => simp only [h1] at hsv; have := V.pure_ok hsv; injection this with h _; injection h with h _; exact (notLin ⟨_, h⟩).elim
    · cases h1 : ctx.regOf bind n with
      | none => simp only [h1] at hsv; exact (refuse_ok hsv).elim
      | some _ => simp only [h1] at hsv; have := V.pure_ok hsv; injection this with h _; injection h with h _; exact (notLin ⟨_, h⟩).elim
  | call f args =>
    cases args with
    | nil => simp only [symValue] at hsv; exact (refuse_ok hsv).elim
    | cons e1 rest1 =>
      cases rest1 with
      | nil =>
        simp only [symValue] at hsv
        obtain ⟨⟨ev1, sa⟩, _, _, h2⟩ := V.bind_ok hsv
        cases ev1 with
        | equal _ _ | below _ _ => exact (refuse_ok h2).elim
        | lin _ =>
          by_cases hd : (f == "data") = true
          · simp only [hd, ite_true] at h2; exact (notLin (symData_lin h2).1).elim
          · simp only [hd, ite_false] at h2
            by_cases ho : (f == "on16") = true
            · simp only [ho, ite_true] at h2; exact (notLin (symOn16_lin h2).1).elim
            · simp only [ho, ite_false] at h2; exact (notLin (symPrim1_lin h2).1).elim
      | cons e2 rest2 =>
        cases rest2 with
        | cons _ _ => simp only [symValue] at hsv; exact (refuse_ok hsv).elim
        | nil =>
          simp only [symValue] at hsv
          obtain ⟨⟨ev1, sa1⟩, r1, hsv1, hsv⟩ := V.bind_ok hsv
          obtain ⟨⟨ev2, sa2⟩, r2, hsv2, hsv⟩ := V.bind_ok hsv
          cases ev1 with
          | equal _ _ | below _ _ => exact (refuse_ok hsv).elim
          | lin x1 =>
            cases ev2 with
            | equal _ _ | below _ _ => exact (refuse_ok hsv).elim
            | lin x2 =>
              have hfb : ((f = "equal" ∧ val = .equal x1 x2) ∨ (f = "below" ∧ val = .below x1 x2)) ∧ x = x1 ∧ y = x2 ∧ s1 = sa2 := by
                cases hms : memSize f with
                | some sz => simp only [hms] at hsv; exact (notLin (symLoad_lin hsv).1).elim
                | none =>
                  simp only [hms] at hsv
                  by_cases hor : (f == "or64") = true
                  · simp only [hor, ite_true] at hsv; exact (notLin (symOr_lin hsv).1).elim
                  · simp only [hor, ite_false] at hsv
                    obtain ⟨_, _, heq, hbl⟩ := symPrim_flags hsv
                    rcases he with h3 | h3
                    · obtain ⟨hf, ex, ey, es⟩ := heq x y h3; subst ex ey; exact ⟨Or.inl ⟨hf, h3⟩, rfl, rfl, es⟩
                    · obtain ⟨hf, ex, ey, es⟩ := hbl x y h3; subst ex ey; exact ⟨Or.inr ⟨hf, h3⟩, rfl, rfl, es⟩
              obtain ⟨hfeb, rfl, rfl, es1⟩ := hfb
              subst s1
              have hlo : lowOnly bind f [e1, e2] = none := by
                rcases hfeb with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [lowOnly]
              have hmw : (memWidth f).isSome = false := by
                rcases hfeb with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
              simp only [markOf, hlo, hmw, Bool.false_eq_true, ite_false, marksOf] at hm
              cases hm1 : markOf ctx bind s sa2 e1 with
              | none => simp [hm1] at hm
              | some b1 =>
                cases hm2 : markOf ctx bind s sa2 e2 with
                | none => simp [hm1, hm2] at hm
                | some b2 =>
                  simp only [hm1, hm2, Option.some.injEq, Bool.or_eq_false_iff] at hm
                  obtain ⟨rfl, rfl, _⟩ := hm
                  obtain ⟨ρa1, va1, ca1, hve1a, va1lt, eva1, bda1⟩ := symValue_sound Ea bind e1 hsv1 Ha wf
                  obtain ⟨ρa2, va2, ca2, hve2a, va2lt, eva2, bda2⟩ := symValue_sound Ea bind e2 hsv2 ca1.holds ca1.wf
                  obtain ⟨ρb1, vb1, cb1, hve1b, vb1lt, evb1, bdb1⟩ := symValue_sound Eb bind e1 hsv1 Hb wf
                  obtain ⟨ρb2, vb2, cb2, hve2b, vb2lt, evb2, bdb2⟩ := symValue_sound Eb bind e2 hsv2 cb1.holds cb1.wf
                  have ca := ca1.then ca2
                  have cb := cb1.then cb2
                  obtain ⟨aq1, em1⟩ := markOf_sound Ea Ma Ha wf ca e1 hm1
                  obtain ⟨aq2, em2⟩ := markOf_sound Ea Ma Ha wf ca e2 hm2
                  have hv1eq := (expr_alike A e1 aq1).2.2.2 (em1 rfl)
                  have hv2eq := (expr_alike A e2 aq2).2.2.2 (em2 rfl)
                  have h1 : va1 = vb1 := by
                    have h1a := value_all e1 hve1a
                    have h1b := value_all e1 hve1b
                    rw [hv1eq, h1b] at h1a
                    exact (Option.some.inj h1a).symm
                  have h2 : va2 = vb2 := by
                    have h2a := value_all e2 hve2a
                    have h2b := value_all e2 hve2b
                    rw [hv2eq, h2b] at h2a
                    exact (Option.some.inj h2a).symm
                  have eva1' : (va1 : Int) = ev ρa2 x := by rw [← ev_agree bda1 ca2.agree]; exact eva1
                  have evb1' : (vb1 : Int) = ev ρb2 x := by rw [← ev_agree bdb1 cb2.agree]; exact evb1
                  have bda1' : bounded sa2.nvars x := bounded_mono ca2.mono bda1
                  have eqx : ev ρa2 x = ev ρb2 x := by rw [← eva1', ← evb1', h1]
                  have eqy : ev ρa2 y = ev ρb2 y := by rw [← eva2, ← evb2, h2]
                  rcases hfeb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · refine ⟨ρa2, ρb2, if va1 = va2 then 1 else 0, if vb1 = vb2 then 1 else 0, ca, cb, ?_, ?_, ?_, ?_, eqx, eqy⟩
                    · simp only [value, values, hve1a, hve2a, memSize, prim, Nat.mod_eq_of_lt va1lt, Nat.mod_eq_of_lt va2lt]; by_cases h : va1 = va2 <;> simp [h]
                    · simp only [value, values, hve1b, hve2b, memSize, prim, Nat.mod_eq_of_lt vb1lt, Nat.mod_eq_of_lt vb2lt]; by_cases h : vb1 = vb2 <;> simp [h]
                    · exact ⟨by by_cases h : va1 = va2 <;> simp [h, ← eva1', ← eva2]; omega, bda1', bda2⟩
                    · exact ⟨by by_cases h : vb1 = vb2 <;> simp [h, ← evb1', ← evb2]; omega, bda1', bda2⟩
                  · refine ⟨ρa2, ρb2, if va1 < va2 then 1 else 0, if vb1 < vb2 then 1 else 0, ca, cb, ?_, ?_, ?_, ?_, eqx, eqy⟩
                    · simp only [value, values, hve1a, hve2a, memSize, prim, Nat.mod_eq_of_lt va1lt, Nat.mod_eq_of_lt va2lt]; by_cases h : va1 < va2 <;> simp [h]
                    · simp only [value, values, hve1b, hve2b, memSize, prim, Nat.mod_eq_of_lt vb1lt, Nat.mod_eq_of_lt vb2lt]; by_cases h : vb1 < vb2 <;> simp [h]
                    · exact ⟨by by_cases h : va1 < va2 <;> simp [h, ← eva1', ← eva2], bda1', bda2⟩
                    · exact ⟨by by_cases h : vb1 < vb2 <;> simp [h, ← evb1', ← evb2], bda1', bda2⟩

/-! ## Flag preservation across non-flag statements and `settle` -/

theorem symLoadWords_flags {ctx : Ctx} {s s1 : Sym} {addr : Row} {w : Nat} {l : List Nat} {items rest : Items}
    (h : symLoadWords ctx s addr w items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  have hval : ∀ {bytes badSize : String},
      (match findValArray addr ctx.contract.valArrays 0 with
       | some (k, _, _, l0, ch, el, c) =>
         let i := c.toNat / el
         if 0 < ch ∧ 0 < el ∧ el % 4 = 0 ∧ c.toNat + 4 * w ≤ el * (i + 1) then do
           entail s.facts (Lin.sub (Lin.var l0) (Lin.const ((i + 1) * ch)))
           let j := ctx.contract.fixeds.length + ctx.contract.inouts.length + ctx.contract.regions.length + k
           let made := termsOf intern ((List.range w).map fun m => Node.input j (c.toNat / 4 + m)) s.tab
           pure (made.1, { s with tab := made.2 })
         else refuse badSize
       | none => refuse s!"{bytes} bytes that are of no run of words given to read") items = .ok ((l, s1), rest) →
      s1.zf = s.zf ∧ s1.cf = s.cf := by
    intro bytes badSize h'
    cases hfv : findValArray addr ctx.contract.valArrays 0 with
    | none => simp only [hfv] at h'; exact (refuse_ok (items := items) h').elim
    | some found =>
      obtain ⟨k, _, _, l0, ch, el, c⟩ := found
      simp only [hfv] at h'
      split at h'
      · obtain ⟨_, _, _, h'⟩ := V.bind_ok h'
        have := V.pure_ok h'; injection this with h' _; injection h' with _ h'; subst h'; exact ⟨rfl, rfl⟩
      · exact (refuse_ok (items := items) h').elim
  have hframe : ∀ {bytes badSize : String},
      (match Lin.isConst (Lin.sub addr (Lin.var RSP)), s.sp with
       | some o, some sp =>
         if sp ≤ o ∧ o + 4 * (w : Int) ≤ 0 then
           match (if w % 2 = 0 then framePairRows s o (w / 2) else none) with
           | some rows => let made := termsOf wAtom rows s.tab; pure (made.1, { s with tab := made.2 })
           | none =>
             match frameWIds s.frameW o w 0 with
             | some ids => pure (ids, s)
             | none => refuse s!"{bytes} bytes of the frame that are not known words"
         else refuse s!"{bytes} bytes that are of no run of words given to read"
       | _, _ =>
         match findValArray addr ctx.contract.valArrays 0 with
         | some (k, _, _, l0, ch, el, c) =>
           let i := c.toNat / el
           if 0 < ch ∧ 0 < el ∧ el % 4 = 0 ∧ c.toNat + 4 * w ≤ el * (i + 1) then do
             entail s.facts (Lin.sub (Lin.var l0) (Lin.const ((i + 1) * ch)))
             let j := ctx.contract.fixeds.length + ctx.contract.inouts.length + ctx.contract.regions.length + k
             let made := termsOf intern ((List.range w).map fun m => Node.input j (c.toNat / 4 + m)) s.tab
             pure (made.1, { s with tab := made.2 })
           else refuse badSize
         | none => refuse s!"{bytes} bytes that are of no run of words given to read") items = .ok ((l, s1), rest) →
      s1.zf = s.zf ∧ s1.cf = s.cf := by
    intro bytes badSize h'
    cases hc : Lin.isConst (Lin.sub addr (Lin.var RSP)) with
    | none => simp only [hc] at h'; exact hval h'
    | some o =>
      cases hsp : s.sp with
      | none => simp only [hc, hsp] at h'; exact hval h'
      | some sp =>
        simp only [hc, hsp] at h'
        split at h'
        · cases hpr : (if w % 2 = 0 then framePairRows s o (w / 2) else none) <;> simp only [hpr] at h'
          · cases hfw : frameWIds s.frameW o w 0 <;> simp only [hfw] at h'
            · exact (refuse_ok (items := items) h').elim
            · have := V.pure_ok h'; injection this with h' _; injection h' with _ h'; subst h'; exact ⟨rfl, rfl⟩
          · have := V.pure_ok h'; injection this with h' _; injection h' with _ h'; subst h'; exact ⟨rfl, rfl⟩
        · exact (refuse_ok (items := items) h').elim
  unfold symLoadWords at h
  cases hf : findOut addr ctx.contract.fixeds 0 with
  | some loc =>
    simp only [hf] at h
    cases loc with
    | out j off =>
      dsimp only at h
      cases hc : Lin.isConst off <;> simp only [hc] at h
      · exact (refuse_ok (items := items) h).elim
      · cases hg : ctx.contract.fixeds[j]? <;> simp only [hg] at h
        · exact (refuse_ok (items := items) h).elim
        · split at h
          · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
          · exact (refuse_ok (items := items) h).elim
    | frame _ | region _ _ | data _ =>
      dsimp only at h
      cases hf2 : findOut addr ctx.contract.outs 0 <;> simp only [hf2] at h
      · exact hframe h
      · rename_i loc2; cases loc2 with
        | frame _ | region _ _ | data _ => dsimp only at h; exact hframe h
        | out w0 off =>
          dsimp only at h
          cases hc : Lin.isConst off <;> simp only [hc] at h
          · exact (refuse_ok (items := items) h).elim
          · cases hg : ctx.contract.outs[w0]? <;> simp only [hg] at h
            · exact (refuse_ok (items := items) h).elim
            · rename_i p0; obtain ⟨_, r0, _⟩ := p0
              cases hr : runAt r0 (ctx.contract.fixeds ++ ctx.contract.inouts) 0 <;> simp only [hr] at h
              · exact (refuse_ok (items := items) h).elim
              · rename_i j0; cases hj : (ctx.contract.fixeds ++ ctx.contract.inouts)[j0]? <;> simp only [hj] at h
                · exact (refuse_ok (items := items) h).elim
                · split at h
                  · exact (refuse_ok (items := items) h).elim
                  · split at h
                    · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
                    · exact (refuse_ok (items := items) h).elim
  | none =>
    simp only [hf] at h
    cases hf2 : findOut addr ctx.contract.outs 0 <;> simp only [hf2] at h
    · exact hframe h
    · rename_i loc2; cases loc2 with
      | frame _ | region _ _ | data _ => dsimp only at h; exact hframe h
      | out w0 off =>
        dsimp only at h
        cases hc : Lin.isConst off <;> simp only [hc] at h
        · exact (refuse_ok (items := items) h).elim
        · cases hg : ctx.contract.outs[w0]? <;> simp only [hg] at h
          · exact (refuse_ok (items := items) h).elim
          · rename_i p0; obtain ⟨_, r0, _⟩ := p0
            cases hr : runAt r0 (ctx.contract.fixeds ++ ctx.contract.inouts) 0 <;> simp only [hr] at h
            · exact (refuse_ok (items := items) h).elim
            · rename_i j0; cases hj : (ctx.contract.fixeds ++ ctx.contract.inouts)[j0]? <;> simp only [hj] at h
              · exact (refuse_ok (items := items) h).elim
              · split at h
                · exact (refuse_ok (items := items) h).elim
                · split at h
                  · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
                  · exact (refuse_ok (items := items) h).elim

theorem symMemWords_flags {ctx : Ctx} {bind : Bind} {s s1 : Sym} {args : List Expr} {w : Nat} {l : List Nat} {items rest : Items}
    (h : symMemWords ctx bind s args w items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symMemWords at h
  cases ha : symWordAddr ctx bind s args <;> simp only [ha] at h
  · exact (refuse_ok (items := items) h).elim
  · exact symLoadWords_flags h

theorem symHalves_flags {s s1 : Sym} {x : Row} {l : List Nat} {items rest : Items}
    (h : symHalves s x items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symHalves at h
  by_cases h1 : (Lin.high x == Lin.const 0 && (Lin.isConst x).isNone) = true
  · simp only [h1, ite_true] at h
    have := V.pure_ok h; injection this with h _; injection h with _ h; subst h
    exact symDivide_flags s x W32i
  · simp only [h1, ite_false] at h
    by_cases h2 : (Lin.isConst (Lin.word x)).isNone = true
    · simp only [h2, ite_true] at h
      obtain ⟨_, _, _, h⟩ := V.bind_ok h; obtain ⟨_, _, _, h⟩ := V.bind_ok h
      have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
    · simp only [h2, ite_false] at h
      have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩

theorem symEach32_flags {bind : Bind} {s s1 : Sym} {args : List Expr} {l : List Nat} {items rest : Items}
    (h : symEach32 bind s args items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symEach32 at h
  rcases args with _ | ⟨e1, _ | ⟨a, _ | ⟨b, _ | _⟩⟩⟩
  · exact (refuse_ok (items := items) h).elim
  · exact (refuse_ok (items := items) h).elim
  · exact (refuse_ok (items := items) h).elim
  · cases e1 with
    | number _ | lane _ _ | call _ _ => exact (refuse_ok (items := items) h).elim
    | name op =>
      dsimp only at h
      cases hx : symVec bind s a with
      | none => simp only [hx] at h; exact (refuse_ok (items := items) h).elim
      | some xv =>
        simp only [hx] at h
        cases hy : symVec bind s b with
        | none =>
          simp only [hy] at h
          cases hn : symNumber bind b with
          | none => simp only [hn] at h; exact (refuse_ok (items := items) h).elim
          | some nv =>
            simp only [hn] at h
            by_cases h1 : (op == "ror32") = true
            · simp only [h1, ite_true] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
            · simp only [h1, ite_false] at h
              by_cases h2 : (op == "shl32") = true
              · simp only [h2, ite_true] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
              · simp only [h2, ite_false] at h
                by_cases h3 : (op == "shr32") = true
                · simp only [h3, ite_true] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
                · simp only [h3, ite_false] at h; exact (refuse_ok (items := items) h).elim
        | some yv =>
          simp only [hy] at h
          by_cases h1 : (op == "add32") = true
          · simp only [h1, ite_true] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
          · simp only [h1, ite_false] at h
            by_cases h2 : (op == "xor32") = true
            · simp only [h2, ite_true] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
            · simp only [h2, ite_false] at h
              by_cases h3 : (op == "or32") = true
              · simp only [h3, ite_true] at h
                cases ho : orTurns s.terms (xv.zip yv) <;> simp only [ho] at h
                · exact (refuse_ok (items := items) h).elim
                · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
              · simp only [h3, ite_false] at h; exact (refuse_ok (items := items) h).elim
  · exact (refuse_ok (items := items) h).elim

theorem symShuffle_flags {bind : Bind} {s s1 : Sym} {args : List Expr} {l : List Nat} {items rest : Items}
    (h : symShuffle bind s args items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symShuffle at h
  rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · exact (refuse_ok (items := items) h).elim
  · exact (refuse_ok (items := items) h).elim
  · dsimp only at h
    cases hx : symVec bind s a with
    | none => simp only [hx] at h; exact (refuse_ok (items := items) h).elim
    | some xv =>
      simp only [hx] at h
      cases hy : symVec bind s b with
      | none => simp only [hy] at h; exact (refuse_ok (items := items) h).elim
      | some yv =>
        simp only [hy] at h
        cases hc : (constWords s.terms yv).bind shuffleTurn <;> simp only [hc] at h
        · exact (refuse_ok (items := items) h).elim
        · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
  · exact (refuse_ok (items := items) h).elim

theorem symLanes_flags {ctx : Ctx} {bind : Bind} {s s1 : Sym} {v : Expr} {l : List Nat} {items rest : Items}
    (h : symLanes ctx bind s v items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  cases v with
  | number _ | lane _ _ => simp only [symLanes] at h; exact (refuse_ok (items := items) h).elim
  | name n =>
    simp only [symLanes] at h
    cases hv : symVec bind s (.name n) <;> simp only [hv] at h
    · exact (refuse_ok (items := items) h).elim
    · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
  | call f args =>
    simp only [symLanes] at h
    cases h1 : (f == "mem128")
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      cases h2 : (f == "words")
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
        cases h3 : (f == "lanes_of64")
        · simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
          cases h4 : (f == "lanes")
          · simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
            cases h5 : (f == "each32")
            · simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
              cases h6 : (f == "shuffle_bytes")
              · simp only [h6, Bool.false_eq_true, ↓reduceIte] at h
                unfold symMoved at h
                rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨i, _ | _⟩⟩⟩
                all_goals try (simp only at h; exact (refuse_ok (items := items) h).elim)
                dsimp only at h
                cases hx : symVec bind s a <;> cases hy : symVec bind s b <;> cases hi : symNumber bind i <;> simp only [hx, hy, hi] at h
                all_goals try exact (refuse_ok (items := items) h).elim
                cases hp : (f == "pick4")
                · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
                  cases hb : (f == "blend4")
                  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
                    cases hh : (f == "blend_halves")
                    · simp only [hh, Bool.false_eq_true, ↓reduceIte] at h; exact (refuse_ok (items := items) h).elim
                    · simp only [hh, ↓reduceIte] at h
                      split at h
                      · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
                      · exact (refuse_ok (items := items) h).elim
                  · simp only [hb, ↓reduceIte] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
                · simp only [hp, ↓reduceIte] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
              · simp only [h6, ↓reduceIte] at h; exact symShuffle_flags h
            · simp only [h5, ↓reduceIte] at h; exact symEach32_flags h
          · simp only [h4, ↓reduceIte] at h
            rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | _⟩⟩⟩⟩
            all_goals first
              | (simp only at h; exact (refuse_ok (items := items) h).elim)
              | (dsimp only at h
                 cases ha : symLane bind s a <;> cases hb : symLane bind s b <;> cases hc : symLane bind s c <;> cases hd : symLane bind s d <;> simp only [ha, hb, hc, hd] at h
                 all_goals first
                   | exact (refuse_ok (items := items) h).elim
                   | (have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩))
        · simp only [h3, ↓reduceIte] at h
          rcases args with _ | ⟨a, _ | _⟩
          · simp only at h; exact (refuse_ok (items := items) h).elim
          · dsimp only at h
            cases hr : symReg ctx bind s a <;> simp only [hr] at h
            · exact (refuse_ok (items := items) h).elim
            · exact symHalves_flags h
          · simp only at h; exact (refuse_ok (items := items) h).elim
      · simp only [h2, ↓reduceIte] at h
        rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | _⟩⟩⟩⟩
        all_goals first
          | (simp only at h; exact (refuse_ok (items := items) h).elim)
          | (dsimp only at h; cases hka : symNumber bind a <;> cases hkb : symNumber bind b <;> cases hkc : symNumber bind c <;> cases hkd : symNumber bind d <;> simp only [hka, hkb, hkc, hkd] at h
             all_goals first | exact (refuse_ok (items := items) h).elim | (have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩))
    · simp only [h1, ↓reduceIte] at h; exact symMemWords_flags h

theorem symLaneTerms_flags {α : Type} {s s1 : Sym} {mk : α → Tab → Nat × Tab} {xs : List α} {l : List Nat} {items rest : Items}
    (h : symLaneTerms s mk xs items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symLaneTerms at h
  have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩

theorem symSpreadScalar16_flags {ctx : Ctx} {bind : Bind} {s s1 : Sym} {a : Expr} {l : List Nat} {items rest : Items}
    (h : symSpreadScalar16 ctx bind s a items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symSpreadScalar16 at h
  obtain ⟨⟨v, sa⟩, _, hv, h⟩ := V.bind_ok h
  have h1 := symValue_flags bind a hv
  cases v with
  | lin x => have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact h1
  | equal _ _ | below _ _ => exact (refuse_ok h).elim

theorem symSpread16_flags {ctx : Ctx} {bind : Bind} {s s1 : Sym} {e : Expr} {l : List Nat} {items rest : Items}
    (h : symSpread16 ctx bind s e items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  cases e with
  | number _ | lane _ _ | name _ => exact symSpreadScalar16_flags h
  | call f args =>
    simp only [symSpread16] at h
    by_cases h1 : (f == "mem32") = true
    · simp only [h1, ite_true] at h
      obtain ⟨⟨l0, sa⟩, _, hm, hp⟩ := V.bind_ok h
      have := V.pure_ok hp; injection this with hp _; injection hp with _ hs; subst hs
      exact symMemWords_flags hm
    · simp only [h1, ite_false] at h
      by_cases h2 : (f == "low32") = true
      · simp only [h2, ite_true] at h
        rcases args with _ | ⟨a, _ | _⟩
        · exact (refuse_ok (items := items) h).elim
        · exact symSpreadScalar16_flags h
        · exact (refuse_ok (items := items) h).elim
      · simp only [h2, ite_false] at h; exact symSpreadScalar16_flags h

theorem symShuffle512_flags {bind : Bind} {s s1 : Sym} {f : String} {args : List Expr} {l : List Nat} {items rest : Items}
    (h : symShuffle512 bind s f args items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symShuffle512 at h
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | _⟩⟩⟩⟩⟩⟩
  · exact (refuse_ok (items := items) h).elim
  · exact (refuse_ok (items := items) h).elim
  · exact (refuse_ok (items := items) h).elim
  · dsimp only [symPair512] at h
    cases hx : symVec512 bind s a <;> cases hy : symVec512 bind s b <;> simp only [hx, hy] at h
    all_goals first
      | exact (refuse_ok (items := items) h).elim
      | (by_cases hq : (f == "quarters") = true
         · simp only [hq, ite_true] at h
           cases hn : symNumber bind p0 <;> simp only [hn] at h
           · exact (refuse_ok (items := items) h).elim
           · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
         · simp only [hq, ite_false] at h; exact (refuse_ok (items := items) h).elim)
  · simp only at h; exact (refuse_ok (items := items) h).elim
  · simp only at h; exact (refuse_ok (items := items) h).elim
  · cases p0 <;> cases p1 <;> cases p2 <;> cases p3
    all_goals try (simp only at h; exact (refuse_ok (items := items) h).elim)
    dsimp only [symPair512] at h
    cases hx : symVec512 bind s a <;> cases hy : symVec512 bind s b <;> simp only [hx, hy] at h
    all_goals first
      | exact (refuse_ok (items := items) h).elim
      | (split at h
         · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
         · exact (refuse_ok (items := items) h).elim)
  · simp only at h; exact (refuse_ok (items := items) h).elim

theorem symSpillLoad_flags {ctx : Ctx} {bind : Bind} {s s1 : Sym} {args : List Expr} {l : List Nat} {items rest : Items}
    (h : symSpillLoad ctx bind s args items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symSpillLoad at h
  cases ha : symWordAddr ctx bind s args with
  | none => simp only [ha] at h; exact (refuse_ok (items := items) h).elim
  | some a =>
    simp only [ha] at h
    cases hf : s.spill.find? (fun x => frameOffset a == x.1) <;> simp only [hf] at h
    · exact (refuse_ok (items := items) h).elim
    · by_cases hal : aligned64 a = true
      · simp only [hal, ite_true] at h; obtain ⟨_, _, _, h⟩ := V.bind_ok h
        have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
      · simp only [hal, ite_false] at h; exact (refuse_ok (items := items) h).elim

theorem symSpillStore_flags {ctx : Ctx} {bind : Bind} {s s1 : Sym} {args : List Expr} {l : List Nat} {items rest : Items}
    (h : symSpillStore ctx bind s args l items = .ok (s1, rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symSpillStore at h
  cases ha : symWordAddr ctx bind s args with
  | none => simp only [ha] at h; exact (refuse_ok (items := items) h).elim
  | some a =>
    simp only [ha] at h
    by_cases hal : aligned64 a = true
    · simp only [hal, ite_true] at h; obtain ⟨_, _, _, h⟩ := V.bind_ok h; obtain ⟨_, _, _, h⟩ := V.bind_ok h
      have := V.pure_ok h; injection this with h _; subst h; exact ⟨rfl, rfl⟩
    · simp only [hal, ite_false] at h; exact (refuse_ok (items := items) h).elim

theorem symLoadBlock_flags {s s1 : Sym} {v j p l0 : Nat} {addr : Row} {l : List Nat} {items rest : Items}
    (h : symLoadBlock s v j p l0 addr items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symLoadBlock at h
  by_cases hp : (p % 8 != 0) = true
  · simp only [hp, ite_true] at h; exact (refuse_ok (items := items) h).elim
  · simp only [hp, ite_false] at h
    obtain ⟨_, _, _, h⟩ := V.bind_ok h; obtain ⟨_, _, _, h⟩ := V.bind_ok h
    exact symLaneTerms_flags (s := { s with nvars := s.nvars + 16, known := .block j p (Lin.sub addr (Lin.var v)) ((List.range 16).map (s.nvars + ·)) :: s.known }) h

theorem symCellLoad_flags {ctx : Ctx} {s s1 : Sym} {a : Row} {l0 l : List Nat} {items rest : Items}
    (h : symCellLoad ctx s a l0 items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symCellLoad at h
  obtain ⟨_, _, _, h⟩ := V.bind_ok h
  have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩

theorem symMem512_flags {ctx : Ctx} {bind : Bind} {s s1 : Sym} {f : String} {args : List Expr} {l : List Nat} {items rest : Items}
    (h : symMem512 ctx bind s f args items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symMem512 at h
  by_cases h1 : (f == "mem512") = true
  · simp only [h1, ite_true] at h
    cases hf1 : (symWordAddr ctx bind s args).bind fun a => (findLane ctx.contract a s.known).map fun x => (a, x) with
    | some p => simp only [hf1] at h; exact symLoadBlock_flags h
    | none =>
      simp only [hf1] at h
      cases hf2 : (symWordAddr ctx bind s args).bind fun a => (s.spill.find? fun (o, _) => frameOffset a == o).map fun c => (a, c) with
      | some p => simp only [hf2] at h; exact symCellLoad_flags h
      | none => simp only [hf2] at h; exact symMemWords_flags h
  · simp only [h1, ite_false] at h
    by_cases h2 : (f == "mem512a") = true
    · simp only [h2, ite_true] at h; exact symSpillLoad_flags h
    · simp only [h2, ite_false] at h; exact (refuse_ok (items := items) h).elim

theorem symEachOp_flags {s s1 : Sym} {op : String} {x y l : List Nat} {items rest : Items}
    (h : symEachOp s op x y items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symEachOp at h
  by_cases h1 : (op == "add32") = true
  · simp only [h1, ite_true] at h; exact symLaneTerms_flags h
  · simp only [h1, ite_false] at h
    by_cases h2 : (op == "xor32") = true
    · simp only [h2, ite_true] at h; exact symLaneTerms_flags h
    · simp only [h2, ite_false] at h
      by_cases h3 : (op == "ult32") = true
      · simp only [h3, ite_true] at h; exact symLaneTerms_flags h
      · simp only [h3, ite_false] at h; exact (refuse_ok (items := items) h).elim

theorem symEach512_flags {ctx : Ctx} {bind : Bind} {s s1 : Sym} {op : String} {a b : Expr} {l : List Nat} {items rest : Items}
    (h : symEach512 ctx bind s op a b items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symEach512 at h
  by_cases hr : (op == "ror32") = true
  · simp only [hr, ite_true] at h
    cases hx : symVec512 bind s a <;> cases hn : symNumber bind b <;> simp only [hx, hn] at h
    all_goals first | exact (refuse_ok (items := items) h).elim | exact symLaneTerms_flags h
  · simp only [hr, ite_false] at h
    cases b with
    | call f args =>
      dsimp only at h
      by_cases hw : (f == "words16") = true
      · simp only [hw, ite_true] at h
        cases hx : symVec512 bind s a <;> cases hk : words16 bind args <;> simp only [hx, hk] at h
        all_goals try exact (refuse_ok (items := items) h).elim
        by_cases ha : (op == "add32") = true
        · simp only [ha, ite_true] at h; exact symLaneTerms_flags h
        · simp only [ha, ite_false] at h; exact (refuse_ok (items := items) h).elim
      · simp only [hw, ite_false] at h
        obtain ⟨⟨y, sa⟩, _, hm, h⟩ := V.bind_ok h
        have h1 := symMem512_flags hm
        cases hx : symVec512 bind sa a <;> simp only [hx] at h
        · exact (refuse_ok h).elim
        · have h2 := symEachOp_flags h; exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
    | number n =>
      dsimp only at h
      cases hx : symVec512 bind s a <;> cases hy : symVec512 bind s (.number n) <;> simp only [hx, hy] at h
      all_goals first | exact (refuse_ok (items := items) h).elim | exact symEachOp_flags h
    | lane x i =>
      dsimp only at h
      cases hx : symVec512 bind s a <;> cases hy : symVec512 bind s (.lane x i) <;> simp only [hx, hy] at h
      all_goals first | exact (refuse_ok (items := items) h).elim | exact symEachOp_flags h
    | name n =>
      dsimp only at h
      cases hx : symVec512 bind s a <;> cases hy : symVec512 bind s (.name n) <;> simp only [hx, hy] at h
      all_goals first | exact (refuse_ok (items := items) h).elim | exact symEachOp_flags h

theorem symLanes512_flags {ctx : Ctx} {bind : Bind} {s s1 : Sym} {v : Expr} {l : List Nat} {items rest : Items}
    (h : symLanes512 ctx bind s v items = .ok ((l, s1), rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  cases v with
  | number _ | lane _ _ => simp only [symLanes512] at h; exact (refuse_ok (items := items) h).elim
  | name n =>
    simp only [symLanes512] at h
    cases hv : symVec512 bind s (.name n) <;> simp only [hv] at h
    · exact (refuse_ok (items := items) h).elim
    · have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
  | call f args =>
    simp only [symLanes512] at h
    by_cases h1 : (f == "zeros16" && args.isEmpty) = true
    · simp only [h1, ite_true] at h; have := V.pure_ok h; injection this with h _; injection h with _ h; subst h; exact ⟨rfl, rfl⟩
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : (f == "spread16") = true
      · simp only [h2, ite_true] at h
        rcases args with _ | ⟨e, _ | _⟩
        · simp only at h; exact (refuse_ok (items := items) h).elim
        · cases e with
          | call g gs =>
            rcases gs with _ | ⟨a, _ | _⟩
            · simp only at h; exact (refuse_ok (items := items) h).elim
            · dsimp only at h
              by_cases hg : (g == "lane32") = true
              · simp only [hg, ite_true] at h; exact symSpread16_flags h
              · simp only [hg, ↓reduceIte] at h; exact (refuse_ok (items := items) h).elim
            · simp only at h; exact (refuse_ok (items := items) h).elim
          | number _ | lane _ _ | name _ => simp only at h; exact (refuse_ok (items := items) h).elim
        · simp only at h; exact (refuse_ok (items := items) h).elim
      · simp only [h2, ↓reduceIte] at h
        by_cases h3 : (f == "each32") = true
        · simp only [h3, ite_true] at h
          rcases args with _ | ⟨eop, _ | ⟨a, _ | ⟨b, _ | _⟩⟩⟩
          · simp only at h; exact (refuse_ok (items := items) h).elim
          · simp only at h; exact (refuse_ok (items := items) h).elim
          · simp only at h; exact (refuse_ok (items := items) h).elim
          · cases eop with
            | name op => exact symEach512_flags h
            | number _ | lane _ _ | call _ _ => simp only at h; exact (refuse_ok (items := items) h).elim
          · simp only at h; exact (refuse_ok (items := items) h).elim
        · simp only [h3, ↓reduceIte] at h
          by_cases h4 : (f == "mem512" || f == "mem512a") = true
          · simp only [h4, ite_true] at h; exact symMem512_flags h
          · simp only [h4, ↓reduceIte] at h
            by_cases h5 : (f == "choose16") = true
            · simp only [h5, ite_true] at h
              rcases args with _ | ⟨m, _ | ⟨eop, _ | ⟨c, _ | _⟩⟩⟩
              · simp only at h; exact (refuse_ok (items := items) h).elim
              · simp only at h; exact (refuse_ok (items := items) h).elim
              · simp only at h; exact (refuse_ok (items := items) h).elim
              · cases eop with
                | call g gs =>
                  rcases gs with _ | ⟨op0, _ | ⟨a, _ | ⟨b, _ | _⟩⟩⟩
                  · simp only at h; exact (refuse_ok (items := items) h).elim
                  · simp only at h; exact (refuse_ok (items := items) h).elim
                  · simp only at h; exact (refuse_ok (items := items) h).elim
                  · cases op0 with
                    | name op =>
                      dsimp only at h
                      by_cases hg : (g == "each32") = true
                      · simp only [hg, ite_true] at h
                        cases hm : symVec512 bind s m <;> cases hx : symVec512 bind s a <;> cases hy : symVec512 bind s b <;> cases hc : symVec512 bind s c <;> simp only [hm, hx, hy, hc] at h
                        all_goals try exact (refuse_ok (items := items) h).elim
                        obtain ⟨⟨nw, sa⟩, _, ho, hl⟩ := V.bind_ok h
                        have f1 := symEachOp_flags ho; have f2 := symLaneTerms_flags hl
                        exact ⟨f2.1.trans f1.1, f2.2.trans f1.2⟩
                      · simp only [hg, ↓reduceIte] at h; exact (refuse_ok (items := items) h).elim
                    | number _ | lane _ _ | call _ _ => simp only at h; exact (refuse_ok (items := items) h).elim
                  · simp only at h; exact (refuse_ok (items := items) h).elim
                | number _ | lane _ _ | name _ => simp only at h; exact (refuse_ok (items := items) h).elim
              · simp only at h; exact (refuse_ok (items := items) h).elim
            · simp only [h5, ↓reduceIte] at h; exact symShuffle512_flags h

theorem symStoreWords_flags {ctx : Ctx} {s s1 : Sym} {addr : Row} {l : List Nat} {w : Nat} {items rest : Items}
    (h : symStoreWords ctx s addr l w items = .ok (s1, rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  have hfr : ∀ {bytes : String},
      (match Lin.isConst (Lin.sub addr (Lin.var RSP)), s.sp with
       | some o, some sp =>
         if -(ctx.contract.stack : Int) ≤ o ∧ sp ≤ o ∧ o + 4 * (w : Int) ≤ 0 ∧ l.length == w then
           pure { s with
             spill := [], range := none,
             frame := s.frame.filter fun (cell : Int × Row) => decide (cell.1 + 8 ≤ o) || decide (o + 4 * (w : Int) ≤ cell.1),
             frameW := ((List.range w).map fun (k : Nat) => (o + 4 * (k : Int), l.getD k 0)) ++
                       s.frameW.filter fun (cell : Int × Nat) => decide (cell.1 + 4 ≤ o) || decide (o + 4 * (w : Int) ≤ cell.1) }
         else refuse s!"{bytes} bytes written to what is no run given to write"
       | _, _ => refuse s!"{bytes} bytes written to what is no run given to write") items = .ok (s1, rest) →
      s1.zf = s.zf ∧ s1.cf = s.cf := by
    intro bytes h'
    cases hc : Lin.isConst (Lin.sub addr (Lin.var RSP)) <;> cases hsp : s.sp <;> simp only [hc, hsp] at h'
    all_goals try exact (refuse_ok (items := items) h').elim
    split at h'
    · have := V.pure_ok h'; injection this with h' _; subst h'; exact ⟨rfl, rfl⟩
    · exact (refuse_ok (items := items) h').elim
  unfold symStoreWords at h
  cases hf : findOut addr ctx.contract.outs 0 <;> simp only [hf] at h
  · exact hfr h
  · rename_i loc; cases loc with
    | frame _ | region _ _ | data _ => dsimp only at h; exact hfr h
    | out w0 off =>
      dsimp only at h
      cases hc : Lin.isConst off <;> cases hg : ctx.contract.outs[w0]? <;> simp only [hc, hg] at h
      all_goals try exact (refuse_ok (items := items) h).elim
      split at h
      · exact (refuse_ok (items := items) h).elim
      · split at h
        · exact (refuse_ok (items := items) h).elim
        · split at h
          · exact (refuse_ok (items := items) h).elim
          · have := V.pure_ok h; injection this with h _; subst h
            unfold rememberStore; exact ⟨rfl, rfl⟩

theorem symStore8_flags {ctx : Ctx} {s s1 : Sym} {w n : Nat} {o x : Row} {items rest : Items}
    (h : symStore8 ctx s w n o x items = .ok (s1, rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symStore8 at h
  cases hc : Lin.isConst o with
  | none => simp only [hc] at h; exact (refuse_ok (items := items) h).elim
  | some c =>
    simp only [hc] at h
    have ht : (s.touch ctx w).zf = s.zf ∧ (s.touch ctx w).cf = s.cf := by
      unfold Sym.touch; cases ctx.contract.outs[w]? with
      | none => exact ⟨rfl, rfl⟩
      | some p => dsimp only; split
                  · cases runAt p.2.1 ctx.contract.wordRuns 0 <;> exact ⟨rfl, rfl⟩
                  · exact ⟨rfl, rfl⟩
    by_cases h1 : 0 ≤ c ∧ c % 4 = 0 ∧ c + 8 ≤ n ∧ s.wrote.all (fun e => e.1 != w) = true
    · simp only [h1, ite_true] at h
      by_cases h2 : (Lin.hasHigh x && knownNonneg s (Lin.word x) && plain s.facts (Lin.sub (Lin.const (W32i - 1)) (Lin.word x))) = true
      · simp only [h2, ite_true] at h; have := V.pure_ok h; injection this with h _; subst h; exact ht
      · simp only [h2, ite_false] at h; have := V.pure_ok h; injection this with h _; subst h
        have hd := symDivide_flags (s.touch ctx w) x W32i
        exact ⟨hd.1.trans ht.1, hd.2.trans ht.2⟩
    · simp only [h1, ite_false] at h; exact (refuse_ok (items := items) h).elim

theorem symTouchFrame_flags {ctx : Ctx} {s s1 : Sym} {a : Row} {items rest : Items}
    (h : symTouchFrame ctx s a items = .ok (s1, rest)) : s1.zf = s.zf ∧ s1.cf = s.cf := by
  unfold symTouchFrame at h
  obtain ⟨_, _, _, h⟩ := V.bind_ok h; obtain ⟨_, _, _, h⟩ := V.bind_ok h
  have := V.pure_ok h; injection this with h _; subst h; exact ⟨rfl, rfl⟩

theorem settle_flags {ctx : Ctx} {s s1 : Sym} {items rest : Items}
    (h : settle ctx s items = .ok (s1, rest)) : s1.zf = s.zf ∧ s1.cf = s.cf ∧ s1.q = s.q := by
  unfold settle at h
  cases hsp : s.sp with
  | some sp =>
    simp only [hsp] at h
    by_cases hc : sp ≤ 0 ∧ -(ctx.contract.stack : Int) ≤ sp
    · simp only [hc, ite_true] at h; have := V.pure_ok h; injection this with h _; subst h; exact ⟨rfl, rfl, rfl⟩
    · simp only [hc, ite_false] at h; exact (refuse_ok (items := items) h).elim
  | none =>
    simp only [hsp] at h
    by_cases hs : stackSame s = true
    · simp only [hs, ite_true] at h; have := V.pure_ok h; injection this with h _; subst h; exact ⟨rfl, rfl, rfl⟩
    · simp only [hs, ite_false] at h
      obtain ⟨_, _, _, h⟩ := V.bind_ok h
      have := V.pure_ok h; injection this with h _; subst h; exact ⟨rfl, rfl, rfl⟩

end Ode

