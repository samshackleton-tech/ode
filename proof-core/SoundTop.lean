import SoundCall
import SoundCallL
import SoundMarks
import SoundSpecW
import SoundWide
import SoundList
import Plain
import SoundTrace
import SoundTail
/-!
# Why the verifier's yes is right, 4: instructions, paths, and the theorem
-/
namespace Ode
open Arithmetic

/-- An effect the verifier accepts runs in the machine model and preserves the verifier's invariant. -/
theorem symStmt_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s' : Sym} {stmt : Stmt}
    {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symStmt ctx bind s stmt items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (base u : Nat) :
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧ execStmt (ctx.contract.perm ctx.pieces s0) bind base u st stmt = some st' ∧ st'.rip = st.rip := by
  cases stmt with
  | vset _ _ => exact symVset_sound E bind h H wf base u
  | vset512 _ _ => exact symVset512_sound E bind h H wf base u
  | nothing | ret | retLink _ | call _ | callLink _ _ | jump _ _ | set _ _ =>
    exact symStmt_scalar E bind h H wf base u (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun a x h8 H8 wf8 hw8 ha8 sx8 => symStore8_sound E a x h8 H8 wf8 hw8 ha8 sx8)

/-- What the verifier holds of a state speaks of its registers, flags, memory and vector registers, and of
where the files' data lies: it is so of any state with the same ones (whatever its place in the code, its
marks and its trace). -/
theorem Holds.fields {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st st' : State} (H : Holds ctx s0 ρ s st)
    (hr : st'.reg = st.reg) (hz : st'.zf = st.zf) (hc : st'.cf = st.cf) (hm : st'.mem = st.mem) (hv : st'.vec = st.vec)
    (hd : st'.data = st.data) :
    Holds ctx s0 ρ s st' := by
  refine ⟨H.entry, ⟨H.data.1, hd.trans H.data.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, H.facts, H.bytes, H.spec, ?_, ?_, ?_, H.known, (by rw [hm]; exact H.range), by rw [hv]; exact H.vecIntact⟩
  · rw [hr]; exact H.reg
  · rw [hr]; exact H.small
  · rw [hz]; exact H.zf
  · rw [hc]; exact H.cf
  · rw [hm]; exact H.frame
  · rw [hm]; exact H.frameW
  · rw [hm]; exact H.mem
  · rw [hm]; exact H.wrote
  · have W := H.words
    unfold VecOk at W ⊢
    rw [hv, hm]; exact W

theorem Holds.rip {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (x : Nat) :
    Holds ctx s0 ρ s { st with rip := x } := H.fields rfl rfl rfl rfl rfl rfl

theorem Carried.fields {ctx : Ctx} {s0 : State} {ρ ρ' : Nat → Int} {s s' : Sym} {st st' : State} (c : Carried ctx s0 ρ s ρ' s' st)
    (hr : st'.reg = st.reg) (hz : st'.zf = st.zf) (hc : st'.cf = st.cf) (hm : st'.mem = st.mem) (hv : st'.vec = st.vec)
    (hd : st'.data = st.data) :
    Carried ctx s0 ρ s ρ' s' st' := ⟨c.agree, c.mono, c.holds.fields hr hz hc hm hv hd, c.wf⟩

/-- What a contract promises of the state at the return speaks of its registers, its memory and where it
goes on: it is so of any state with the same ones. -/
theorem post_fields {c : Contract} {defs : List Def} {s0 st st' : State} (h : c.post defs s0 st)
    (hr : st'.reg = st.reg) (hm : st'.mem = st.mem) (hrip : st'.rip = st.rip) (hv : st'.vec = st.vec) : c.post defs s0 st' := by
  simp only [Contract.post, Ensure.holds, EnsureW.holds, Contract.envAfter, hr, hm, hrip, hv] at h ⊢
  exact h

/-- The statements of an effect, one after another: the machine that stops where something marked shows
does not stop, and what the verifier has as not marked after them is not marked. -/
theorem stmts_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) (base : Nat) (u : Nat → Nat) :
    ∀ (stmts : List Stmt) (k : Nat) {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State},
    fold (symStmtQ ctx bind) s stmts items = .ok (s', rest) → Holds ctx s0 ρ s st → WF ctx s → MarksOk ctx s0 s.q st →
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧
      execAllQ (ctx.contract.perm ctx.pieces s0) bind base u k st stmts = some (.next st') ∧ st'.rip = st.rip ∧ MarksOk ctx s0 s'.q st'
  | [], k, s, s', items, rest, ρ, st, h, H, wf, M => by
    simp only [fold] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, st, Carried.here H wf, rfl, rfl, M⟩
  | stmt :: more, k, s, s', items, rest, ρ, st, h, H, wf, M => by
    simp only [fold] at h
    obtain ⟨sq, r1, eq, h⟩ := V.bind_ok h
    simp only [symStmtQ] at eq
    obtain ⟨s1, r0, e1, eq⟩ := V.bind_ok eq
    rw [stmtMarks_light] at eq
    cases hm : stmtMarks ctx bind s s1 stmt with
    | none => simp only [hm] at eq; exact (refuse_ok eq).elim
    | some q' =>
      simp only [hm] at eq
      have := V.pure_ok eq
      injection this with hsq _
      subst hsq
      obtain ⟨ρ1, st1, c1, x1, rip1⟩ := symStmt_sound E bind e1 H wf base (u k)
      obtain ⟨quiet, M1⟩ := stmtMarks_sound E M H wf c1 x1 hm
      -- the machine goes on from that state with its marks and its trace brought up to date
      have c1' : Carried ctx s0 ρ s ρ1 { s1 with q := q' } (noted bind st stmt st1) := (c1.q q').fields rfl rfl rfl rfl rfl rfl
      obtain ⟨ρ2, st2, c2, x2, rip2, M2⟩ := stmts_sound E bind base u more (k + 1) h c1'.holds c1'.wf M1
      refine ⟨ρ2, st2, c1'.then c2, ?_, rip2.trans rip1, M2⟩
      cases stmt with
      | ret => simp only [symStmt] at e1; exact (refuse_ok e1).elim
      | retLink _ => simp only [symStmt] at e1; exact (refuse_ok e1).elim
      | callLink _ _ => simp only [symStmt] at e1; exact (refuse_ok e1).elim
      | nothing => simp only [execAllQ, quiet, if_true, x1]; exact x2
      | set _ _ => simp only [execAllQ, quiet, if_true, x1]; exact x2
      | vset _ _ => simp only [execAllQ, quiet, if_true, x1]; exact x2
      | vset512 _ _ => simp only [execAllQ, quiet, if_true, x1]; exact x2
      | jump _ _ => simp only [execAllQ, quiet, if_true, x1]; exact x2
      | call _ => simp only [execAllQ, quiet, if_true, x1]; exact x2

theorem stackGoals_bounded {ctx : Ctx} {s : Sym} (wf : WF ctx s) {g : Row} (m : g ∈ stackGoals ctx s) : bounded s.nvars g := by
  have off := bounded_sub (wf.reg RSP ctx.rsp_lt) (bounded_var (x := RSP) (Nat.lt_of_lt_of_le ctx.rsp_lt wf.regs))
  simp only [stackGoals, List.mem_cons, List.mem_append, List.mem_map, Option.mem_toList] at m
  rcases m with rfl | rfl | ⟨⟨o, _⟩, _, rfl⟩ | ⟨⟨o, ids⟩, hs, rfl⟩
  · exact bounded_add off (bounded_const _ _)
  · exact bounded_scale (-1) off
  · exact bounded_sub (bounded_const _ _) off
  · exact bounded_sub (wf.words.spill o ids hs).1 off

theorem settle_sound {ctx : Ctx} {s0 : State} {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : settle ctx s items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) : Carried ctx s0 ρ s ρ s' st := by
  cases hsp : s.sp with
  | none =>
    simp only [settle, hsp] at h
    by_cases hsame : stackSame s = true
    · rw [if_pos hsame] at h
      have hs := V.pure_ok h
      injection hs with heq _; subst s'
      exact ⟨Agree.refl _ _, Nat.le_refl _,
        ⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, H.frame, (fun _ _ m => nomatch m), H.facts,
         H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range, H.vecIntact⟩,
        ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, (fun _ _ m => nomatch m), wf.facts,
         wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩⟩
    rw [if_neg hsame] at h
    obtain ⟨q, _, hc, he⟩ := V.bind_ok h
    cases q
    have hs := V.pure_ok he
    injection hs with heq _; subst s'
    exact ⟨Agree.refl _ _, Nat.le_refl _,
      ⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, H.frame, (fun _ _ m => nomatch m),
       fun g m => (List.mem_append.mp m).elim (entails_sound H.facts hc g) (H.facts g),
       H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range, H.vecIntact⟩,
      ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, (fun _ _ m => nomatch m),
       fun _ m => (List.mem_append.mp m).elim (fun mg => stackGoals_bounded wf (List.mem_filter.mp mg).1) (wf.facts _),
       wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩⟩
  | some sp =>
    simp only [settle, hsp] at h
    split at h
    next =>
      have := V.pure_ok h
      injection this with h1 _
      subst h1
      exact ⟨Agree.refl _ _, Nat.le_refl _,
        ⟨H.entry, H.data, H.reg, H.small, H.zf, H.cf, fun o v m => H.frame o v (List.mem_filter.mp m).1,
         fun o i m => H.frameW o i (List.mem_filter.mp m).1, H.facts, H.bytes, H.spec, H.mem, H.wrote,
         ⟨H.words.vec, H.words.intact, H.words.wrote, fun _ _ h => nomatch h⟩, H.known, H.range, H.vecIntact⟩,
        ⟨wf.base, wf.reg, wf.zf, wf.cf, fun o v m => wf.frame o v (List.mem_filter.mp m).1,
         fun o i m => wf.frameW o i (List.mem_filter.mp m).1, wf.facts, wf.bytes, wf.spec, wf.wrote,
         wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known, wf.range⟩⟩
    next => exact (refuse_ok h).elim

/-! ## A jump on a flag -/

/-- The way the flag is in fact set is among the ways gone. -/
theorem ways_sound {ctx : Ctx} {s0 : State} {s : Sym} {want : Bool} {target next : Nat} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (b : Bool) :
    ∀ (w : List (Bool × List Row)) {nexts : List (Sym × Next)} {items rest : Items},
    ways s want target next w items = .ok (nexts, rest) →
    (∀ sr ∈ w, ∀ r ∈ sr.2, bounded s.nvars r) →
    (∃ sr ∈ w, sr.1 = b ∧ ∀ r ∈ sr.2, r.holds ρ) →
    ∃ s', (s', Next.at (if b == want then target else next)) ∈ nexts ∧ Carried ctx s0 ρ s ρ s' st ∧ s'.q = s.q
  | [], _, _, _, _, _, hex => by
    obtain ⟨sr, m, _⟩ := hex
    cases m
  | (set, rows) :: more, nexts, items, rest, h, hb, hex => by
    simp only [ways] at h
    obtain ⟨now, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨others, r2, e2, h⟩ := V.bind_ok h
    have a1 := assume_sound e1 ρ H.facts
    obtain ⟨sr, m, hset, hrows⟩ := hex
    cases m with
    | head =>
      cases now with
      | none => exact (a1 hrows).elim
      | some s1 =>
        simp only at a1 h
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        refine ⟨s1, by rw [← hset]; exact List.mem_cons_self .., ?_⟩
        rcases a1 with rfl | rfl
        · exact ⟨Carried.here H wf, rfl⟩
        · exact ⟨⟨Agree.refl _ _, Nat.le_refl _, H.more rows hrows, wf.more rows (hb (set, rows) (List.mem_cons_self ..))⟩, rfl⟩
    | tail _ m =>
      obtain ⟨s', m', hs', hq'⟩ := ways_sound H wf b more e2 (fun sr m => hb sr (List.mem_cons_of_mem _ m)) ⟨sr, m, hset, hrows⟩
      cases now with
      | none =>
        simp only at h
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        exact ⟨s', m', hs', hq'⟩
      | some s1 =>
        simp only at h
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        exact ⟨s', List.mem_cons_of_mem _ m', hs', hq'⟩

theorem flagWays_spec {f : Flag} {w : List (Bool × List Row)} {ρ : Nat → Int} {b : Bool} {n : Nat}
    (h : flagWays f = some w) (hf : f.holds ρ b) (hb : f.bounded n) :
    (∀ sr ∈ w, ∀ r ∈ sr.2, bounded n r) ∧ (∃ sr ∈ w, sr.1 = b ∧ ∀ r ∈ sr.2, r.holds ρ) := by
  cases f with
  | unknown => simp [flagWays] at h
  | equal x y =>
    simp only [flagWays] at h
    injection h with h
    subst h
    simp only [Flag.holds] at hf
    refine ⟨?_, ?_⟩
    · intro sr m r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
      rcases m with rfl | rfl | rfl <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      · rcases hr with rfl | rfl
        · exact bounded_sub hb.1 hb.2
        · exact bounded_sub hb.2 hb.1
      · subst hr; exact bounded_sub (bounded_sub hb.1 hb.2) (bounded_const _ _)
      · subst hr; exact bounded_sub (bounded_sub hb.2 hb.1) (bounded_const _ _)
    · by_cases e : ev ρ x = ev ρ y
      · refine ⟨_, List.mem_cons_self .., by simp [hf, e], ?_⟩
        intro r hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl <;> rw [holds_iff, ev_sub] <;> omega
      · by_cases l : ev ρ y < ev ρ x
        · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp [hf, e], ?_⟩
          intro r hr
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          subst hr
          rw [holds_iff]; simp only [ev_sub, ev_const]; omega
        · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp [hf, e], ?_⟩
          intro r hr
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          subst hr
          rw [holds_iff]; simp only [ev_sub, ev_const]; omega
  | below x y =>
    simp only [flagWays] at h
    injection h with h
    subst h
    simp only [Flag.holds] at hf
    refine ⟨?_, ?_⟩
    · intro sr m r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
      rcases m with rfl | rfl <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      · subst hr; exact bounded_sub (bounded_sub hb.2 hb.1) (bounded_const _ _)
      · subst hr; exact bounded_sub hb.1 hb.2
    · by_cases l : ev ρ x < ev ρ y
      · refine ⟨_, List.mem_cons_self .., by simp [hf, l], ?_⟩
        intro r hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        subst hr
        rw [holds_iff]; simp only [ev_sub, ev_const]; omega
      · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp [hf, l], ?_⟩
        intro r hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        subst hr
        rw [holds_iff, ev_sub]; omega


theorem jumpWays_sound {ctx : Ctx} {s0 : State} {s : Sym} {want : Bool} {target next : Nat}
    {ρ : Nat → Int} {st : State} {f : Flag} {nexts : List (Sym × Next)} {items rest : Items}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (b : Bool)
    (h : jumpWays s want target next f items = .ok (nexts, rest))
    (hf : f.holds ρ b) (hb : f.bounded s.nvars) :
    ∃ s', (s', Next.at (if b == want then target else next)) ∈ nexts ∧ Carried ctx s0 ρ s ρ s' st ∧ s'.q = s.q := by
  cases f with
  | unknown => simp only [jumpWays] at h; exact (refuse_ok h).elim
  | below x y =>
    simp only [jumpWays] at h
    obtain ⟨bd, ex⟩ := flagWays_spec (f := .below x y) rfl hf hb
    exact ways_sound H wf b _ h bd ex
  | equal x y =>
    simp only [jumpWays] at h
    obtain ⟨yes, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨no, r2, e2, h⟩ := V.bind_ok h
    have hp := V.pure_ok h; injection hp with h1 _; subst h1
    simp only [Flag.holds] at hf
    by_cases he : ev ρ x = ev ρ y
    · have hbtrue : b = true := by simp [hf, he]
      subst hbtrue
      unfold assumeEq at e1
      have hnotneq : hasNeq s.spec x y = false := by
        cases hn : hasNeq s.spec x y with
        | false => rfl
        | true => exact (hasNeq_sound hn H.spec he).elim
      simp only [hnotneq, Bool.false_eq_true, ↓reduceIte] at e1
      obtain ⟨now, r1', ea, e1⟩ := V.bind_ok e1
      have ha := assume_sound ea ρ H.facts
      have hrows : ∀ r ∈ [Lin.sub x y, Lin.sub y x], r.holds ρ := by
        intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl <;> rw [holds_iff, ev_sub] <;> omega
      cases now with
      | none => exact (ha hrows).elim
      | some s1 =>
        have hpy := V.pure_ok e1; injection hpy with hy _; subst hy
        have hbd : ∀ r ∈ [Lin.sub x y, Lin.sub y x], bounded s.nvars r := by
          intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | rfl
          · exact bounded_sub hb.1 hb.2
          · exact bounded_sub hb.2 hb.1
        refine ⟨s1, List.mem_append_left _ (by simp), ?_⟩
        rcases ha with rfl | rfl
        · exact ⟨Carried.here H wf, rfl⟩
        · exact ⟨⟨Agree.refl _ _, Nat.le_refl _, H.more _ hrows, wf.more _ hbd⟩, rfl⟩
    · have hbfalse : b = false := by simp [hf, he]
      subst hbfalse
      unfold assumeNeq at e2
      cases hc : Lin.isConst (Lin.sub x y) with
      | some k =>
        by_cases hk : k = 0
        · subst hk
          have ev0 := ev_isConst hc (ρ := ρ)
          rw [ev_sub] at ev0; omega
        · have hk' : (k == 0) = false := beq_false_of_ne hk
          simp only [hc, hk', Bool.false_eq_true, ↓reduceIte] at e2
          have hp2 := V.pure_ok e2; injection hp2 with hno _; subst hno
          exact ⟨s, List.mem_append_right _ (by simp), Carried.here H wf, rfl⟩
      | none =>
      simp only [hc] at e2
      have hbd : ∀ sr ∈ [(false, [Lin.sub (Lin.sub x y) (Lin.const 1)]), (false, [Lin.sub (Lin.sub y x) (Lin.const 1)])], ∀ r ∈ sr.2, bounded s.nvars r := by
        intro sr m r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
        rcases m with rfl | rfl <;> (simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; subst hr)
        · exact bounded_sub (bounded_sub hb.1 hb.2) (bounded_const _ _)
        · exact bounded_sub (bounded_sub hb.2 hb.1) (bounded_const _ _)
      have hex : ∃ sr ∈ [(false, [Lin.sub (Lin.sub x y) (Lin.const 1)]), (false, [Lin.sub (Lin.sub y x) (Lin.const 1)])], sr.1 = false ∧ ∀ r ∈ sr.2, r.holds ρ := by
        by_cases l : ev ρ y < ev ρ x
        · refine ⟨_, List.mem_cons_self .., rfl, ?_⟩
          intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; subst hr
          rw [holds_iff]; simp only [ev_sub, ev_const]; omega
        · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, ?_⟩
          intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; subst hr
          rw [holds_iff]; simp only [ev_sub, ev_const]; omega
      cases hl : r1.line r1.next with
      | none => simp only [hl] at e2; exact (need_ok e2).elim
      | some it =>
        simp only [hl] at e2
        cases it with
        | tag nm k =>
          simp only at e2
          split at e2
          · injection e2 with hno
            injection hno with hno _
            subst hno
            have hne : SFact.holds ctx s0 ρ (.neq (Lin.sub x y)) := by
              simp only [SFact.holds, ev_sub]; omega
            refine ⟨{ s with spec := .neq (Lin.sub x y) :: s.spec },
              List.mem_append_right _ (by simp),
              ⟨Agree.refl _ _, Nat.le_refl _, H.withSpec _ hne, wf.withSpec _ (bounded_sub hb.1 hb.2)⟩, rfl⟩
          · obtain ⟨s', m', c', q'⟩ := ways_sound H wf false _ e2 hbd hex
            exact ⟨s', List.mem_append_right _ m', c', q'⟩
        | _ =>
          simp only at e2
          obtain ⟨s', m', c', q'⟩ := ways_sound H wf false _ e2 hbd hex
          exact ⟨s', List.mem_append_right _ m', c', q'⟩

theorem jumpTarget_value {bind : Bind} {target : Expr} {t : Nat} (h : jumpTarget bind target = some t) (perm : Perm) (st : State) :
    value perm bind st target = some t := by
  cases target with
  | name n =>
    simp only [jumpTarget] at h
    split at h
    next hl => simp only [value, hl, if_true]; exact h
    next => contradiction
  | number _ => simp [jumpTarget] at h
  | lane _ _ => simp [jumpTarget] at h
  | call _ _ => simp [jumpTarget] at h

/-! ## The return -/

/-- An `ensures` of a whole run of words that the verifier has passed, after the rows the proof file gives
there (`symEnsureKnown`), holds. -/
theorem symEnsureKnown_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s : Sym} {e : EnsureW}
    {items : Items} {r : Unit × Items} {ρ : Nat → Int} {st st' : State}
    (h : symEnsureKnown ctx s e items = .ok r) (H : Holds ctx s0 ρ s st) (wf : WF ctx s)
    (hpv : ctx.contract.preVals ctx.defs s0) (hmem : st'.mem = st.mem) :
    e.holds ctx.contract ctx.defs s0 st' := by
  unfold symEnsureKnown at h
  obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
  have C := symKnow_sound (ctx := ctx) KNOWN e1 H wf
  exact symEnsureW_sound E hpv h C.holds C.wf hmem

/-- At a return the verifier has passed: the stack pointer is where it was at entry; and the contract's
promise is so of every state that has this state's memory and its registers but the stack pointer, the
stack pointer above the bytes of the address returned to (`slot`: eight on x86-64, none on AArch64), and
that goes on at the address the contract has the function return to. (The two machines' returns leave
such states: `symReturn_x86`, `symReturn_arm`.) -/
theorem symReturn_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s : Sym} {items : Items}
    {r : Unit × Items} {ρ : Nat → Int} {st : State}
    (h : symReturn ctx s items = .ok r) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) :
    st.reg RSP = s0.reg RSP ∧
    ∀ st' : State, st'.mem = st.mem → st'.vec = st.vec → (∀ r, r ≠ RSP → st'.reg r = st.reg r) →
      st'.reg RSP = st.reg RSP + ctx.contract.slot → st'.rip = ctx.contract.backTo s0 →
      ctx.contract.post ctx.defs s0 st' := by
  unfold symReturn at h
  split at h
  next => exact (refuse_ok h).elim
  next hsp =>
    split at h
    next => exact (refuse_ok h).elim
    next hcs =>
    split at h
    next => exact (refuse_ok h).elim
    next hkv =>
      have hsp' : s.sp = some 0 := by simpa using hsp
      have hcs' : ∀ r ∈ ctx.contract.keeps, s.reg r = Lin.var r := by simpa using hcs
      have hkv' : ∀ r ∈ ctx.contract.keepsVec, r ∈ s.vecIntact := by
        intro r hr
        have all : (ctx.contract.keepsVec.all fun r => s.vecIntact.contains r) = true := by simpa using hkv
        exact List.contains_iff_mem.mp (List.all_eq_true.mp all r hr)
      have e := ev_isConst (ρ := ρ) hsp'
      simp only [ev_sub, ev_var] at e
      have h1 := H.reg RSP ctx.rsp_lt
      have h2 := H.entry RSP ctx.rsp_lt
      have hrsp : st.reg RSP = s0.reg RSP := by omega
      refine ⟨hrsp, fun st' hmem hvec hreg hsp1 hrip => ?_⟩
      have hrr_spec := retReg_spec ctx.contract
      have hrax' : st'.reg ctx.contract.retReg = st.reg ctx.contract.retReg := hreg ctx.contract.retReg hrr_spec.2.1
      have lt0 : ctx.contract.retReg < ctx.nreg := hrr_spec.1
      -- every `ensures` of a whole run of words: of this state's memory, which the return leaves as it is
      obtain ⟨_, rW, enW, h⟩ := V.bind_ok h
      have hensW : ctx.contract.preVals ctx.defs s0 → ∀ e ∈ ctx.contract.ensuresW, e.holds ctx.contract ctx.defs s0 st' := by
        intro hpv e me
        obtain ⟨items', r', hr⟩ := each_mem enW e me
        exact symEnsureKnown_sound E hr H wf hpv hmem
      -- every `ensures` first: of the state the return leaves, whose memory and return register are this state's
      obtain ⟨sE, rE, en, h⟩ := V.bind_ok h
      have henvB : EnvB s.nvars (symEnvAfter ctx.contract s) := by
        have hsym := (symEnv_bounded ctx.contract).mono wf.regs
        unfold symEnvAfter
        split
        · intro nv m
          rcases List.mem_cons.mp m with rfl | m
          · exact wf.reg ctx.contract.retReg lt0
          · exact hsym nv m
        · exact hsym
      have henv : ∀ ρ', Agree s.nvars ρ ρ' → semEnv ctx s0 ρ' (symEnvAfter ctx.contract s) = ctx.contract.envAfter s0 st' := by
        intro ρ' a
        have hsym := semEnv_symEnv ctx s0 ρ' (fun r hr => by rw [← a r (Nat.lt_of_lt_of_le hr wf.regs)]; exact H.entry r hr)
        have hrax : ev ρ' (s.reg ctx.contract.retReg) = (st.reg ctx.contract.retReg : Int) := by
          rw [← ev_agree (wf.reg ctx.contract.retReg lt0) a]; exact (H.reg ctx.contract.retReg lt0).symm
        cases hres : ctx.contract.result with
        | none => simp only [symEnvAfter, Contract.envAfter, hres]; exact hsym
        | some name =>
          simp only [symEnvAfter, Contract.envAfter, hres]
          show (name, semv ctx s0 ρ' (.lin (s.reg ctx.contract.retReg))) :: semEnv ctx s0 ρ' (symEnv ctx.contract) = _
          rw [hsym]
          simp only [semv, hrax, hrax']
      obtain ⟨ρE, cE, hens⟩ := symEnsures_sound E en H wf henvB henv hmem
      have habove := E.above
      refine ⟨hrip, by rw [hsp1, hrsp], ?_, ?_, ?_, ?_, (fun hpv => ⟨hens, hensW hpv⟩), fun r hr => by rw [hvec]; exact H.vecIntact r (hkv' r hr)⟩
      · intro r hr
        obtain ⟨lt, ne, _⟩ := keeps_spec hr
        rw [hreg r ne]
        have := H.reg r lt
        rw [hcs' r hr, ev_var, H.entry r lt] at this
        omega
      · intro a ha ho
        rw [hmem]
        exact H.mem a ha ho
      · intro e he
        simp only [he] at h
        obtain ⟨⟨res, s1⟩, r1, e1, h⟩ := V.bind_ok h
        obtain ⟨ρ1, c1, sem, bd⟩ := seval_sound E _ e e1 cE.holds cE.wf ((symEnv_bounded ctx.contract).mono cE.wf.regs)
        rw [semEnv_symEnv ctx s0 ρ1 c1.holds.entry] at sem
        rw [hrax']
        have hrax := c1.holds.reg ctx.contract.retReg lt0
        cases res with
        | list _ => exact (refuse_ok h).elim
        | val v =>
          cases v with
          | region _ => exact (refuse_ok h).elim
          | bool _ => exact (refuse_ok h).elim
          | lin v =>
            simp only at h
            obtain ⟨_, r2, g1, h⟩ := V.bind_ok h
            have g1 := entail_sound g1 ρ1 c1.holds.facts
            have g2 := entail_sound h ρ1 c1.holds.facts
            simp only [ev_sub] at g1 g2
            simp only [SRes.sem, semv] at sem
            have : ev ρ1 v = (st.reg ctx.contract.retReg : Int) := by omega
            rw [this] at sem
            exact sem
        | tail c =>
          simp only at h
          obtain ⟨s2, r2, g1, h⟩ := V.bind_ok h
          obtain ⟨ρ2, c2, gh⟩ := specGoal_sound E 16 g1 c1.holds c1.wf ⟨bd, c1.wf.reg ctx.contract.retReg lt0⟩
          simp only [SFact.holds] at gh
          rw [← ev_agree (c1.wf.reg ctx.contract.retReg lt0) c2.agree, ← hrax] at gh
          exact (sem _).mpr ((CallValue_agree bd c2.agree _).mpr gh)
      · intro r
        by_cases hr : r = RSP
        · subst hr; rw [hsp1, hrsp]; exact habove
        · rw [hreg r hr]; exact H.small r

/-- A return the verifier has passed, on x86-64, in the machine's words: the eight bytes of the address to
return to may be read, and the state the machine's return leaves is one the contract promises. -/
theorem symReturn_x86 {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s : Sym} {items : Items}
    {r : Unit × Items} {ρ : Nat → Int} {st : State}
    (h : symReturn ctx s items = .ok r) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (ha : ctx.contract.arm64 = false) :
    allowed (ctx.contract.perm ctx.pieces s0).read (st.reg RSP) 8 = true ∧
    ctx.contract.post ctx.defs s0 (setReg { st with rip := load st.mem (st.reg RSP) 8 } RSP (st.reg RSP + 8)) := by
  obtain ⟨hrsp, post⟩ := symReturn_sound E h H wf
  have hslot : ctx.contract.slot = 8 := by simp only [Contract.slot, ha, Bool.false_eq_true, if_false]
  have hstack := E.stack
  have habove := E.above
  rw [hslot] at habove
  refine ⟨allowed_of _ _ _ ?_, post _ rfl rfl (fun r hr => ?_) ?_ ?_⟩
  · intro x hx1 hx2
    simp only [Contract.perm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    left; left; left; left; left; right; omega
  · show (if r = RSP then (st.reg RSP + 8) % M64 else st.reg r) = st.reg r
    rw [if_neg hr]
  · show (if RSP = RSP then (st.reg RSP + 8) % M64 else st.reg RSP) = st.reg RSP + ctx.contract.slot
    rw [if_pos rfl, hslot, Nat.mod_eq_of_lt (by omega)]
  · show load st.mem (st.reg RSP) 8 = ctx.contract.backTo s0
    simp only [Contract.backTo, ha, Bool.false_eq_true, if_false]
    rw [hrsp]
    apply load_congr
    intro x hx1 hx2
    apply H.mem
    · simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    · exact E.frame_notOut (by omega) (by omega)

/-- A return the verifier has passed, on AArch64, where the register that held the address to return to
holds what it held at entry: the state the machine's return leaves is one the contract promises. -/
theorem symReturn_arm {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s : Sym} {items : Items}
    {r : Unit × Items} {ρ : Nat → Int} {st : State}
    (h : symReturn ctx s items = .ok r) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (ha : ctx.contract.arm64 = true)
    (hl : s.reg LINK = Lin.var LINK) :
    ctx.contract.post ctx.defs s0 { st with rip := st.reg LINK } := by
  obtain ⟨hrsp, post⟩ := symReturn_sound E h H wf
  have hslot : ctx.contract.slot = 0 := by simp only [Contract.slot, ha, if_true]
  have lt : LINK < ctx.nreg := by
    show LINK < ctx.contract.regs
    simp only [Contract.regs, ha, if_true]
    decide
  refine post _ rfl rfl (fun _ _ => rfl) (by rw [hslot, Nat.add_zero]) ?_
  show st.reg LINK = ctx.contract.backTo s0
  simp only [Contract.backTo, ha, if_true]
  have := H.reg LINK lt
  rw [hl, ev_var, H.entry LINK lt] at this
  omega

/-! ## An instruction -/

/-- The state an instruction's statements start in: the place in the code is the next instruction's, and
the instruction's own address has been observed. -/
abbrev started (p : Program) (i : Instr) (st : State) : State :=
  { st with rip := p.base + i.next, trace := st.trace ++ [(st.rip, 0)] }

theorem shape_ret : ∀ {l : List Stmt}, shape l = .ret → l = [.ret]
  | [], h => by simp [shape] at h
  | [s], h => by
    cases s with
    | ret => rfl
    | set _ _ => unfold shape at h; split at h <;> simp_all
    | _ => simp [shape] at h
  | _ :: _ :: _, h => by simp [shape] at h

theorem shape_jump {target : Expr} {cond : Option (String × Bool)} : ∀ {l : List Stmt}, shape l = .jump target cond → l = [.jump target cond]
  | [], h => by simp [shape] at h
  | [s], h => by
    cases s with
    | jump _ _ => simp [shape] at h; rcases h with ⟨rfl, rfl⟩; rfl
    | set _ _ => unfold shape at h; split at h <;> simp_all
    | _ => simp [shape] at h
  | _ :: _ :: _, h => by simp [shape] at h

theorem shape_retLink {r : String} : ∀ {l : List Stmt}, shape l = .retLink r → l = [.retLink r]
  | [], h => by simp [shape] at h
  | [s], h => by
    cases s with
    | retLink _ => simp [shape] at h; subst h; rfl
    | set _ _ => unfold shape at h; split at h <;> simp_all
    | _ => simp [shape] at h
  | _ :: _ :: _, h => by simp [shape] at h

theorem shape_select {dst cond : String} {a b : Expr} :
    ∀ {l : List Stmt}, shape l = .select dst cond a b → l = [.set (.name dst) (.call "select" [.name cond, a, b])]
  | [], h => by simp [shape] at h
  | [s], h => by
    cases s with
    | set pl val =>
      cases pl with
      | name d =>
        cases val with
        | call fn args =>
          cases args with
          | cons c rest =>
            cases c with
            | name cn =>
              cases rest with
              | cons e1 rest2 =>
                cases rest2 with
                | cons e2 rest3 =>
                  cases rest3 with
                  | nil =>
                    by_cases hf : fn = "select"
                    · subst hf; simp [shape] at h; rcases h with ⟨rfl, rfl, rfl, rfl⟩; rfl
                    · simp [shape, hf] at h
                  | cons _ _ => simp [shape] at h
                | nil => simp [shape] at h
              | nil => simp [shape] at h
            | _ => simp [shape] at h
          | nil => simp [shape] at h
        | _ => simp [shape] at h
      | _ => simp [shape] at h
    | _ => simp [shape] at h
  | _ :: _ :: _, h => by simp [shape] at h

theorem selectCond_sound {cond flag : String} {want : Bool} (st : State)
    (h : selectCond cond = some (flag, want)) :
    flagVal st cond = some (if (condFlag st flag == want) then 1 else 0) ∧
    flagMark st.marks cond = some (condMark st.marks flag) ∧
    isNumberLetter cond = false := by
  unfold selectCond at h
  by_cases h1 : cond = "zf"
  · subst h1; simp at h; rcases h with ⟨rfl, rfl⟩; simp [flagVal, flagMark, condFlag, condMark, isNumberLetter]
  · by_cases h2 : cond = "nzf"
    · subst h2; simp at h; rcases h with ⟨rfl, rfl⟩; cases st.zf <;> simp [flagVal, flagMark, condFlag, condMark, isNumberLetter]
    · by_cases h3 : cond = "cf"
      · subst h3; simp at h; rcases h with ⟨rfl, rfl⟩; simp [flagVal, flagMark, condFlag, condMark, isNumberLetter]
      · by_cases h4 : cond = "ncf"
        · subst h4; simp at h; rcases h with ⟨rfl, rfl⟩; cases st.cf <;> simp [flagVal, flagMark, condFlag, condMark, isNumberLetter]
        · by_cases h5 : cond = "hi"
          · subst h5; simp at h; rcases h with ⟨rfl, rfl⟩
            cases hz : st.zf <;> cases hc : st.cf <;> cases hmz : st.marks.zf <;> cases hmc : st.marks.cf <;>
              simp [flagVal, flagMark, condFlag, condMark, isNumberLetter, hz, hc, hmz, hmc]
          · by_cases h6 : cond = "nhi"
            · subst h6; simp at h; rcases h with ⟨rfl, rfl⟩
              cases hz : st.zf <;> cases hc : st.cf <;> cases hmz : st.marks.zf <;> cases hmc : st.marks.cf <;>
                simp [flagVal, flagMark, condFlag, condMark, isNumberLetter, hz, hc, hmz, hmc]
            · simp [h1, h2, h3, h4, h5, h6] at h

theorem setSelectReg_holds {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) {d r : Nat} {v : Row} (hv : (st.reg r : Int) = ev ρ v) (q' : SMarks)
    (m' : Marks) (tr' : List (Nat × Nat)) (rip' : Nat) :
    Holds ctx s0 ρ (setSelectReg s d v q')
      { setReg st d (st.reg r) with marks := m', trace := tr', rip := rip' } := by
  refine ⟨H.entry, H.data, ?_, ?_, H.zf, H.cf, H.frame, H.frameW, H.facts, H.bytes, H.spec, H.mem, H.wrote, H.words, H.known, H.range, H.vecIntact⟩
  · intro x hx
    simp only [setSelectReg, setReg]
    by_cases hxd : x = d
    · subst hxd; simp [Nat.mod_eq_of_lt (H.small r), hv]
    · simp [hxd, H.reg x hx]
  · intro x
    simp only [setReg]
    by_cases hxd : x = d
    · subst hxd; simp [Nat.mod_lt _ (by decide : 0 < M64)]
    · simp [hxd, H.small x]

theorem setSelectReg_wf {ctx : Ctx} {s : Sym} (wf : WF ctx s) {d : Nat} {v : Row} (hv : bounded s.nvars v) (q' : SMarks) :
    WF ctx (setSelectReg s d v q') := by
  refine ⟨wf.base, ?_, wf.zf, wf.cf, wf.frame, wf.frameW, wf.facts, wf.bytes, wf.spec, wf.wrote,
    ⟨wf.words.table, wf.words.atoms, wf.words.vec, wf.words.rotrs, wf.words.wrote, wf.words.spill⟩, wf.known, wf.range⟩
  intro x hx
  simp only [setSelectReg]
  split
  · exact hv
  · exact wf.reg x hx

theorem setSelectReg_marksOk {ctx : Ctx} {s0 : State} {s : Sym} {st : State} (M : MarksOk ctx s0 s.q st)
    {bind : Bind} {dst cond na nb flag : String} {want : Bool} {d ra rb : Nat}
    (hsc : selectCond cond = some (flag, want))
    (hd : regOf bind dst = some d) (hna : isNumberLetter na = false) (hnb : isNumberLetter nb = false)
    (hra : regOf bind na = some ra) (hrb : regOf bind nb = some rb) :
    let m := !(symCondClean s.q flag && s.q.regq.contains ra && s.q.regq.contains rb)
    let q' : SMarks := { s.q with
      regq := if m then s.q.regq.filter (· != d) else d :: s.q.regq.filter (· != d),
      lowq := if m then s.q.lowq.filter (· != d) else d :: s.q.lowq.filter (· != d) }
    MarksOk ctx s0 q' (noted bind st (.set (.name dst) (.call "select" [.name cond, .name na, .name nb])) (setReg st d (st.reg ra))) := by
  intro m q'
  obtain ⟨_, hfm, hcnum⟩ := selectCond_sound st hsc
  have hdst_zf : (dst == "zf") = false := by
    by_cases h1 : dst = "zf"
    · subst h1; have : regOf bind "zf" = none := by simp [regOf, isRegisterLetter]; decide
      rw [this] at hd; cases hd
    · exact beq_false_of_ne h1
  have hdst_cf : (dst == "cf") = false := by
    by_cases h1 : dst = "cf"
    · subst h1; have : regOf bind "cf" = none := by simp [regOf, isRegisterLetter]; decide
      rw [this] at hd; cases hd
    · exact beq_false_of_ne h1
  have hm_false : m = false → exprMark bind st (.call "select" [.name cond, .name na, .name nb]) = false := by
    intro hm0
    have hcl : symCondClean s.q flag = true ∧ ra ∈ s.q.regq ∧ rb ∈ s.q.regq := by
      simp only [m, Bool.not_eq_false', Bool.and_eq_true, List.contains_iff_mem] at hm0
      exact ⟨hm0.1.1, hm0.1.2, hm0.2⟩
    have hcm : condMark st.marks flag = false := by
      have h1 := hcl.1; unfold symCondClean at h1; unfold condMark
      by_cases hz : (flag == "zf") = true
      · simp only [hz, ↓reduceIte] at h1 ⊢; exact M.zf h1
      · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
        by_cases hh : (flag == "hi") = true
        · simp only [hh, ↓reduceIte, Bool.and_eq_true] at h1 ⊢; simp [M.cf h1.1, M.zf h1.2]
        · simp only [hh, Bool.false_eq_true, ↓reduceIte] at h1 ⊢; exact M.cf h1
    have hma := M.reg ra hcl.2.1
    have hmb := M.reg rb hcl.2.2
    simp [exprMark, lowOnly, exprMarks, hcnum, hfm, hcm, hna, hnb,
      flagMark_none_of_regOf hra, flagMark_none_of_regOf hrb, hra, hrb, hma, hmb, memWidth]
  have hlow_eq : lowMark bind st (.call "select" [.name cond, .name na, .name nb]) =
      exprMark bind st (.call "select" [.name cond, .name na, .name nb]) := by
    simp [lowMark]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    show (marksAfter bind st (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))).reg r = false
    simp only [marksAfter, stmtParts, hdst_zf, hdst_cf, hd, Bool.false_eq_true, ↓reduceIte]
    cases hm : m with
    | true =>
      simp only [q', hm, ↓reduceIte, List.mem_filter, bne_iff_ne] at hr
      simp only [hr.2, ↓reduceIte]
      exact M.reg r hr.1
    | false =>
      simp only [q', hm, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_filter, bne_iff_ne] at hr
      rcases hr with rfl | ⟨hr1, hr2⟩
      · simp only [↓reduceIte]; exact hm_false hm
      · simp only [hr2, ↓reduceIte]; exact M.reg r hr1
  · intro hzq
    show (marksAfter bind st (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))).zf = false
    simp only [marksAfter, stmtParts, hdst_zf, hdst_cf, hd, Bool.false_eq_true, ↓reduceIte]
    exact M.zf hzq
  · intro hcq
    show (marksAfter bind st (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))).cf = false
    simp only [marksAfter, stmtParts, hdst_zf, hdst_cf, hd, Bool.false_eq_true, ↓reduceIte]
    exact M.cf hcq
  · intro a h1 h2
    show (marksAfter bind st (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))).mem a = s0.marks.mem a
    simp only [marksAfter, stmtParts, hdst_zf, hdst_cf, hd, Bool.false_eq_true, ↓reduceIte]
    exact M.stable a h1 h2
  · show CellsOk ctx s0 q'.fq (marksAfter bind st (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))).mem
    simp only [marksAfter, stmtParts, hdst_zf, hdst_cf, hd, Bool.false_eq_true, ↓reduceIte]
    exact M.frame
  · intro r hr
    show ((marksAfter bind st (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))).reg r &&
          (marksAfter bind st (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))).low r) = false
    simp only [marksAfter, stmtParts, hdst_zf, hdst_cf, hd, Bool.false_eq_true, ↓reduceIte, hlow_eq]
    cases hm : m with
    | true =>
      simp only [q', hm, ↓reduceIte, List.mem_filter, bne_iff_ne] at hr
      simp only [hr.2, ↓reduceIte]
      exact M.low r hr.1
    | false =>
      simp only [q', hm, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_filter, bne_iff_ne] at hr
      rcases hr with rfl | ⟨hr1, hr2⟩
      · simp only [↓reduceIte, hm_false hm, Bool.and_self]
      · simp only [hr2, ↓reduceIte]; exact M.low r hr1

theorem symReturn_sp {ctx : Ctx} {s : Sym} {items : Items} {r : Unit × Items} (h : symReturn ctx s items = .ok r) : s.sp = some 0 := by
  unfold symReturn at h
  split at h
  next => exact (refuse_ok h).elim
  next hsp => simpa using hsp

/-- An instruction the verifier has gone through, of the machine that stops where something marked shows:
whatever the unknowns turn out to be it does not fault and does not stop; if it returns, what the contract
says the function leaves is so; if it goes on, it goes on at one of the places the verifier went on at, in
a state of which what the verifier holds there is so, the marks too. -/
theorem symCondClean_sound {ctx : Ctx} {s0 : State} {q : SMarks} {st : State} (M : MarksOk ctx s0 q st)
    (flag : String) (h : symCondClean q flag = true) : condMark st.marks flag = false := by
  unfold symCondClean at h; unfold condMark
  by_cases hz : (flag == "zf") = true
  · simp only [hz, ↓reduceIte] at h ⊢; exact M.zf h
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hh : (flag == "hi") = true
    · simp only [hh, ↓reduceIte, Bool.and_eq_true] at h ⊢
      simp [M.cf h.1, M.zf h.2]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact M.cf h

theorem symCondFlag_holds {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (flag : String) : (symCondFlag s flag).holds ρ (condFlag st flag) := by
  unfold symCondFlag condFlag
  by_cases hz : (flag == "zf") = true
  · simp only [hz, ↓reduceIte]; exact H.zf
  · simp only [hz, Bool.false_eq_true, ↓reduceIte]
    by_cases hh : (flag == "hi") = true
    · simp only [hh, ↓reduceIte]
      cases hzf : s.zf with
      | unknown | below _ _ => simp [Flag.holds]
      | equal a b =>
        cases hcf : s.cf with
        | unknown | equal _ _ => simp [Flag.holds]
        | below a' b' =>
          simp only
          split
          next hsame =>
            simp only [Bool.and_eq_true, Lin.same_iff] at hsame
            obtain ⟨rfl, rfl⟩ := hsame
            have h1 := H.zf; rw [hzf] at h1; simp only [Flag.holds] at h1
            have h2 := H.cf; rw [hcf] at h2; simp only [Flag.holds] at h2
            simp only [Flag.holds, h1, h2]
            by_cases hlt : ev ρ b < ev ρ a <;> by_cases heq : ev ρ a = ev ρ b <;> by_cases hlt2 : ev ρ a < ev ρ b <;> simp_all <;> omega
          next => simp [Flag.holds]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte]; exact H.cf

theorem symCondFlag_bounded {ctx : Ctx} {s : Sym} (wf : WF ctx s) (flag : String) :
    (symCondFlag s flag).bounded s.nvars := by
  unfold symCondFlag
  by_cases hz : (flag == "zf") = true
  · simp only [hz, ↓reduceIte]; exact wf.zf
  · simp only [hz, Bool.false_eq_true, ↓reduceIte]
    by_cases hh : (flag == "hi") = true
    · simp only [hh, ↓reduceIte]
      cases hzf : s.zf with
      | unknown | below _ _ => simp [Flag.bounded]
      | equal a b =>
        cases hcf : s.cf with
        | unknown | equal _ _ => simp [Flag.bounded]
        | below a' b' =>
          simp only
          split
          · have h1 := wf.zf; rw [hzf] at h1; exact ⟨h1.2, h1.1⟩
          · simp [Flag.bounded]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte]; exact wf.cf

theorem condFlag_alike {a b : State} (A : Alike a b) (flag : String) (h : condMark a.marks flag = false) :
    condFlag a flag = condFlag b flag := by
  unfold condMark at h; unfold condFlag
  by_cases hz : (flag == "zf") = true
  · simp only [hz, ↓reduceIte] at h ⊢; exact A.zf h
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hh : (flag == "hi") = true
    · simp only [hh, ↓reduceIte, Bool.or_eq_false_iff] at h ⊢
      rw [A.cf h.1, A.zf h.2]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact A.cf h

theorem symCondFlag_valEq {ρa ρb : Nat → Int} {s : Sym} (FE : FlagEq ρa ρb s) (flag : String)
    (h : symCondClean s.q flag = true) : FlagValEq ρa ρb (symCondFlag s flag) := by
  unfold symCondClean at h; unfold symCondFlag
  by_cases hz : (flag == "zf") = true
  · simp only [hz, ↓reduceIte] at h ⊢; exact FE.1 h
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hh : (flag == "hi") = true
    · simp only [hh, ↓reduceIte, Bool.and_eq_true] at h ⊢
      cases hzf : s.zf with
      | unknown | below _ _ => simp [FlagValEq]
      | equal a b =>
        cases hcf : s.cf with
        | unknown | equal _ _ => simp [FlagValEq]
        | below a' b' =>
          simp only
          split
          · have h1 := FE.1 h.2; rw [hzf] at h1; exact ⟨h1.2, h1.1⟩
          · simp [FlagValEq]
    · simp only [hh, Bool.false_eq_true, ↓reduceIte] at h ⊢; exact FE.2 h

theorem symInstr_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s : Sym} {i : Instr}
    {nexts : List (Sym × Next)} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symInstr ctx s i items = .ok (nexts, rest)) (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (M : MarksOk ctx s0 s.q st) (u : Nat → Nat) :
    ∃ o, execQ (ctx.contract.perm ctx.pieces s0) p i u st = some o ∧
      match o with
      | .next st' => ∃ s' pc ρ', (s', Next.at pc) ∈ nexts ∧ st'.rip = p.base + pc ∧ Carried ctx s0 ρ s ρ' s' st' ∧ MarksOk ctx s0 s'.q st'
      | .returned st' => ctx.contract.left ctx.defs s0 st' := by
  have Hs : Holds ctx s0 ρ s (started p i st) := H.fields rfl rfl rfl rfl rfl rfl
  have Ms : MarksOk ctx s0 s.q (started p i st) := M.fields rfl
  cases hs : shape i.effect with
  | ret =>
    -- a return to the address at the stack pointer: x86-64's
    have heff := shape_ret hs
    simp only [symInstr, hs] at h
    split at h
    next => exact (refuse_ok h).elim
    next ha =>
    have ha : ctx.contract.arm64 = false := by simpa using ha
    obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
    split at h
    next => exact (refuse_ok h).elim
    next hq =>
      have hq : RSP ∈ s.q.regq ∧ (ctx.contract.resultFollowsTrace = true → 0 ∈ s.q.regq) := by
        simpa using hq
      obtain ⟨al, post⟩ := symReturn_x86 E e1 (H.rip (p.base + i.next)) wf ha
      have qr := return_quiet E Ms Hs ha (symReturn_sp e1) (List.contains_iff_mem.mpr hq.1)
      refine ⟨.returned (setReg { started p i st with rip := load st.mem (st.reg RSP) 8, trace := (started p i st).trace ++ [(st.reg RSP, 8)] } RSP (st.reg RSP + 8)),
        by simp only [execQ, heff, execAllQ]; rw [if_pos (by rw [qr]; exact al)], post_fields post rfl rfl rfl rfl, ?_, ?_, ?_⟩
      · show st.marks.reg RSP = false
        exact M.reg RSP hq.1
      · intro hg
        show st.marks.reg 0 = false
        exact M.reg 0 (hq.2 hg)
      · exact M.stable
  | retLink r =>
    -- a return to the address a register holds: AArch64's
    have heff := shape_retLink hs
    simp only [symInstr, hs] at h
    split at h
    next => exact (refuse_ok h).elim
    next hm =>
    split at h
    next => exact (refuse_ok h).elim
    next hlink =>
    have hm : ctx.contract.arm64 = true ∧ regIndex r = some LINK := by simpa using hm
    have hlink : s.reg LINK = Lin.var LINK := by simpa using hlink
    obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
    split at h
    next => exact (refuse_ok h).elim
    next hq =>
      have hq : RSP ∈ s.q.regq ∧ LINK ∈ s.q.regq ∧ (ctx.contract.resultFollowsTrace = true → 0 ∈ s.q.regq) := by
        simpa using hq
      have post := symReturn_arm E e1 (H.rip (p.base + i.next)) wf hm.1 hlink
      have hmk : st.marks.reg LINK = false := M.reg LINK hq.2.1
      refine ⟨.returned { started p i st with rip := st.reg LINK },
        by simp only [execQ, heff, execAllQ, hm.2, Option.bind, hmk, Bool.false_eq_true, if_false], post_fields post rfl rfl rfl rfl, ?_, ?_, ?_⟩
      · show st.marks.reg RSP = false
        exact M.reg RSP hq.1
      · intro hg
        show st.marks.reg 0 = false
        exact M.reg 0 (hq.2.2 hg)
      · exact M.stable
  | jump target cond =>
    have heff := shape_jump hs
    simp only [symInstr, hs] at h
    cases ht : jumpTarget i.bind target with
    | none => simp only [ht] at h; exact (refuse_ok h).elim
    | some t =>
      simp only [ht] at h
      have hv := jumpTarget_value ht (ctx.contract.perm ctx.pieces s0) (started p i st)
      obtain ⟨qa, qb⟩ := jumpTarget_quiet ht (started p i st)
      cases cond with
      | none =>
        simp only at h
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        have hqs : quietStmt i.bind (started p i st) (.jump target none) = true := by
          simp only [quietStmt, qa, qb, Bool.not_false, Bool.and_true]
        refine ⟨.next (noted i.bind (started p i st) (.jump target none) { started p i st with rip := p.base + t }),
          by simp [execQ, heff, execAllQ, hqs, execStmt, hv], s, t, ρ, List.mem_cons_self .., rfl, Carried.here (H.fields rfl rfl rfl rfl rfl rfl) wf, M.fields rfl⟩
      | some fw =>
        obtain ⟨flag, want⟩ := fw
        simp only at h
        cases hcl : symCondClean s.q flag with
        | false => simp only [hcl, Bool.not_false, ↓reduceIte] at h; exact (refuse_ok h).elim
        | true =>
          simp only [hcl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          have hmk : condMark st.marks flag = false := symCondClean_sound M flag hcl
          have hqs : quietStmt i.bind (started p i st) (.jump target (some (flag, want))) = true := by
            simp only [quietStmt, qa, qb, Bool.not_false, Bool.and_true, Bool.true_and, Bool.not_eq_true']
            exact hmk
          obtain ⟨s', m, c', q'⟩ := jumpWays_sound H wf (condFlag st flag) h (symCondFlag_holds H flag) (symCondFlag_bounded wf flag)
          have hstf : condFlag (started p i st) flag = condFlag st flag := rfl
          by_cases taken : (condFlag st flag == want) = true
          · rw [if_pos taken] at m
            exact ⟨.next (noted i.bind (started p i st) (.jump target (some (flag, want))) { started p i st with rip := p.base + t }),
              by simp only [execQ, heff, execAllQ, hqs, ↓reduceIte, execStmt, hstf, taken, hv, Option.map], s', t, ρ, m, rfl,
              c'.fields rfl rfl rfl rfl rfl rfl, by rw [q']; exact M.fields rfl⟩
          · rw [if_neg taken] at m
            exact ⟨.next (noted i.bind (started p i st) (.jump target (some (flag, want))) (started p i st)),
              by simp only [execQ, heff, execAllQ, hqs, ↓reduceIte, execStmt, hstf, taken, Bool.false_eq_true], s', i.next, ρ, m, rfl,
              c'.fields rfl rfl rfl rfl rfl rfl, by rw [q']; exact M.fields rfl⟩
  | select dst cond a b =>
    have heff := shape_select hs
    simp only [symInstr, hs] at h
    cases hsc : selectCond cond with
    | none => simp only [hsc] at h; exact (refuse_ok h).elim
    | some fw =>
      obtain ⟨flag, want⟩ := fw
      simp only [hsc] at h
      cases hd : ctx.regOf i.bind dst with
      | none => simp only [hd] at h; exact (refuse_ok h).elim
      | some d =>
        cases a with
        | number _ | lane _ _ | call _ _ => simp only [hd] at h; exact (refuse_ok h).elim
        | name na =>
          cases b with
          | number _ | lane _ _ | call _ _ => simp only [hd] at h; exact (refuse_ok h).elim
          | name nb =>
            simp only [hd] at h
            split at h
            next => exact (refuse_ok h).elim
            next hnum =>
              have hnum : isNumberLetter na = false ∧ isNumberLetter nb = false := by simpa using hnum
              cases hra : ctx.regOf i.bind na with
              | none => simp only [hra] at h; exact (refuse_ok h).elim
              | some ra =>
                cases hrb : ctx.regOf i.bind nb with
                | none => simp only [hra, hrb] at h; exact (refuse_ok h).elim
                | some rb =>
                  simp only [hra, hrb] at h
                  split at h
                  next => exact (refuse_ok h).elim
                  next =>
                    split at h
                    next => exact (refuse_ok h).elim
                    next =>
                      obtain ⟨hd', _⟩ := Ctx.regOf_some hd
                      obtain ⟨hra', hralt⟩ := Ctx.regOf_some hra
                      obtain ⟨hrb', hrblt⟩ := Ctx.regOf_some hrb
                      obtain ⟨w, r1, hw, hmap⟩ := V.bind_ok h
                      have hmp := V.pure_ok hmap; injection hmp with hnext _; subst hnext
                      obtain ⟨s', mw, c', _⟩ := jumpWays_sound H wf (condFlag st flag) hw (symCondFlag_holds H flag) (symCondFlag_bounded wf flag)
                      obtain ⟨hfv, _, hcnum⟩ := selectCond_sound (started p i st) hsc
                      have hdst_zf : (dst == "zf") = false := by
                        by_cases h1 : dst = "zf"
                        · subst h1; have : regOf i.bind "zf" = none := by simp [regOf, isRegisterLetter]; decide
                          rw [this] at hd'; cases hd'
                        · exact beq_false_of_ne h1
                      have hdst_cf : (dst == "cf") = false := by
                        by_cases h1 : dst = "cf"
                        · subst h1; have : regOf i.bind "cf" = none := by simp [regOf, isRegisterLetter]; decide
                          rw [this] at hd'; cases hd'
                        · exact beq_false_of_ne h1
                      have hqs : quietStmt i.bind (started p i st) (.set (.name dst) (.call "select" [.name cond, .name na, .name nb])) = true := by
                        simp [quietStmt, stmtParts, addrsQuiet, addrsQuietAll, memWidth]
                      have hval : value (ctx.contract.perm ctx.pieces s0) i.bind (started p i st)
                          (.call "select" [.name cond, .name na, .name nb]) =
                          some (if (condFlag st flag == want) = true then st.reg ra else st.reg rb) := by
                        simp only [value, values, hcnum, hfv, hnum.1, hnum.2,
                          flagVal_none_regOf hra', flagVal_none_regOf hrb', hra', hrb',
                          Option.map, memSize, prim, Bool.false_eq_true, ↓reduceIte]
                        have hcf_st : condFlag (started p i st) flag = condFlag st flag := rfl
                        rw [hcf_st]
                        by_cases ht : (condFlag st flag == want) = true <;> simp [ht]
                      let m := !(symCondClean s.q flag && s.q.regq.contains ra && s.q.regq.contains rb)
                      let q' : SMarks := { s.q with
                        regq := if m then s.q.regq.filter (· != d) else d :: s.q.regq.filter (· != d),
                        lowq := if m then s.q.lowq.filter (· != d) else d :: s.q.lowq.filter (· != d) }
                      have hM' : MarksOk ctx s0 q' (noted i.bind (started p i st)
                          (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))
                          (setReg (started p i st) d (if (condFlag st flag == want) = true then st.reg ra else st.reg rb))) := by
                        have hbase := setSelectReg_marksOk Ms hsc hd' hnum.1 hnum.2 hra' hrb'
                        exact hbase.fields rfl
                      have hex : execQ (ctx.contract.perm ctx.pieces s0) p i u st =
                          some (.next (noted i.bind (started p i st)
                            (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))
                            (setReg (started p i st) d (if (condFlag st flag == want) = true then st.reg ra else st.reg rb)))) := by
                        simp [execQ, heff, execAllQ, hqs, execStmt, hval, isUnknown, hdst_zf, hdst_cf, hd']
                      by_cases taken : (condFlag st flag == want) = true
                      · rw [if_pos taken] at mw
                        have hmem : (setSelectReg s' d (s.reg ra) q', Next.at i.next) ∈
                            w.map (fun x => match x.2 with | .at 1 => (setSelectReg x.1 d (s.reg ra) q', .at i.next) | _ => (setSelectReg x.1 d (s.reg rb) q', .at i.next)) :=
                          List.mem_map.mpr ⟨(s', .at 1), mw, rfl⟩
                        have hcar : Carried ctx s0 ρ s ρ (setSelectReg s' d (s.reg ra) q')
                            (noted i.bind (started p i st) (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))
                              (setReg (started p i st) d (if (condFlag st flag == want) = true then st.reg ra else st.reg rb))) := by
                          refine ⟨c'.agree, c'.mono, ?_, setSelectReg_wf c'.wf (bounded_mono c'.mono (wf.reg ra hralt)) q'⟩
                          rw [if_pos taken]
                          exact setSelectReg_holds c'.holds (H.reg ra hralt) q' _ _ _
                        exact ⟨_, hex, setSelectReg s' d (s.reg ra) q', i.next, ρ, hmem, rfl, hcar, hM'⟩
                      · rw [if_neg taken] at mw
                        have hmem : (setSelectReg s' d (s.reg rb) q', Next.at i.next) ∈
                            w.map (fun x => match x.2 with | .at 1 => (setSelectReg x.1 d (s.reg ra) q', .at i.next) | _ => (setSelectReg x.1 d (s.reg rb) q', .at i.next)) :=
                          List.mem_map.mpr ⟨(s', .at 0), mw, rfl⟩
                        have hcar : Carried ctx s0 ρ s ρ (setSelectReg s' d (s.reg rb) q')
                            (noted i.bind (started p i st) (.set (.name dst) (.call "select" [.name cond, .name na, .name nb]))
                              (setReg (started p i st) d (if (condFlag st flag == want) = true then st.reg ra else st.reg rb))) := by
                          refine ⟨c'.agree, c'.mono, ?_, setSelectReg_wf c'.wf (bounded_mono c'.mono (wf.reg rb hrblt)) q'⟩
                          rw [if_neg taken]
                          exact setSelectReg_holds c'.holds (H.reg rb hrblt) q' _ _ _
                        exact ⟨_, hex, setSelectReg s' d (s.reg rb) q', i.next, ρ, hmem, rfl, hcar, hM'⟩
  | plain =>
    simp only [symInstr, hs] at h
    obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨s2, r2, e2, h⟩ := V.bind_ok h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    obtain ⟨ρ1, st1, c1, x1, rip1, M1⟩ := stmts_sound E i.bind p.base u i.effect 0 e1 Hs wf Ms
    have c2 := settle_sound e2 c1.holds c1.wf
    exact ⟨.next st1, x1, _, i.next, ρ1, List.mem_cons_self .., rip1, (c1.then c2).q _, M1⟩

/-! ## The program's own bytes, at a call -/

/-- At a call the program is loaded, as it was at the caller's entry: its files' read-only data lies where it
lay, and the caller has written none of it (no byte of it is in the caller's frame or in a run given to
write, where alone memory and marks may have changed), nor is the address to come back to written into it. -/
theorem loaded_call {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (q : Program) (i : Instr) {c : Contract}
    (hl : callLink i = c.link) (h8 : c.slot ≤ st.reg RSP)
    (hw : allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true) :
    Loaded ctx.pieces (afterCall p q i st) := by
  intro k pc hk
  obtain ⟨fit, al, bytes⟩ := E.loaded k pc hk
  have hdata : (afterCall p q i st).data = s0.data := (afterCall_data p q i st).trans H.data.2
  rw [hdata]
  refine ⟨fit, al, fun j hj => ?_⟩
  obtain ⟨hf, ho⟩ := E.apart _ (inPieces_iff.mpr ⟨k, pc, hk, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩)
  have hnot : ¬ (st.reg RSP - c.slot ≤ s0.data k + j ∧ s0.data k + j < st.reg RSP - c.slot + c.slot) := fun hin => by
    have := allowed_at hw _ hin.1 hin.2
    simp [Contract.perm, hf, ho] at this
  rw [afterCall_mem hl h8 (by omega), H.mem _ hf ho]
  exact bytes j hj

/-- At a call, nothing the called function may write, and no byte of the address to come back to, is of the
program's own bytes (its files' read-only data, its code): all of that the caller may write, and of what the
caller may write it is so. -/
theorem clear_call {world : List Program} {ctx : Ctx} {s0 : State} (Kc : ctx.contract.clear world ctx.pieces s0)
    {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) {c : Contract} (p q : Program) (i : Instr)
    (hl : callLink i = c.link)
    (hw : allowed (ctx.contract.perm ctx.pieces s0).write (st.reg RSP - c.slot) c.slot = true)
    (hwrite : ∀ a, (c.perm ctx.pieces (afterCall p q i st)).write a = true → (ctx.contract.perm ctx.pieces s0).write a = true) :
    c.clear world ctx.pieces (afterCall p q i st) := by
  intro a hfix
  have hfix0 : Fixed world ctx.pieces s0 a := by
    rcases hfix with h | h
    · left; rw [← inPieces_data (show (afterCall p q i st).data = s0.data from (afterCall_data p q i st).trans H.data.2) a]; exact h
    · right; exact h
  obtain ⟨hf, ho, _⟩ := Kc a hfix0
  have hnw : (ctx.contract.perm ctx.pieces s0).write a = false := by simp [Contract.perm, hf, ho]
  have hcw : (c.perm ctx.pieces (afterCall p q i st)).write a = false := by
    cases hx : (c.perm ctx.pieces (afterCall p q i st)).write a with
    | false => rfl
    | true => rw [hwrite a hx] at hnw; cases hnw
  simp only [Contract.perm, Bool.or_eq_false_iff] at hcw
  refine ⟨hcw.1, hcw.2, fun hin => ?_⟩
  rw [afterCall_rsp hl] at hin
  have := allowed_at hw a hin.1 hin.2
  rw [hnw] at this
  cases this

/-! ## Clearing a register mark by value (`symRevealReg`, `symClears`) -/

theorem post_plain {c : Contract} {defs : List Def} {s0 s1 s2 : State} (hp : s1.plain = s2.plain)
    (h : c.post defs s0 s1) : c.post defs s0 s2 :=
  post_fields h (congrArg State.reg hp).symm (congrArg State.mem hp).symm (congrArg State.rip hp).symm (congrArg State.vec hp).symm

theorem symRevealReg_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0)
    {s s' : Sym} {r : Nat} {e : SExpr} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symRevealReg ctx s r e items = .ok (s', rest))
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) :
    r < ctx.nreg ∧ ctx.contract.traceClean e = true ∧
    s' = { s with q := { s.q with regq := r :: s.q.regq } } ∧
    Value ctx.defs (ctx.contract.env s0) e (.int (st.reg r)) := by
  unfold symRevealReg at h
  split at h
  next => exact (refuse_ok h).elim
  next hr =>
    have hr : r < ctx.nreg := by simpa using hr
    split at h
    next => exact (refuse_ok h).elim
    next _ =>
      split at h
      next => exact (refuse_ok h).elim
      next hcl =>
      have hcl : ctx.contract.traceClean e = true := by simpa using hcl
      obtain ⟨⟨res, s1⟩, r1, e1, h⟩ := V.bind_ok h
      obtain ⟨ρ1, c1, sem, bd⟩ := seval_sound E _ e e1 H wf ((symEnv_bounded ctx.contract).mono wf.regs)
      rw [semEnv_symEnv ctx s0 ρ1 c1.holds.entry] at sem
      have hreg := c1.holds.reg r hr
      cases res with
      | list _ => exact (refuse_ok h).elim
      | val v =>
        cases v with
        | region _ | bool _ => exact (refuse_ok h).elim
        | lin v =>
          simp only at h
          obtain ⟨_, r2, g1, h⟩ := V.bind_ok h
          obtain ⟨_, r3, g2, h⟩ := V.bind_ok h
          have hp := V.pure_ok h; injection hp with hs' _; subst hs'
          have g1 := entail_sound g1 ρ1 c1.holds.facts
          have g2 := entail_sound g2 ρ1 c1.holds.facts
          simp only [ev_sub] at g1 g2
          simp only [SRes.sem, semv] at sem
          have : ev ρ1 v = (st.reg r : Int) := by omega
          rw [this] at sem
          exact ⟨hr, hcl, rfl, sem⟩
      | tail c =>
        simp only at h
        obtain ⟨s2, r2, g1, h⟩ := V.bind_ok h
        have hp := V.pure_ok h; injection hp with hs' _; subst hs'
        obtain ⟨ρ2, c2, gh⟩ := specGoal_sound E 16 g1 c1.holds c1.wf ⟨bd, c1.wf.reg r hr⟩
        simp only [SFact.holds] at gh
        rw [← ev_agree (c1.wf.reg r hr) c2.agree, ← hreg] at gh
        exact ⟨hr, hcl, rfl, (sem _).mpr ((CallValue_agree bd c2.agree _).mpr gh)⟩

theorem symClears_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) :
    ∀ (fuel : Nat) {pc : Nat} {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State},
    symClears ctx pc fuel s items = .ok (s', rest) →
    Holds ctx s0 ρ s st → WF ctx s → MarksOk ctx s0 s.q st →
    ∃ st', st'.plain = st.plain ∧ Holds ctx s0 ρ s' st' ∧ WF ctx s' ∧ MarksOk ctx s0 s'.q st' ∧
      s'.nvars = s.nvars ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧ s'.q.zq = s.q.zq ∧ s'.q.cq = s.q.cq
  | 0, _, s, s', items, rest, ρ, st, h, H, wf, M => by
    simp only [symClears] at h
    have hp := V.pure_ok h; injection hp with hs' _; subst hs'
    exact ⟨st, rfl, H, wf, M, rfl, rfl, rfl, rfl, rfl⟩
  | fuel + 1, pc, s, s', items, rest, ρ, st, h, H, wf, M => by
    simp only [symClears] at h
    obtain ⟨opt, r1, _, h⟩ := V.bind_ok h
    cases opt with
    | none =>
      have hp := V.pure_ok h; injection hp with hs' _; subst hs'
      exact ⟨st, rfl, H, wf, M, rfl, rfl, rfl, rfl, rfl⟩
    | some re =>
      obtain ⟨r, e⟩ := re
      obtain ⟨s1, r2, hrev, hrest⟩ := V.bind_ok h
      obtain ⟨_, _, hs1, _⟩ := symRevealReg_sound E hrev H wf
      subst hs1
      have H1 : Holds ctx s0 ρ { s with q := { s.q with regq := r :: s.q.regq } } (unmarkReg st r) :=
        (H.q _).fields rfl rfl rfl rfl rfl rfl
      have M1 : MarksOk ctx s0 { s.q with regq := r :: s.q.regq } (unmarkReg st r) :=
        M.unmarkReg r
      obtain ⟨st', hpl, H', wf', M', hnv, hzf, hcf, hzq, hcq⟩ :=
        symClears_sound E fuel hrest H1 (wf.q _) M1
      exact ⟨st', hpl.trans (unmarkReg_plain st r), H', wf', M', hnv, hzf, hcf, hzq, hcq⟩

theorem symClears_empty {ctx : Ctx} (he : ctx.contract.traceExprs.isEmpty = true) :
    ∀ (fuel : Nat) {pc : Nat} {s s' : Sym} {items rest : Items},
    symClears ctx pc fuel s items = .ok (s', rest) → s' = s
  | 0, _, _, _, _, _, h => by
    simp only [symClears] at h; have hp := V.pure_ok h; injection hp with hs' _
  | fuel + 1, _, _, _, _, _, h => by
    simp only [symClears] at h
    obtain ⟨opt, _, _, h⟩ := V.bind_ok h
    cases opt with
    | none => have hp := V.pure_ok h; injection hp with hs' _
    | some re =>
      obtain ⟨r, e⟩ := re
      obtain ⟨_, _, hrev, _⟩ := V.bind_ok h
      unfold symRevealReg at hrev
      split at hrev
      · exact (refuse_ok hrev).elim
      · exact (refuse_ok (by simpa [he] using hrev)).elim

/-! ## Paths -/

/-- One instruction, in general: if from every state the machine can go on in, at a place the verifier
went on at, the machine runs to its return and leaves what the contract promises, so it does from here.
At a call, the called function runs by its contract, which it meets, and the machine goes on after it. -/
theorem step_runs {world : List Program} {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (W : CalleesMeetAt world ctx s0)
    (Kc : ctx.contract.clear world ctx.pieces s0)
    {s : Sym} {pc : Nat} {i : Instr}
    {nexts : List (Sym × Next)} {items rest : Items} {ρ : Nat → Int} {st : State}
    (hl : ctx.code.lookup pc = some i) (h : symNext ctx s i items = .ok (nexts, rest))
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hrip : st.rip = p.base + pc) (M : MarksOk ctx s0 s.q st)
    (K : ∀ s' pc' ρ' st', (s', Next.at pc') ∈ nexts → st'.rip = p.base + pc' → Carried ctx s0 ρ s ρ' s' st' →
      MarksOk ctx s0 s'.q st' → RunsPlain world (ctx.contract.perm ctx.pieces s0) p (ctx.contract.post ctx.defs s0) st') :
    RunsPlain world (ctx.contract.perm ctx.pieces s0) p (ctx.contract.post ctx.defs s0) st := by
  have hfetch : p.fetch st.rip = some i := by
    unfold Program.fetch
    rw [hrip, if_neg (by omega), E.code, Nat.add_sub_cancel_left]
    exact hl
  cases hc : callTarget i with
  | none =>
    cases ht : tailTarget i with
    | none =>
      simp only [symNext, hc, ht] at h
      apply RunsPlain.step _ p _ st i hfetch
      · intro u hn
        obtain ⟨o, ho, _⟩ := symInstr_sound E h H wf M u
        have hx := execQ_exec ho
        rw [hx] at hn
        cases hn
      · intro u st' hx
        obtain ⟨o, ho, hmatch⟩ := symInstr_sound E h H wf M u
        have ho' := execQ_exec ho
        rw [hx] at ho'
        injection ho' with ho'
        subst ho'
        obtain ⟨s', pc', ρ', m, hrip', c', M'⟩ := hmatch
        exact K s' pc' ρ' st' m hrip' c' M'
      · intro u st' hx
        obtain ⟨o, ho, hmatch⟩ := symInstr_sound E h H wf M u
        have ho' := execQ_exec ho
        rw [hx] at ho'
        injection ho' with ho'
        subst ho'
        exact hmatch.1
    | some name =>
      simp only [symNext, hc, ht] at h
      cases hl2 : ctx.callees.lookup name with
      | none => simp only [hl2] at h; exact (refuse_ok h).elim
      | some c =>
        simp only [hl2] at h
        obtain ⟨_, _, htail, _⟩ := V.bind_ok h
        unfold symTail at htail
        split at htail
        next => exact (refuse_ok htail).elim
        next htf =>
        have T : TailOk ctx s name c := tailFits_spec (by simpa using htf)
        obtain ⟨_, _, _, htail⟩ := V.bind_ok htail
        obtain ⟨s1, _, e0, htail⟩ := V.bind_ok htail
        obtain ⟨_, _, e1, htail⟩ := V.bind_ok htail
        obtain ⟨s', _, e2, htail⟩ := V.bind_ok htail
        split at htail
        next => exact (refuse_ok htail).elim
        next hcq =>
        have c1 := symKnow_sound KNOWN e0 H wf
        have T1 := symKnow_tailOk T KNOWN e0
        have EX := tailPreOk_sound E T1 c1.holds e1
        obtain ⟨q, hq, fitq, meets⟩ := W name c hl2
        obtain ⟨hpre, hread, hwrite, hpost⟩ := tailCall'_sound E T1 EX e2 c1.holds c1.wf q fitq
        have hbd : ∀ r m, ctx.recBound name c s0 = some (r, m) → (afterTail q st).reg r < m := by
          intro r m hb
          unfold Ctx.recBound at hb
          have hne : (ctx.selfName == some name) = false := beq_false_of_ne T.notSelf
          simp only [hne, Bool.false_eq_true, ite_false] at hb
          cases hb
        have hrun := runsPlain_data (meets (afterTail q st) hbd (loaded_tail E c1.holds q) (clear_tail Kc T1 c1.holds q hwrite) hpre)
        rw [afterTail_data] at hrun
        apply RunsPlain.tail _ p _ st i name q (c.perm ctx.pieces (afterTail q st)) hfetch ht hq hread hwrite
        refine runsPlain_mono (fun s2 ⟨hpost2, hdata2⟩ => ?_) hrun
        obtain ⟨ρ', c'⟩ := hpost s2 hpost2 hdata2
        have hret : ∀ (t : State), t.mem = (setReg s2 RSP (s0.reg RSP)).mem → t.vec = (setReg s2 RSP (s0.reg RSP)).vec →
            (∀ r, r ≠ RSP → t.reg r = (setReg s2 RSP (s0.reg RSP)).reg r) →
            t.reg RSP = s0.reg RSP + ctx.contract.slot → t.rip = ctx.contract.backTo s0 →
            ctx.contract.post ctx.defs s0 t := by
          by_cases hsel : hasSelect ctx.code = true
          · simp only [hsel, Bool.true_and, ↓reduceIte] at htail
            split at htail
            · exact (refuse_ok htail).elim
            · split at htail
              · exact (refuse_ok htail).elim
              · split at htail
                · exact (refuse_ok htail).elim
                · intro t hm hv hr hsp hrip
                  exact (symReturn_sound E htail (c'.q _).holds (c'.q _).wf).2 t hm hv hr
                    (by simp [setReg, Nat.mod_eq_of_lt (E.small RSP)]; exact hsp) hrip
          · have hsel' : hasSelect ctx.code = false := Bool.eq_false_iff.mpr hsel
            simp only [hsel', Bool.false_eq_true, Bool.false_and, ↓reduceIte] at htail
            split at htail
            · exact (refuse_ok htail).elim
            · intro t hm hv hr hsp hrip
              exact (symReturn_sound E htail (c'.q _).holds (c'.q _).wf).2 t hm hv hr
                (by simp [setReg, Nat.mod_eq_of_lt (E.small RSP)]; exact hsp) hrip
        apply hret s2 rfl rfl (fun r hr => by simp [setReg, hr])
        · have hs2rsp := hpost2.2.1
          simp only [afterTail] at hs2rsp
          rw [hs2rsp, T1.rsp_eq c1.holds, T1.slot]
        · rw [hpost2.1, T1.backTo_eq E c1.holds q]
  | some name =>
    simp only [symNext, hc] at h
    cases hl2 : ctx.callees.lookup name with
    | none => simp only [hl2] at h; exact (refuse_ok h).elim
    | some c =>
      simp only [hl2] at h
      split at h
      next => exact (refuse_ok h).elim
      next hfit =>
      have hfit : callFits ctx s i c = true := by simpa using hfit
      have F := callFits_sound E H hfit
      split at h
      next => exact (refuse_ok h).elim
      next =>
      obtain ⟨_, _, _, h⟩ := V.bind_ok h
      obtain ⟨s', r1, e1, h⟩ := V.bind_ok h
      split at h
      next => exact (refuse_ok h).elim
      next hcq =>
      have hcq : callQuiet ctx (quietAtCall s c) c = true := by simpa using hcq
      have := V.pure_ok h
      injection this with hn _
      subst hn
      obtain ⟨q, hq, fitq, meets⟩ := W name c hl2
      have hcode : (pc, i) ∈ p.code := by rw [E.code]; exact lookup_mem hl
      obtain ⟨h8, hw, hpre, hdec, hread, hwrite, hpost⟩ := symCall_sound E e1 H wf q fitq i F (E.fits hcode)
      obtain ⟨_, _, hafter⟩ := callQuiet_sound E (quietAtCall_marks M c) (quietAtCall_holds H c) hcq q i F hw hwrite
      have hbd : ∀ r m, ctx.recBound name c s0 = some (r, m) → (afterCall p q i st).reg r < m := by
        intro r m hb
        unfold Ctx.recBound at hb
        split at hb
        next hself =>
          have hself' : ctx.selfName = some name := by simpa using hself
          cases hd : c.decreases with
          | none => simp [hd] at hb
          | some d =>
            simp only [hd, Option.bind_some] at hb
            cases hr : c.regOf d with
            | none => simp [hr] at hb
            | some r' =>
              simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
              obtain ⟨rfl, rfl⟩ := hb
              exact hdec hself' d r' hd hr
        next => cases hb
      have hrun := runsPlain_data (meets _ hbd (loaded_call E H q i F.link h8 hw) (clear_call Kc H p q i F.link hw hwrite) hpre)
      rw [afterCall_data] at hrun
      exact RunsPlain.call _ p _ st i name q (c.perm ctx.pieces (afterCall p q i st))
        (fun s2 => c.post ctx.defs (afterCall p q i st) s2 ∧ s2.data = st.data) c.keeps
        hfetch hc hq
        (fun hnone => by
          have hs := (Contract.link_none (F.link.symm.trans hnone)).2
          rw [hs] at h8 hw
          exact ⟨h8, hw⟩)
        hread hwrite hrun
        (fun s2 lf2 r hr => by
          have := lf2.1.2.2.1 r hr
          obtain ⟨_, ne, nl⟩ := keeps_spec hr
          rw [this, afterCall_reg F.link (callKeeps ne nl)])
        (fun s2 lf2 => by
          let cleanRet := if hasSelect ctx.code then c.resultFollowsTrace && callReturnsClean ctx (quietAtCall s c) c
                          else callReturnsClean ctx (quietAtCall s c) c
          let s2m : State := { s2 with marks := postCallMarks c cleanRet (afterCall p q i st) }
          have hpost_m : c.post ctx.defs (afterCall p q i st) s2m := post_fields lf2.1 rfl rfl rfl rfl
          have hdata_m : s2m.data = st.data := lf2.2
          have hqm : s2m.marks.reg RSP = false ∧ (cleanRet = true → s2m.marks.reg c.retReg = false) ∧
              ∀ a, c.inFrame (afterCall p q i st) a = false → c.inOut (afterCall p q i st) a = false →
                s2m.marks.mem a = (afterCall p q i st).marks.mem a := by
            refine ⟨by simp [s2m, postCallMarks], fun hc0 => by simp [s2m, postCallMarks, hc0], fun a hf ho => ?_⟩
            simp [s2m, postCallMarks, hf, ho]
          obtain ⟨hrip2, ρ', c'⟩ := hpost s2m hpost_m hdata_m
          have hcont := K _ i.next ρ' (backFrom c.keeps st s2m) (List.mem_cons_self ..) hrip2
            ((c'.q _).fields rfl rfl rfl rfl rfl rfl)
            (hafter cleanRet s2m (fun hcr => callReturnsClean_givesNumber (by
              dsimp only [cleanRet] at hcr; split at hcr
              · exact (Bool.and_eq_true _ _ |>.mp hcr).2
              · exact hcr)) hqm)
          exact runsPlain_of_plain (fun _ _ => post_plain) hcont _ rfl)

/-- What the verifier relies on along a path, of each place the path has come to, `n` being the unknowns
in use and `ρ` what they are: from every state of the machine at that place of which the place says what
it says, whose number is less than the number of the place's general state on this path, the machine runs
to the function's return and leaves what the contract promises. -/
def Relied (world : List Program) (ctx : Ctx) (p : Program) (s0 : State) (seen : List Seen) (n : Nat) (ρ : Nat → Int) : Prop :=
  ∀ e ∈ seen, (∀ nr ∈ e.place.names, nr.2 < ctx.nreg) ∧ e.first.nvars ≤ n ∧ bounded n e.d ∧
    ∀ ρ' st', AtPlace ctx e.place s0 e.first ρ ρ' st' → st'.rip = p.base + e.place.pc →
      MarksOk ctx s0 { regq := e.first.q.regq, fq := e.first.q.fq } st' →
      (∃ m : Int, Value ctx.defs (placeVals ctx e.place s0 st') e.place.decreases (.int m) ∧ m + 1 ≤ ev ρ e.d) →
      RunsPlain world (ctx.contract.perm ctx.pieces s0) p (ctx.contract.post ctx.defs s0) st'

theorem Relied.carried {world : List Program} {ctx : Ctx} {p : Program} {s0 : State} {seen : List Seen} {n n' : Nat} {ρ ρ' : Nat → Int}
    (T : Relied world ctx p s0 seen n ρ) (le : n ≤ n') (a : Agree n ρ ρ') : Relied world ctx p s0 seen n' ρ' := by
  intro e m
  obtain ⟨hn, hf, hd, run⟩ := T e m
  refine ⟨hn, Nat.le_trans hf le, bounded_mono le hd, ?_⟩
  intro ρx stx A hrip Mx ⟨k, val, lt⟩
  refine run ρx stx ⟨Agree.trans (Nat.le_refl _) (Agree.mono hf a) A.outer, A.entry, A.data, A.kept, A.small, A.frame, A.mem, A.facts, A.lanes, A.cells, A.wrote, A.vecIntact⟩ hrip Mx ⟨k, val, ?_⟩
  rw [ev_agree hd a]
  exact lt

/-- What the verifier relies on of each join place already verified in the current scope `base` (whose
unknowns are `n = base.nvars` with values `ρb`): from every state matching `e.first`, the machine runs to the
function's return and leaves what the contract promises. -/
def ReliedJoin (world : List Program) (ctx : Ctx) (p : Program) (s0 : State)
    (jdone : List JoinEntry) (n : Nat) (ρb : Nat → Int) : Prop :=
  ∀ e ∈ jdone, (∀ nr ∈ e.place.names, nr.2 < ctx.nreg) ∧ e.first.nvars = n ∧
    ∀ ρ' st', AtPlace ctx e.place s0 e.first ρb ρ' st' → st'.rip = p.base + e.place.pc →
      MarksOk ctx s0 { regq := e.first.q.regq, fq := e.first.q.fq } st' →
      RunsPlain world (ctx.contract.perm ctx.pieces s0) p (ctx.contract.post ctx.defs s0) st'

theorem eachState_prop {α β : Type} {P : β → Prop} {f : β → α → V β} :
    ∀ {xs : List α} {acc acc' : β} {items rest : Items},
    eachState f acc xs items = .ok (acc', rest) → P acc →
    (∀ x ∈ xs, ∀ b b' it it', P b → f b x it = .ok (b', it') → P b') →
    P acc' ∧ (∀ x ∈ xs, ∃ b b' it it', P b ∧ f b x it = .ok (b', it'))
  | [], _, _, _, _, h, hp, _ => by
    have := V.pure_ok h; injection this with h1 _; subst h1
    exact ⟨hp, fun _ m => nomatch m⟩
  | x :: more, acc, acc', items, rest, h, hp, hstep => by
    simp only [eachState] at h
    obtain ⟨mid, r1, h1, h2⟩ := V.bind_ok h
    have hpm : P mid := hstep x (List.mem_cons_self ..) acc mid items r1 hp h1
    obtain ⟨hpa, hmem⟩ := eachState_prop h2 hpm (fun y my => hstep y (List.mem_cons_of_mem _ my))
    refine ⟨hpa, fun y my => ?_⟩
    cases my with
    | head => exact ⟨acc, mid, items, r1, hp, h1⟩
    | tail _ m => exact hmem y m

/-- The paths from a state of which what the verifier holds is so: the machine runs to the function's
return and leaves what the contract promises, and every join place added to `jdone'` in the scope `base`
is sound for every concrete state arriving there. -/
theorem explore_sound {world : List Program} {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (W : CalleesMeetAt world ctx s0)
    (Kc : ctx.contract.clear world ctx.pieces s0) :
    ∀ (fuel : Nat) {base : Sym} {seen : List Seen} {jstack : List Nat} {jdone jdone' : List JoinEntry}
      {s : Sym} {pc : Nat} {items rest : Items} {ρb : Nat → Int} {stb : State},
    explore ctx fuel base seen jstack jdone s pc items = .ok (jdone', rest) →
    Holds ctx s0 ρb base stb → WF ctx base →
    Relied world ctx p s0 seen base.nvars ρb →
    ReliedJoin world ctx p s0 jdone base.nvars ρb →
    ReliedJoin world ctx p s0 jdone' base.nvars ρb ∧
    (∀ ρ st, base.nvars ≤ s.nvars → Agree base.nvars ρb ρ →
      Holds ctx s0 ρ s st → WF ctx s → st.rip = p.base + pc → MarksOk ctx s0 s.q st →
      RunsPlain world (ctx.contract.perm ctx.pieces s0) p (ctx.contract.post ctx.defs s0) st)
  | 0, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _ => by
    simp only [explore] at h
    exact (refuse_ok h).elim
  | fuel + 1, base, seen, jstack, jdone, jdone', s, pc, items, rest, ρb, stb, h, Hb, wfb, Tb, Jb => by
    cases hl : ctx.code.lookup pc with
    | none => simp only [explore, hl] at h; exact (refuse_ok h).elim
    | some i =>
      simp only [explore, hl] at h
      obtain ⟨sc, r0, hc, h⟩ := V.bind_ok h
      obtain ⟨nexts, r1, e1, h⟩ := V.bind_ok h
      have honward_J : ∀ nx ∈ nexts, ∀ jd jd' it it',
          ReliedJoin world ctx p s0 jd base.nvars ρb →
          onward ctx base seen jstack (explore ctx fuel) jd nx it = .ok (jd', it') →
          ReliedJoin world ctx p s0 jd' base.nvars ρb := by
        intro nx _ jd jd' it it' Jcur hbody
        rcases nx with ⟨snx, nxt⟩
        cases nxt with
        | returned =>
          simp only [onward] at hbody
          have := V.pure_ok hbody; injection this with h1 _; subst h1; exact Jcur
        | «at» pc' =>
          simp only [onward] at hbody
          cases hp : ctx.places.find? (fun p => p.pc == pc') with
          | none =>
            simp only [hp] at hbody
            exact (explore_sound E W Kc fuel hbody Hb wfb Tb Jcur).1
          | some pl =>
            simp only [hp] at hbody
            have epc : pl.pc = pc' := by simpa using List.find?_some hp
            cases hj : pl.isJoin with
            | false =>
              simp only [hj, Bool.false_eq_true, ↓reduceIte] at hbody
              cases hs : seen.find? (fun e => e.place.pc == pc') with
              | some e =>
                simp only [hs] at hbody
                obtain ⟨_, _, _, hpur⟩ := V.bind_ok hbody
                have := V.pure_ok hpur; injection this with h1 _; subst h1; exact Jcur
              | none =>
                simp only [hs] at hbody
                obtain ⟨⟨_, _, _⟩, _, _, h2⟩ := V.bind_ok hbody
                obtain ⟨_, _, _, hpur⟩ := V.bind_ok h2
                have := V.pure_ok hpur; injection this with h1 _; subst h1; exact Jcur
            | true =>
              simp only [hj, ↓reduceIte] at hbody
              split at hbody
              · exact (refuse_ok hbody).elim
              · cases hjd : jd.find? (fun e => e.place.pc == pc') with
                | some e =>
                  simp only [hjd] at hbody
                  obtain ⟨_, _, _, hpur⟩ := V.bind_ok hbody
                  have := V.pure_ok hpur; injection this with h1 _; subst h1; exact Jcur
                | none =>
                  simp only [hjd] at hbody
                  cases hfirst : joinFirst ctx base snx pl with
                  | none => simp only [hfirst] at hbody; exact (refuse_ok hbody).elim
                  | some first =>
                    simp only [hfirst] at hbody
                    obtain ⟨_, _, _, h2⟩ := V.bind_ok hbody
                    obtain ⟨g, _, eg, h3⟩ := V.bind_ok h2
                    obtain ⟨jmid, _, hgo, hpur⟩ := V.bind_ok h3
                    have := V.pure_ok hpur; injection this with h1 _; subst h1
                    obtain ⟨hnames, hnv, G⟩ := generalizeJoin_sound E pl hfirst eg Hb wfb
                    obtain ⟨Jmid, runG⟩ := explore_sound E W Kc fuel hgo Hb wfb Tb Jcur
                    intro je mje
                    cases mje with
                    | head =>
                      refine ⟨hnames, hnv, ?_⟩
                      intro ρx stx Ax hripx Mx
                      obtain ⟨ρ'', Hg, wg, leg, agx⟩ := G ρx stx Ax
                      have agb : Agree base.nvars ρb ρ'' := Agree.trans (Nat.le_refl _) (hnv ▸ Ax.outer) agx
                      exact runG ρ'' stx leg agb (Hg.q _) (wg.q _) (by rw [← epc]; exact hripx) Mx
                    | tail _ mt => exact Jmid je mt
      obtain ⟨Jout, hmem⟩ := eachState_prop (P := fun jd => ReliedJoin world ctx p s0 jd base.nvars ρb) h Jb honward_J
      refine ⟨Jout, ?_⟩
      intro ρ st hle hag H wf hrip M
      obtain ⟨stc, hplc, Hc, wfc, Mc, hnv, _, _, _, _⟩ := symClears_sound E CLEARS hc H wf M
      have hripc : stc.rip = p.base + pc := (congrArg State.rip hplc).trans hrip
      have hlec : base.nvars ≤ sc.nvars := hnv ▸ hle
      refine runsPlain_of_plain (fun _ _ => post_plain) ?_ _ hplc
      apply step_runs E W Kc hl e1 Hc wfc hripc Mc
      intro s' pc' ρ' st' m hrip' c' M'
      obtain ⟨jd, jd', items', r', Jcur, hbody⟩ := hmem (s', Next.at pc') m
      have hle' : base.nvars ≤ s'.nvars := Nat.le_trans hlec c'.mono
      have hag' : Agree base.nvars ρb ρ' := Agree.trans hlec hag c'.agree
      have T' : Relied world ctx p s0 seen s'.nvars ρ' := Tb.carried hle' hag'
      simp only [onward] at hbody
      cases hp : ctx.places.find? (fun p => p.pc == pc') with
      | none =>
        simp only [hp] at hbody
        exact (explore_sound E W Kc fuel hbody Hb wfb Tb Jcur).2 ρ' st' hle' hag' c'.holds c'.wf hrip' M'
      | some pl =>
        simp only [hp] at hbody
        have epc : pl.pc = pc' := by simpa using List.find?_some hp
        cases hj : pl.isJoin with
        | true =>
          simp only [hj, ↓reduceIte] at hbody
          split at hbody
          · exact (refuse_ok hbody).elim
          · cases hjd : jd.find? (fun e => e.place.pc == pc') with
            | some e =>
              simp only [hjd] at hbody
              have em : e ∈ jd := List.mem_of_find?_eq_some hjd
              have eq : e.place.pc = pc' := by simpa using List.find?_some hjd
              obtain ⟨_, _, harr, _⟩ := V.bind_ok hbody
              obtain ⟨hn, hnv, run⟩ := Jcur e em
              have A := arriveJoin_sound E e.place hn harr c'.holds c'.wf (hnv.symm ▸ hag')
              exact run ρ' st' A (by rw [eq]; exact hrip') (M'.fewer (arriveJoin_q harr).1 (arriveJoin_q harr).2)
            | none =>
              simp only [hjd] at hbody
              cases hfirst : joinFirst ctx base s' pl with
              | none => simp only [hfirst] at hbody; exact (refuse_ok hbody).elim
              | some first =>
                simp only [hfirst] at hbody
                obtain ⟨_, _, harr, h2⟩ := V.bind_ok hbody
                obtain ⟨g, _, eg, h3⟩ := V.bind_ok h2
                obtain ⟨_, _, hgo, _⟩ := V.bind_ok h3
                obtain ⟨hnames, hnv, G⟩ := generalizeJoin_sound E pl hfirst eg Hb wfb
                have runG := (explore_sound E W Kc fuel hgo Hb wfb Tb Jcur).2
                have A := arriveJoin_sound E pl hnames harr c'.holds c'.wf (hnv.symm ▸ hag')
                obtain ⟨ρ'', Hg, wg, leg, agx⟩ := G ρ' st' A
                have agb : Agree base.nvars ρb ρ'' := Agree.trans (Nat.le_refl _) (hnv ▸ A.outer) agx
                exact runG ρ'' st' leg agb (Hg.q _) (wg.q _) hrip' (M'.fewer (arriveJoin_q harr).1 (arriveJoin_q harr).2)
        | false =>
          simp only [hj, Bool.false_eq_true, ↓reduceIte] at hbody
          cases hs : seen.find? (fun e => e.place.pc == pc') with
          | some e =>
            simp only [hs] at hbody
            have em : e ∈ seen := List.mem_of_find?_eq_some hs
            have eq : e.place.pc = pc' := by simpa using List.find?_some hs
            obtain ⟨_, _, harr, _⟩ := V.bind_ok hbody
            obtain ⟨hn, hf, hd, run⟩ := T' e em
            obtain ⟨A, k, val, lt⟩ := arrive_sound E e.place hn harr c'.holds c'.wf hd
            exact run ρ' st' A (by rw [eq]; exact hrip') (M'.fewer (arrive_q harr).1 (arrive_q harr).2) ⟨k, val, lt⟩
          | none =>
            simp only [hs] at hbody
            obtain ⟨⟨g, d, first⟩, r2, e2, h2⟩ := V.bind_ok hbody
            obtain ⟨_, _, hgo, _⟩ := V.bind_ok h2
            obtain ⟨hn, ρ1, ag1, le1, A1, wg, leg, hd, G⟩ := generalize_sound E pl e2 c'.holds c'.wf
            have T1 : Relied world ctx p s0 seen first.nvars ρ1 := T'.carried le1 ag1
            have all : ∀ (n : Nat) (ρx : Nat → Int) (stx : State), AtPlace ctx pl s0 first ρ1 ρx stx → stx.rip = p.base + pl.pc →
                MarksOk ctx s0 { regq := placeQuiet ctx pl s'.q.regq, fq := s'.q.fq } stx →
                Value ctx.defs (placeVals ctx pl s0 stx) pl.decreases (.int (n : Int)) →
                RunsPlain world (ctx.contract.perm ctx.pieces s0) p (ctx.contract.post ctx.defs s0) stx := by
              intro n
              induction n using Nat.strongRecOn with
              | ind n ih =>
                intro ρx stx A hripx Mx val
                obtain ⟨ρ'', Hg, agx, pos, val'⟩ := G ρx stx A
                have same := Value.unique val val'
                injection same with same
                have a1 : Agree first.nvars ρ1 ρ'' := Agree.trans (Nat.le_refl _) A.outer agx
                have Tinner : Relied world ctx p s0 (⟨pl, d, { first with q := { regq := placeQuiet ctx pl s'.q.regq, fq := s'.q.fq } }⟩ :: seen) g.nvars ρ'' := by
                  intro e me
                  cases me with
                  | head =>
                    refine ⟨hn, leg, hd, ?_⟩
                    intro ρy sty Ay hripy My ⟨k, valy, lty⟩
                    have Ay1 : AtPlace ctx pl s0 first ρ1 ρy sty :=
                      ⟨Agree.trans (Nat.le_refl _) a1 Ay.outer, Ay.entry, Ay.data, Ay.kept, Ay.small, Ay.frame, Ay.mem, Ay.facts, Ay.lanes, Ay.cells, Ay.wrote, Ay.vecIntact⟩
                    obtain ⟨ρz, _, _, posz, valz⟩ := G ρy sty Ay1
                    have samez := Value.unique valy valz
                    injection samez with samez
                    have lty : k + 1 ≤ ev ρ'' d := lty
                    have small : k.toNat < n := by omega
                    exact ih k.toNat small ρy sty Ay1 hripy My (by rw [Int.toNat_of_nonneg (by omega)]; exact valy)
                  | tail _ me => exact (T1.carried leg a1) e me
                exact (explore_sound E W Kc fuel hgo (Hg.q _) (wg.q _) Tinner (fun _ m => nomatch m)).2
                  ρ'' stx (Nat.le_refl _) (Agree.refl _ _) (Hg.q _) (wg.q _) (by rw [← epc]; exact hripx) Mx
            obtain ⟨ρ'', _, _, pos, val⟩ := G ρ1 st' A1
            exact all (ev ρ'' d).toNat ρ1 st' A1 (by rw [epc]; exact hrip')
              (M'.fewer (placeQuiet_all ctx pl s'.q.regq) (List.all_eq_true.mpr fun _ hm => List.contains_iff_mem.mpr hm))
              (by rw [Int.toNat_of_nonneg pos]; exact val)

/-! ## The entry, and the theorem -/

/-- At entry, each fact the verifier starts from is so of what the registers hold. -/
theorem entryFacts_hold {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) :
    ∀ f ∈ entryFacts ctx, f.holds (fun k => (s0.reg k : Int)) := by
  have hstack := E.stack
  have habove := E.above
  unfold M64 at habove
  intro f m
  simp only [entrySym, entryFacts, List.mem_append] at m
  rcases m with (((((((m | m) | m) | m) | m) | m) | m) | m) | m
  · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hl
    have := E.small r
    unfold M64 at this
    simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl
    · rw [holds_iff, ev_var]; omega
    · rw [holds_iff, ev_sub, ev_const, ev_var]; simp only [top]; omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
    rcases m with rfl | rfl
    · rw [holds_iff, ev_sub, ev_const, ev_var]; omega
    · rw [holds_iff, ev_sub, ev_const, ev_var]; omega
  · obtain ⟨⟨b, l⟩, hm, rfl⟩ := List.mem_map.mp m
    have := (E.region hm).1
    unfold M64 at this
    rw [holds_iff]; simp only [ev_sub, ev_const, ev_var]; omega
  · obtain ⟨⟨x, b, n⟩, hm, rfl⟩ := List.mem_map.mp m
    have := (E.out hm).1
    unfold M64 at this
    rw [holds_iff]; simp only [ev_sub, ev_const, ev_var]; omega
  · obtain ⟨⟨x, b⟩, hm, hf⟩ := List.mem_filterMap.mp m
    cases hr : ctx.contract.regOf x with
    | none => simp [hr] at hf
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at hf
      subst hf
      have := E.bound hm hr
      rw [holds_iff]; simp only [ev_sub, ev_const, ev_var]; omega
  · obtain ⟨⟨x, b, n⟩, hm, rfl⟩ := List.mem_map.mp m
    have := (E.fixed hm).1
    unfold M64 at this
    rw [holds_iff]; simp only [ev_sub, ev_const, ev_var]; omega
  · obtain ⟨⟨x, k⟩, hm, hf⟩ := List.mem_filterMap.mp m
    cases hr : ctx.contract.regOf x with
    | none => simp [hr] at hf
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at hf
      subst hf
      have := E.atLeast hm hr
      rw [holds_iff]; simp only [ev_sub, ev_const, ev_var]; omega
  · obtain ⟨⟨x, r, count, l⟩, hm, hf⟩ := List.mem_filterMap.mp m
    split at hf
    next hc =>
      injection hf with hf; subst hf
      unfold Contract.tables at hm
      obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hm
      -- the blocks end below 2^64, and lie apart from the frame and the bytes of the address to return
      -- to, of which there is a byte: so they end at least 64 bytes below 2^64
      obtain ⟨fit, apart, _, _⟩ := E.lane hj hc.1
      have hbyte := hc.2
      have above := E.above
      unfold M64 at fit above
      rw [holds_iff]; simp only [ev_sub, ev_const, ev_scale, ev_var]; omega
    next => cases hf
  · obtain ⟨⟨k, ts⟩, hm, rfl⟩ := List.mem_map.mp m
    rw [holds_iff, ev_preLineRow]
    have hcongr := foldl_preLine_congr ctx.contract (fun r => ev (fun k => (s0.reg k : Int)) (Lin.var r))
      (fun r => (s0.reg r : Int)) (fun _ r _ => ev_var _ r) ts 0
    exact (congrArg (0 ≤ k + ·) hcongr).mpr (E.preLine hm)

/-- Each fact the verifier starts from speaks of the registers at entry alone. -/
theorem entryFacts_bounded (ctx : Ctx) : ∀ f ∈ entryFacts ctx, bounded ctx.nreg f := by
  intro f m
  simp only [entrySym, entryFacts, List.mem_append] at m
  rcases m with (((((((m | m) | m) | m) | m) | m) | m) | m) | m
  · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    have hr := List.mem_range.mp hr
    simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl
    · exact bounded_var hr
    · exact bounded_sub (bounded_const _ _) (bounded_var hr)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
    rcases m with rfl | rfl
    · exact bounded_sub (bounded_var ctx.rsp_lt) (bounded_const _ _)
    · exact bounded_sub (bounded_const _ _) (bounded_var ctx.rsp_lt)
  · obtain ⟨⟨b, l⟩, hm, rfl⟩ := List.mem_map.mp m
    have := regions_lt hm
    exact bounded_sub (bounded_sub (bounded_const _ _) (bounded_var this.1)) (bounded_var this.2)
  · obtain ⟨⟨x, b, n⟩, hm, rfl⟩ := List.mem_map.mp m
    exact bounded_sub (bounded_const _ _) (bounded_var (outs_lt hm))
  · obtain ⟨⟨x, b⟩, hm, hf⟩ := List.mem_filterMap.mp m
    cases hr : ctx.contract.regOf x with
    | none => simp [hr] at hf
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at hf
      subst hf
      exact bounded_sub (bounded_const _ _) (bounded_var (argRegs_lt (regOfIn_mem x ctx.contract.args ctx.contract.argRegs r hr)))
  · obtain ⟨⟨x, b, n⟩, hm, rfl⟩ := List.mem_map.mp m
    exact bounded_sub (bounded_const _ _) (bounded_var (fixeds_lt hm))
  · obtain ⟨⟨x, k⟩, hm, hf⟩ := List.mem_filterMap.mp m
    cases hr : ctx.contract.regOf x with
    | none => simp [hr] at hf
    | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at hf
      subst hf
      exact bounded_sub (bounded_var (argRegs_lt (regOfIn_mem x ctx.contract.args ctx.contract.argRegs r hr))) (bounded_const _ _)
  · obtain ⟨⟨x, r, count, l⟩, hm, hf⟩ := List.mem_filterMap.mp m
    split at hf
    next =>
      injection hf with hf; subst hf
      unfold Contract.tables at hm
      obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hm
      exact bounded_sub (bounded_const _ _) (bounded_scale _ (bounded_var (tableAt_lt hj)))
    next => cases hf
  · obtain ⟨⟨k, ts⟩, _, rfl⟩ := List.mem_map.mp m
    exact preLineRow_bounded ctx.contract Lin.var ctx.nreg (fun x r hr => bounded_var (argRegs_lt (regOfIn_mem x ctx.contract.args ctx.contract.argRegs r hr))) k ts

/-- What the unknowns are at entry: unknown `r`, for each register `r` of the function's machine, is what
that register holds, and the unknown after them is where the read-only data of the function's own file lies. -/
def entryRho (ctx : Ctx) (s0 : State) : Nat → Int := fun k => if k = ctx.nreg then (ctx.own s0 : Int) else (s0.reg k : Int)

theorem entryRho_reg (ctx : Ctx) (s0 : State) {r : Nat} (h : r < ctx.nreg) : entryRho ctx s0 r = s0.reg r := by
  show (if r = ctx.nreg then (ctx.own s0 : Int) else (s0.reg r : Int)) = s0.reg r
  rw [if_neg (by omega)]

theorem entryRho_data (ctx : Ctx) (s0 : State) : entryRho ctx s0 (dataVar ctx) = ctx.own s0 := by
  show (if ctx.nreg = ctx.nreg then (ctx.own s0 : Int) else (s0.reg ctx.nreg : Int)) = ctx.own s0
  rw [if_pos rfl]

/-- At entry, what the verifier starts from about the data's address is so: it is a number from 0 up, and
the data ends below 2^64. -/
theorem dataFacts_hold {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) :
    ∀ f ∈ dataFacts ctx, f.holds (entryRho ctx s0) ∧ bounded (ctx.nreg + 1) f := by
  intro f m
  unfold dataFacts at m
  split at m
  · cases m
  next he =>
    have hd : ctx.data ≠ [] := fun e => he (by rw [e]; rfl)
    have fit := E.data_fits hd
    unfold M64 at fit
    have bv : bounded (ctx.nreg + 1) (Lin.var (dataVar ctx)) := bounded_var (show dataVar ctx < ctx.nreg + 1 from Nat.lt_succ_self _)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
    rcases m with rfl | rfl
    · exact ⟨by rw [holds_iff, ev_var, entryRho_data]; omega, bv⟩
    · exact ⟨by rw [holds_iff, ev_sub, ev_const, ev_var, entryRho_data]; omega, bounded_sub (bounded_const _ _) bv⟩

private theorem symDivide_q (s : Sym) (x : Row) (m : Int) : (symDivide s x m).2.2.q = s.q := by
  unfold symDivide; split <;> rfl

private theorem addValArrayFacts_q (s : Sym) : ∀ vas, (addValArrayFacts s vas).q = s.q
  | [] => rfl
  | (_, _, l, ch, _) :: more => by
    simp only [addValArrayFacts]
    rw [addValArrayFacts_q, symDivide_q]

private theorem addValArrayFacts_flags (s : Sym) : ∀ vas, (addValArrayFacts s vas).zf = s.zf ∧ (addValArrayFacts s vas).cf = s.cf
  | [] => ⟨rfl, rfl⟩
  | (_, _, l, ch, _) :: more => by
    simp only [addValArrayFacts]
    exact ⟨((addValArrayFacts_flags _ more).1).trans (symDivide_flags s (Lin.var l) (ch : Int)).1,
           ((addValArrayFacts_flags _ more).2).trans (symDivide_flags s (Lin.var l) (ch : Int)).2⟩

private theorem entrySym_q (ctx : Ctx) :
    (entrySym ctx).q = { regq := ctx.contract.cleanAtEntry ++ ctx.contract.link.toList } := by
  unfold entrySym
  exact addValArrayFacts_q _ _

private theorem entrySym_flags (ctx : Ctx) : (entrySym ctx).zf = .unknown ∧ (entrySym ctx).cf = .unknown := by
  unfold entrySym
  exact addValArrayFacts_flags _ _

private theorem addValArrayFacts_carried {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) :
    ∀ (vas : List (String × Nat × Nat × Nat × Nat)) {ρ : Nat → Int} {s : Sym},
      (∀ va ∈ vas, va ∈ ctx.contract.valArrays) →
      Holds ctx s0 ρ s s0 → WF ctx s →
      ∃ ρ', Carried ctx s0 ρ s ρ' (addValArrayFacts s vas) s0
  | [], ρ, s, _, H, wf => ⟨ρ, Carried.here H wf⟩
  | (x, r, l, ch, el) :: more, ρ, s, hvas, H, wf => by
    have mva : (x, r, l, ch, el) ∈ ctx.contract.valArrays := hvas _ (List.mem_cons_self ..)
    obtain ⟨r_lt, l_lt, hch_pos, hel_pos, _⟩ := valArrays_lt mva
    obtain ⟨hfit, _, _⟩ := E.valArray mva
    have bl : bounded s.nvars (Lin.var l) := bounded_var (Nat.lt_of_lt_of_le l_lt wf.regs)
    have hl0 : 0 ≤ ev ρ (Lin.var l) := by rw [ev_var, H.entry l l_lt]; omega
    obtain ⟨ρ1, C1, hq, _, bq, _⟩ := symDivide_sound H wf bl (by omega : (0 : Int) < ch) hl0
    have hbd : bounded (symDivide s (Lin.var l) (ch : Int)).2.2.nvars
        (Lin.sub (Lin.const top) (Lin.add (Lin.var r) (Lin.scale (el : Int) (symDivide s (Lin.var l) (ch : Int)).1))) :=
      bounded_sub (bounded_const _ _) (bounded_add (bounded_var (Nat.lt_of_lt_of_le r_lt C1.wf.regs)) (bounded_scale _ bq))
    have hhold : (Lin.sub (Lin.const top) (Lin.add (Lin.var r) (Lin.scale (el : Int) (symDivide s (Lin.var l) (ch : Int)).1))).holds ρ1 := by
      rw [holds_iff, ev_sub, ev_const, ev_add, ev_var, ev_scale, C1.holds.entry r r_lt, hq, ev_var, H.entry l l_lt]
      have hdiv : (s0.reg l : Int) / (ch : Int) = ((s0.reg l / ch : Nat) : Int) := (Int.natCast_ediv (s0.reg l) ch).symm
      have hmul : (el : Int) * ((s0.reg l / ch : Nat) : Int) = ((el * (s0.reg l / ch) : Nat) : Int) := (Int.natCast_mul el _).symm
      rw [hdiv, hmul]; unfold M64 at hfit; unfold top; omega
    have C2 : Carried ctx s0 ρ s ρ1
        { (symDivide s (Lin.var l) (ch : Int)).2.2 with
          facts := Lin.sub (Lin.const top) (Lin.add (Lin.var r) (Lin.scale (el : Int) (symDivide s (Lin.var l) (ch : Int)).1)) :: (symDivide s (Lin.var l) (ch : Int)).2.2.facts } s0 :=
      C1.then ⟨Agree.refl _ _, Nat.le_refl _,
        C1.holds.more [_] (fun f m => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at m; subst m; exact hhold),
        C1.wf.more [_] (fun f m => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at m; subst m; exact hbd)⟩
    obtain ⟨ρ2, C3⟩ := addValArrayFacts_carried E more (fun va m => hvas va (List.mem_cons_of_mem _ m)) C2.holds C2.wf
    exact ⟨ρ2, C2.then C3⟩

/-- At entry, what the verifier starts from is so (the unknowns being what the registers hold, where
the data of the function's own file lies, and the value-array chunk counts). -/
theorem entry_holds {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) :
    ∃ ρ, Holds ctx s0 ρ (entrySym ctx) s0 ∧ WF ctx (entrySym ctx) := by
  let s0sym : Sym :=
    { reg := Lin.var, zf := .unknown, cf := .unknown, frame := [], facts := entryFacts ctx ++ dataFacts ctx, bytes := [], spec := [], nvars := ctx.nreg + 1,
      wrote := [], intact := List.range ctx.contract.outs.length,
      vecIntact := ctx.contract.keepsVec,
      q := { regq := ctx.contract.cleanAtEntry ++ ctx.contract.link.toList } }
  have agree : ∀ k, k < ctx.nreg → (fun k => (s0.reg k : Int)) k = entryRho ctx s0 k := fun k hk => (entryRho_reg ctx s0 hk).symm
  have H0 : Holds ctx s0 (entryRho ctx s0) s0sym s0 := by
    refine ⟨fun r hr => entryRho_reg ctx s0 hr, ⟨entryRho_data ctx s0, rfl⟩,
           (fun r hr => by show (s0.reg r : Int) = ev (entryRho ctx s0) (Lin.var r); rw [ev_var, entryRho_reg ctx s0 hr]),
           E.small, trivial, trivial, (fun _ _ m => nomatch m), (fun _ _ m => nomatch m),
           (fun f m => by
              rcases List.mem_append.mp m with m | m
              · rw [holds_iff, ← ev_agree (entryFacts_bounded ctx f m) agree]; exact entryFacts_hold E f m
              · exact (dataFacts_hold E f m).1),
           (fun _ _ _ m => nomatch m), (fun _ m => nomatch m), (fun _ _ _ => rfl),
           (fun _ _ _ m => nomatch m),
           ⟨(fun x ids h => by simp [s0sym] at h), (fun _ _ _ _ _ _ _ _ => rfl),
            (fun w j i m => by simp [s0sym] at m), fun _ _ h => nomatch h⟩,
           (fun k m => by simp [s0sym] at m), (fun _ h => nomatch h), fun _ _ => rfl⟩
  have wf0 : WF ctx s0sym := by
    refine ⟨Nat.le_refl _, fun r hr => bounded_var (Nat.lt_succ_of_lt hr), trivial, trivial,
           (fun _ _ m => nomatch m), (fun _ _ m => nomatch m),
           (fun f m => by
              rcases List.mem_append.mp m with m | m
              · exact bounded_mono (show ctx.nreg ≤ ctx.nreg + 1 from Nat.le_succ _) (entryFacts_bounded ctx f m)
              · exact (dataFacts_hold E f m).2),
           (fun _ _ _ m => nomatch m), (fun _ m => nomatch m), (fun _ _ _ m => nomatch m),
           ⟨fun i n h => by simp [s0sym, Sym.terms, Tab.list] at h, fun j r h => by simp [s0sym, Sym.terms, Tab.list] at h,
            fun x ids h => by simp [s0sym] at h,
            (fun j a n h => by simp [s0sym, Sym.terms, Tab.list] at h), (fun w j i h => by simp [s0sym] at h), fun _ _ h => nomatch h⟩,
           (fun k m => by simp [s0sym] at m), fun _ h => nomatch h⟩
  obtain ⟨ρ', C⟩ := addValArrayFacts_carried E ctx.contract.valArrays (fun _ m => m) H0 wf0
  exact ⟨ρ', C.holds, C.wf⟩

/-- **What the verifier's yes stands for.** If the verifier says yes of a proof, whatever the proof is, and
every function this one calls meets the contract its call was taken by, then the function's code meets its
contract (`Meets`): from every state at entry in which the program is loaded, in which nothing the function
may write is of the program's own bytes, and of which the caller has seen to what the contract asks, the
machine runs on instructions of the function and of those it calls, touches only memory the contract
allows, and after finitely many instructions returns to its caller with the stack pointer, the registers a
callee keeps and all memory outside its frame as they were, and in rax the value the contract's `returns`
has by the specification's definitions. -/
theorem perm_with_marks (c : Contract) (pieces : List Piece) (s0 : State) (mk : Marks) :
    c.perm pieces { s0 with marks := mk } = c.perm pieces s0 := by
  unfold Contract.perm Contract.inFrame Contract.inOut Contract.inFixed Contract.inLane Contract.inValArray inPieces
  rfl

theorem envIn_with_marks (c : Contract) (s0 : State) (mk : Marks) :
    ∀ args regs, envIn c { s0 with marks := mk } args regs = envIn c s0 args regs
  | [], _ => rfl
  | (_, k) :: _, [] => by cases k <;> rfl
  | (x, .number) :: args, r :: regs => by simp only [envIn, envIn_with_marks c s0 mk args regs]
  | (x, .bytes len) :: args, r :: regs => by simp only [envIn, envIn_with_marks c s0 mk args regs]
  | (x, .out n) :: args, r :: regs => by simp only [envIn, envIn_with_marks c s0 mk args regs]
  | (x, .fixed n) :: args, r :: regs => by simp only [envIn, envIn_with_marks c s0 mk args regs]
  | (x, .inout n) :: args, r :: regs => by simp only [envIn, envIn_with_marks c s0 mk args regs]
  | (x, .valArray _ _ _) :: args, r :: regs => by simp only [envIn, envIn_with_marks c s0 mk args regs]

theorem envWIn_with_marks (c : Contract) (s0 : State) (mk : Marks) :
    ∀ args regs, envWIn c { s0 with marks := mk } args regs = envWIn c s0 args regs
  | [], _ => rfl
  | (_, k) :: _, [] => by cases k <;> rfl
  | (x, .number) :: args, r :: regs => by simp only [envWIn, envWIn_with_marks c s0 mk args regs]
  | (x, .bytes len) :: args, r :: regs => by simp only [envWIn, envWIn_with_marks c s0 mk args regs]
  | (x, .out n) :: args, r :: regs => by simp only [envWIn, envWIn_with_marks c s0 mk args regs]
  | (x, .fixed n) :: args, r :: regs => by simp only [envWIn, envWIn_with_marks c s0 mk args regs]
  | (x, .inout n) :: args, r :: regs => by simp only [envWIn, envWIn_with_marks c s0 mk args regs]
  | (x, .valArray _ _ _) :: args, r :: regs => by simp only [envWIn, envWIn_with_marks c s0 mk args regs]

theorem stackAt_with_marks (c : Contract) (s0 : State) (mk : Marks) :
    c.stackAt { s0 with marks := mk } = c.stackAt s0 := by
  unfold Contract.stackAt
  cases c.stackBits with
  | none => rfl
  | some sb => cases c.regOf sb.arg <;> rfl

theorem post_entry_with_marks (c : Contract) (defs : List Def) (s0 st : State) (mk : Marks) :
    c.post defs { s0 with marks := mk } st ↔ c.post defs s0 st := by
  have henv : c.env { s0 with marks := mk } = c.env s0 := envIn_with_marks c s0 mk _ _
  have henvAfter : c.envAfter { s0 with marks := mk } st = c.envAfter s0 st := by
    unfold Contract.envAfter; cases c.result <;> simp [henv]
  have henvW : c.envW { s0 with marks := mk } = c.envW s0 := by
    unfold Contract.envW Contract.lanesEnv; rw [envWIn_with_marks]; rfl
  have hpreVals : c.preVals defs { s0 with marks := mk } ↔ c.preVals defs s0 := by
    unfold Contract.preVals; simp only [henvW]
  unfold Contract.post Ensure.holds EnsureW.holds
  simp only [Contract.backTo, Contract.inFrame, Contract.inOut, stackAt_with_marks, henv, henvAfter, henvW, hpreVals]

theorem verdictOne_ok {ctx : Ctx} {proof : List Item} (h : verdictOne ctx proof = none) :
    ctx.contract.stackBitsOk = true ∧ ctx.contract.decreasesOk = true ∧
    (hasSelect ctx.code = true → ctx.contract.traceExprs.isEmpty = true) ∧
    ∃ r, verify ctx (Items.ofList proof) = .ok r := by
  unfold verdictOne at h
  split at h
  · cases h
  next =>
    split at h
    · cases h
    next hsb =>
      split at h
      · cases h
      next hd =>
        split at h
        · cases h
        next hsel =>
          cases hv : verify ctx (Items.ofList proof) with
          | error why => simp [hv] at h
          | ok r =>
            have hsel' : hasSelect ctx.code = true → ctx.contract.traceExprs.isEmpty = true := by
              intro hs
              cases h0 : ctx.contract.traceExprs.isEmpty with
              | true => rfl
              | false => exact absurd (by simp [hs, h0]) hsel
            exact ⟨by simpa using hsb, by simpa using hd, hsel', r, rfl⟩

theorem verifyOne_sound_at (world : List Program) (ctx : Ctx) (p : Program) (proof : List Item) (hcode : p.code = ctx.code)
    (h : verdictOne ctx proof = none) (s0 : State) (W : CalleesMeetAt world ctx s0)
    (loaded : Loaded ctx.pieces s0) (clear : ctx.contract.clear world ctx.pieces s0) (pre : ctx.contract.pre p s0) :
    RunsPlain world (ctx.contract.perm ctx.pieces s0) p (ctx.contract.post ctx.defs s0) s0 := by
  let s0' : State := { s0 with marks := {} }
  have hq : ctx.contract.quietAt s0' := by
    refine ⟨fun _ _ => rfl, ?_, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
    unfold Contract.backQuiet; split
    · rfl
    · intro _ _; rfl
  have E : Setting ctx p s0' :=
    ⟨hcode, pre, hq, loaded, fun _ _ _ _ _ => rfl, fun a ha => ⟨(clear a (Or.inl ha)).1, (clear a (Or.inl ha)).2.1⟩⟩
  obtain ⟨_, _, _, r, hv⟩ := verdictOne_ok h
  unfold verify at hv
  obtain ⟨_, r1, e1, _⟩ := V.bind_ok hv
  obtain ⟨ρ0, H, wf⟩ := entry_holds E
  have W' : CalleesMeetAt world ctx s0' := W
  have hr := (explore_sound E W' clear PATH e1 H wf (fun e m => nomatch m) (fun e m => nomatch m)).2
    ρ0 s0' (Nat.le_refl _) (Agree.refl _ _) H wf (by rw [E.rip]; rfl)
    (by rw [entrySym_q]; exact ⟨(fun _ _ => rfl), (fun x => by cases x), (fun x => by cases x), (fun _ _ _ => rfl), CellsOk.nil, (fun _ m => nomatch m)⟩)
  rw [perm_with_marks] at hr
  have hr' := runsPlain_mono (fun t ht => (post_entry_with_marks ctx.contract ctx.defs s0 t {}).mp ht) hr
  exact runsPlain_of_plain (fun _ _ => post_plain) hr' s0 rfl

theorem verifyOne_sound (world : List Program) (ctx : Ctx) (p : Program) (proof : List Item) (hcode : p.code = ctx.code)
    (W : CalleesMeet world ctx) (h : verdictOne ctx proof = none) : Meets world ctx.pieces ctx.contract ctx.defs p :=
  fun s0 loaded clear pre => verifyOne_sound_at world ctx p proof hcode h s0
    (fun name c hl => let ⟨q, hq, hf, M⟩ := W name c hl; ⟨q, hq, hf, M.below _⟩) loaded clear pre

theorem verifyOne_sound_rec (world : List Program) (pieces : List Piece) (defs : List Def)
    (runsOk : List String) (done : List (String × Contract)) (f : Fn) (p : Program)
    (hp : findProgram world f.name = some p) (hc : p.code = f.code) (hf : p.fits)
    (I : ∀ name c, done.lookup name = some c → ∃ q, findProgram world name = some q ∧ q.fits ∧ Meets world pieces c defs q)
    (hpass : verdictOne
      { code := f.code, contract := f.contract, defs := defs, places := f.places,
        callees := if f.contract.decreases.isSome then (f.name, f.contract) :: done else done,
        selfName := if f.contract.decreases.isSome then some f.name else none,
        pieces := pieces, piece := f.piece, runsCallees := runsOk } f.proof = none) :
    Meets world pieces f.contract defs p := by
  let ctx : Ctx :=
    { code := f.code, contract := f.contract, defs := defs, places := f.places,
      callees := if f.contract.decreases.isSome then (f.name, f.contract) :: done else done,
      selfName := if f.contract.decreases.isSome then some f.name else none,
      pieces := pieces, piece := f.piece, runsCallees := runsOk }
  cases hdec : f.contract.decreases with
  | none =>
    have W : CalleesMeet world ctx := fun name c hl => by
      simp only [ctx, hdec, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hl
      exact I name c hl
    exact verifyOne_sound world ctx p f.proof hc W hpass
  | some d =>
    have hdok := (verdictOne_ok hpass).2.1
    simp only [ctx, Contract.decreasesOk, hdec] at hdok
    cases hr : f.contract.regOf d with
    | none => simp [hr] at hdok
    | some rDec =>
      have all : ∀ n s0, s0.reg rDec = n →
          Loaded pieces s0 → f.contract.clear world pieces s0 → f.contract.pre p s0 →
          RunsPlain world (f.contract.perm pieces s0) p (f.contract.post defs s0) s0 := by
        intro n
        refine Nat.strongRecOn n fun n ih => ?_
        intro s0 heq loaded clear pre
        have W : CalleesMeetAt world ctx s0 := by
          intro name c hl
          simp only [ctx, hdec, Option.isSome_some, ↓reduceIte, List.lookup_cons] at hl
          cases hn : (name == f.name) with
          | true =>
            rw [hn] at hl; injection hl with hl
            have e : name = f.name := by simpa using hn
            subst hl e
            refine ⟨p, hp, hf, fun sc hbd hl' hc' hp' => ?_⟩
            have hlt : sc.reg rDec < s0.reg rDec := hbd rDec (s0.reg rDec) (by
              simp [Ctx.recBound, ctx, hdec, hr])
            exact ih (sc.reg rDec) (by omega) sc rfl hl' hc' hp'
          | false =>
            rw [hn] at hl
            obtain ⟨q, hq, fitq, Mq⟩ := I name c hl
            exact ⟨q, hq, fitq, Mq.below _⟩
        exact verifyOne_sound_at world ctx p f.proof hc hpass s0 W loaded clear pre
      exact fun s0 hl hc' hp' => all (s0.reg rDec) s0 rfl hl hc' hp'

theorem verify_sound (world : List Program) (ctx : Ctx) (p : Program) (proof : List Item) (hcode : p.code = ctx.code)
    (W : CalleesMeet world ctx) (h : verdict ctx proof = none) : Meets world ctx.pieces ctx.contract ctx.defs p := by
  unfold verdict at h
  cases hv : verdictOne ctx proof with
  | some why => simp [hv] at h
  | none => exact verifyOne_sound world ctx p proof hcode W hv

/-! ## The functions of a statement, together -/

/-- The functions there are have, under each function's name, the instructions the statement gives for it,
lying in memory. -/
def Linked (world : List Program) (fns : List Fn) : Prop :=
  ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧ p.code = f.code ∧ p.fits

theorem verdictFrom_sound (world : List Program) (pieces : List Piece) (defs : List Def) :
    ∀ (fns : List Fn) (runsOk : List String) (done : List (String × Contract)),
    (∀ name c, done.lookup name = some c → ∃ q, findProgram world name = some q ∧ q.fits ∧ Meets world pieces c defs q) →
    Linked world fns → verdictFrom.go pieces defs runsOk done fns = none →
    ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧ Meets world pieces f.contract defs p
  | [], _, _, _, _, _ => fun f m => nomatch m
  | f :: more, runsOk, done, I, L, h => by
    simp only [verdictFrom.go] at h
    split at h
    · cases h
    · let ctx : Ctx :=
        { code := f.code, contract := f.contract, defs := defs, places := f.places,
          callees := if f.contract.decreases.isSome then (f.name, f.contract) :: done else done,
          selfName := if f.contract.decreases.isSome then some f.name else none,
          pieces := pieces, piece := f.piece, runsCallees := runsOk }
      cases hv : verdict ctx f.proof with
      | some why => simp [ctx, hv] at h
      | none =>
        simp only [ctx, hv] at h
        obtain ⟨p, hp, hc, hf⟩ := L f (List.mem_cons_self ..)
        have hpass1 : verdictOne ctx f.proof = none := by
          unfold verdict at hv; cases hv1 : verdictOne ctx f.proof with
          | none => rfl
          | some _ => rw [hv1] at hv; cases hv
        have M : Meets world pieces f.contract defs p := verifyOne_sound_rec world pieces defs runsOk done f p hp hc hf I hpass1
        have I' : ∀ name c, ((f.name, f.contract) :: done).lookup name = some c →
            ∃ q, findProgram world name = some q ∧ q.fits ∧ Meets world pieces c defs q := by
          intro name c hl
          rw [List.lookup_cons] at hl
          cases hn : (name == f.name) with
          | true =>
            rw [hn] at hl
            injection hl with hl
            have e : name = f.name := by simpa using hn
            subst hl e
            exact ⟨p, hp, hf, M⟩
          | false =>
            rw [hn] at hl
            exact I name c hl
        intro g m
        cases m with
        | head => exact ⟨p, hp, M⟩
        | tail _ m => exact verdictFrom_sound world pieces defs more _ _ I' (fun g m => L g (List.mem_cons_of_mem _ m)) h g m

/-- **What the verifier's yes of a statement stands for.** If the verifier says yes of the functions of a
statement, whatever the proofs are, then every one of them meets its contract: given only that the
functions there are have, under each name, the instructions the statement gives, lying in memory. Nothing
is assumed of any function: each one called is itself in the statement, and is shown before its caller.
`pieces` is the read-only data of the object files, as the statement gives it: a function meets its
contract wherever the program is loaded (`Meets`: from every state in which that data lies in memory, at
any addresses, and nothing the function may write is of the program's own bytes). -/
theorem verify_all_sound (world : List Program) (pieces : List Piece) (defs : List Def) (fns : List Fn) (L : Linked world fns)
    (h : verdictAll pieces defs fns = none) :
    ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧ Meets world pieces f.contract defs p :=
  verdictFrom_sound world pieces defs fns [] [] (fun name c hl => by simp [List.lookup] at hl) L h

/-! ## Two-run lockstep trace and result soundness (`verify_all_trace`, `verify_all_result`) -/

mutual
  theorem markOf_bytes (ctx : Ctx) (bind : Bind) (s s1 s1' : Sym) (hb : s1'.bytes = s1.bytes) :
      ∀ (e : Expr), markOf ctx bind s s1' e = markOf ctx bind s s1 e
    | .number _ => rfl
    | .lane _ _ => rfl
    | .name _ => rfl
    | .call f args => by
      simp only [markOf, marksOf_bytes ctx bind s s1 s1' hb args, publicLoad, hb]
  theorem marksOf_bytes (ctx : Ctx) (bind : Bind) (s s1 s1' : Sym) (hb : s1'.bytes = s1.bytes) :
      ∀ (es : List Expr), marksOf ctx bind s s1' es = marksOf ctx bind s s1 es
    | [] => rfl
    | e :: es => by simp only [marksOf, markOf_bytes ctx bind s s1 s1' hb e, marksOf_bytes ctx bind s s1 s1' hb es]
end

theorem FlagValEq.mono {n : Nat} {ρa ρa' ρb ρb' : Nat → Int} {f : Flag}
    (hb : f.bounded n) (aa : Agree n ρa ρa') (ab : Agree n ρb ρb') (h : FlagValEq ρa ρb f) :
    FlagValEq ρa' ρb' f := by
  cases f with
  | unknown => trivial
  | equal x y =>
    exact ⟨by rw [← ev_agree hb.1 aa, ← ev_agree hb.1 ab]; exact h.1,
           by rw [← ev_agree hb.2 aa, ← ev_agree hb.2 ab]; exact h.2⟩
  | below x y =>
    exact ⟨by rw [← ev_agree hb.1 aa, ← ev_agree hb.1 ab]; exact h.1,
           by rw [← ev_agree hb.2 aa, ← ev_agree hb.2 ab]; exact h.2⟩

theorem symStmt_nonflag_flags {ctx : Ctx} {bind : Bind} {s s1 : Sym} {stmt : Stmt} {items rest : Items}
    (h : symStmt ctx bind s stmt items = .ok (s1, rest))
    (hnz : ∀ v, stmt ≠ .set (.name "zf") v) (hnc : ∀ v, stmt ≠ .set (.name "cf") v) :
    s1.zf = s.zf ∧ s1.cf = s.cf := by
  cases stmt with
  | nothing => simp only [symStmt] at h; have := V.pure_ok h; injection this with h _; subst h; exact ⟨rfl, rfl⟩
  | ret | retLink _ | call _ | callLink _ _ | jump _ _ => simp only [symStmt] at h; exact (refuse_ok h).elim
  | vset place v =>
    simp only [symStmt] at h
    cases place with
    | number _ | lane _ _ => exact (refuse_ok h).elim
    | name n =>
      dsimp only at h
      cases h128 : (n == "above128")
      · simp only [h128, Bool.false_eq_true, ↓reduceIte] at h
        cases hv : vecOf bind n with
        | none => simp only [hv] at h; exact (refuse_ok h).elim
        | some r =>
          simp only [hv] at h
          obtain ⟨⟨l, sa⟩, _, hl, hp⟩ := V.bind_ok h
          split at hp
          · have := V.pure_ok hp; injection this with hp _; subst hp
            show sa.zf = s.zf ∧ sa.cf = s.cf; exact symLanes_flags hl
          · exact (refuse_ok hp).elim
      · simp only [h128, ↓reduceIte] at h
        split at h
        · have := V.pure_ok h; injection this with h _; subst h; exact ⟨rfl, rfl⟩
        · exact (refuse_ok h).elim
    | call f args =>
      rcases args with _ | ⟨b, _ | ⟨n, _ | _⟩⟩
      · exact (refuse_ok h).elim
      · exact (refuse_ok h).elim
      · dsimp only at h
        cases h128 : (f == "mem128")
        · simp only [h128, Bool.false_eq_true, ↓reduceIte] at h; exact (refuse_ok h).elim
        · simp only [h128, ↓reduceIte] at h
          cases hv : symVec bind s v <;> cases hx : symReg ctx bind s b <;> cases hk : symNumber bind n <;> simp only [hv, hx, hk] at h
          all_goals first | exact (refuse_ok h).elim | exact symStoreWords_flags h
      · exact (refuse_ok h).elim
  | vset512 place v =>
    simp only [symStmt] at h
    cases place with
    | number _ | lane _ _ => exact (refuse_ok h).elim
    | name n =>
      dsimp only at h
      cases hv : vecOf512 bind n with
      | none => simp only [hv] at h; exact (refuse_ok h).elim
      | some r =>
        simp only [hv] at h
        obtain ⟨⟨l, sa⟩, _, hl, hp⟩ := V.bind_ok h
        split at hp
        · have := V.pure_ok hp; injection this with hp _; subst hp
          show sa.zf = s.zf ∧ sa.cf = s.cf; exact symLanes512_flags hl
        · exact (refuse_ok hp).elim
    | call f args =>
      rcases args with _ | ⟨b, _ | ⟨n, _ | _⟩⟩
      · exact (refuse_ok h).elim
      · exact (refuse_ok h).elim
      · dsimp only at h
        cases h512 : (f == "mem512")
        · simp only [h512, Bool.false_eq_true, ↓reduceIte] at h
          cases h512a : (f == "mem512a")
          · simp only [h512a, Bool.false_eq_true, ↓reduceIte] at h; exact (refuse_ok h).elim
          · simp only [h512a, ↓reduceIte] at h
            cases hv : symVec512 bind s v <;> simp only [hv] at h
            · exact (refuse_ok h).elim
            · exact symSpillStore_flags h
        · simp only [h512, ↓reduceIte] at h
          cases hv : symVec512 bind s v <;> cases hx : symReg ctx bind s b <;> cases hk : symNumber bind n <;> simp only [hv, hx, hk] at h
          all_goals first | exact (refuse_ok h).elim | exact symStoreWords_flags h
      · exact (refuse_ok h).elim
  | set place v =>
    simp only [symStmt] at h
    cases hu : isUnknown v
    · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨ev, sa⟩, _, hsv, h⟩ := V.bind_ok h
      have hf1 := symValue_flags bind v hsv
      cases place with
      | number _ | lane _ _ => exact (refuse_ok h).elim
      | name n =>
        have hnzb : (n == "zf") = false := beq_false_of_ne (fun e => hnz v (by rw [e]))
        have hncb : (n == "cf") = false := beq_false_of_ne (fun e => hnc v (by rw [e]))
        simp only [hnzb, hncb, Bool.false_eq_true, ↓reduceIte] at h
        cases hr : regOf bind n <;> cases ev <;> simp only [hr] at h
        all_goals first
          | exact (refuse_ok h).elim
          | (have := V.pure_ok h; injection this with h _; subst h; exact hf1)
      | call f args =>
        rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
        · exact (refuse_ok h).elim
        · exact (refuse_ok h).elim
        · dsimp only at h
          obtain ⟨⟨va, s1a⟩, _, h1, h⟩ := V.bind_ok h
          obtain ⟨⟨vb, s2a⟩, _, h2, h⟩ := V.bind_ok h
          have f1 := symValue_flags bind a h1
          have f2 := symValue_flags bind b h2
          have f123 : s2a.zf = s.zf ∧ s2a.cf = s.cf :=
            ⟨f2.1.trans (f1.1.trans hf1.1), f2.2.trans (f1.2.trans hf1.2)⟩
          cases ev with
          | equal _ _ | below _ _ => dsimp only at h; exact (refuse_ok h).elim
          | lin lx =>
            cases va with
            | equal _ _ | below _ _ => dsimp only at h; exact (refuse_ok h).elim
            | lin la =>
              cases vb with
              | equal _ _ | below _ _ => dsimp only at h; exact (refuse_ok h).elim
              | lin lb =>
                dsimp only at h
                cases hloc : locate ctx (Lin.add (signed la) (signed lb)) with
                | some loc =>
                  simp only [hloc] at h
                  cases loc with
                  | frame c =>
                    dsimp only at h
                    split at h
                    · have := V.pure_ok h; injection this with h _; subst h; exact f123
                    · exact (refuse_ok h).elim
                  | out w o =>
                    dsimp only at h
                    cases hg : ctx.contract.outs[w]? <;> simp only [hg] at h
                    · exact (refuse_ok h).elim
                    · split at h
                      · obtain ⟨_, _, _, h⟩ := V.bind_ok h; obtain ⟨_, _, _, h⟩ := V.bind_ok h
                        obtain ⟨_, _, _, h⟩ := V.bind_ok h; obtain ⟨_, _, _, h⟩ := V.bind_ok h
                        split at h
                        · exact (refuse_ok h).elim
                        · cases hrm : keepWrote w o s2a.wrote <;> simp only [hrm] at h
                          · exact (refuse_ok h).elim
                          · obtain ⟨_, _, _, h⟩ := V.bind_ok h
                            have := V.pure_ok h; injection this with h _; subst h; exact f123
                      · split at h
                        · have f4 := symStore8_flags h
                          exact ⟨f4.1.trans f123.1, f4.2.trans f123.2⟩
                        · exact (refuse_ok h).elim
                  | region _ _ | data _ => exact (refuse_ok h).elim
                | none =>
                  simp only [hloc] at h
                  split at h
                  · have f4 := symTouchFrame_flags h
                    exact ⟨f4.1.trans f123.1, f4.2.trans f123.2⟩
                  · exact (refuse_ok h).elim
        · exact (refuse_ok h).elim
    · simp only [hu, ↓reduceIte] at h
      cases place with
      | name n =>
        have hnzb : (n == "zf") = false := beq_false_of_ne (fun e => hnz v (by rw [e]))
        have hncb : (n == "cf") = false := beq_false_of_ne (fun e => hnc v (by rw [e]))
        simp only [hnzb, hncb, Bool.false_eq_true, ↓reduceIte] at h
        exact (refuse_ok h).elim
      | number _ | lane _ _ | call _ _ => exact (refuse_ok h).elim

theorem stmtMarks_nonflag_q {ctx : Ctx} {bind : Bind} {s s1 : Sym} {stmt : Stmt} {q' : SMarks}
    (hm : stmtMarks ctx bind s s1 stmt = some q')
    (hnz : ∀ v, stmt ≠ .set (.name "zf") v) (hnc : ∀ v, stmt ≠ .set (.name "cf") v) :
    q'.zq = s.q.zq ∧ q'.cq = s.q.cq := by
  cases stmt with
  | nothing => simp only [stmtMarks, Option.some.injEq] at hm; subst hm; exact ⟨rfl, rfl⟩
  | ret | retLink _ | call _ | callLink _ _ | jump _ _ => simp [stmtMarks] at hm
  | vset place v =>
    simp only [stmtMarks] at hm
    split at hm
    · cases place <;> simp only at hm
      · injection hm with h; subst h; exact ⟨rfl, rfl⟩
      · injection hm with h; subst h; exact ⟨rfl, rfl⟩
      · injection hm with h; subst h; exact ⟨rfl, rfl⟩
      · split at hm
        · injection hm with h; subst h; exact ⟨rfl, rfl⟩
        · cases hm
    · cases hm
  | vset512 place v =>
    simp only [stmtMarks] at hm
    split at hm
    · cases place <;> simp only at hm
      · injection hm with h; subst h; exact ⟨rfl, rfl⟩
      · injection hm with h; subst h; exact ⟨rfl, rfl⟩
      · injection hm with h; subst h; exact ⟨rfl, rfl⟩
      · split at hm
        · injection hm with h; subst h; exact ⟨rfl, rfl⟩
        · cases hm
    · cases hm
  | set place v =>
    simp only [stmtMarks] at hm
    cases hmv : markOf ctx bind s s1 v with
    | none => simp only [hmv] at hm; cases hm
    | some m =>
      simp only [hmv] at hm
      cases place with
      | number _ | lane _ _ => cases hm
      | name n =>
        have hnzb : (n == "zf") = false := beq_false_of_ne (fun e => hnz v (by rw [e]))
        have hncb : (n == "cf") = false := beq_false_of_ne (fun e => hnc v (by rw [e]))
        simp only [hnzb, hncb, Bool.false_eq_true, ↓reduceIte] at hm
        cases hr : regOf bind n <;> simp only [hr] at hm
        · cases hm
        · injection hm with h; subst h; exact ⟨rfl, rfl⟩
      | call f args =>
        dsimp only at hm
        split at hm
        · injection hm with h; subst h; exact ⟨rfl, rfl⟩
        · cases hm

/-- Two-run symbolic execution of a single statement with flag-operand equality preservation (`FlagEq`). -/
theorem symStmtQ_two {ctx : Ctx} {p : Program} {a0 b0 : State} (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (bind : Bind) (base : Nat) {s s' : Sym} {stmt : Stmt} {items rest : Items}
    {ρa ρb : Nat → Int} {sta stb : State} (ua ub : Nat)
    (h : symStmtQ ctx bind s stmt items = .ok (s', rest))
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb) (wf : WF ctx s)
    (Ma : MarksOk ctx a0 s.q sta) (Mb : MarksOk ctx b0 s.q stb)
    (A : Alike sta stb) (FE : FlagEq ρa ρb s) :
    ∃ ρa' ρb' sta1 stb1,
      quietStmt bind sta stmt = true ∧ quietStmt bind stb stmt = true ∧
      execStmt (ctx.contract.perm ctx.pieces a0) bind base ua sta stmt = some sta1 ∧
      execStmt (ctx.contract.perm ctx.pieces b0) bind base ub stb stmt = some stb1 ∧
      Carried ctx a0 ρa s ρa' s' (noted bind sta stmt sta1) ∧
      Carried ctx b0 ρb s ρb' s' (noted bind stb stmt stb1) ∧
      sta1.rip = sta.rip ∧ stb1.rip = stb.rip ∧
      MarksOk ctx a0 s'.q (noted bind sta stmt sta1) ∧
      MarksOk ctx b0 s'.q (noted bind stb stmt stb1) ∧
      Alike (noted bind sta stmt sta1) (noted bind stb stmt stb1) ∧
      FlagEq ρa' ρb' s' := by
  simp only [symStmtQ] at h
  obtain ⟨s1, r0, e1, h⟩ := V.bind_ok h
  rw [stmtMarks_light] at h
  cases hm : stmtMarks ctx bind s s1 stmt with
  | none => simp only [hm] at h; exact (refuse_ok h).elim
  | some q' =>
    simp only [hm] at h
    have hp := V.pure_ok h; injection hp with hs' _; subst hs'
    by_cases hzf : ∃ v, stmt = .set (.name "zf") v
    · obtain ⟨v, rfl⟩ := hzf
      simp only [stmtMarks] at hm
      cases hmv : markOf ctx bind s s1 v with
      | none => simp only [hmv] at hm; cases hm
      | some m =>
        simp only [hmv, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hm; subst hm
        cases m with
        | true =>
          obtain ⟨ρa', sta1, ca, xa, ripa⟩ := symStmt_sound Ea bind e1 Ha wf base ua
          obtain ⟨ρb', stb1, cb, xb, ripb⟩ := symStmt_sound Eb bind e1 Hb wf base ub
          have hml : stmtMarks ctx bind s s1 (.set (.name "zf") v) = some { s.q with zq := false } := by
            simp [stmtMarks, hmv]
          obtain ⟨qa, Ma'⟩ := stmtMarks_sound Ea Ma Ha wf ca xa hml
          obtain ⟨qb, Mb'⟩ := stmtMarks_sound Eb Mb Hb wf cb xb hml
          have hcf : s1.cf = s.cf := by
            simp only [symStmt, beq_self_eq_true, ↓reduceIte] at e1
            cases hu : isUnknown v
            · simp only [hu, Bool.false_eq_true, ↓reduceIte] at e1
              obtain ⟨⟨val, sa⟩, _, hsv, hp⟩ := V.bind_ok e1
              have hf := (symValue_flags bind v hsv).2
              cases val with
              | equal _ _ => dsimp only at hp; have := V.pure_ok hp; injection this with h _; subst h; exact hf
              | below _ _ => dsimp only at hp; have := V.pure_ok hp; injection this with h _; subst h; exact hf
              | lin _ => dsimp only at hp; exact (refuse_ok hp).elim
            · simp only [hu, ↓reduceIte] at e1
              have := V.pure_ok e1; injection this with h _; subst h; rfl
          refine ⟨ρa', ρb', sta1, stb1, qa, qb, xa, xb,
            (ca.q _).fields rfl rfl rfl rfl rfl rfl, (cb.q _).fields rfl rfl rfl rfl rfl rfl,
            ripa, ripb, Ma', Mb', stmt_alike A qa xa xb, ?_⟩
          refine ⟨(fun h => by cases h), (fun hcq => ?_)⟩
          rw [hcf]; exact FlagValEq.mono wf.cf ca.agree cb.agree (FE.2 hcq)
        | false =>
          have hnotu : isUnknown v = false := by
            cases v with
            | name n =>
              simp only [isUnknown]
              cases hn : (n == "unknown")
              · rfl
              · have e : n = "unknown" := by simpa using hn
                subst e
                have hc : cleanExpr bind s.q.regq (.name "unknown") = false := by
                  simp only [cleanExpr, show isNumberLetter "unknown" = false from by decide,
                    regOf, show isRegisterLetter "unknown" = false from by decide,
                    show regIndex "unknown" = none from by decide, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
                simp [markOf, hc] at hmv
            | _ => rfl
          simp only [symStmt, hnotu, Bool.false_eq_true, ↓reduceIte] at e1
          obtain ⟨⟨val, sa⟩, _, hsv, hp⟩ := V.bind_ok e1
          simp only [beq_self_eq_true, ↓reduceIte] at hp
          have hcf : sa.cf = s.cf := (symValue_flags bind v hsv).2
          cases val with
          | lin _ => dsimp only at hp; exact (refuse_ok hp).elim
          | equal x y =>
            dsimp only at hp
            have hp' := V.pure_ok hp; injection hp' with hs1 _; subst hs1
            have hmv_sa : markOf ctx bind s sa v = some false := by
              rw [← markOf_bytes ctx bind s sa { sa with zf := .equal x y } rfl v]; exact hmv
            obtain ⟨ρa', ρb', xa, xb, ca, cb, hva, hvb, sema, semb, heqx, heqy⟩ :=
              symValue_flag_operands Ea Eb bind hsv Ha Hb wf Ma A hmv_sa (Or.inl rfl)
            have exa : execStmt (ctx.contract.perm ctx.pieces a0) bind base ua sta (.set (.name "zf") v) = some { sta with zf := xa != 0 } := by
              simp [execStmt, hnotu, hva]
            have exb : execStmt (ctx.contract.perm ctx.pieces b0) bind base ub stb (.set (.name "zf") v) = some { stb with zf := xb != 0 } := by
              simp [execStmt, hnotu, hvb]
            have ca1 : Carried ctx a0 ρa s ρa' { sa with zf := .equal x y } { sta with zf := xa != 0 } :=
              ⟨ca.agree, ca.mono, ca.holds.setZf _ _ (Flag.equal_holds sema.1), ca.wf.setZf _ sema.2⟩
            have cb1 : Carried ctx b0 ρb s ρb' { sa with zf := .equal x y } { stb with zf := xb != 0 } :=
              ⟨cb.agree, cb.mono, cb.holds.setZf _ _ (Flag.equal_holds semb.1), cb.wf.setZf _ semb.2⟩
            have hml : stmtMarks ctx bind s { sa with zf := .equal x y } (.set (.name "zf") v) = some { s.q with zq := true } := by
              simp [stmtMarks, hmv]
            obtain ⟨qa, Ma'⟩ := stmtMarks_sound Ea Ma Ha wf ca1 exa hml
            obtain ⟨qb, Mb'⟩ := stmtMarks_sound Eb Mb Hb wf cb1 exb hml
            refine ⟨ρa', ρb', { sta with zf := xa != 0 }, { stb with zf := xb != 0 }, qa, qb, exa, exb,
              (ca1.q _).fields rfl rfl rfl rfl rfl rfl, (cb1.q _).fields rfl rfl rfl rfl rfl rfl,
              rfl, rfl, Ma', Mb', stmt_alike A qa exa exb, ⟨(fun _ => ⟨heqx, heqy⟩), (fun hcq => ?_)⟩⟩
            show FlagValEq ρa' ρb' sa.cf; rw [hcf]
            exact FlagValEq.mono wf.cf ca.agree cb.agree (FE.2 hcq)
          | below x y =>
            dsimp only at hp
            have hp' := V.pure_ok hp; injection hp' with hs1 _; subst hs1
            have hmv_sa : markOf ctx bind s sa v = some false := by
              rw [← markOf_bytes ctx bind s sa { sa with zf := .below x y } rfl v]; exact hmv
            obtain ⟨ρa', ρb', xa, xb, ca, cb, hva, hvb, sema, semb, heqx, heqy⟩ :=
              symValue_flag_operands Ea Eb bind hsv Ha Hb wf Ma A hmv_sa (Or.inr rfl)
            have exa : execStmt (ctx.contract.perm ctx.pieces a0) bind base ua sta (.set (.name "zf") v) = some { sta with zf := xa != 0 } := by
              simp [execStmt, hnotu, hva]
            have exb : execStmt (ctx.contract.perm ctx.pieces b0) bind base ub stb (.set (.name "zf") v) = some { stb with zf := xb != 0 } := by
              simp [execStmt, hnotu, hvb]
            have ca1 : Carried ctx a0 ρa s ρa' { sa with zf := .below x y } { sta with zf := xa != 0 } :=
              ⟨ca.agree, ca.mono, ca.holds.setZf _ _ (Flag.below_holds sema.1), ca.wf.setZf _ sema.2⟩
            have cb1 : Carried ctx b0 ρb s ρb' { sa with zf := .below x y } { stb with zf := xb != 0 } :=
              ⟨cb.agree, cb.mono, cb.holds.setZf _ _ (Flag.below_holds semb.1), cb.wf.setZf _ semb.2⟩
            have hml : stmtMarks ctx bind s { sa with zf := .below x y } (.set (.name "zf") v) = some { s.q with zq := true } := by
              simp [stmtMarks, hmv]
            obtain ⟨qa, Ma'⟩ := stmtMarks_sound Ea Ma Ha wf ca1 exa hml
            obtain ⟨qb, Mb'⟩ := stmtMarks_sound Eb Mb Hb wf cb1 exb hml
            refine ⟨ρa', ρb', { sta with zf := xa != 0 }, { stb with zf := xb != 0 }, qa, qb, exa, exb,
              (ca1.q _).fields rfl rfl rfl rfl rfl rfl, (cb1.q _).fields rfl rfl rfl rfl rfl rfl,
              rfl, rfl, Ma', Mb', stmt_alike A qa exa exb, ⟨(fun _ => ⟨heqx, heqy⟩), (fun hcq => ?_)⟩⟩
            show FlagValEq ρa' ρb' sa.cf; rw [hcf]
            exact FlagValEq.mono wf.cf ca.agree cb.agree (FE.2 hcq)
    · by_cases hcf : ∃ v, stmt = .set (.name "cf") v
      · obtain ⟨v, rfl⟩ := hcf
        simp only [stmtMarks] at hm
        cases hmv : markOf ctx bind s s1 v with
        | none => simp only [hmv] at hm; cases hm
        | some m =>
          simp only [hmv, beq_self_eq_true, show ("cf" == "zf") = false from rfl, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hm
          subst hm
          cases m with
          | true =>
            obtain ⟨ρa', sta1, ca, xa, ripa⟩ := symStmt_sound Ea bind e1 Ha wf base ua
            obtain ⟨ρb', stb1, cb, xb, ripb⟩ := symStmt_sound Eb bind e1 Hb wf base ub
            have hml : stmtMarks ctx bind s s1 (.set (.name "cf") v) = some { s.q with cq := false } := by
              simp [stmtMarks, hmv]
            obtain ⟨qa, Ma'⟩ := stmtMarks_sound Ea Ma Ha wf ca xa hml
            obtain ⟨qb, Mb'⟩ := stmtMarks_sound Eb Mb Hb wf cb xb hml
            have hzf' : s1.zf = s.zf := by
              simp only [symStmt] at e1
              cases hu : isUnknown v
              · simp only [hu, Bool.false_eq_true, ↓reduceIte] at e1
                obtain ⟨⟨val, sa⟩, _, hsv, hp⟩ := V.bind_ok e1
                simp only [beq_self_eq_true, show ("cf" == "zf") = false from rfl, Bool.false_eq_true, ↓reduceIte] at hp
                have hf := (symValue_flags bind v hsv).1
                cases val with
                | equal _ _ => dsimp only at hp; have := V.pure_ok hp; injection this with h _; subst h; exact hf
                | below _ _ => dsimp only at hp; have := V.pure_ok hp; injection this with h _; subst h; exact hf
                | lin _ => dsimp only at hp; exact (refuse_ok hp).elim
              · simp only [hu, ↓reduceIte, beq_self_eq_true, show ("cf" == "zf") = false from rfl, Bool.false_eq_true] at e1
                have := V.pure_ok e1; injection this with h _; subst h; rfl
            refine ⟨ρa', ρb', sta1, stb1, qa, qb, xa, xb,
              (ca.q _).fields rfl rfl rfl rfl rfl rfl, (cb.q _).fields rfl rfl rfl rfl rfl rfl,
              ripa, ripb, Ma', Mb', stmt_alike A qa xa xb, ?_⟩
            refine ⟨(fun hzq => ?_), (fun h => by cases h)⟩
            rw [hzf']; exact FlagValEq.mono wf.zf ca.agree cb.agree (FE.1 hzq)
          | false =>
            have hnotu : isUnknown v = false := by
              cases v with
              | name n =>
                simp only [isUnknown]
                cases hn : (n == "unknown")
                · rfl
                · have e : n = "unknown" := by simpa using hn
                  subst e
                  have hc : cleanExpr bind s.q.regq (.name "unknown") = false := by
                    simp only [cleanExpr, show isNumberLetter "unknown" = false from by decide,
                      regOf, show isRegisterLetter "unknown" = false from by decide,
                      show regIndex "unknown" = none from by decide, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
                  simp [markOf, hc] at hmv
              | _ => rfl
            simp only [symStmt, hnotu, Bool.false_eq_true, ↓reduceIte] at e1
            obtain ⟨⟨val, sa⟩, _, hsv, hp⟩ := V.bind_ok e1
            simp only [beq_self_eq_true, show ("cf" == "zf") = false from rfl, Bool.false_eq_true, ↓reduceIte] at hp
            have hzf' : sa.zf = s.zf := (symValue_flags bind v hsv).1
            cases val with
            | lin _ => dsimp only at hp; exact (refuse_ok hp).elim
            | equal x y =>
              dsimp only at hp
              have hp' := V.pure_ok hp; injection hp' with hs1 _; subst hs1
              have hmv_sa : markOf ctx bind s sa v = some false := by
                rw [← markOf_bytes ctx bind s sa { sa with cf := .equal x y } rfl v]; exact hmv
              obtain ⟨ρa', ρb', xa, xb, ca, cb, hva, hvb, sema, semb, heqx, heqy⟩ :=
                symValue_flag_operands Ea Eb bind hsv Ha Hb wf Ma A hmv_sa (Or.inl rfl)
              have exa : execStmt (ctx.contract.perm ctx.pieces a0) bind base ua sta (.set (.name "cf") v) = some { sta with cf := xa != 0 } := by
                simp [execStmt, hnotu, hva]
              have exb : execStmt (ctx.contract.perm ctx.pieces b0) bind base ub stb (.set (.name "cf") v) = some { stb with cf := xb != 0 } := by
                simp [execStmt, hnotu, hvb]
              have ca1 : Carried ctx a0 ρa s ρa' { sa with cf := .equal x y } { sta with cf := xa != 0 } :=
                ⟨ca.agree, ca.mono, ca.holds.setCf _ _ (Flag.equal_holds sema.1), ca.wf.setCf _ sema.2⟩
              have cb1 : Carried ctx b0 ρb s ρb' { sa with cf := .equal x y } { stb with cf := xb != 0 } :=
                ⟨cb.agree, cb.mono, cb.holds.setCf _ _ (Flag.equal_holds semb.1), cb.wf.setCf _ semb.2⟩
              have hml : stmtMarks ctx bind s { sa with cf := .equal x y } (.set (.name "cf") v) = some { s.q with cq := true } := by
                simp [stmtMarks, hmv]
              obtain ⟨qa, Ma'⟩ := stmtMarks_sound Ea Ma Ha wf ca1 exa hml
              obtain ⟨qb, Mb'⟩ := stmtMarks_sound Eb Mb Hb wf cb1 exb hml
              refine ⟨ρa', ρb', { sta with cf := xa != 0 }, { stb with cf := xb != 0 }, qa, qb, exa, exb,
                (ca1.q _).fields rfl rfl rfl rfl rfl rfl, (cb1.q _).fields rfl rfl rfl rfl rfl rfl,
                rfl, rfl, Ma', Mb', stmt_alike A qa exa exb, ⟨(fun hzq => ?_), (fun _ => ⟨heqx, heqy⟩)⟩⟩
              show FlagValEq ρa' ρb' sa.zf; rw [hzf']
              exact FlagValEq.mono wf.zf ca.agree cb.agree (FE.1 hzq)
            | below x y =>
              dsimp only at hp
              have hp' := V.pure_ok hp; injection hp' with hs1 _; subst hs1
              have hmv_sa : markOf ctx bind s sa v = some false := by
                rw [← markOf_bytes ctx bind s sa { sa with cf := .below x y } rfl v]; exact hmv
              obtain ⟨ρa', ρb', xa, xb, ca, cb, hva, hvb, sema, semb, heqx, heqy⟩ :=
                symValue_flag_operands Ea Eb bind hsv Ha Hb wf Ma A hmv_sa (Or.inr rfl)
              have exa : execStmt (ctx.contract.perm ctx.pieces a0) bind base ua sta (.set (.name "cf") v) = some { sta with cf := xa != 0 } := by
                simp [execStmt, hnotu, hva]
              have exb : execStmt (ctx.contract.perm ctx.pieces b0) bind base ub stb (.set (.name "cf") v) = some { stb with cf := xb != 0 } := by
                simp [execStmt, hnotu, hvb]
              have ca1 : Carried ctx a0 ρa s ρa' { sa with cf := .below x y } { sta with cf := xa != 0 } :=
                ⟨ca.agree, ca.mono, ca.holds.setCf _ _ (Flag.below_holds sema.1), ca.wf.setCf _ sema.2⟩
              have cb1 : Carried ctx b0 ρb s ρb' { sa with cf := .below x y } { stb with cf := xb != 0 } :=
                ⟨cb.agree, cb.mono, cb.holds.setCf _ _ (Flag.below_holds semb.1), cb.wf.setCf _ semb.2⟩
              have hml : stmtMarks ctx bind s { sa with cf := .below x y } (.set (.name "cf") v) = some { s.q with cq := true } := by
                simp [stmtMarks, hmv]
              obtain ⟨qa, Ma'⟩ := stmtMarks_sound Ea Ma Ha wf ca1 exa hml
              obtain ⟨qb, Mb'⟩ := stmtMarks_sound Eb Mb Hb wf cb1 exb hml
              refine ⟨ρa', ρb', { sta with cf := xa != 0 }, { stb with cf := xb != 0 }, qa, qb, exa, exb,
                (ca1.q _).fields rfl rfl rfl rfl rfl rfl, (cb1.q _).fields rfl rfl rfl rfl rfl rfl,
                rfl, rfl, Ma', Mb', stmt_alike A qa exa exb, ⟨(fun hzq => ?_), (fun _ => ⟨heqx, heqy⟩)⟩⟩
              show FlagValEq ρa' ρb' sa.zf; rw [hzf']
              exact FlagValEq.mono wf.zf ca.agree cb.agree (FE.1 hzq)
      · have hnz' : ∀ v, stmt ≠ .set (.name "zf") v := fun v e => hzf ⟨v, e⟩
        have hnc' : ∀ v, stmt ≠ .set (.name "cf") v := fun v e => hcf ⟨v, e⟩
        obtain ⟨ρa', sta1, ca, xa, ripa⟩ := symStmt_sound Ea bind e1 Ha wf base ua
        obtain ⟨ρb', stb1, cb, xb, ripb⟩ := symStmt_sound Eb bind e1 Hb wf base ub
        obtain ⟨qa, Ma'⟩ := stmtMarks_sound Ea Ma Ha wf ca xa hm
        obtain ⟨qb, Mb'⟩ := stmtMarks_sound Eb Mb Hb wf cb xb hm
        obtain ⟨hfz, hfc⟩ := symStmt_nonflag_flags e1 hnz' hnc'
        obtain ⟨hqz, hqc⟩ := stmtMarks_nonflag_q hm hnz' hnc'
        refine ⟨ρa', ρb', sta1, stb1, qa, qb, xa, xb,
          (ca.q _).fields rfl rfl rfl rfl rfl rfl, (cb.q _).fields rfl rfl rfl rfl rfl rfl,
          ripa, ripb, Ma', Mb', stmt_alike A qa xa xb, ?_⟩
        refine ⟨fun hzq => ?_, fun hcq => ?_⟩
        · show FlagValEq ρa' ρb' s1.zf; rw [hfz]
          exact FlagValEq.mono wf.zf ca.agree cb.agree (FE.1 (hqz.symm.trans hzq))
        · show FlagValEq ρa' ρb' s1.cf; rw [hfc]
          exact FlagValEq.mono wf.cf ca.agree cb.agree (FE.2 (hqc.symm.trans hcq))

theorem stmts_two_sound {ctx : Ctx} {p : Program} {a0 b0 : State} (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (bind : Bind) (base : Nat) (ua ub : Nat → Nat) :
    ∀ (stmts : List Stmt) (k : Nat) {s s' : Sym} {items rest : Items} {ρa ρb : Nat → Int} {sta stb : State},
    fold (symStmtQ ctx bind) s stmts items = .ok (s', rest) →
    Holds ctx a0 ρa s sta → Holds ctx b0 ρb s stb → WF ctx s →
    MarksOk ctx a0 s.q sta → MarksOk ctx b0 s.q stb → Alike sta stb → FlagEq ρa ρb s →
    ∃ ρa' ρb' sta' stb',
      Carried ctx a0 ρa s ρa' s' sta' ∧ Carried ctx b0 ρb s ρb' s' stb' ∧
      execAllQ (ctx.contract.perm ctx.pieces a0) bind base ua k sta stmts = some (.next sta') ∧
      execAllQ (ctx.contract.perm ctx.pieces b0) bind base ub k stb stmts = some (.next stb') ∧
      sta'.rip = sta.rip ∧ stb'.rip = stb.rip ∧
      MarksOk ctx a0 s'.q sta' ∧ MarksOk ctx b0 s'.q stb' ∧ Alike sta' stb' ∧ FlagEq ρa' ρb' s'
  | [], k, s, s', items, rest, ρa, ρb, sta, stb, h, Ha, Hb, wf, Ma, Mb, A, FE => by
    simp only [fold] at h
    have hp := V.pure_ok h; injection hp with h1 _; subst h1
    exact ⟨ρa, ρb, sta, stb, Carried.here Ha wf, Carried.here Hb wf, rfl, rfl, rfl, rfl, Ma, Mb, A, FE⟩
  | stmt :: more, k, s, s', items, rest, ρa, ρb, sta, stb, h, Ha, Hb, wf, Ma, Mb, A, FE => by
    simp only [fold] at h
    obtain ⟨sq, r1, eq, h⟩ := V.bind_ok h
    obtain ⟨ρa1, ρb1, sta1, stb1, qa, qb, xa, xb, ca1, cb1, ripa1, ripb1, Ma1, Mb1, A1, FE1⟩ :=
      symStmtQ_two Ea Eb bind base (ua k) (ub k) eq Ha Hb wf Ma Mb A FE
    obtain ⟨ρa2, ρb2, sta2, stb2, ca2, cb2, xa2, xb2, ripa2, ripb2, Ma2, Mb2, A2, FE2⟩ :=
      stmts_two_sound Ea Eb bind base ua ub more (k + 1) h ca1.holds cb1.holds ca1.wf Ma1 Mb1 A1 FE1
    have hnotr : stmt ≠ .ret ∧ (∀ r, stmt ≠ .retLink r) ∧ (∀ x r, stmt ≠ .callLink x r) := by
      simp only [symStmtQ] at eq
      obtain ⟨s1, _, e1, _⟩ := V.bind_ok eq
      refine ⟨?_, ?_, ?_⟩
      · intro e; subst e; simp [symStmt] at e1; exact (refuse_ok e1).elim
      · intro r e; subst e; simp [symStmt] at e1; exact (refuse_ok e1).elim
      · intro x r e; subst e; simp [symStmt] at e1; exact (refuse_ok e1).elim
    have mk : ∀ (perm : Perm) (u : Nat → Nat) (st st1 : State) (q : quietStmt bind st stmt = true)
        (x : execStmt perm bind base (u k) st stmt = some st1) {o : Outcome},
        execAllQ perm bind base u (k + 1) (noted bind st stmt st1) more = some o →
        execAllQ perm bind base u k st (stmt :: more) = some o := by
      intro perm u st st1 q x o xo
      cases stmt with
      | ret => exact (hnotr.1 rfl).elim
      | retLink r => exact (hnotr.2.1 r rfl).elim
      | callLink x0 r => exact (hnotr.2.2 x0 r rfl).elim
      | nothing | set _ _ | vset _ _ | vset512 _ _ | jump _ _ | call _ =>
        simp only [execAllQ, q, ↓reduceIte, x]; exact xo
    exact ⟨ρa2, ρb2, sta2, stb2, ca1.then ca2, cb1.then cb2,
      mk _ ua sta sta1 qa xa xa2, mk _ ub stb stb1 qb xb xb2,
      ripa2.trans ripa1, ripb2.trans ripb1, Ma2, Mb2, A2, FE2⟩

theorem ways_two_sound {ctx : Ctx} {a0 b0 : State} {s : Sym} {want : Bool} {target next : Nat}
    {ρa ρb : Nat → Int} {sta stb : State}
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb) (wf : WF ctx s) (b : Bool) :
    ∀ (w : List (Bool × List Row)) {nexts : List (Sym × Next)} {items rest : Items},
    ways s want target next w items = .ok (nexts, rest) →
    (∀ sr ∈ w, ∀ r ∈ sr.2, bounded s.nvars r) →
    (∃ sr ∈ w, sr.1 = b ∧ (∀ r ∈ sr.2, r.holds ρa) ∧ (∀ r ∈ sr.2, r.holds ρb)) →
    ∃ s', (s', Next.at (if b == want then target else next)) ∈ nexts ∧
      Carried ctx a0 ρa s ρa s' sta ∧ Carried ctx b0 ρb s ρb s' stb ∧
      s'.q = s.q ∧ s'.zf = s.zf ∧ s'.cf = s.cf
  | [], _, _, _, _, _, hex => by obtain ⟨sr, m, _⟩ := hex; cases m
  | (set, rows) :: more, nexts, items, rest, h, hb, hex => by
    simp only [ways] at h
    obtain ⟨now, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨others, r2, e2, h⟩ := V.bind_ok h
    have aa := assume_sound e1 ρa Ha.facts
    have ab := assume_sound e1 ρb Hb.facts
    obtain ⟨sr, m, hset, hrowsa, hrowsb⟩ := hex
    cases m with
    | head =>
      cases now with
      | none => exact (aa hrowsa).elim
      | some s1 =>
        simp only at aa ab h
        have hp := V.pure_ok h; injection hp with h1 _; subst h1
        refine ⟨s1, by rw [← hset]; exact List.mem_cons_self .., ?_⟩
        rcases aa with rfl | rfl
        · exact ⟨Carried.here Ha wf, Carried.here Hb wf, rfl, rfl, rfl⟩
        · exact ⟨⟨Agree.refl _ _, Nat.le_refl _, Ha.more rows hrowsa, wf.more rows (hb (set, rows) (List.mem_cons_self ..))⟩,
                 ⟨Agree.refl _ _, Nat.le_refl _, Hb.more rows hrowsb, wf.more rows (hb (set, rows) (List.mem_cons_self ..))⟩,
                 rfl, rfl, rfl⟩
    | tail _ m =>
      obtain ⟨s', m', ca', cb', hq', hzf', hcf'⟩ :=
        ways_two_sound Ha Hb wf b more e2 (fun sr m => hb sr (List.mem_cons_of_mem _ m)) ⟨sr, m, hset, hrowsa, hrowsb⟩
      cases now with
      | none =>
        simp only at h; have hp := V.pure_ok h; injection hp with h1 _; subst h1
        exact ⟨s', m', ca', cb', hq', hzf', hcf'⟩
      | some s1 =>
        simp only at h; have hp := V.pure_ok h; injection hp with h1 _; subst h1
        exact ⟨s', List.mem_cons_of_mem _ m', ca', cb', hq', hzf', hcf'⟩

theorem flagWays_two_spec {f : Flag} {w : List (Bool × List Row)} {ρa ρb : Nat → Int} {b : Bool} {n : Nat}
    (h : flagWays f = some w) (hfa : f.holds ρa b) (hfb : f.holds ρb b) (hb : f.bounded n) (fe : FlagValEq ρa ρb f) :
    (∀ sr ∈ w, ∀ r ∈ sr.2, bounded n r) ∧
    (∃ sr ∈ w, sr.1 = b ∧ (∀ r ∈ sr.2, r.holds ρa) ∧ (∀ r ∈ sr.2, r.holds ρb)) := by
  have h1 := (flagWays_spec h hfa hb).1
  refine ⟨h1, ?_⟩
  cases f with
  | unknown => simp [flagWays] at h
  | equal x y =>
    simp only [flagWays, Option.some.injEq] at h; subst h
    obtain ⟨hx, hy⟩ := fe
    simp only [Flag.holds] at hfa hfb
    by_cases e : ev ρa x = ev ρa y
    · refine ⟨_, List.mem_cons_self .., by simp [hfa, e], ?_, ?_⟩ <;>
        (intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
         rcases hr with rfl | rfl <;> rw [holds_iff, ev_sub] <;> omega)
    · by_cases l : ev ρa y < ev ρa x
      · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp [hfa, e], ?_, ?_⟩ <;>
          (intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; subst hr
           rw [holds_iff]; simp only [ev_sub, ev_const]; omega)
      · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), by simp [hfa, e], ?_, ?_⟩ <;>
          (intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; subst hr
           rw [holds_iff]; simp only [ev_sub, ev_const]; omega)
  | below x y =>
    simp only [flagWays, Option.some.injEq] at h; subst h
    obtain ⟨hx, hy⟩ := fe
    simp only [Flag.holds] at hfa hfb
    by_cases l : ev ρa x < ev ρa y
    · refine ⟨_, List.mem_cons_self .., by simp [hfa, l], ?_, ?_⟩ <;>
        (intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; subst hr
         rw [holds_iff]; simp only [ev_sub, ev_const]; omega)
    · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp [hfa, l], ?_, ?_⟩ <;>
        (intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; subst hr
         rw [holds_iff, ev_sub]; omega)


theorem jumpWays_two_sound {ctx : Ctx} {a0 b0 : State} {s : Sym} {want : Bool} {target next : Nat}
    {ρa ρb : Nat → Int} {sta stb : State} {f : Flag} {nexts : List (Sym × Next)} {items rest : Items}
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb) (wf : WF ctx s) (b : Bool)
    (h : jumpWays s want target next f items = .ok (nexts, rest))
    (hfa : f.holds ρa b) (hfb : f.holds ρb b) (hb : f.bounded s.nvars) (fe : FlagValEq ρa ρb f) :
    ∃ s', (s', Next.at (if b == want then target else next)) ∈ nexts ∧
      Carried ctx a0 ρa s ρa s' sta ∧ Carried ctx b0 ρb s ρb s' stb ∧
      s'.q = s.q ∧ s'.zf = s.zf ∧ s'.cf = s.cf := by
  cases f with
  | unknown => simp only [jumpWays] at h; exact (refuse_ok h).elim
  | below x y =>
    simp only [jumpWays] at h
    obtain ⟨bd, ex⟩ := flagWays_two_spec (f := .below x y) rfl hfa hfb hb fe
    exact ways_two_sound Ha Hb wf b _ h bd ex
  | equal x y =>
    simp only [jumpWays] at h
    obtain ⟨yes, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨no, r2, e2, h⟩ := V.bind_ok h
    have hp := V.pure_ok h; injection hp with h1 _; subst h1
    obtain ⟨hx, hy⟩ := fe
    simp only [Flag.holds] at hfa hfb
    by_cases he : ev ρa x = ev ρa y
    · have hbtrue : b = true := by simp [hfa, he]
      subst hbtrue
      unfold assumeEq at e1
      have hnotneq : hasNeq s.spec x y = false := by
        cases hn : hasNeq s.spec x y with
        | false => rfl
        | true => exact (hasNeq_sound hn Ha.spec he).elim
      simp only [hnotneq, Bool.false_eq_true, ↓reduceIte] at e1
      obtain ⟨now, r1', ea, e1⟩ := V.bind_ok e1
      have ha := assume_sound ea ρa Ha.facts
      have hrowsa : ∀ r ∈ [Lin.sub x y, Lin.sub y x], r.holds ρa := by
        intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl <;> rw [holds_iff, ev_sub] <;> omega
      have hrowsb : ∀ r ∈ [Lin.sub x y, Lin.sub y x], r.holds ρb := by
        intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl <;> rw [holds_iff, ev_sub] <;> omega
      cases now with
      | none => exact (ha hrowsa).elim
      | some s1 =>
        have hpy := V.pure_ok e1; injection hpy with hy' _; subst hy'
        have hbd : ∀ r ∈ [Lin.sub x y, Lin.sub y x], bounded s.nvars r := by
          intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | rfl
          · exact bounded_sub hb.1 hb.2
          · exact bounded_sub hb.2 hb.1
        refine ⟨s1, List.mem_append_left _ (by simp), ?_⟩
        rcases ha with rfl | rfl
        · exact ⟨Carried.here Ha wf, Carried.here Hb wf, rfl, rfl, rfl⟩
        · exact ⟨⟨Agree.refl _ _, Nat.le_refl _, Ha.more _ hrowsa, wf.more _ hbd⟩,
                 ⟨Agree.refl _ _, Nat.le_refl _, Hb.more _ hrowsb, wf.more _ hbd⟩, rfl, rfl, rfl⟩
    · have hbfalse : b = false := by simp [hfa, he]
      subst hbfalse
      unfold assumeNeq at e2
      cases hc : Lin.isConst (Lin.sub x y) with
      | some k =>
        by_cases hk : k = 0
        · subst hk
          have ev0 := ev_isConst hc (ρ := ρa)
          rw [ev_sub] at ev0; omega
        · have hk' : (k == 0) = false := beq_false_of_ne hk
          simp only [hc, hk', Bool.false_eq_true, ↓reduceIte] at e2
          have hp2 := V.pure_ok e2; injection hp2 with hno _; subst hno
          exact ⟨s, List.mem_append_right _ (by simp), Carried.here Ha wf, Carried.here Hb wf, rfl, rfl, rfl⟩
      | none =>
      simp only [hc] at e2
      have hbd : ∀ sr ∈ [(false, [Lin.sub (Lin.sub x y) (Lin.const 1)]), (false, [Lin.sub (Lin.sub y x) (Lin.const 1)])], ∀ r ∈ sr.2, bounded s.nvars r := by
        intro sr m r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
        rcases m with rfl | rfl <;> (simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; subst hr)
        · exact bounded_sub (bounded_sub hb.1 hb.2) (bounded_const _ _)
        · exact bounded_sub (bounded_sub hb.2 hb.1) (bounded_const _ _)
      have hex : ∃ sr ∈ [(false, [Lin.sub (Lin.sub x y) (Lin.const 1)]), (false, [Lin.sub (Lin.sub y x) (Lin.const 1)])],
          sr.1 = false ∧ (∀ r ∈ sr.2, r.holds ρa) ∧ (∀ r ∈ sr.2, r.holds ρb) := by
        by_cases l : ev ρa y < ev ρa x
        · refine ⟨_, List.mem_cons_self .., rfl, ?_, ?_⟩ <;>
            (intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; subst hr
             rw [holds_iff]; simp only [ev_sub, ev_const]; omega)
        · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, ?_, ?_⟩ <;>
            (intro r hr; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr; subst hr
             rw [holds_iff]; simp only [ev_sub, ev_const]; omega)
      cases hl : r1.line r1.next with
      | none => simp only [hl] at e2; exact (need_ok e2).elim
      | some it =>
        simp only [hl] at e2
        cases it with
        | tag nm k =>
          simp only at e2
          split at e2
          · injection e2 with hno
            injection hno with hno _
            subst hno
            have hnea : SFact.holds ctx a0 ρa (.neq (Lin.sub x y)) := by simp only [SFact.holds, ev_sub]; omega
            have hneb : SFact.holds ctx b0 ρb (.neq (Lin.sub x y)) := by simp only [SFact.holds, ev_sub]; omega
            refine ⟨{ s with spec := .neq (Lin.sub x y) :: s.spec },
              List.mem_append_right _ (by simp),
              ⟨Agree.refl _ _, Nat.le_refl _, Ha.withSpec _ hnea, wf.withSpec _ (bounded_sub hb.1 hb.2)⟩,
              ⟨Agree.refl _ _, Nat.le_refl _, Hb.withSpec _ hneb, wf.withSpec _ (bounded_sub hb.1 hb.2)⟩,
              rfl, rfl, rfl⟩
          · obtain ⟨s', m', ca', cb', q', zf', cf'⟩ := ways_two_sound Ha Hb wf false _ e2 hbd hex
            exact ⟨s', List.mem_append_right _ m', ca', cb', q', zf', cf'⟩
        | _ =>
          simp only at e2
          obtain ⟨s', m', ca', cb', q', zf', cf'⟩ := ways_two_sound Ha Hb wf false _ e2 hbd hex
          exact ⟨s', List.mem_append_right _ m', ca', cb', q', zf', cf'⟩

theorem symInstr_two_sound {ctx : Ctx} {p : Program} {a0 b0 : State} (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    {s : Sym} {i : Instr} {nexts : List (Sym × Next)} {items rest : Items}
    {ρa ρb : Nat → Int} {sta stb : State}
    (hnosel : ∀ d c t f, shape i.effect ≠ .select d c t f)
    (h : symInstr ctx s i items = .ok (nexts, rest))
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb) (wf : WF ctx s)
    (Ma : MarksOk ctx a0 s.q sta) (Mb : MarksOk ctx b0 s.q stb)
    (A : Alike sta stb) (FE : FlagEq ρa ρb s) (ua ub : Nat → Nat) :
    ∃ oa ob,
      execQ (ctx.contract.perm ctx.pieces a0) p i ua sta = some oa ∧
      execQ (ctx.contract.perm ctx.pieces b0) p i ub stb = some ob ∧
      match oa, ob with
      | .next sta', .next stb' =>
        ∃ s' pc ρa' ρb', (s', Next.at pc) ∈ nexts ∧
          sta'.rip = p.base + pc ∧ stb'.rip = p.base + pc ∧
          Carried ctx a0 ρa s ρa' s' sta' ∧ Carried ctx b0 ρb s ρb' s' stb' ∧
          MarksOk ctx a0 s'.q sta' ∧ MarksOk ctx b0 s'.q stb' ∧
          Alike sta' stb' ∧ FlagEq ρa' ρb' s'
      | .returned ra, .returned rb =>
        ctx.contract.left ctx.defs a0 ra ∧ ctx.contract.left ctx.defs b0 rb ∧ Alike ra rb
      | _, _ => False := by
  have Hsa : Holds ctx a0 ρa s (started p i sta) := Ha.fields rfl rfl rfl rfl rfl rfl
  have Hsb : Holds ctx b0 ρb s (started p i stb) := Hb.fields rfl rfl rfl rfl rfl rfl
  have Msa : MarksOk ctx a0 s.q (started p i sta) := Ma.fields rfl
  have Msb : MarksOk ctx b0 s.q (started p i stb) := Mb.fields rfl
  have As : Alike (started p i sta) (started p i stb) :=
    ⟨A.marks, rfl, A.data, by simp [started, A.trace, A.rip], A.reg, A.zf, A.cf, A.mem, A.low⟩
  cases hs : shape i.effect with
  | ret =>
    obtain ⟨oa, hoa, hma⟩ := symInstr_sound Ea h Ha wf Ma ua
    obtain ⟨ob, hob, hmb⟩ := symInstr_sound Eb h Hb wf Mb ub
    have hlike := execQ_alike A hoa hob
    have heff := shape_ret hs
    cases oa with
    | next _ => simp [execQ, heff, execAllQ] at hoa
    | returned ra =>
      cases ob with
      | next _ => exact hlike.elim
      | returned rb => exact ⟨.returned ra, .returned rb, hoa, hob, hma, hmb, hlike⟩
  | retLink r =>
    obtain ⟨oa, hoa, hma⟩ := symInstr_sound Ea h Ha wf Ma ua
    obtain ⟨ob, hob, hmb⟩ := symInstr_sound Eb h Hb wf Mb ub
    have hlike := execQ_alike A hoa hob
    have heff := shape_retLink hs
    cases oa with
    | next _ =>
      simp only [execQ, heff, execAllQ] at hoa
      cases hr : regIndex r <;> simp only [hr, Option.bind] at hoa
      · cases hoa
      · split at hoa <;> cases hoa
    | returned ra =>
      cases ob with
      | next _ => exact hlike.elim
      | returned rb => exact ⟨.returned ra, .returned rb, hoa, hob, hma, hmb, hlike⟩
  | jump target cond =>
    have heff := shape_jump hs
    simp only [symInstr, hs] at h
    cases ht : jumpTarget i.bind target with
    | none => simp only [ht] at h; exact (refuse_ok h).elim
    | some t =>
      simp only [ht] at h
      have hva := jumpTarget_value ht (ctx.contract.perm ctx.pieces a0) (started p i sta)
      have hvb := jumpTarget_value ht (ctx.contract.perm ctx.pieces b0) (started p i stb)
      obtain ⟨qaa, qba⟩ := jumpTarget_quiet ht (started p i sta)
      obtain ⟨qab, qbb⟩ := jumpTarget_quiet ht (started p i stb)
      cases cond with
      | none =>
        have hp := V.pure_ok h; injection hp with hn _; subst hn
        have hqsa : quietStmt i.bind (started p i sta) (.jump target none) = true := by
          simp only [quietStmt, qaa, qba, Bool.not_false, Bool.and_true]
        have hqsb : quietStmt i.bind (started p i stb) (.jump target none) = true := by
          simp only [quietStmt, qab, qbb, Bool.not_false, Bool.and_true]
        have exa : execQ (ctx.contract.perm ctx.pieces a0) p i ua sta =
            some (.next (noted i.bind (started p i sta) (.jump target none) { started p i sta with rip := p.base + t })) := by
          simp [execQ, heff, execAllQ, hqsa, execStmt, hva]
        have exb : execQ (ctx.contract.perm ctx.pieces b0) p i ub stb =
            some (.next (noted i.bind (started p i stb) (.jump target none) { started p i stb with rip := p.base + t })) := by
          simp [execQ, heff, execAllQ, hqsb, execStmt, hvb]
        have hlike := execQ_alike A exa exb
        exact ⟨_, _, exa, exb, s, t, ρa, ρb, List.mem_cons_self .., rfl, rfl,
          (Carried.here Hsa wf).fields rfl rfl rfl rfl rfl rfl,
          (Carried.here Hsb wf).fields rfl rfl rfl rfl rfl rfl,
          Msa.fields rfl, Msb.fields rfl, hlike, FE⟩
      | some fw =>
        obtain ⟨flag, want⟩ := fw
        simp only at h
        cases hq : symCondClean s.q flag with
        | false => simp only [hq, Bool.not_false, ↓reduceIte] at h; exact (refuse_ok h).elim
        | true =>
          simp only [hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          ·
            have hmka : condMark sta.marks flag = false := symCondClean_sound Ma flag hq
            have hmkb : condMark stb.marks flag = false := symCondClean_sound Mb flag hq
            have heqb : condFlag sta flag = condFlag stb flag := condFlag_alike A flag hmka
            have hfa : (symCondFlag s flag).holds ρa (condFlag sta flag) := symCondFlag_holds Ha flag
            have hfb : (symCondFlag s flag).holds ρb (condFlag sta flag) := by rw [heqb]; exact symCondFlag_holds Hb flag
            have hbd : (symCondFlag s flag).bounded s.nvars := symCondFlag_bounded wf flag
            have hfe : FlagValEq ρa ρb (symCondFlag s flag) := symCondFlag_valEq FE flag hq
            obtain ⟨s', ms', ca', cb', hsq', hszf', hscf'⟩ :=
              jumpWays_two_sound Hsa Hsb wf (condFlag sta flag) h hfa hfb hbd hfe
            have hqsa : quietStmt i.bind (started p i sta) (.jump target (some (flag, want))) = true := by
              simp only [quietStmt, qaa, qba, Bool.not_false, Bool.and_true, Bool.true_and, Bool.not_eq_true']
              exact hmka
            have hqsb : quietStmt i.bind (started p i stb) (.jump target (some (flag, want))) = true := by
              simp only [quietStmt, qab, qbb, Bool.not_false, Bool.and_true, Bool.true_and, Bool.not_eq_true']
              exact hmkb
            have hta : execQ (ctx.contract.perm ctx.pieces a0) p i ua sta =
                some (.next (noted i.bind (started p i sta) (.jump target (some (flag, want)))
                  (if (condFlag sta flag == want) = true then { started p i sta with rip := p.base + t } else started p i sta))) := by
              simp only [execQ, heff, execAllQ, hqsa, ↓reduceIte, execStmt, hva]
              have hstf : condFlag (started p i sta) flag = condFlag sta flag := rfl
              rw [hstf]
              cases hcond : (condFlag sta flag == want) <;> simp
            have htb : execQ (ctx.contract.perm ctx.pieces b0) p i ub stb =
                some (.next (noted i.bind (started p i stb) (.jump target (some (flag, want)))
                  (if (condFlag sta flag == want) = true then { started p i stb with rip := p.base + t } else started p i stb))) := by
              simp only [execQ, heff, execAllQ, hqsb, ↓reduceIte, execStmt, hvb]
              have hcond_eq : condFlag (started p i stb) flag = condFlag sta flag := heqb.symm
              rw [hcond_eq]
              cases hcond : (condFlag sta flag == want) <;> simp
            have hlike := execQ_alike A hta htb
            have hripa : (noted i.bind (started p i sta) (.jump target (some (flag, want)))
                (if (condFlag sta flag == want) = true then { started p i sta with rip := p.base + t } else started p i sta)).rip =
                p.base + (if condFlag sta flag == want then t else i.next) := by
              cases (condFlag sta flag == want) <;> simp [noted, started]
            have hripb : (noted i.bind (started p i stb) (.jump target (some (flag, want)))
                (if (condFlag sta flag == want) = true then { started p i stb with rip := p.base + t } else started p i stb)).rip =
                p.base + (if condFlag sta flag == want then t else i.next) := by
              cases (condFlag sta flag == want) <;> simp [noted, started]
            have hca'' : Carried ctx a0 ρa s ρa s'
                (noted i.bind (started p i sta) (.jump target (some (flag, want)))
                  (if (condFlag sta flag == want) = true then { started p i sta with rip := p.base + t } else started p i sta)) := by
              cases (condFlag sta flag == want) <;>
                simp only [Bool.false_eq_true, ↓reduceIte] <;> exact ca'.fields rfl rfl rfl rfl rfl rfl
            have hcb'' : Carried ctx b0 ρb s ρb s'
                (noted i.bind (started p i stb) (.jump target (some (flag, want)))
                  (if (condFlag sta flag == want) = true then { started p i stb with rip := p.base + t } else started p i stb)) := by
              cases (condFlag sta flag == want) <;>
                simp only [Bool.false_eq_true, ↓reduceIte] <;> exact cb'.fields rfl rfl rfl rfl rfl rfl
            have hma' : MarksOk ctx a0 s'.q
                (noted i.bind (started p i sta) (.jump target (some (flag, want)))
                  (if (condFlag sta flag == want) = true then { started p i sta with rip := p.base + t } else started p i sta)) := by
              rw [hsq']; exact Msa.fields rfl
            have hmb' : MarksOk ctx b0 s'.q
                (noted i.bind (started p i stb) (.jump target (some (flag, want)))
                  (if (condFlag sta flag == want) = true then { started p i stb with rip := p.base + t } else started p i stb)) := by
              rw [hsq']; exact Msb.fields rfl
            have hfe' : FlagEq ρa ρb s' := ⟨(fun h1 => by rw [hszf']; exact FE.1 (hsq'.symm ▸ h1)),
                                             (fun h2 => by rw [hscf']; exact FE.2 (hsq'.symm ▸ h2))⟩
            exact ⟨_, _, hta, htb, s', _, ρa, ρb, ms', hripa, hripb, hca'', hcb'', hma', hmb', hlike, hfe'⟩
  | select d c t f => exact (hnosel d c t f hs).elim
  | plain =>
    simp only [symInstr, hs] at h
    obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨s2, r2, e2, h⟩ := V.bind_ok h
    have hp := V.pure_ok h; injection hp with hn _; subst hn
    obtain ⟨ρa1, ρb1, sta1, stb1, ca1, cb1, xa, xb, ripa, ripb, Ma1, Mb1, A1, FE1⟩ :=
      stmts_two_sound Ea Eb i.bind p.base ua ub i.effect 0 e1 Hsa Hsb wf Msa Msb As FE
    have ca2 := settle_sound e2 ca1.holds ca1.wf
    have cb2 := settle_sound e2 cb1.holds cb1.wf
    obtain ⟨hfz, hfc, _⟩ := settle_flags e2
    have hfe2 : FlagEq ρa1 ρb1 { s2 with q := s1.q } :=
      ⟨fun h1 => by show FlagValEq ρa1 ρb1 s2.zf; rw [hfz]; exact FE1.1 h1,
       fun h2 => by show FlagValEq ρa1 ρb1 s2.cf; rw [hfc]; exact FE1.2 h2⟩
    exact ⟨.next sta1, .next stb1, xa, xb, { s2 with q := s1.q }, i.next, ρa1, ρb1,
      List.mem_cons_self .., ripa, ripb, ca1.then (ca2.q s1.q), cb1.then (cb2.q s1.q),
      Ma1, Mb1, A1, hfe2⟩

theorem symClears_two {ctx : Ctx} {p : Program} {a0 b0 : State} (Ea : Setting ctx p a0) (Eb : Setting ctx p b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0) :
    ∀ (fuel : Nat) {pc : Nat} {s s' : Sym} {items rest : Items} {ρa ρb : Nat → Int} {sta stb : State},
    symClears ctx pc fuel s items = .ok (s', rest) →
    Holds ctx a0 ρa s sta → Holds ctx b0 ρb s stb → WF ctx s →
    MarksOk ctx a0 s.q sta → MarksOk ctx b0 s.q stb → Alike sta stb → FlagEq ρa ρb s →
    ∃ sta' stb', sta'.plain = sta.plain ∧ stb'.plain = stb.plain ∧
      Holds ctx a0 ρa s' sta' ∧ Holds ctx b0 ρb s' stb' ∧ WF ctx s' ∧
      MarksOk ctx a0 s'.q sta' ∧ MarksOk ctx b0 s'.q stb' ∧
      Alike sta' stb' ∧ FlagEq ρa ρb s' ∧ s'.nvars = s.nvars
  | 0, _, s, s', items, rest, ρa, ρb, sta, stb, h, Ha, Hb, wf, Ma, Mb, A, FE => by
    simp only [symClears] at h; have hp := V.pure_ok h; injection hp with h1 _; subst h1
    exact ⟨sta, stb, rfl, rfl, Ha, Hb, wf, Ma, Mb, A, FE, rfl⟩
  | fuel + 1, pc, s, s', items, rest, ρa, ρb, sta, stb, h, Ha, Hb, wf, Ma, Mb, A, FE => by
    simp only [symClears] at h
    obtain ⟨opt, _, _, h⟩ := V.bind_ok h
    cases opt with
    | none =>
      have hp := V.pure_ok h; injection hp with h1 _; subst h1
      exact ⟨sta, stb, rfl, rfl, Ha, Hb, wf, Ma, Mb, A, FE, rfl⟩
    | some re =>
      obtain ⟨r, e⟩ := re
      obtain ⟨s1, _, hrev, hrest⟩ := V.bind_ok h
      obtain ⟨_, hcl, hs1, hvala⟩ := symRevealReg_sound Ea hrev Ha wf
      obtain ⟨_, _, _, hvalb⟩ := symRevealReg_sound Eb hrev Hb wf
      subst hs1
      have hsame := (traceClean_same ta hcl (.int (sta.reg r))).mp hvala
      have hregeq : sta.reg r = stb.reg r := by
        have := Value.unique hsame hvalb; injection this with h; exact Int.ofNat.inj h
      have A1 : Alike (unmarkReg sta r) (unmarkReg stb r) := unmarkReg_alike A hregeq
      have Ha1 : Holds ctx a0 ρa { s with q := { s.q with regq := r :: s.q.regq } } (unmarkReg sta r) :=
        (Ha.q _).fields rfl rfl rfl rfl rfl rfl
      have Hb1 : Holds ctx b0 ρb { s with q := { s.q with regq := r :: s.q.regq } } (unmarkReg stb r) :=
        (Hb.q _).fields rfl rfl rfl rfl rfl rfl
      obtain ⟨sta', stb', hpla, hplb, Ha', Hb', wf', Ma', Mb', A', FE', hnv⟩ :=
        symClears_two Ea Eb ta fuel hrest Ha1 Hb1 (wf.q _) (Ma.unmarkReg r) (Mb.unmarkReg r) A1 ⟨FE.1, FE.2⟩
      exact ⟨sta', stb', hpla.trans (unmarkReg_plain sta r), hplb.trans (unmarkReg_plain stb r),
        Ha', Hb', wf', Ma', Mb', A', FE', hnv⟩

/-- Direct two-run trace and result non-interference for a single function, stated with zero marks. -/
def TraceOk (world : List Program) (pieces : List Piece) (c : Contract) (defs : List Def) (p : Program) : Prop :=
  ∀ a b : State,
    Loaded pieces a → c.clear world pieces a → c.pre p a →
    Loaded pieces b → c.clear world pieces b → c.pre p b →
    c.traceAgree defs a b →
    ∀ a' b' : State, EndsP world p a.plain a' → EndsP world p b.plain b' →
      a'.trace = b'.trace ∧ (c.resultFollowsTrace = true → a'.reg 0 = b'.reg 0)

def TraceOkBelow (world : List Program) (pieces : List Piece) (c : Contract) (defs : List Def) (p : Program)
    (bound : Option (Nat × Nat)) : Prop :=
  ∀ a0 b0, (∀ r m, bound = some (r, m) → a0.reg r < m) →
    Loaded pieces a0 → c.clear world pieces a0 → c.pre p a0 →
    Loaded pieces b0 → c.clear world pieces b0 → c.pre p b0 →
    c.traceAgree defs a0 b0 →
    ∀ a' b', EndsP world p a0.plain a' → EndsP world p b0.plain b' →
      a'.trace = b'.trace ∧ (c.resultFollowsTrace = true → a'.reg 0 = b'.reg 0)

theorem TraceOk.below {world : List Program} {pieces : List Piece} {c : Contract} {defs : List Def} {p : Program}
    (T : TraceOk world pieces c defs p) (bound : Option (Nat × Nat)) : TraceOkBelow world pieces c defs p bound :=
  fun a0 b0 _ la ka pa lb kb pb ta a' b' Epa Epb => T a0 b0 la ka pa lb kb pb ta a' b' Epa Epb

def CalleesTrace (world : List Program) (ctx : Ctx) (a0 : State) : Prop :=
  ∀ name c, ctx.callees.lookup name = some c →
    ∃ q, findProgram world name = some q ∧ q.fits ∧
      c.stackBitsOk = true ∧
      (ctx.selfName = some name → c.decreases = ctx.contract.decreases ∧ ∀ d, c.regOf d = ctx.contract.regOf d) ∧
      MeetsBelow world ctx.pieces c ctx.defs q (ctx.recBound name c a0) ∧
      TraceOkBelow world ctx.pieces c ctx.defs q (ctx.recBound name c a0) ∧
      (∀ rh, c.resultHidden = some rh → c.result.isSome = true ∧
        TraceOkBelow world ctx.pieces (c.forResult rh) ctx.defs q (ctx.recBound name c a0))

theorem CalleesTrace.meet {world : List Program} {ctx : Ctx} {a0 : State} (W : CalleesTrace world ctx a0) : CalleesMeetAt world ctx a0 :=
  fun name c hl => let ⟨q, hq, hf, _, _, M, _, _⟩ := W name c hl; ⟨q, hq, hf, M⟩

theorem stackAt_eq_of_traceAgree {c : Contract} {defs : List Def} {a b : State}
    (hsb : c.stackBitsOk = true) (ta : c.traceAgree defs a b) : c.stackAt a = c.stackAt b := by
  unfold Contract.stackAt
  unfold Contract.stackBitsOk at hsb
  cases h : c.stackBits with
  | none => rfl
  | some sb =>
    simp only [h, Bool.and_eq_true] at hsb
    cases hr : c.regOf sb.arg with
    | none => simp [hr] at hsb
    | some r =>
      simp only [hr] at hsb
      have hmem : r ∈ c.cleanAtEntry := List.contains_iff_mem.mp hsb.2
      simp only [hr, ta.2.2.2.2.2.1 r hmem]

theorem decReg_eq_of_traceAgree {c : Contract} {defs : List Def} {a b : State}
    (hd : c.decreasesOk = true) (ta : c.traceAgree defs a b)
    {d : String} {r : Nat} (h1 : c.decreases = some d) (h2 : c.regOf d = some r) : a.reg r = b.reg r := by
  unfold Contract.decreasesOk at hd
  simp only [h1, h2] at hd
  exact ta.2.2.2.2.2.1 r (List.contains_iff_mem.mp hd)

def ReliedTrace (world : List Program) (ctx : Ctx) (p : Program) (a0 b0 : State)
    (seen : List Seen) (n : Nat) (ρa ρb : Nat → Int) : Prop :=
  ∀ e ∈ seen, (∀ nr ∈ e.place.names, nr.2 < ctx.nreg) ∧ e.first.nvars ≤ n ∧ bounded n e.d ∧
    ∀ ρa' ρb' sta' stb',
      AtPlace ctx e.place a0 e.first ρa ρa' sta' →
      AtPlace ctx e.place b0 e.first ρb ρb' stb' →
      sta'.rip = p.base + e.place.pc → stb'.rip = p.base + e.place.pc →
      MarksOk ctx a0 { regq := e.first.q.regq, fq := e.first.q.fq } sta' →
      MarksOk ctx b0 { regq := e.first.q.regq, fq := e.first.q.fq } stb' →
      Alike sta' stb' →
      (∃ m : Int, Value ctx.defs (placeVals ctx e.place a0 sta') e.place.decreases (.int m) ∧ m + 1 ≤ ev ρa e.d) →
      ∀ a' b', EndsP world p sta'.plain a' → EndsP world p stb'.plain b' →
        a'.trace = b'.trace ∧ (ctx.contract.resultFollowsTrace = true → a'.reg 0 = b'.reg 0)

theorem ReliedTrace.carried {world : List Program} {ctx : Ctx} {p : Program} {a0 b0 : State}
    {seen : List Seen} {n n' : Nat} {ρa ρa' ρb ρb' : Nat → Int}
    (T : ReliedTrace world ctx p a0 b0 seen n ρa ρb) (le : n ≤ n') (aa : Agree n ρa ρa') (ab : Agree n ρb ρb') :
    ReliedTrace world ctx p a0 b0 seen n' ρa' ρb' := by
  intro e m
  obtain ⟨hn, hf, hd, run⟩ := T e m
  refine ⟨hn, Nat.le_trans hf le, bounded_mono le hd, ?_⟩
  intro ρax ρbx stax stbx Aa Ab hripa hripb Ma Mb A ⟨k, val, lt⟩ a' b' Ea Eb
  refine run ρax ρbx stax stbx
    ⟨Agree.trans (Nat.le_refl _) (Agree.mono hf aa) Aa.outer, Aa.entry, Aa.data, Aa.kept, Aa.small, Aa.frame, Aa.mem, Aa.facts, Aa.lanes, Aa.cells, Aa.wrote, Aa.vecIntact⟩
    ⟨Agree.trans (Nat.le_refl _) (Agree.mono hf ab) Ab.outer, Ab.entry, Ab.data, Ab.kept, Ab.small, Ab.frame, Ab.mem, Ab.facts, Ab.lanes, Ab.cells, Ab.wrote, Ab.vecIntact⟩
    hripa hripb Ma Mb A ⟨k, val, ?_⟩ a' b' Ea Eb
  rw [ev_agree hd aa]; exact lt

theorem forResult_argRegs (c : Contract) (rh : List String) :
    (c.forResult rh).argRegs = c.argRegs := by
  unfold Contract.argRegs Contract.forResult; rfl

theorem forResult_regOf (c : Contract) (rh : List String) (x : String) :
    (c.forResult rh).regOf x = c.regOf x := by
  unfold Contract.regOf; rw [forResult_argRegs]; rfl

theorem forResult_regions (c : Contract) (rh : List String) :
    (c.forResult rh).regions = c.regions := by
  unfold Contract.regions
  rw [forResult_argRegs]
  have go : ∀ args regs, regionsIn (c.forResult rh) args regs = regionsIn c args regs := by
    intro args; induction args with
    | nil => intro _; rfl
    | cons ak more ih =>
      obtain ⟨nm, k⟩ := ak
      intro regs; cases regs with
      | nil => cases k <;> rfl
      | cons r rs => cases k <;> simp only [regionsIn, forResult_regOf, ih]
  exact go c.args _

theorem forResult_tableAt (c : Contract) (rh : List String) (j : Nat) :
    (c.forResult rh).tableAt j = c.tableAt j := by
  unfold Contract.tableAt Contract.fixeds
  rw [forResult_argRegs]
  have h2 : (c.forResult rh).args = c.args := rfl
  have h3 : (c.forResult rh).lanes = c.lanes := rfl
  rw [h2, h3]
  cases (fixedsIn c.args c.argRegs)[j]? with
  | none => rfl
  | some p =>
    dsimp only
    cases c.lanes.lookup p.1 with
    | none => rfl
    | some y => simp only [forResult_regOf]

theorem forResult_stackAt (c : Contract) (rh : List String) (s : State) :
    (c.forResult rh).stackAt s = c.stackAt s := by
  unfold Contract.stackAt
  have h1 : (c.forResult rh).stack = c.stack := rfl
  have h2 : (c.forResult rh).stackBits = c.stackBits := rfl
  rw [h1, h2]
  cases c.stackBits with
  | none => rfl
  | some sb => simp only [forResult_regOf]

theorem forResult_preLineVal (c : Contract) (rh : List String) (s : State) (k : Int) (ts : List (String × Int)) :
    preLineVal (c.forResult rh) s k ts = preLineVal c s k ts := by
  unfold preLineVal; rfl

theorem forResult_valArrays (c : Contract) (rh : List String) :
    (c.forResult rh).valArrays = c.valArrays := by
  unfold Contract.valArrays
  rw [forResult_argRegs]
  have h2 : (c.forResult rh).args = c.args := rfl
  rw [h2]
  have go : ∀ args regs, valArraysIn (c.forResult rh) args regs = valArraysIn c args regs := by
    intro args; induction args with
    | nil => intro _; rfl
    | cons ak more ih =>
      obtain ⟨nm, k⟩ := ak
      intro regs; cases regs with
      | nil => cases k <;> rfl
      | cons r rs => cases k <;> simp only [valArraysIn, forResult_regOf, ih]
  exact go c.args _

theorem forResult_pre (c : Contract) (rh : List String) (p : Program) (s : State) :
    (c.forResult rh).pre p s ↔ c.pre p s := by
  unfold Contract.pre
  have h1 : (c.forResult rh).outs = c.outs := rfl
  have h2 : (c.forResult rh).fixeds = c.fixeds := rfl
  have h3 : (c.forResult rh).slot = c.slot := rfl
  have h4 : (c.forResult rh).preLines = c.preLines := rfl
  simp only [forResult_regions, forResult_regOf, forResult_tableAt, forResult_stackAt, forResult_preLineVal, forResult_valArrays, h1, h2, h3, h4]
  rfl

theorem forResult_clear (c : Contract) (rh : List String) (world : List Program) (pieces : List Piece) (s : State) :
    (c.forResult rh).clear world pieces s ↔ c.clear world pieces s := by
  unfold Contract.clear Contract.inFrame Contract.inOut Contract.outs Contract.slot
  rw [forResult_argRegs]
  have h1 : (c.forResult rh).args = c.args := rfl
  have h2 : (c.forResult rh).arm64 = c.arm64 := rfl
  simp only [forResult_stackAt, h1, h2]

theorem step_trace {world : List Program} {ctx : Ctx} {p : Program} {a0 b0 : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0) (W : CalleesTrace world ctx a0)
    (hdok : ctx.contract.decreasesOk = true) (hno : hasSelect ctx.code = false)
    (Ka : ctx.contract.clear world ctx.pieces a0) (Kb : ctx.contract.clear world ctx.pieces b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0)
    {s : Sym} {pc : Nat} {i : Instr} {nexts : List (Sym × Next)} {items rest : Items}
    {ρa ρb : Nat → Int} {sta stb : State}
    (hl : ctx.code.lookup pc = some i) (h : symNext ctx s i items = .ok (nexts, rest))
    (Ha : Holds ctx a0 ρa s sta) (Hb : Holds ctx b0 ρb s stb) (wf : WF ctx s)
    (hripa : sta.rip = p.base + pc) (hripb : stb.rip = p.base + pc)
    (Ma : MarksOk ctx a0 s.q sta) (Mb : MarksOk ctx b0 s.q stb)
    (A : Alike sta stb) (FE : FlagEq ρa ρb s)
    (K : ∀ s' pc' ρa' ρb' sta' stb', (s', Next.at pc') ∈ nexts →
      sta'.rip = p.base + pc' → stb'.rip = p.base + pc' →
      Carried ctx a0 ρa s ρa' s' sta' → Carried ctx b0 ρb s ρb' s' stb' →
      MarksOk ctx a0 s'.q sta' → MarksOk ctx b0 s'.q stb' →
      Alike sta' stb' → FlagEq ρa' ρb' s' →
      ∀ a' b', EndsP world p sta'.plain a' → EndsP world p stb'.plain b' →
        a'.trace = b'.trace ∧ (ctx.contract.resultFollowsTrace = true → a'.reg 0 = b'.reg 0)) :
    ∀ a' b', EndsP world p sta.plain a' → EndsP world p stb.plain b' →
      a'.trace = b'.trace ∧ (ctx.contract.resultFollowsTrace = true → a'.reg 0 = b'.reg 0) := by
  have hfetcha : p.fetch sta.rip = some i := by
    unfold Program.fetch; rw [hripa, if_neg (by omega), Ea.code, Nat.add_sub_cancel_left]; exact hl
  have hfetchb : p.fetch stb.rip = some i := by
    unfold Program.fetch; rw [hripb, if_neg (by omega), Eb.code, Nat.add_sub_cancel_left]; exact hl
  intro a' b' Epa Epb
  cases hc : callTarget i with
  | none =>
    cases ht : tailTarget i with
    | none =>
      simp only [symNext, hc, ht] at h
      have noCall : ∀ {st : State} {t : State}, p.fetch st.rip = some i →
          EndsP world p st.plain t →
          (∃ u, execP Perm.all p i u st.plain = some (.returned t)) ∨
          (∃ u s1, execP Perm.all p i u st.plain = some (.next s1) ∧ EndsP world p s1 t) := by
        intro st t hf Ep
        cases Ep with
        | ret _ _ i2 u _ hf2 hx =>
          have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
          subst e; exact Or.inl ⟨u, hx⟩
        | step _ _ i2 u s1 _ hf2 hx E1 =>
          have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
          subst e; exact Or.inr ⟨u, s1, hx, E1⟩
        | call _ _ i2 _ _ _ _ hf2 hc2 _ _ _ =>
          have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
          subst e; rw [hc] at hc2; cases hc2
        | tail _ _ i2 _ _ _ hf2 ht2 _ _ =>
          have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
          subst e; rw [ht] at ht2; cases ht2
      have hnosel : ∀ d c t f, shape i.effect ≠ .select d c t f := by
        intro d c t f hs
        have hmem := lookup_mem hl
        have heff := shape_select hs
        have hany : hasSelect ctx.code = true := by
          unfold hasSelect
          exact List.any_eq_true.mpr ⟨(pc, i), hmem, by rw [heff]; rfl⟩
        rw [hno] at hany; cases hany
      rcases noCall hfetcha Epa with ⟨ua, hxa⟩ | ⟨ua, s1a, hxa, E1a⟩ <;>
      rcases noCall hfetchb Epb with ⟨ub, hxb⟩ | ⟨ub, s1b, hxb, E1b⟩
      · obtain ⟨oa, ob, hoa, hob, hmatch⟩ := symInstr_two_sound Ea Eb hnosel h Ha Hb wf Ma Mb A FE ua ub
        have hpa : execP Perm.all p i ua sta.plain = some oa.plain := by rw [exec_plain, exec_all (execQ_exec hoa)]; rfl
        have hpb : execP Perm.all p i ub stb.plain = some ob.plain := by rw [exec_plain, exec_all (execQ_exec hob)]; rfl
        rw [hxa] at hpa; rw [hxb] at hpb
        obtain ⟨ra, rfl, rfl⟩ := outcome_returned (Option.some.inj hpa).symm
        obtain ⟨rb, rfl, rfl⟩ := outcome_returned (Option.some.inj hpb).symm
        obtain ⟨lfa, _, Alr⟩ := hmatch
        exact ⟨Alr.trace, fun hrf => Alr.reg 0 (lfa.2.2.1 hrf)⟩
      · obtain ⟨oa, ob, hoa, hob, hmatch⟩ := symInstr_two_sound Ea Eb hnosel h Ha Hb wf Ma Mb A FE ua ub
        have hpa : execP Perm.all p i ua sta.plain = some oa.plain := by rw [exec_plain, exec_all (execQ_exec hoa)]; rfl
        have hpb : execP Perm.all p i ub stb.plain = some ob.plain := by rw [exec_plain, exec_all (execQ_exec hob)]; rfl
        rw [hxa] at hpa; rw [hxb] at hpb
        obtain ⟨ra, rfl, _⟩ := outcome_returned (Option.some.inj hpa).symm
        obtain ⟨sb1, rfl, _⟩ := outcome_next (Option.some.inj hpb).symm
        exact hmatch.elim
      · obtain ⟨oa, ob, hoa, hob, hmatch⟩ := symInstr_two_sound Ea Eb hnosel h Ha Hb wf Ma Mb A FE ua ub
        have hpa : execP Perm.all p i ua sta.plain = some oa.plain := by rw [exec_plain, exec_all (execQ_exec hoa)]; rfl
        have hpb : execP Perm.all p i ub stb.plain = some ob.plain := by rw [exec_plain, exec_all (execQ_exec hob)]; rfl
        rw [hxa] at hpa; rw [hxb] at hpb
        obtain ⟨sa1, rfl, _⟩ := outcome_next (Option.some.inj hpa).symm
        obtain ⟨rb, rfl, _⟩ := outcome_returned (Option.some.inj hpb).symm
        exact hmatch.elim
      · obtain ⟨oa, ob, hoa, hob, hmatch⟩ := symInstr_two_sound Ea Eb hnosel h Ha Hb wf Ma Mb A FE ua ub
        have hpa : execP Perm.all p i ua sta.plain = some oa.plain := by rw [exec_plain, exec_all (execQ_exec hoa)]; rfl
        have hpb : execP Perm.all p i ub stb.plain = some ob.plain := by rw [exec_plain, exec_all (execQ_exec hob)]; rfl
        rw [hxa] at hpa; rw [hxb] at hpb
        obtain ⟨sa1, rfl, rfl⟩ := outcome_next (Option.some.inj hpa).symm
        obtain ⟨sb1, rfl, rfl⟩ := outcome_next (Option.some.inj hpb).symm
        obtain ⟨s', pc', ρa', ρb', m, hra, hrb, ca', cb', Ma', Mb', A', FE'⟩ := hmatch
        exact K s' pc' ρa' ρb' sa1 sb1 m hra hrb ca' cb' Ma' Mb' A' FE' a' b' E1a E1b
    | some name =>
      simp only [symNext, hc, ht] at h
      cases hl2 : ctx.callees.lookup name with
      | none => simp only [hl2] at h; exact (refuse_ok h).elim
      | some c =>
        simp only [hl2] at h
        obtain ⟨_, _, htail, _⟩ := V.bind_ok h
        unfold symTail at htail
        split at htail
        next => exact (refuse_ok htail).elim
        next htf =>
        have T : TailOk ctx s name c := tailFits_spec (by simpa using htf)
        obtain ⟨_, _, _, htail⟩ := V.bind_ok htail
        obtain ⟨s1, _, e0, htail⟩ := V.bind_ok htail
        obtain ⟨_, _, e1, htail⟩ := V.bind_ok htail
        obtain ⟨s', _, e2, htail⟩ := V.bind_ok htail
        split at htail
        next => exact (refuse_ok htail).elim
        next hcq =>
        have hcq : callQuiet ctx (quietAtCall s1 c) c = true := by simpa using hcq
        simp only [hno, Bool.false_eq_true, ↓reduceIte, Bool.false_and] at htail
        split at htail
        next => exact (refuse_ok htail).elim
        next hretq =>
        obtain ⟨q, hq, fitq, _, _, meets, trok, trok2⟩ := W name c hl2
        have isTail : ∀ {st t : State}, p.fetch st.rip = some i → EndsP world p st.plain t →
            EndsP world q (afterTail q st).plain t := by
          intro st t hf Ep
          have no : ∀ u, execP Perm.all p i u st.plain = none := fun u => by rw [exec_plain, exec_tail ht]; rfl
          cases Ep with
          | ret _ _ i2 u _ hf2 hx =>
            have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
            subst e; rw [no u] at hx; cases hx
          | step _ _ i2 u _ _ hf2 hx _ =>
            have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
            subst e; rw [no u] at hx; cases hx
          | call _ _ i2 _ _ _ _ hf2 hc2 _ _ _ =>
            have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
            subst e; rw [hc] at hc2; cases hc2
          | tail _ _ i2 name2 q2 _ hf2 ht2 hw2 Ein =>
            have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
            subst e
            rw [ht] at ht2; injection ht2 with e; subst e
            rw [hq] at hw2; injection hw2 with e; subst e
            exact Ein
        have Eina := isTail hfetcha Epa
        have Einb := isTail hfetchb Epb
        have c1a := symKnow_sound KNOWN e0 Ha wf
        have c1b := symKnow_sound KNOWN e0 Hb wf
        have T1 := symKnow_tailOk T KNOWN e0
        have hqeq : s1.q = s.q := (symKnow_sp KNOWN e0).2.1
        have Ma1 : MarksOk ctx a0 s1.q sta := hqeq ▸ Ma
        have Mb1 : MarksOk ctx b0 s1.q stb := hqeq ▸ Mb
        have EXa := tailPreOk_sound Ea T1 c1a.holds e1
        have EXb := tailPreOk_sound Eb T1 c1b.holds e1
        obtain ⟨hprea, _, hwritea, _⟩ := tailCall'_sound Ea T1 EXa e2 c1a.holds c1a.wf q fitq
        obtain ⟨hpreb, _, hwriteb, _⟩ := tailCall'_sound Eb T1 EXb e2 c1b.holds c1b.wf q fitq
        have hbda : ∀ r m, ctx.recBound name c a0 = some (r, m) → (afterTail q sta).reg r < m := by
          intro r m hb; unfold Ctx.recBound at hb
          have hne : (ctx.selfName == some name) = false := beq_false_of_ne T.notSelf
          simp only [hne, Bool.false_eq_true, ite_false] at hb; cases hb
        have hbdb : ∀ r m, ctx.recBound name c a0 = some (r, m) → (afterTail q stb).reg r < m := by
          intro r m hb; unfold Ctx.recBound at hb
          have hne : (ctx.selfName == some name) = false := beq_false_of_ne T.notSelf
          simp only [hne, Bool.false_eq_true, ite_false] at hb; cases hb
        have hloada := loaded_tail Ea c1a.holds q
        have hloadb := loaded_tail Eb c1b.holds q
        have hclra := clear_tail Ka T1 c1a.holds q hwritea
        have hclrb := clear_tail Kb T1 c1b.holds q hwriteb
        have hruna := runsPlain_data (meets (afterTail q sta) hbda hloada hclra hprea)
        have hrunb := runsPlain_data (meets (afterTail q stb) hbdb hloadb hclrb hpreb)
        obtain ⟨s2a, ⟨hpost2a, _⟩, ha'eq⟩ := runsPlain_endsP hruna Eina
        obtain ⟨s2b, ⟨hpost2b, _⟩, hb'eq⟩ := runsPlain_endsP hrunb Einb
        have T1q : TailOk ctx (quietAtCall s1 c) name c :=
          ⟨T1.notSelf, T1.machine, T1.sp0, T1.rspClean, T1.linkOk, T1.keeps, T1.keepsVec,
           T1.noLanes, T1.noValArrays, T1.noFrameOut, T1.noFrameFix⟩
        have hta_call := tailQuiet_traceAgree (q := q) Ea Eb ta T1q
          (quietAtCall_holds c1a.holds c) (quietAtCall_holds c1b.holds c)
          (quietAtCall_marks Ma1 c) (quietAtCall_marks Mb1 c) A hcq
        obtain ⟨htr, hrf2⟩ := trok _ _ hbda hloada hclra hprea hloadb hclrb hpreb hta_call a' b' Eina Einb
        refine ⟨htr, fun hrft => ?_⟩
        have hri0 : ctx.contract.result.isSome = true := (Bool.and_eq_true _ _ |>.mp hrft).1
        have hrr0 : ctx.contract.retReg = 0 := (retReg_spec ctx.contract).2.2.2 hri0
        let cleanRet := callReturnsClean ctx (quietAtCall s1 c) c
        let q' := afterCallQ cleanRet c (quietAtCall s1 c)
        have hmem0 : 0 ∈ q'.regq := by
          have hnot : ¬(ctx.contract.resultFollowsTrace = true ∧ q'.regq.contains ctx.contract.retReg = false) := by
            simpa [q', cleanRet, Bool.and_eq_true, Bool.not_eq_true'] using hretq
          have hcont : q'.regq.contains 0 = true := by
            rw [← hrr0]; cases hc0 : q'.regq.contains ctx.contract.retReg with
            | true => rfl
            | false => exact absurd ⟨hrft, hc0⟩ hnot
          exact List.contains_iff_mem.mp hcont
        have ha0 : a'.reg 0 = s2a.reg 0 := by rw [ha'eq]; rfl
        have hb0 : b'.reg 0 = s2b.reg 0 := by rw [hb'eq]; rfl
        simp only [q', afterCallQ, List.mem_append, List.mem_filter, List.contains_iff_mem] at hmem0
        rcases hmem0 with hhead | ⟨hq0, hkeep0⟩
        · have hcr : cleanRet = true ∧ c.retReg = 0 := by
            cases hcr' : cleanRet with
            | false =>
              simp only [hcr', Bool.false_eq_true, ite_false, List.mem_singleton] at hhead
              exact absurd hhead (by decide)
            | true =>
              simp only [hcr', ite_true, List.mem_cons, List.mem_singleton] at hhead
              rcases hhead with h0 | h0
              · exact ⟨rfl, h0.symm⟩
              · exact absurd h0 (by decide)
          obtain ⟨hcr, hcreg0⟩ := hcr
          simp only [cleanRet, callReturnsClean] at hcr
          cases hret : c.returns with
          | some e =>
            simp only [hret] at hcr
            have hvea := hpost2a.2.2.2.2.1 e hret
            have hveb := hpost2b.2.2.2.2.1 e hret
            have hsame := (tailExprClean_same Ea Eb ta T1q
              (quietAtCall_holds c1a.holds c) (quietAtCall_holds c1b.holds c)
              (quietAtCall_marks Ma1 c) (quietAtCall_marks Mb1 c) A hcr (.int (s2a.reg c.retReg))).mp hvea
            have hu := Value.unique hsame hveb
            injection hu with hu
            have hreg_eq : s2a.reg c.retReg = s2b.reg c.retReg := Int.ofNat.inj hu
            rw [hcreg0] at hreg_eq; omega
          | none =>
            simp only [hret] at hcr
            by_cases hrf : c.resultFollowsTrace = true
            · exact hrf2 hrf
            · simp only [hrf, Bool.false_eq_true, ite_false] at hcr
              cases hri : c.result.isSome with
              | false => simp [hri] at hcr
              | true =>
                simp only [hri, ite_true] at hcr
                cases hrh : c.resultHidden with
                | none => simp [hrh] at hcr
                | some rh =>
                  simp only [hrh] at hcr
                  obtain ⟨_, trokr⟩ := trok2 rh hrh
                  have T1_r : TailOk ctx (quietAtCall s1 c) name (c.forResult rh) :=
                    ⟨T1q.notSelf, T1q.machine, T1q.sp0, T1q.rspClean, T1q.linkOk,
                     by intro r hr; rw [show (c.forResult rh).keeps = c.keeps from rfl]; exact T1q.keeps r hr,
                     by intro v hv; rw [show (c.forResult rh).keepsVec = c.keepsVec from rfl]; exact T1q.keepsVec v hv,
                     T1q.noLanes,
                     (by
                       have hgo : ∀ args regs, valArraysIn (c.forResult rh) args regs = valArraysIn c args regs := by
                         intro args; induction args with
                         | nil => intro regs; rfl
                         | cons ak more ih =>
                           obtain ⟨nm, kd⟩ := ak
                           intro regs; cases regs with
                           | nil => simp [valArraysIn]
                           | cons r rs =>
                             cases kd with
                             | valArray len ch el =>
                               simp only [valArraysIn, show (c.forResult rh).regOf len = c.regOf len from rfl, ih]
                             | number | bytes _ | out _ | fixed _ | inout _ => simp only [valArraysIn, ih]
                       exact (hgo c.args c.argRegs).trans T1q.noValArrays),
                     by intro x hx; rw [show (c.forResult rh).outs = c.outs from rfl] at hx; exact T1q.noFrameOut x hx,
                     by intro x hx; rw [show (c.forResult rh).fixeds = c.fixeds from rfl] at hx; exact T1q.noFrameFix x hx⟩
                  have hta_r := tailQuiet_traceAgree (q := q) (c := c.forResult rh) Ea Eb ta T1_r
                    (quietAtCall_holds c1a.holds c) (quietAtCall_holds c1b.holds c)
                    (quietAtCall_marks Ma1 c) (quietAtCall_marks Mb1 c) A hcr
                  have hrf_r : (c.forResult rh).resultFollowsTrace = true := by
                    simp [Contract.forResult, Contract.resultFollowsTrace, hri]
                  exact (trokr _ _ hbda hloada ((forResult_clear c rh _ _ _).mpr hclra) ((forResult_pre c rh _ _).mpr hprea)
                    hloadb ((forResult_clear c rh _ _ _).mpr hclrb) ((forResult_pre c rh _ _).mpr hpreb)
                    hta_r a' b' Eina Einb).2 hrf_r
        · have hmk0 : sta.marks.reg 0 = false := (quietAtCall_marks Ma1 c).reg 0 hq0
          have heq_st : sta.reg 0 = stb.reg 0 := A.reg 0 hmk0
          have hk_a : s2a.reg 0 = sta.reg 0 := hpost2a.2.2.1 0 hkeep0
          have hk_b : s2b.reg 0 = stb.reg 0 := hpost2b.2.2.1 0 hkeep0
          omega
  | some name =>
    simp only [symNext, hc] at h
    cases hl2 : ctx.callees.lookup name with
    | none => simp only [hl2] at h; exact (refuse_ok h).elim
    | some c =>
      simp only [hl2] at h
      split at h
      next => exact (refuse_ok h).elim
      next hfit =>
      have hfit : callFits ctx s i c = true := by simpa using hfit
      have Fa := callFits_sound Ea Ha hfit
      have Fb := callFits_sound Eb Hb hfit
      simp only [hno, Bool.false_eq_true, Bool.false_and, ↓reduceIte] at h
      obtain ⟨_, _, _, h⟩ := V.bind_ok h
      obtain ⟨s', r1, e1, h⟩ := V.bind_ok h
      split at h
      next => exact (refuse_ok h).elim
      next hcq =>
      have hcq : callQuiet ctx (quietAtCall s c) c = true := by simpa using hcq
      have hp := V.pure_ok h; injection hp with hn _; subst hn
      obtain ⟨q, hq, fitq, hsbok, hself_eq, meets, trok, trok2⟩ := W name c hl2
      have isCall : ∀ {st t : State}, p.fetch st.rip = some i → EndsP world p st.plain t →
          ∃ s1, EndsP world q (afterCall p q i st).plain s1 ∧ EndsP world p s1 t := by
        intro st t hf Ep
        have no : ∀ u, execP Perm.all p i u st.plain = none := fun u => by rw [exec_plain, exec_call hc]; rfl
        cases Ep with
        | ret _ _ i2 u _ hf2 hx =>
          have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
          subst e; rw [no u] at hx; cases hx
        | step _ _ i2 u _ _ hf2 hx _ =>
          have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
          subst e; rw [no u] at hx; cases hx
        | call _ _ i2 name2 q2 s1 _ hf2 hc2 hw2 Ein Eout =>
          have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
          subst e
          rw [hc] at hc2; injection hc2 with e; subst e
          rw [hq] at hw2; injection hw2 with e; subst e
          rw [afterCallP_plain] at Ein
          exact ⟨s1, Ein, Eout⟩
        | tail _ _ i2 _ _ _ hf2 ht2 _ _ =>
          have e : i2 = i := by have := hf2; rw [show st.plain.rip = st.rip from rfl, hf] at this; exact (Option.some.inj this).symm
          subst e
          rw [tailTarget_not_call ht2] at hc; cases hc
      obtain ⟨s1a, Eina, Eouta⟩ := isCall hfetcha Epa
      obtain ⟨s1b, Einb, Eoutb⟩ := isCall hfetchb Epb
      have hcode : (pc, i) ∈ p.code := by rw [Ea.code]; exact lookup_mem hl
      obtain ⟨h8a, hwa, hprea, hdeca, hreada, hwritea, hposta⟩ := symCall_sound Ea e1 Ha wf q fitq i Fa (Ea.fits hcode)
      obtain ⟨h8b, hwb, hpreb, hdecb, hreadb, hwriteb, hpostb⟩ := symCall_sound Eb e1 Hb wf q fitq i Fb (Eb.fits hcode)
      have hbda : ∀ r m, ctx.recBound name c a0 = some (r, m) → (afterCall p q i sta).reg r < m := by
        intro r m hb
        unfold Ctx.recBound at hb
        split at hb
        next hself =>
          have hself' : ctx.selfName = some name := by simpa using hself
          cases hd : c.decreases with
          | none => simp [hd] at hb
          | some d =>
            simp only [hd, Option.bind_some] at hb
            cases hr : c.regOf d with
            | none => simp [hr] at hb
            | some r' =>
              simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
              obtain ⟨rfl, rfl⟩ := hb
              exact hdeca hself' d r' hd hr
        next => cases hb
      have hbdb : ∀ r m, ctx.recBound name c a0 = some (r, m) → (afterCall p q i stb).reg r < m := by
        intro r m hb
        unfold Ctx.recBound at hb
        split at hb
        next hself =>
          have hself' : ctx.selfName = some name := by simpa using hself
          obtain ⟨hdeq, hreq⟩ := hself_eq hself'
          cases hd : c.decreases with
          | none => simp [hd] at hb
          | some d =>
            simp only [hd, Option.bind_some] at hb
            cases hr : c.regOf d with
            | none => simp [hr] at hb
            | some r' =>
              simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
              obtain ⟨rfl, rfl⟩ := hb
              have hlt := hdecb hself' d r' hd hr
              have hreg_eq := decReg_eq_of_traceAgree hdok ta (hdeq.symm.trans hd) ((hreq d).symm.trans hr)
              omega
        next => cases hb
      have hloada := loaded_call Ea Ha q i Fa.link h8a hwa
      have hloadb := loaded_call Eb Hb q i Fb.link h8b hwb
      have hclra := clear_call Ka Ha p q i Fa.link hwa hwritea
      have hclrb := clear_call Kb Hb p q i Fb.link hwb hwriteb
      have hruna := runsPlain_data (meets _ hbda hloada hclra hprea)
      have hrunb := runsPlain_data (meets _ hbdb hloadb hclrb hpreb)
      rw [afterCall_data] at hruna hrunb
      obtain ⟨s2a, ⟨hpost2a, hdata2a⟩, hs1a⟩ := runsPlain_endsP hruna Eina
      obtain ⟨s2b, ⟨hpost2b, hdata2b⟩, hs1b⟩ := runsPlain_endsP hrunb Einb
      have hta_call := callQuiet_traceAgree Ea Eb ta (quietAtCall_holds Ha c) (quietAtCall_holds Hb c)
        (quietAtCall_marks Ma c) (quietAtCall_marks Mb c) A Fa Fb h8a h8b hwa hwb hwritea hcq
      obtain ⟨htr2, hrf2⟩ := trok _ _ hbda hloada hclra hprea hloadb hclrb hpreb hta_call s1a s1b Eina Einb
      have htr2' : s2a.trace = s2b.trace := by
        have e1 : s1a.trace = s2a.trace := by rw [hs1a]; rfl
        have e2 : s1b.trace = s2b.trace := by rw [hs1b]; rfl
        exact e1.symm.trans (htr2.trans e2)
      let cleanRet := callReturnsClean ctx (quietAtCall s c) c
      have hret0 : cleanRet = true → s2a.reg c.retReg = s2b.reg c.retReg := by
        intro hcr
        show s2a.reg c.retReg = s2b.reg c.retReg
        have heq0 : s1a.reg 0 = s1b.reg 0 → c.retReg = 0 → s2a.reg c.retReg = s2b.reg c.retReg := fun h0 hr0 => by
          rw [hr0]
          have e1 : s1a.reg 0 = s2a.reg 0 := by rw [hs1a]; rfl
          have e2 : s1b.reg 0 = s2b.reg 0 := by rw [hs1b]; rfl
          omega
        simp only [cleanRet, callReturnsClean] at hcr
        cases hret : c.returns with
        | some e =>
          simp only [hret] at hcr
          have hvea := hpost2a.2.2.2.2.1 e hret
          have hveb := hpost2b.2.2.2.2.1 e hret
          have hsame := (callExprClean_same Ea Eb ta (quietAtCall_holds Ha c) (quietAtCall_holds Hb c)
            (quietAtCall_marks Ma c) (quietAtCall_marks Mb c) A Fa Fb h8a h8b hwa hwb hcr (.int (s2a.reg c.retReg))).mp hvea
          have hu := Value.unique hsame hveb
          injection hu with hu; exact Int.ofNat.inj hu
        | none =>
          simp only [hret] at hcr
          by_cases hrf : c.resultFollowsTrace = true
          · have hri : c.result.isSome = true := (Bool.and_eq_true _ _ |>.mp hrf).1
            exact heq0 (hrf2 hrf) ((retReg_spec c).2.2.2 hri)
          · simp only [hrf] at hcr
            cases hri : c.result.isSome with
            | false => simp [hri] at hcr
            | true =>
              simp only [hri, ↓reduceIte] at hcr
              cases hrh : c.resultHidden with
              | none => simp [hrh] at hcr
              | some rh =>
                simp only [hrh] at hcr
                obtain ⟨_, trokr⟩ := trok2 rh hrh
                have Fa_r : Fits ctx sta i (c.forResult rh) := ⟨Fa.machine, Fa.link, Fa.aligned⟩
                have Fb_r : Fits ctx stb i (c.forResult rh) := ⟨Fb.machine, Fb.link, Fb.aligned⟩
                have hta_r := callQuiet_traceAgree (c := c.forResult rh) Ea Eb ta
                  (quietAtCall_holds Ha c) (quietAtCall_holds Hb c)
                  (quietAtCall_marks Ma c) (quietAtCall_marks Mb c) A Fa_r Fb_r h8a h8b hwa hwb hwritea hcr
                have hrf_r : (c.forResult rh).resultFollowsTrace = true := by
                  simp [Contract.forResult, Contract.resultFollowsTrace, hri]
                exact heq0 ((trokr _ _ hbda hloada ((forResult_clear c rh _ _ _).mpr hclra) ((forResult_pre c rh _ _).mpr hprea)
                  hloadb ((forResult_clear c rh _ _ _).mpr hclrb) ((forResult_pre c rh _ _).mpr hpreb)
                  hta_r s1a s1b Eina Einb).2 hrf_r) ((retReg_spec c).2.2.2 hri)
      obtain ⟨hrspa, _, haftera⟩ := callQuiet_sound Ea (quietAtCall_marks Ma c) (quietAtCall_holds Ha c) hcq q i Fa hwa hwritea
      obtain ⟨_, _, hafterb⟩ := callQuiet_sound Eb (quietAtCall_marks Mb c) (quietAtCall_holds Hb c) hcq q i Fb hwb hwriteb
      have Ac : Alike (afterCall p q i sta) (afterCall p q i stb) := afterCall_alike A (fun _ => hrspa)
      let s2am : State := { s2a with marks := postCallMarks c cleanRet (afterCall p q i sta) }
      let s2bm : State := { s2b with marks := postCallMarks c cleanRet (afterCall p q i stb) }
      have hmk_eq : s2am.marks = s2bm.marks := by
        have hsp_eq : (afterCall p q i sta).reg RSP = (afterCall p q i stb).reg RSP := hta_call.2.2.2.1
        have hout_eq : ∀ addr, c.inOut (afterCall p q i sta) addr = c.inOut (afterCall p q i stb) addr := by
          intro addr
          unfold Contract.inOut
          have hall : ∀ x ∈ c.outs,
              (decide ((afterCall p q i sta).reg x.2.1 ≤ addr) && decide (addr < (afterCall p q i sta).reg x.2.1 + x.2.2)) =
              (decide ((afterCall p q i stb).reg x.2.1 ≤ addr) && decide (addr < (afterCall p q i stb).reg x.2.1 + x.2.2)) := by
            intro ⟨nm, r, n⟩ hm
            have hr_cl : r ∈ c.cleanAtEntry := by
              have hcl : ∀ args regs, (nm, r, n) ∈ outsIn args regs → r ∈ cleanIn c args regs := by
                intro args; induction args with
                | nil => intro regs h; cases h
                | cons ak more ih =>
                  intro regs h; cases regs with
                  | nil => cases ak.2 <;> simp [outsIn] at h
                  | cons r0 rs =>
                    cases ak with
                    | mk nm0 k0 =>
                      cases k0 with
                      | out n0 =>
                        simp only [outsIn, List.mem_cons] at h
                        simp only [cleanIn, List.mem_append, List.mem_singleton]
                        rcases h with h1 | h2
                        · injection h1 with _ h1; injection h1 with h1 _; exact Or.inl h1
                        · exact Or.inr (ih rs h2)
                      | inout n0 =>
                        simp only [outsIn, List.mem_cons] at h
                        simp only [cleanIn, List.mem_append, List.mem_singleton]
                        rcases h with h1 | h2
                        · injection h1 with _ h1; injection h1 with h1 _; exact Or.inl h1
                        · exact Or.inr (ih rs h2)
                      | number | bytes _ | fixed _ | valArray _ _ =>
                        simp only [outsIn] at h
                        simp only [cleanIn, List.mem_append]
                        exact Or.inr (ih rs h)
              exact List.mem_cons_of_mem RSP (hcl c.args c.argRegs hm)
            have heq := hta_call.2.2.2.2.2.1 r hr_cl
            simp [heq]
          have any_congr : ∀ (l : List (String × Nat × Nat)) (f g : String × Nat × Nat → Bool),
              (∀ x ∈ l, f x = g x) → l.any f = l.any g := by
            intro l f g hfg; induction l with
            | nil => rfl
            | cons x xs ih => simp only [List.any_cons, hfg x (List.mem_cons_self ..), ih (fun y hy => hfg y (List.mem_cons_of_mem _ hy))]
          exact any_congr c.outs _ _ hall
        have hstack_eq : c.stackAt (afterCall p q i sta) = c.stackAt (afterCall p q i stb) :=
          stackAt_eq_of_traceAgree hsbok hta_call
        have hfr_eq : ∀ addr, c.inFrame (afterCall p q i sta) addr = c.inFrame (afterCall p q i stb) addr := by
          intro addr; simp [Contract.inFrame, hsp_eq, hstack_eq]
        have hmem_mk : (afterCall p q i sta).marks.mem = (afterCall p q i stb).marks.mem :=
          congrArg Marks.mem Ac.marks
        show postCallMarks c cleanRet (afterCall p q i sta) = postCallMarks c cleanRet (afterCall p q i stb)
        unfold postCallMarks
        congr 1
        funext addr
        simp [hfr_eq addr, hout_eq addr, hmem_mk]
      have As2m : Alike s2am s2bm := by
        refine ⟨hmk_eq, ?_, ?_, htr2', ?_, (fun h => by simp [s2am, postCallMarks] at h),
          (fun h => by simp [s2am, postCallMarks] at h), ?_, (fun _ h => by simp [s2am, postCallMarks] at h)⟩
        · show s2a.rip = s2b.rip
          rw [hpost2a.1, hpost2b.1]; exact hta_call.2.2.2.2.1
        · show s2a.data = s2b.data
          rw [hdata2a, hdata2b]; exact A.data
        · intro r hr
          simp only [s2am, postCallMarks, Bool.not_eq_false', Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hr
          rcases hr with rfl | ⟨hcr, rfl⟩
          · show s2a.reg RSP = s2b.reg RSP
            rw [hpost2a.2.1, hpost2b.2.1, hta_call.2.2.2.1]
          · exact hret0 hcr
        · intro addr ha
          simp only [s2am, postCallMarks] at ha
          cases hfr : c.inFrame (afterCall p q i sta) addr <;>
          cases hou : c.inOut (afterCall p q i sta) addr <;>
            simp only [hfr, hou, Bool.true_or, Bool.or_true, Bool.false_or, ↓reduceIte] at ha
          · have hfrb : c.inFrame (afterCall p q i stb) addr = false := by
              rw [← hfr]; simp [Contract.inFrame, hta_call.2.2.2.1, stackAt_eq_of_traceAgree hsbok hta_call]
            have houb : c.inOut (afterCall p q i stb) addr = false := by
              have hme : (postCallMarks c cleanRet (afterCall p q i sta)).mem addr =
                         (postCallMarks c cleanRet (afterCall p q i stb)).mem addr :=
                congrFun (congrArg Marks.mem hmk_eq) addr
              simp only [postCallMarks, hfr, hou, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hfrb] at hme
              have ha' : (afterCall p q i sta).marks.mem addr = false := ha
              cases hb0 : c.inOut (afterCall p q i stb) addr with
              | false => rfl
              | true => simp [hb0, ha'] at hme
            show s2a.mem addr = s2b.mem addr
            rw [hpost2a.2.2.2.1 addr hfr hou, hpost2b.2.2.2.1 addr hfrb houb]
            exact Ac.mem addr ha
          · cases ha
          · cases ha
          · cases ha
      have hkept_a : ∀ r ∈ c.keeps, s2am.reg r = sta.reg r := fun r hr => by
        obtain ⟨_, ne, nl⟩ := keeps_spec hr
        show s2a.reg r = sta.reg r
        rw [hpost2a.2.2.1 r hr, afterCall_reg Fa.link (callKeeps ne nl)]
      have hkept_b : ∀ r ∈ c.keeps, s2bm.reg r = stb.reg r := fun r hr => by
        obtain ⟨_, ne, nl⟩ := keeps_spec hr
        show s2b.reg r = stb.reg r
        rw [hpost2b.2.2.1 r hr, afterCall_reg Fb.link (callKeeps ne nl)]
      have Aback : Alike (backFrom c.keeps sta s2am) (backFrom c.keeps stb s2bm) :=
        backFrom_alike A As2m hkept_a hkept_b
      have hqma : s2am.marks.reg RSP = false ∧ (cleanRet = true → s2am.marks.reg c.retReg = false) ∧
          ∀ a, c.inFrame (afterCall p q i sta) a = false → c.inOut (afterCall p q i sta) a = false →
            s2am.marks.mem a = (afterCall p q i sta).marks.mem a :=
        ⟨by simp [s2am, postCallMarks], fun h0 => by simp [s2am, postCallMarks, h0],
         fun a hf ho => by simp [s2am, postCallMarks, hf, ho]⟩
      have hqmb : s2bm.marks.reg RSP = false ∧ (cleanRet = true → s2bm.marks.reg c.retReg = false) ∧
          ∀ a, c.inFrame (afterCall p q i stb) a = false → c.inOut (afterCall p q i stb) a = false →
            s2bm.marks.mem a = (afterCall p q i stb).marks.mem a :=
        ⟨by simp [s2bm, postCallMarks], fun h0 => by simp [s2bm, postCallMarks, h0],
         fun a hf ho => by simp [s2bm, postCallMarks, hf, ho]⟩
      obtain ⟨hripa2, ρa', ca'⟩ := hposta s2am (post_fields hpost2a rfl rfl rfl rfl) hdata2a
      obtain ⟨hripb2, ρb', cb'⟩ := hpostb s2bm (post_fields hpost2b rfl rfl rfl rfl) hdata2b
      have hpla2 : (backFrom c.keeps sta s2am).plain = s1a := hs1a.symm
      have hplb2 : (backFrom c.keeps stb s2bm).plain = s1b := hs1b.symm
      exact K _ i.next ρa' ρb' (backFrom c.keeps sta s2am) (backFrom c.keeps stb s2bm)
        (List.mem_cons_self ..) hripa2 hripb2
        ((ca'.q _).fields rfl rfl rfl rfl rfl rfl) ((cb'.q _).fields rfl rfl rfl rfl rfl rfl)
        (haftera cleanRet s2am (fun hcr => callReturnsClean_givesNumber hcr) hqma)
        (hafterb cleanRet s2bm (fun hcr => callReturnsClean_givesNumber hcr) hqmb)
        Aback ⟨(fun h => by cases h), (fun h => by cases h)⟩
        a' b' (hpla2 ▸ Eouta) (hplb2 ▸ Eoutb)

def ReliedJoinTrace (world : List Program) (ctx : Ctx) (p : Program) (a0 b0 : State)
    (jdone : List JoinEntry) (n : Nat) (ρab ρbb : Nat → Int) : Prop :=
  ∀ e ∈ jdone, (∀ nr ∈ e.place.names, nr.2 < ctx.nreg) ∧ e.first.nvars = n ∧
    ∀ ρa' ρb' sta' stb', AtPlace ctx e.place a0 e.first ρab ρa' sta' → AtPlace ctx e.place b0 e.first ρbb ρb' stb' →
      sta'.rip = p.base + e.place.pc → stb'.rip = p.base + e.place.pc →
      MarksOk ctx a0 { regq := e.first.q.regq, fq := e.first.q.fq } sta' →
      MarksOk ctx b0 { regq := e.first.q.regq, fq := e.first.q.fq } stb' →
      Alike sta' stb' →
      ∀ a' b', EndsP world p sta'.plain a' → EndsP world p stb'.plain b' →
        a'.trace = b'.trace ∧ (ctx.contract.resultFollowsTrace = true → a'.reg 0 = b'.reg 0)

theorem explore_trace {world : List Program} {ctx : Ctx} {p : Program} {a0 b0 : State}
    (Ea : Setting ctx p a0) (Eb : Setting ctx p b0) (W : CalleesTrace world ctx a0)
    (hdok : ctx.contract.decreasesOk = true) (hno : hasSelect ctx.code = false)
    (Ka : ctx.contract.clear world ctx.pieces a0) (Kb : ctx.contract.clear world ctx.pieces b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0) :
    ∀ (fuel : Nat) {base : Sym} {seen : List Seen} {jstack : List Nat} {jdone jdone' : List JoinEntry}
      {s : Sym} {pc : Nat} {items rest : Items} {ρab ρbb : Nat → Int} {stab stbb : State},
    explore ctx fuel base seen jstack jdone s pc items = .ok (jdone', rest) →
    Holds ctx a0 ρab base stab → Holds ctx b0 ρbb base stbb → WF ctx base →
    ReliedTrace world ctx p a0 b0 seen base.nvars ρab ρbb →
    ReliedJoinTrace world ctx p a0 b0 jdone base.nvars ρab ρbb →
    ReliedJoinTrace world ctx p a0 b0 jdone' base.nvars ρab ρbb ∧
    (∀ ρa ρb sta stb, base.nvars ≤ s.nvars → Agree base.nvars ρab ρa → Agree base.nvars ρbb ρb →
      Holds ctx a0 ρa s sta → Holds ctx b0 ρb s stb → WF ctx s →
      sta.rip = p.base + pc → stb.rip = p.base + pc →
      MarksOk ctx a0 s.q sta → MarksOk ctx b0 s.q stb →
      Alike sta stb → FlagEq ρa ρb s →
      ∀ a' b', EndsP world p sta.plain a' → EndsP world p stb.plain b' →
        a'.trace = b'.trace ∧ (ctx.contract.resultFollowsTrace = true → a'.reg 0 = b'.reg 0))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _, _ => by
    simp only [explore] at h; exact (refuse_ok h).elim
  | fuel + 1, base, seen, jstack, jdone, jdone', s, pc, items, rest, ρab, ρbb, stab, stbb, h, Hab, Hbb, wfb, Tb, Jb => by
    cases hl : ctx.code.lookup pc with
    | none => simp only [explore, hl] at h; exact (refuse_ok h).elim
    | some i =>
      simp only [explore, hl] at h
      obtain ⟨sc, r0, hc, h⟩ := V.bind_ok h
      obtain ⟨nexts, r1, e1, h⟩ := V.bind_ok h
      have honward_J : ∀ nx ∈ nexts, ∀ jd jd' it it',
          ReliedJoinTrace world ctx p a0 b0 jd base.nvars ρab ρbb →
          onward ctx base seen jstack (explore ctx fuel) jd nx it = .ok (jd', it') →
          ReliedJoinTrace world ctx p a0 b0 jd' base.nvars ρab ρbb := by
        intro nx _ jd jd' it it' Jcur hbody
        rcases nx with ⟨snx, nxt⟩
        cases nxt with
        | returned =>
          simp only [onward] at hbody
          have := V.pure_ok hbody; injection this with h1 _; subst h1; exact Jcur
        | «at» pc' =>
          simp only [onward] at hbody
          cases hp : ctx.places.find? (fun p => p.pc == pc') with
          | none =>
            simp only [hp] at hbody
            exact (explore_trace Ea Eb W hdok hno Ka Kb ta fuel hbody Hab Hbb wfb Tb Jcur).1
          | some pl =>
            simp only [hp] at hbody
            have epc : pl.pc = pc' := by simpa using List.find?_some hp
            cases hj : pl.isJoin with
            | false =>
              simp only [hj, Bool.false_eq_true, ↓reduceIte] at hbody
              cases hs : seen.find? (fun e => e.place.pc == pc') with
              | some e =>
                simp only [hs] at hbody
                obtain ⟨_, _, _, hpur⟩ := V.bind_ok hbody
                have := V.pure_ok hpur; injection this with h1 _; subst h1; exact Jcur
              | none =>
                simp only [hs] at hbody
                obtain ⟨⟨_, _, _⟩, _, _, h2⟩ := V.bind_ok hbody
                obtain ⟨_, _, _, hpur⟩ := V.bind_ok h2
                have := V.pure_ok hpur; injection this with h1 _; subst h1; exact Jcur
            | true =>
              simp only [hj, ↓reduceIte] at hbody
              split at hbody
              · exact (refuse_ok hbody).elim
              · cases hjd : jd.find? (fun e => e.place.pc == pc') with
                | some e =>
                  simp only [hjd] at hbody
                  obtain ⟨_, _, _, hpur⟩ := V.bind_ok hbody
                  have := V.pure_ok hpur; injection this with h1 _; subst h1; exact Jcur
                | none =>
                  simp only [hjd] at hbody
                  cases hfirst : joinFirst ctx base snx pl with
                  | none => simp only [hfirst] at hbody; exact (refuse_ok hbody).elim
                  | some first =>
                    simp only [hfirst] at hbody
                    obtain ⟨_, _, _, h2⟩ := V.bind_ok hbody
                    obtain ⟨g, _, eg, h3⟩ := V.bind_ok h2
                    obtain ⟨jmid, _, hgo, hpur⟩ := V.bind_ok h3
                    have := V.pure_ok hpur; injection this with h1 _; subst h1
                    obtain ⟨hnames, hnv, Ga⟩ := generalizeJoin_sound Ea pl hfirst eg Hab wfb
                    obtain ⟨_, _, Gb⟩ := generalizeJoin_sound Eb pl hfirst eg Hbb wfb
                    obtain ⟨Jmid, runG⟩ := explore_trace Ea Eb W hdok hno Ka Kb ta fuel hgo Hab Hbb wfb Tb Jcur
                    intro je mje
                    cases mje with
                    | head =>
                      refine ⟨hnames, hnv, ?_⟩
                      intro ρax ρbx stax stbx Aax Abx hripax hripbx Max Mbx Ax
                      obtain ⟨ρa'', Hga, wg, leg, agax⟩ := Ga ρax stax Aax
                      obtain ⟨ρb'', Hgb, _, _, agbx⟩ := Gb ρbx stbx Abx
                      have agab : Agree base.nvars ρab ρa'' := Agree.trans (Nat.le_refl _) (hnv ▸ Aax.outer) agax
                      have agbb : Agree base.nvars ρbb ρb'' := Agree.trans (Nat.le_refl _) (hnv ▸ Abx.outer) agbx
                      exact runG ρa'' ρb'' stax stbx leg agab agbb (Hga.q _) (Hgb.q _) (wg.q _)
                        (by rw [← epc]; exact hripax) (by rw [← epc]; exact hripbx) Max Mbx Ax
                        ⟨(fun h => by cases h), (fun h => by cases h)⟩
                    | tail _ mt => exact Jmid je mt
      obtain ⟨Jout, hmem⟩ := eachState_prop (P := fun jd => ReliedJoinTrace world ctx p a0 b0 jd base.nvars ρab ρbb) h Jb honward_J
      refine ⟨Jout, ?_⟩
      intro ρa ρb sta stb hle haga hagb Ha Hb wf hripa hripb Ma Mb A FE a' b' Epa Epb
      obtain ⟨stca, stcb, hpla, hplb, Hca, Hcb, wfc, Mca, Mcb, Ac, FEc, hnv⟩ :=
        symClears_two Ea Eb ta CLEARS hc Ha Hb wf Ma Mb A FE
      have hripca : stca.rip = p.base + pc := (congrArg State.rip hpla).trans hripa
      have hripcb : stcb.rip = p.base + pc := (congrArg State.rip hplb).trans hripb
      have hlec : base.nvars ≤ sc.nvars := hnv ▸ hle
      refine step_trace Ea Eb W hdok hno Ka Kb ta hl e1 Hca Hcb wfc hripca hripcb Mca Mcb Ac FEc ?_ a' b' (hpla.symm ▸ Epa) (hplb.symm ▸ Epb)
      intro s' pc' ρa' ρb' sta' stb' m hripa' hripb' ca' cb' Ma' Mb' A' FE'
      obtain ⟨jd, jd', items', r', Jcur, hbody⟩ := hmem (s', Next.at pc') m
      have hle' : base.nvars ≤ s'.nvars := Nat.le_trans hlec ca'.mono
      have haga' : Agree base.nvars ρab ρa' := Agree.trans hlec haga ca'.agree
      have hagb' : Agree base.nvars ρbb ρb' := Agree.trans hlec hagb cb'.agree
      have T' : ReliedTrace world ctx p a0 b0 seen s'.nvars ρa' ρb' := Tb.carried hle' haga' hagb'
      simp only [onward] at hbody
      cases hp : ctx.places.find? (fun p => p.pc == pc') with
      | none =>
        simp only [hp] at hbody
        exact (explore_trace Ea Eb W hdok hno Ka Kb ta fuel hbody Hab Hbb wfb Tb Jcur).2
          ρa' ρb' sta' stb' hle' haga' hagb' ca'.holds cb'.holds ca'.wf hripa' hripb' Ma' Mb' A' FE'
      | some pl =>
        simp only [hp] at hbody
        have epc : pl.pc = pc' := by simpa using List.find?_some hp
        cases hj : pl.isJoin with
        | true =>
          simp only [hj, ↓reduceIte] at hbody
          split at hbody
          · exact (refuse_ok hbody).elim
          · cases hjd : jd.find? (fun e => e.place.pc == pc') with
            | some e =>
              simp only [hjd] at hbody
              have em : e ∈ jd := List.mem_of_find?_eq_some hjd
              have eq : e.place.pc = pc' := by simpa using List.find?_some hjd
              obtain ⟨_, _, harr, _⟩ := V.bind_ok hbody
              obtain ⟨hn, hnv, run⟩ := Jcur e em
              have Aa := arriveJoin_sound Ea e.place hn harr ca'.holds ca'.wf (hnv.symm ▸ haga')
              have Ab := arriveJoin_sound Eb e.place hn harr cb'.holds cb'.wf (hnv.symm ▸ hagb')
              exact run ρa' ρb' sta' stb' Aa Ab (by rw [eq]; exact hripa') (by rw [eq]; exact hripb')
                (Ma'.fewer (arriveJoin_q harr).1 (arriveJoin_q harr).2)
                (Mb'.fewer (arriveJoin_q harr).1 (arriveJoin_q harr).2) A'
            | none =>
              simp only [hjd] at hbody
              cases hfirst : joinFirst ctx base s' pl with
              | none => simp only [hfirst] at hbody; exact (refuse_ok hbody).elim
              | some first =>
                simp only [hfirst] at hbody
                obtain ⟨_, _, harr, h2⟩ := V.bind_ok hbody
                obtain ⟨g, _, eg, h3⟩ := V.bind_ok h2
                obtain ⟨_, _, hgo, _⟩ := V.bind_ok h3
                obtain ⟨hnames, hnv, Ga⟩ := generalizeJoin_sound Ea pl hfirst eg Hab wfb
                obtain ⟨_, _, Gb⟩ := generalizeJoin_sound Eb pl hfirst eg Hbb wfb
                have runG := (explore_trace Ea Eb W hdok hno Ka Kb ta fuel hgo Hab Hbb wfb Tb Jcur).2
                have Aa := arriveJoin_sound Ea pl hnames harr ca'.holds ca'.wf (hnv.symm ▸ haga')
                have Ab := arriveJoin_sound Eb pl hnames harr cb'.holds cb'.wf (hnv.symm ▸ hagb')
                obtain ⟨ρa'', Hga, wg, leg, agax⟩ := Ga ρa' sta' Aa
                obtain ⟨ρb'', Hgb, _, _, agbx⟩ := Gb ρb' stb' Ab
                have agab : Agree base.nvars ρab ρa'' := Agree.trans (Nat.le_refl _) (hnv ▸ Aa.outer) agax
                have agbb : Agree base.nvars ρbb ρb'' := Agree.trans (Nat.le_refl _) (hnv ▸ Ab.outer) agbx
                exact runG ρa'' ρb'' sta' stb' leg agab agbb (Hga.q _) (Hgb.q _) (wg.q _)
                  hripa' hripb'
                  (Ma'.fewer (arriveJoin_q harr).1 (arriveJoin_q harr).2)
                  (Mb'.fewer (arriveJoin_q harr).1 (arriveJoin_q harr).2) A'
                  ⟨(fun h => by cases h), (fun h => by cases h)⟩
        | false =>
          simp only [hj, Bool.false_eq_true, ↓reduceIte] at hbody
          cases hs : seen.find? (fun e => e.place.pc == pc') with
          | some e =>
            simp only [hs] at hbody
            have em : e ∈ seen := List.mem_of_find?_eq_some hs
            have eq : e.place.pc = pc' := by simpa using List.find?_some hs
            obtain ⟨_, _, harr, _⟩ := V.bind_ok hbody
            obtain ⟨hn, hf, hd, run⟩ := T' e em
            obtain ⟨Aa, k, vala, lta⟩ := arrive_sound Ea e.place hn harr ca'.holds ca'.wf hd
            obtain ⟨Ab, _, _, _⟩ := arrive_sound Eb e.place hn harr cb'.holds cb'.wf hd
            exact run ρa' ρb' sta' stb' Aa Ab (by rw [eq]; exact hripa') (by rw [eq]; exact hripb')
              (Ma'.fewer (arrive_q harr).1 (arrive_q harr).2) (Mb'.fewer (arrive_q harr).1 (arrive_q harr).2) A' ⟨k, vala, lta⟩
          | none =>
            simp only [hs] at hbody
            obtain ⟨⟨g, d, first⟩, r2, e2, h2⟩ := V.bind_ok hbody
            obtain ⟨_, _, hgo, _⟩ := V.bind_ok h2
            obtain ⟨hn, ρa1, aga1, lea1, Aa1, wg, leg, hd, Ga⟩ := generalize_sound Ea pl e2 ca'.holds ca'.wf
            obtain ⟨_, ρb1, agb1, _, Ab1, _, _, _, Gb⟩ := generalize_sound Eb pl e2 cb'.holds cb'.wf
            have T1 : ReliedTrace world ctx p a0 b0 seen first.nvars ρa1 ρb1 := T'.carried lea1 aga1 agb1
            have all : ∀ (n : Nat) (ρax ρbx : Nat → Int) (stax stbx : State),
                AtPlace ctx pl a0 first ρa1 ρax stax → AtPlace ctx pl b0 first ρb1 ρbx stbx →
                stax.rip = p.base + pl.pc → stbx.rip = p.base + pl.pc →
                MarksOk ctx a0 { regq := placeQuiet ctx pl s'.q.regq, fq := s'.q.fq } stax →
                MarksOk ctx b0 { regq := placeQuiet ctx pl s'.q.regq, fq := s'.q.fq } stbx →
                Alike stax stbx →
                Value ctx.defs (placeVals ctx pl a0 stax) pl.decreases (.int (n : Int)) →
                ∀ a' b', EndsP world p stax.plain a' → EndsP world p stbx.plain b' →
                  a'.trace = b'.trace ∧ (ctx.contract.resultFollowsTrace = true → a'.reg 0 = b'.reg 0) := by
              intro n
              induction n using Nat.strongRecOn with
              | ind n ih =>
                intro ρax ρbx stax stbx Aax Abx hripax hripbx Max Mbx Ax vala
                obtain ⟨ρa'', Hga, agax, posa, vala'⟩ := Ga ρax stax Aax
                obtain ⟨ρb'', Hgb, agbx, _, _⟩ := Gb ρbx stbx Abx
                have same := Value.unique vala vala'; injection same with same
                have aa1 : Agree first.nvars ρa1 ρa'' := Agree.trans (Nat.le_refl _) Aax.outer agax
                have ab1 : Agree first.nvars ρb1 ρb'' := Agree.trans (Nat.le_refl _) Abx.outer agbx
                have Tinner : ReliedTrace world ctx p a0 b0 (⟨pl, d, { first with q := { regq := placeQuiet ctx pl s'.q.regq, fq := s'.q.fq } }⟩ :: seen) g.nvars ρa'' ρb'' := by
                  intro e me
                  cases me with
                  | head =>
                    refine ⟨hn, leg, hd, ?_⟩
                    intro ρay ρby stay stby Aay Aby hripay hripby May Mby Ay ⟨k, valay, ltay⟩
                    have Aay1 : AtPlace ctx pl a0 first ρa1 ρay stay :=
                      ⟨Agree.trans (Nat.le_refl _) aa1 Aay.outer, Aay.entry, Aay.data, Aay.kept, Aay.small, Aay.frame, Aay.mem, Aay.facts, Aay.lanes, Aay.cells, Aay.wrote, Aay.vecIntact⟩
                    have Aby1 : AtPlace ctx pl b0 first ρb1 ρby stby :=
                      ⟨Agree.trans (Nat.le_refl _) ab1 Aby.outer, Aby.entry, Aby.data, Aby.kept, Aby.small, Aby.frame, Aby.mem, Aby.facts, Aby.lanes, Aby.cells, Aby.wrote, Aby.vecIntact⟩
                    obtain ⟨ρaz, _, _, posz, valz⟩ := Ga ρay stay Aay1
                    have samez := Value.unique valay valz; injection samez with samez
                    have ltay : k + 1 ≤ ev ρa'' d := ltay
                    have small : k.toNat < n := by omega
                    exact ih k.toNat small ρay ρby stay stby Aay1 Aby1 hripay hripby May Mby Ay
                      (by rw [Int.toNat_of_nonneg (by omega)]; exact valay)
                  | tail _ me => exact (T1.carried leg aa1 ab1) e me
                exact (explore_trace Ea Eb W hdok hno Ka Kb ta fuel hgo (Hga.q _) (Hgb.q _) (wg.q _) Tinner (fun _ m => nomatch m)).2
                  ρa'' ρb'' stax stbx (Nat.le_refl _) (Agree.refl _ _) (Agree.refl _ _) (Hga.q _) (Hgb.q _) (wg.q _)
                  (by rw [← epc]; exact hripax) (by rw [← epc]; exact hripbx) Max Mbx Ax
                  ⟨(fun h => by cases h), (fun h => by cases h)⟩
            obtain ⟨ρa'', _, _, posa, vala⟩ := Ga ρa1 sta' Aa1
            exact all (ev ρa'' d).toNat ρa1 ρb1 sta' stb' Aa1 Ab1
              (by rw [epc]; exact hripa') (by rw [epc]; exact hripb')
              (Ma'.fewer (placeQuiet_all ctx pl s'.q.regq) (List.all_eq_true.mpr fun _ hm => List.contains_iff_mem.mpr hm))
              (Mb'.fewer (placeQuiet_all ctx pl s'.q.regq) (List.all_eq_true.mpr fun _ hm => List.contains_iff_mem.mpr hm))
              A' (by rw [Int.toNat_of_nonneg posa]; exact vala)

theorem verifyOne_trace_sound_at (world : List Program) (ctx : Ctx) (p : Program) (proof : List Item) (hcode : p.code = ctx.code)
    (hno : hasSelect ctx.code = false) (h : verdictOne ctx proof = none) (a0 b0 : State) (W : CalleesTrace world ctx a0)
    (la : Loaded ctx.pieces a0) (ka : ctx.contract.clear world ctx.pieces a0) (pa : ctx.contract.pre p a0)
    (lb : Loaded ctx.pieces b0) (kb : ctx.contract.clear world ctx.pieces b0) (pb : ctx.contract.pre p b0)
    (ta : ctx.contract.traceAgree ctx.defs a0 b0)
    (a' b' : State) (Epa : EndsP world p a0.plain a') (Epb : EndsP world p b0.plain b') :
    a'.trace = b'.trace ∧ (ctx.contract.resultFollowsTrace = true → a'.reg 0 = b'.reg 0) := by
  let mk := initMarks ctx.contract ctx.pieces a0
  let a0m : State := { a0 with marks := mk }
  let b0m : State := { b0 with marks := mk }
  have A0 : Alike a0m b0m := initMarks_alike la lb ta
  obtain ⟨qa, qb⟩ := initMarks_quiet (pieces := ctx.pieces) ta
  have dqa : ∀ k pc, ctx.pieces[k]? = some pc → ∀ j, j < pc.bytes.length → a0m.marks.mem (a0m.data k + j) = false :=
    initMarks_dataQuiet (c := ctx.contract) (pieces := ctx.pieces) (a0 := a0)
  have dqb : ∀ k pc, ctx.pieces[k]? = some pc → ∀ j, j < pc.bytes.length → b0m.marks.mem (b0m.data k + j) = false := by
    intro k pc hk j hj; show mk.mem (b0.data k + j) = false; rw [← ta.2.1]; exact dqa k pc hk j hj
  have Ea : Setting ctx p a0m := ⟨hcode, pa, qa, la, dqa, fun a ha => ⟨(ka a (Or.inl ha)).1, (ka a (Or.inl ha)).2.1⟩⟩
  have Eb : Setting ctx p b0m := ⟨hcode, pb, qb, lb, dqb, fun a ha => ⟨(kb a (Or.inl ha)).1, (kb a (Or.inl ha)).2.1⟩⟩
  have tam : ctx.contract.traceAgree ctx.defs a0m b0m := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ta
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun e he v => ?_⟩
    show Value ctx.defs (ctx.contract.env a0m) e v ↔ Value ctx.defs (ctx.contract.env b0m) e v
    rw [show ctx.contract.env a0m = ctx.contract.env a0 from envIn_with_marks _ _ _ _ _,
        show ctx.contract.env b0m = ctx.contract.env b0 from envIn_with_marks _ _ _ _ _]
    exact h9 e he v
  obtain ⟨_, hdok, _, r, hv⟩ := verdictOne_ok h
  unfold verify at hv
  obtain ⟨_, r1, e1, _⟩ := V.bind_ok hv
  obtain ⟨ρa0, Ha, wf⟩ := entry_holds Ea
  obtain ⟨ρb0, Hb, _⟩ := entry_holds Eb
  have Mrega : ∀ r ∈ ctx.contract.cleanAtEntry ++ ctx.contract.link.toList, a0m.marks.reg r = false := by
    intro r hr
    rcases List.mem_append.mp hr with h1 | h2
    · exact qa.1 r h1
    · have hb := qa.2.1; unfold Contract.backQuiet at hb; unfold Contract.link at h2
      cases ha : ctx.contract.arm64 with
      | false => simp [ha] at h2
      | true =>
        simp only [ha, ↓reduceIte] at hb h2
        have e : r = LINK := by simpa using h2
        rw [e]; exact hb
  have Mregb : ∀ r ∈ ctx.contract.cleanAtEntry ++ ctx.contract.link.toList, b0m.marks.reg r = false := by
    intro r hr; exact Mrega r hr
  have Wm : CalleesTrace world ctx a0m := W
  exact (explore_trace Ea Eb Wm hdok hno ka kb tam PATH e1 Ha Hb wf (fun e m => nomatch m) (fun e m => nomatch m)).2
    ρa0 ρb0 a0m b0m (Nat.le_refl _) (Agree.refl _ _) (Agree.refl _ _) Ha Hb wf (by rw [Ea.rip]; rfl) (by rw [Eb.rip]; rfl)
    (by rw [entrySym_q]; exact ⟨Mrega, (fun x => by cases x), (fun x => by cases x), (fun _ _ _ => rfl), CellsOk.nil, (fun _ m => nomatch m)⟩)
    (by rw [entrySym_q]; exact ⟨Mregb, (fun x => by cases x), (fun x => by cases x), (fun _ _ _ => rfl), CellsOk.nil, (fun _ m => nomatch m)⟩)
    A0 (by constructor
           · rw [entrySym_q, (entrySym_flags ctx).1]; intro x; cases x
           · rw [entrySym_q, (entrySym_flags ctx).2]; intro x; cases x) a' b' Epa Epb

/-! ## Single-run mark-tracked soundness (`Runs`) for constant-time conditional select (`cmov`/`csel`) -/

theorem retReg_of_resultFollowsTrace {c : Contract} (h : c.resultFollowsTrace = true) : c.retReg = 0 := by
  unfold Contract.resultFollowsTrace at h
  have hr : c.result.isSome = true := (Bool.and_eq_true _ _ |>.mp h).1
  unfold Contract.retReg
  cases c.customRet with
  | none => rfl
  | some r => simp [hr]

theorem runs_mono {world : List Program} {perm : Perm} {p : Program} {Q Q' : State → Prop}
    (h : ∀ t, Q t → Q' t) : ∀ {s}, Runs world perm p Q s → Runs world perm p Q' s := by
  intro s hr
  induction hr with
  | step perm p Q s i hf hn _ hr ih => exact .step perm p Q' s i hf hn (fun u s' hx => ih u s' hx h) (fun u s' hx => h s' (hr u s' hx))
  | call perm p Q s i nm q inn R hf hc hw hsp hrd hwr hcall hkeep _ ih1 ih2 =>
    exact .call perm p Q' s i nm q inn R hf hc hw hsp hrd hwr hcall hkeep (fun s' hr => ih2 s' hr h)
  | tail perm p Q s i nm q inn hf ht hw hrd hwr _ ih =>
    exact .tail perm p Q' s i nm q inn hf ht hw hrd hwr (ih h)

/-- Postcondition proved under single-run `Runs`: contract postcondition plus mark preservation on `RSP`,
`retReg` (when `resultFollowsTrace`), and memory outside the function's frame and outputs. -/
def runsPost (c : Contract) (defs : List Def) (s0 t : State) : Prop :=
  c.post defs s0 t ∧
  t.marks.reg RSP = false ∧
  (c.resultFollowsTrace = true → t.marks.reg c.retReg = false) ∧
  ∀ a, c.inFrame s0 a = false → c.inOut s0 a = false → t.marks.mem a = s0.marks.mem a

def RunsOk (world : List Program) (pieces : List Piece) (c : Contract) (defs : List Def) (p : Program) : Prop :=
  ∀ s0, Loaded pieces s0 → c.clear world pieces s0 → c.pre p s0 → c.quietAt s0 →
    (∀ k pc, pieces[k]? = some pc → ∀ j, j < pc.bytes.length → s0.marks.mem (s0.data k + j) = false) →
    Runs world (c.perm pieces s0) p (runsPost c defs s0) s0

def RunsOkBelow (world : List Program) (pieces : List Piece) (c : Contract) (defs : List Def) (p : Program)
    (bound : Option (Nat × Nat)) : Prop :=
  ∀ s0, (∀ r m, bound = some (r, m) → s0.reg r < m) →
    Loaded pieces s0 → c.clear world pieces s0 → c.pre p s0 → c.quietAt s0 →
    (∀ k pc, pieces[k]? = some pc → ∀ j, j < pc.bytes.length → s0.marks.mem (s0.data k + j) = false) →
    Runs world (c.perm pieces s0) p (runsPost c defs s0) s0

theorem RunsOk.below {world : List Program} {pieces : List Piece} {c : Contract} {defs : List Def} {p : Program}
    (R : RunsOk world pieces c defs p) (bound : Option (Nat × Nat)) : RunsOkBelow world pieces c defs p bound :=
  fun s0 _ hl hc hp hq hd => R s0 hl hc hp hq hd

def CalleesRunsAt (world : List Program) (ctx : Ctx) (s0 : State) : Prop :=
  ∀ name c, ctx.callees.lookup name = some c →
    (ctx.runsCallees.contains name = true ∨ ctx.selfName = some name) →
    ∃ q, findProgram world name = some q ∧ q.fits ∧ RunsOkBelow world ctx.pieces c ctx.defs q (ctx.recBound name c s0)

theorem tailQuiet_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0)
    {ρ : Nat → Int} {s : Sym} {st : State} {name : String} {c : Contract}
    (T : TailOk ctx s name c) (M : MarksOk ctx s0 s.q st) (H : Holds ctx s0 ρ s st)
    (hq : callQuiet ctx s c = true) (q : Program) :
    c.quietAt (afterTail q st) := by
  simp only [callQuiet, Bool.and_eq_true] at hq
  obtain ⟨⟨⟨⟨hregs, hfix⟩, _⟩, hrun⟩, _⟩ := hq
  have regs : ∀ r ∈ c.cleanAtEntry, st.marks.reg r = false := fun r hr =>
    M.reg r (List.contains_iff_mem.mp (List.all_eq_true.mp hregs r hr))
  refine ⟨fun r hr => regs r hr, ?_, fun r l hm hnh k hk => ?_, fun x r n hm hnot => ?_⟩
  · unfold Contract.backQuiet
    cases ha : c.arm64 with
    | false =>
      simp only [ha, Bool.false_eq_true, ↓reduceIte]
      intro k hk
      have hsp : (afterTail q st).reg RSP = s0.reg RSP := by
        show st.reg RSP = s0.reg RSP; exact T.rsp_eq H
      rw [hsp]
      have hca : ctx.contract.arm64 = false := T.machine.symm.trans ha
      have hbq := E.quiet.2.1; unfold Contract.backQuiet at hbq; simp only [hca, Bool.false_eq_true, ↓reduceIte] at hbq
      have hnf : ctx.contract.inFrame s0 (s0.reg RSP + k) = false := notFrame (Or.inr (by omega))
      have hno : ctx.contract.inOut s0 (s0.reg RSP + k) = false := E.frame_notOut (by omega) (by rw [Contract.slot, if_neg (by rw [hca]; decide)]; omega)
      exact (M.stable _ hnf hno).trans (hbq k hk)
    | true =>
      simp only [ha, ↓reduceIte]
      have hca : ctx.contract.arm64 = true := T.machine.symm.trans ha
      exact M.reg LINK (T.linkOk hca).2
  · have hfound := List.all_eq_true.mp hrun (r, l) hm
    simp only [hnh, Bool.false_or, Bool.and_eq_true] at hfound
    have hfound := hfound.2
    cases hf : findRun s r l ctx.contract.regions 0 with
    | none => simp [hf] at hfound
    | some j =>
      obtain ⟨b0, l0, _, hget, er, el⟩ := findRun_spec hf
      have hnh0 : ctx.contract.hiddenAt b0 = false := by
        rw [hf] at hfound; simp only at hfound
        have hget' : ctx.contract.regions[j]? = some (b0, l0) := by simpa using hget
        rw [hget'] at hfound; simpa using hfound
      have hmem : (b0, l0) ∈ ctx.contract.regions := List.mem_of_getElem? hget
      obtain ⟨hb0, hl0⟩ := regions_lt hmem
      obtain ⟨ra, la⟩ := regions_args hm
      have hregs_eq : ctx.nreg = c.regs := by unfold Ctx.nreg Contract.regs; rw [T.machine]
      have hrlt : r < ctx.nreg := by rw [hregs_eq]; exact argRegs_lt ra
      have hllt : l < ctx.nreg := by rw [hregs_eq]; exact argRegs_lt la
      have vr : st.reg r = s0.reg b0 := by have := H.reg r hrlt; rw [er, ev_var, H.entry b0 hb0] at this; omega
      have vl : st.reg l = s0.reg l0 := by have := H.reg l hllt; rw [el, ev_var, H.entry l0 hl0] at this; omega
      change st.marks.mem (st.reg r + k) = false
      change k < st.reg l at hk
      rw [vr]; rw [vl] at hk
      obtain ⟨_, r2⟩ := E.regionAt hmem
      rw [M.stable _ (notFrame (by omega)) (E.region_notOut hmem (by omega) (by omega))]
      exact E.quiet.2.2.1 b0 l0 hmem hnh0 k hk
  · have hx := List.all_eq_true.mp hfix (x, r, n) hm
    rcases Bool.or_eq_true_iff.mp hx with hh | hframe
    · exact absurd (List.contains_iff_mem.mp hh) hnot
    · have hnone : frameAt s r = none := T.noFrameFix (x, r, n) hm
      rw [hnone] at hframe; simp at hframe

theorem step_runsQ {world : List Program} {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0)
    (W : CalleesRunsAt world ctx s0) (Kc : ctx.contract.clear world ctx.pieces s0)
    (hcap : hasSelect ctx.code = true ∨ hasCallOrTail ctx.code = false)
    {s : Sym} {pc : Nat} {i : Instr} {nexts : List (Sym × Next)} {items rest : Items} {ρ : Nat → Int} {st : State}
    (hl : ctx.code.lookup pc = some i) (h : symNext ctx s i items = .ok (nexts, rest))
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hrip : st.rip = p.base + pc) (M : MarksOk ctx s0 s.q st)
    (K : ∀ s' pc' ρ' st', (s', Next.at pc') ∈ nexts → st'.rip = p.base + pc' → Carried ctx s0 ρ s ρ' s' st' →
      MarksOk ctx s0 s'.q st' → Runs world (ctx.contract.perm ctx.pieces s0) p (runsPost ctx.contract ctx.defs s0) st') :
    Runs world (ctx.contract.perm ctx.pieces s0) p (runsPost ctx.contract ctx.defs s0) st := by
  have hfetch : p.fetch st.rip = some i := by
    unfold Program.fetch; rw [hrip, if_neg (by omega), E.code, Nat.add_sub_cancel_left]; exact hl
  cases hc : callTarget i with
  | none =>
    cases ht : tailTarget i with
    | none =>
      simp only [symNext, hc, ht] at h
      apply Runs.step _ p _ st i hfetch
      · intro u hn; obtain ⟨o, ho, _⟩ := symInstr_sound E h H wf M u; rw [ho] at hn; cases hn
      · intro u st' hx
        obtain ⟨o, ho, hmatch⟩ := symInstr_sound E h H wf M u
        rw [hx] at ho; injection ho with ho; subst ho
        obtain ⟨s', pc', ρ', m, hrip', c', M'⟩ := hmatch
        exact K s' pc' ρ' st' m hrip' c' M'
      · intro u st' hx
        obtain ⟨o, ho, hmatch⟩ := symInstr_sound E h H wf M u
        rw [hx] at ho; injection ho with ho; subst ho
        refine ⟨hmatch.1, hmatch.2.1, fun hrf => ?_, hmatch.2.2.2⟩
        rw [retReg_of_resultFollowsTrace hrf]; exact hmatch.2.2.1 hrf
    | some name =>
      have hsel : hasSelect ctx.code = true := by
        rcases hcap with h1 | hno
        · exact h1
        · have hany : hasCallOrTail ctx.code = true := by
            unfold hasCallOrTail; exact List.any_eq_true.mpr ⟨(pc, i), lookup_mem hl, by simp [ht]⟩
          rw [hno] at hany; cases hany
      simp only [symNext, hc, ht] at h
      cases hl2 : ctx.callees.lookup name with
      | none => simp only [hl2] at h; exact (refuse_ok h).elim
      | some c =>
        simp only [hl2] at h
        obtain ⟨_, _, htail, _⟩ := V.bind_ok h
        unfold symTail at htail
        split at htail
        next => exact (refuse_ok htail).elim
        next htf =>
        have T : TailOk ctx s name c := tailFits_spec (by simpa using htf)
        obtain ⟨_, _, _, htail⟩ := V.bind_ok htail
        obtain ⟨s1, _, e0, htail⟩ := V.bind_ok htail
        obtain ⟨_, _, e1, htail⟩ := V.bind_ok htail
        obtain ⟨s', _, e2, htail⟩ := V.bind_ok htail
        split at htail
        next => exact (refuse_ok htail).elim
        next hcq =>
        have hcq : callQuiet ctx (quietAtCall s1 c) c = true := by simpa using hcq
        simp only [hsel, Bool.true_and, ↓reduceIte] at htail
        split at htail
        next => exact (refuse_ok htail).elim
        next hrun_in =>
        have hrun_in : ctx.runsCallees.contains name = true ∨ ctx.selfName = some name := by
          cases hc1 : ctx.runsCallees.contains name with
          | true => exact Or.inl rfl
          | false =>
            cases hc2 : (ctx.selfName == some name) with
            | true => exact Or.inr (beq_iff_eq.mp hc2)
            | false =>
              simp only [hc1, hc2, Bool.or_self, Bool.not_false, Bool.true_and, not_true_eq_false] at hrun_in
        split at htail
        next => exact (refuse_ok htail).elim
        next hclean_tail =>
        split at htail
        next => exact (refuse_ok htail).elim
        next _ =>
        have c1 := symKnow_sound KNOWN e0 H wf
        have T1 := symKnow_tailOk T KNOWN e0
        have hqeq : s1.q = s.q := (symKnow_sp KNOWN e0).2.1
        have M1 : MarksOk ctx s0 s1.q st := hqeq ▸ M
        have EX := tailPreOk_sound E T1 c1.holds e1
        obtain ⟨q, hq, fitq, hruns⟩ := W name c hl2 hrun_in
        obtain ⟨hpre, hread, hwrite, hpost⟩ := tailCall'_sound E T1 EX e2 c1.holds c1.wf q fitq
        have hbd : ∀ r m, ctx.recBound name c s0 = some (r, m) → (afterTail q st).reg r < m := by
          intro r m hb; unfold Ctx.recBound at hb
          have hne : (ctx.selfName == some name) = false := beq_false_of_ne T.notSelf
          simp only [hne, Bool.false_eq_true, ite_false] at hb; cases hb
        have T1q : TailOk ctx (quietAtCall s1 c) name c :=
          ⟨T1.notSelf, T1.machine, T1.sp0, T1.rspClean, T1.linkOk, T1.keeps, T1.keepsVec,
           T1.noLanes, T1.noValArrays, T1.noFrameOut, T1.noFrameFix⟩
        have hq_tail : c.quietAt (afterTail q st) :=
          tailQuiet_sound E T1q (quietAtCall_marks M1 c) (quietAtCall_holds c1.holds c) hcq q
        have hdata_q : ∀ k pc', ctx.pieces[k]? = some pc' → ∀ j, j < pc'.bytes.length →
            (afterTail q st).marks.mem ((afterTail q st).data k + j) = false := by
          intro k pc' hk j hj
          change st.marks.mem (st.data k + j) = false
          rw [c1.holds.data.2]
          have hnf : ctx.contract.inFrame s0 (s0.data k + j) = false :=
            (Kc _ (Or.inl (inPieces_iff.mpr ⟨k, pc', hk, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩))).1
          have hno : ctx.contract.inOut s0 (s0.data k + j) = false :=
            (Kc _ (Or.inl (inPieces_iff.mpr ⟨k, pc', hk, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩))).2.1
          rw [M.stable _ hnf hno]; exact E.dataQuiet k pc' hk j hj
        have hrun := runs_data (hruns (afterTail q st) hbd (loaded_tail E c1.holds q) (clear_tail Kc T1 c1.holds q hwrite) hpre hq_tail hdata_q)
        rw [afterTail_data] at hrun
        apply Runs.tail _ p _ st i name q (c.perm ctx.pieces (afterTail q st)) hfetch ht hq hread hwrite
        refine runs_mono (fun s2 ⟨⟨hpost2, hsp2, hret2, hmem2⟩, hdata2⟩ => ?_) hrun
        obtain ⟨ρ', c'⟩ := hpost s2 hpost2 hdata2
        let cleanRet := c.resultFollowsTrace && callReturnsClean ctx (quietAtCall s1 c) c
        have c'q : Carried ctx s0 ρ s1 ρ' { s' with q := afterCallQ cleanRet c (quietAtCall s1 c) }
            (setReg s2 RSP (s0.reg RSP)) := c'.q _
        obtain ⟨_, hret⟩ := symReturn_sound E htail c'q.holds c'q.wf
        have hpost0 : ctx.contract.post ctx.defs s0 s2 := by
          apply hret s2 rfl rfl (fun r hr => by simp [setReg, hr])
          · have hs2rsp := hpost2.2.1; simp only [afterTail] at hs2rsp
            rw [hs2rsp, T1.rsp_eq c1.holds, T1.slot]; simp only [setReg, ite_true, Nat.mod_eq_of_lt (E.small RSP)]
          · rw [hpost2.1, T1.backTo_eq E c1.holds q]
        refine ⟨hpost0, hsp2, fun hrf => ?_, fun a hnf hno => ?_⟩
        · have hcr : cleanRet = true := by
            cases hc0 : cleanRet with
            | true => rfl
            | false => exact absurd (by simp [hrf, cleanRet, hc0]) hclean_tail
          have hcrf : c.resultFollowsTrace = true := (Bool.and_eq_true _ _ |>.mp hcr).1
          rw [retReg_of_resultFollowsTrace hrf, ← retReg_of_resultFollowsTrace hcrf]
          exact hret2 hcrf
        · have hc_nf : c.inFrame (afterTail q st) a = false := by
            cases hx : c.inFrame (afterTail q st) a with
            | false => rfl
            | true =>
              have hw1 : (c.perm ctx.pieces (afterTail q st)).write a = true := by simp [Contract.perm, hx]
              have hw0 := hwrite a hw1; simp [Contract.perm, hnf, hno] at hw0
          have hc_no : c.inOut (afterTail q st) a = false := by
            cases hx : c.inOut (afterTail q st) a with
            | false => rfl
            | true =>
              have hw1 : (c.perm ctx.pieces (afterTail q st)).write a = true := by simp [Contract.perm, hx]
              have hw0 := hwrite a hw1; simp [Contract.perm, hnf, hno] at hw0
          exact (hmem2 a hc_nf hc_no).trans (M.stable a hnf hno)
  | some name =>
    have hsel : hasSelect ctx.code = true := by
      rcases hcap with h1 | hno
      · exact h1
      · have hany : hasCallOrTail ctx.code = true := by
          unfold hasCallOrTail; exact List.any_eq_true.mpr ⟨(pc, i), lookup_mem hl, by simp [hc]⟩
        rw [hno] at hany; cases hany
    simp only [symNext, hc] at h
    cases hl2 : ctx.callees.lookup name with
    | none => simp only [hl2] at h; exact (refuse_ok h).elim
    | some c =>
      simp only [hl2] at h
      split at h
      next => exact (refuse_ok h).elim
      next hfit =>
      have hfit : callFits ctx s i c = true := by simpa using hfit
      have F := callFits_sound E H hfit
      simp only [hsel, Bool.true_and, ↓reduceIte] at h
      split at h
      next => exact (refuse_ok h).elim
      next hguard =>
      have hrun_in : ctx.runsCallees.contains name = true ∨ ctx.selfName = some name := by
        have : ¬ (!(ctx.runsCallees.contains name || ctx.selfName == some name) || !(c.keeps == keptAt i)) = true := hguard
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at this
        simpa using this.1
      have hkept_eq : c.keeps = keptAt i := by
        have : ¬ (!(ctx.runsCallees.contains name || ctx.selfName == some name) || !(c.keeps == keptAt i)) = true := hguard
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at this
        simpa using this.2
      obtain ⟨_, _, _, h⟩ := V.bind_ok h
      obtain ⟨s', r1, e1, h⟩ := V.bind_ok h
      split at h
      next => exact (refuse_ok h).elim
      next hcq =>
      have hcq : callQuiet ctx (quietAtCall s c) c = true := by simpa using hcq
      have hp := V.pure_ok h; injection hp with hn _; subst hn
      obtain ⟨q, hq, fitq, hruns⟩ := W name c hl2 hrun_in
      have hcode : (pc, i) ∈ p.code := by rw [E.code]; exact lookup_mem hl
      obtain ⟨h8, hw, hpre, hdec, hread, hwrite, hpost⟩ := symCall_sound E e1 H wf q fitq i F (E.fits hcode)
      obtain ⟨hrsp_m, hq_call, hafter⟩ := callQuiet_sound E (quietAtCall_marks M c) (quietAtCall_holds H c) hcq q i F hw hwrite
      have hbd : ∀ r m, ctx.recBound name c s0 = some (r, m) → (afterCall p q i st).reg r < m := by
        intro r m hb; unfold Ctx.recBound at hb
        split at hb
        next hself =>
          have hself' : ctx.selfName = some name := by simpa using hself
          cases hd : c.decreases with
          | none => simp [hd] at hb
          | some d =>
            simp only [hd, Option.bind_some] at hb
            cases hr : c.regOf d with
            | none => simp [hr] at hb
            | some r' =>
              simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
              obtain ⟨rfl, rfl⟩ := hb; exact hdec hself' d r' hd hr
        next => cases hb
      have hdata_q : ∀ k pc', ctx.pieces[k]? = some pc' → ∀ j, j < pc'.bytes.length →
          (afterCall p q i st).marks.mem ((afterCall p q i st).data k + j) = false := by
        intro k pc' hk j hj
        rw [afterCall_data, afterCall_marks_mem F.link, H.data.2]
        unfold markBytes
        split
        · rfl
        · have hnf : ctx.contract.inFrame s0 (s0.data k + j) = false :=
            (Kc _ (Or.inl (inPieces_iff.mpr ⟨k, pc', hk, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩))).1
          have hno : ctx.contract.inOut s0 (s0.data k + j) = false :=
            (Kc _ (Or.inl (inPieces_iff.mpr ⟨k, pc', hk, Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩))).2.1
          rw [M.stable _ hnf hno]; exact E.dataQuiet k pc' hk j hj
      have hrun := runs_data (hruns (afterCall p q i st) hbd (loaded_call E H q i F.link h8 hw) (clear_call Kc H p q i F.link hw hwrite) hpre hq_call hdata_q)
      rw [afterCall_data] at hrun
      exact Runs.call _ p _ st i name q (c.perm ctx.pieces (afterCall p q i st))
        (fun s2 => runsPost c ctx.defs (afterCall p q i st) s2 ∧ s2.data = st.data)
        hfetch hc hq
        (fun hnone => by
          have hs := (Contract.link_none (F.link.symm.trans hnone)).2
          rw [hs] at h8 hw; exact ⟨h8, hw, hrsp_m⟩)
        hread hwrite hrun
        (fun s2 lf2 r hr => by
          rw [← hkept_eq] at hr
          have := lf2.1.1.2.2.1 r hr
          obtain ⟨_, ne, nl⟩ := keeps_spec hr
          rw [this, afterCall_reg F.link (callKeeps ne nl)])
        (fun s2 ⟨⟨hpost2, hsp2, hret2, hmem2⟩, hdata2⟩ => by
          let cleanRet := c.resultFollowsTrace && callReturnsClean ctx (quietAtCall s c) c
          obtain ⟨hrip2, ρ', c'⟩ := hpost s2 hpost2 hdata2
          rw [← hkept_eq]
          exact K _ i.next ρ' (backFrom c.keeps st s2) (List.mem_cons_self ..) hrip2
            ((c'.q _).fields rfl rfl rfl rfl rfl rfl)
            (hafter cleanRet s2 (fun hcr => callReturnsClean_givesNumber (Bool.and_eq_true _ _ |>.mp hcr).2)
              ⟨hsp2, fun hcr => hret2 (Bool.and_eq_true _ _ |>.mp hcr).1, hmem2⟩))

def ReliedQ (world : List Program) (ctx : Ctx) (p : Program) (s0 : State) (seen : List Seen) (n : Nat) (ρ : Nat → Int) : Prop :=
  ∀ e ∈ seen, (∀ nr ∈ e.place.names, nr.2 < ctx.nreg) ∧ e.first.nvars ≤ n ∧ bounded n e.d ∧
    ∀ ρ' st', AtPlace ctx e.place s0 e.first ρ ρ' st' → st'.rip = p.base + e.place.pc →
      MarksOk ctx s0 { regq := e.first.q.regq, fq := e.first.q.fq } st' →
      (∃ k : Int, Value ctx.defs (placeVals ctx e.place s0 st') e.place.decreases (.int k) ∧ k + 1 ≤ ev ρ e.d) →
      Runs world (ctx.contract.perm ctx.pieces s0) p (runsPost ctx.contract ctx.defs s0) st'

theorem ReliedQ.carried {world : List Program} {ctx : Ctx} {p : Program} {s0 : State} {seen : List Seen}
    {n m : Nat} {ρ ρ' : Nat → Int} (T : ReliedQ world ctx p s0 seen n ρ) (hle : n ≤ m) (hag : Agree n ρ ρ') :
    ReliedQ world ctx p s0 seen m ρ' := by
  intro e me
  obtain ⟨hn, hf, hd, run⟩ := T e me
  exact ⟨hn, Nat.le_trans hf hle, bounded_mono hle hd, fun ρx stx A hrip M ⟨k, val, lt⟩ =>
    run ρx stx ⟨Agree.trans (Nat.le_refl _) (Agree.mono hf hag) A.outer, A.entry, A.data, A.kept, A.small, A.frame, A.mem, A.facts, A.lanes, A.cells, A.wrote, A.vecIntact⟩
      hrip M ⟨k, val, by rwa [ev_agree hd hag]⟩⟩

def ReliedJoinQ (world : List Program) (ctx : Ctx) (p : Program) (s0 : State) (jdone : List JoinEntry) (n : Nat) (ρ : Nat → Int) : Prop :=
  ∀ e ∈ jdone, (∀ nr ∈ e.place.names, nr.2 < ctx.nreg) ∧ e.first.nvars = n ∧
    ∀ ρ' st', AtPlace ctx e.place s0 e.first ρ ρ' st' → st'.rip = p.base + e.place.pc →
      MarksOk ctx s0 { regq := e.first.q.regq, fq := e.first.q.fq } st' →
      Runs world (ctx.contract.perm ctx.pieces s0) p (runsPost ctx.contract ctx.defs s0) st'

theorem explore_runsQ {world : List Program} {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0)
    (W : CalleesRunsAt world ctx s0) (Kc : ctx.contract.clear world ctx.pieces s0)
    (he : ctx.contract.traceExprs.isEmpty = true) (hcap : hasSelect ctx.code = true ∨ hasCallOrTail ctx.code = false) :
    ∀ (fuel : Nat) {base : Sym} {seen : List Seen} {jstack : List Nat} {jdone jdone' : List JoinEntry}
      {s : Sym} {pc : Nat} {items rest : Items} {ρb : Nat → Int} {stb : State},
    explore ctx fuel base seen jstack jdone s pc items = .ok (jdone', rest) →
    Holds ctx s0 ρb base stb → WF ctx base →
    ReliedQ world ctx p s0 seen base.nvars ρb →
    ReliedJoinQ world ctx p s0 jdone base.nvars ρb →
    ReliedJoinQ world ctx p s0 jdone' base.nvars ρb ∧
    (∀ ρ st, base.nvars ≤ s.nvars → Agree base.nvars ρb ρ →
      Holds ctx s0 ρ s st → WF ctx s → st.rip = p.base + pc → MarksOk ctx s0 s.q st →
      Runs world (ctx.contract.perm ctx.pieces s0) p (runsPost ctx.contract ctx.defs s0) st)
  | 0, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _ => by simp only [explore] at h; exact (refuse_ok h).elim
  | fuel + 1, base, seen, jstack, jdone, jdone', s, pc, items, rest, ρb, stb, h, Hb, wfb, Tb, Jb => by
    cases hl : ctx.code.lookup pc with
    | none => simp only [explore, hl] at h; exact (refuse_ok h).elim
    | some i =>
      simp only [explore, hl] at h
      obtain ⟨sc, r0, hc, h⟩ := V.bind_ok h
      have hsc := symClears_empty he CLEARS hc; rw [hsc] at h
      obtain ⟨nexts, r1, e1, h⟩ := V.bind_ok h
      have honward_J : ∀ nx ∈ nexts, ∀ jd jd' it it',
          ReliedJoinQ world ctx p s0 jd base.nvars ρb →
          onward ctx base seen jstack (explore ctx fuel) jd nx it = .ok (jd', it') →
          ReliedJoinQ world ctx p s0 jd' base.nvars ρb := by
        intro nx _ jd jd' it it' Jcur hbody
        rcases nx with ⟨snx, nxt⟩
        cases nxt with
        | returned => simp only [onward] at hbody; have := V.pure_ok hbody; injection this with h1 _; subst h1; exact Jcur
        | «at» pc' =>
          simp only [onward] at hbody
          cases hp : ctx.places.find? (fun p => p.pc == pc') with
          | none => simp only [hp] at hbody; exact (explore_runsQ E W Kc he hcap fuel hbody Hb wfb Tb Jcur).1
          | some pl =>
            simp only [hp] at hbody
            have epc : pl.pc = pc' := by simpa using List.find?_some hp
            cases hj : pl.isJoin with
            | false =>
              simp only [hj, Bool.false_eq_true, ↓reduceIte] at hbody
              cases hs : seen.find? (fun e => e.place.pc == pc') with
              | some e => simp only [hs] at hbody; obtain ⟨_, _, _, hpur⟩ := V.bind_ok hbody; have := V.pure_ok hpur; injection this with h1 _; subst h1; exact Jcur
              | none => simp only [hs] at hbody; obtain ⟨⟨_, _, _⟩, _, _, h2⟩ := V.bind_ok hbody; obtain ⟨_, _, _, hpur⟩ := V.bind_ok h2; have := V.pure_ok hpur; injection this with h1 _; subst h1; exact Jcur
            | true =>
              simp only [hj, ↓reduceIte] at hbody
              split at hbody
              · exact (refuse_ok hbody).elim
              · cases hjd : jd.find? (fun e => e.place.pc == pc') with
                | some e => simp only [hjd] at hbody; obtain ⟨_, _, _, hpur⟩ := V.bind_ok hbody; have := V.pure_ok hpur; injection this with h1 _; subst h1; exact Jcur
                | none =>
                  simp only [hjd] at hbody
                  cases hfirst : joinFirst ctx base snx pl with
                  | none => simp only [hfirst] at hbody; exact (refuse_ok hbody).elim
                  | some first =>
                    simp only [hfirst] at hbody
                    obtain ⟨_, _, _, h2⟩ := V.bind_ok hbody
                    obtain ⟨g, _, eg, h3⟩ := V.bind_ok h2
                    obtain ⟨jmid, _, hgo, hpur⟩ := V.bind_ok h3
                    have := V.pure_ok hpur; injection this with h1 _; subst h1
                    obtain ⟨hnames, hnv, G⟩ := generalizeJoin_sound E pl hfirst eg Hb wfb
                    obtain ⟨Jmid, runG⟩ := explore_runsQ E W Kc he hcap fuel hgo Hb wfb Tb Jcur
                    intro je mje
                    cases mje with
                    | head =>
                      refine ⟨hnames, hnv, ?_⟩
                      intro ρx stx Ax hripx Mx
                      obtain ⟨ρ'', Hg, wg, leg, agx⟩ := G ρx stx Ax
                      have agb : Agree base.nvars ρb ρ'' := Agree.trans (Nat.le_refl _) (hnv ▸ Ax.outer) agx
                      exact runG ρ'' stx leg agb (Hg.q _) (wg.q _) (by rw [← epc]; exact hripx) Mx
                    | tail _ mt => exact Jmid je mt
      obtain ⟨Jout, hmem⟩ := eachState_prop (P := fun jd => ReliedJoinQ world ctx p s0 jd base.nvars ρb) h Jb honward_J
      refine ⟨Jout, ?_⟩
      intro ρ st hle hag H wf hrip M
      apply step_runsQ E W Kc hcap hl e1 H wf hrip M
      intro s' pc' ρ' st' m hrip' c' M'
      obtain ⟨jd, jd', items', r', Jcur, hbody⟩ := hmem (s', Next.at pc') m
      have hle' : base.nvars ≤ s'.nvars := Nat.le_trans hle c'.mono
      have hag' : Agree base.nvars ρb ρ' := Agree.trans hle hag c'.agree
      have T' : ReliedQ world ctx p s0 seen s'.nvars ρ' := Tb.carried hle' hag'
      simp only [onward] at hbody
      cases hp : ctx.places.find? (fun p => p.pc == pc') with
      | none =>
        simp only [hp] at hbody
        exact (explore_runsQ E W Kc he hcap fuel hbody Hb wfb Tb Jcur).2 ρ' st' hle' hag' c'.holds c'.wf hrip' M'
      | some pl =>
        simp only [hp] at hbody
        have epc : pl.pc = pc' := by simpa using List.find?_some hp
        cases hj : pl.isJoin with
        | true =>
          simp only [hj, ↓reduceIte] at hbody
          split at hbody
          · exact (refuse_ok hbody).elim
          · cases hjd : jd.find? (fun e => e.place.pc == pc') with
            | some e =>
              simp only [hjd] at hbody
              have em : e ∈ jd := List.mem_of_find?_eq_some hjd
              have eq : e.place.pc = pc' := by simpa using List.find?_some hjd
              obtain ⟨_, _, harr, _⟩ := V.bind_ok hbody
              obtain ⟨hn, hnv, run⟩ := Jcur e em
              have A := arriveJoin_sound E e.place hn harr c'.holds c'.wf (hnv.symm ▸ hag')
              exact run ρ' st' A (by rw [eq]; exact hrip') (M'.fewer (arriveJoin_q harr).1 (arriveJoin_q harr).2)
            | none =>
              simp only [hjd] at hbody
              cases hfirst : joinFirst ctx base s' pl with
              | none => simp only [hfirst] at hbody; exact (refuse_ok hbody).elim
              | some first =>
                simp only [hfirst] at hbody
                obtain ⟨_, _, harr, h2⟩ := V.bind_ok hbody
                obtain ⟨g, _, eg, h3⟩ := V.bind_ok h2
                obtain ⟨_, _, hgo, _⟩ := V.bind_ok h3
                obtain ⟨hnames, hnv, G⟩ := generalizeJoin_sound E pl hfirst eg Hb wfb
                have runG := (explore_runsQ E W Kc he hcap fuel hgo Hb wfb Tb Jcur).2
                have A := arriveJoin_sound E pl hnames harr c'.holds c'.wf (hnv.symm ▸ hag')
                obtain ⟨ρ'', Hg, wg, leg, agx⟩ := G ρ' st' A
                have agb : Agree base.nvars ρb ρ'' := Agree.trans (Nat.le_refl _) (hnv ▸ A.outer) agx
                exact runG ρ'' st' leg agb (Hg.q _) (wg.q _) hrip' (M'.fewer (arriveJoin_q harr).1 (arriveJoin_q harr).2)
        | false =>
          simp only [hj, Bool.false_eq_true, ↓reduceIte] at hbody
          cases hs : seen.find? (fun e => e.place.pc == pc') with
          | some e =>
            simp only [hs] at hbody
            have em : e ∈ seen := List.mem_of_find?_eq_some hs
            have eq : e.place.pc = pc' := by simpa using List.find?_some hs
            obtain ⟨_, _, harr, _⟩ := V.bind_ok hbody
            obtain ⟨hn, hf, hd, run⟩ := T' e em
            obtain ⟨A, k, val, lt⟩ := arrive_sound E e.place hn harr c'.holds c'.wf hd
            exact run ρ' st' A (by rw [eq]; exact hrip') (M'.fewer (arrive_q harr).1 (arrive_q harr).2) ⟨k, val, lt⟩
          | none =>
            simp only [hs] at hbody
            obtain ⟨⟨g, d, first⟩, r2, e2, h2⟩ := V.bind_ok hbody
            obtain ⟨_, _, hgo, _⟩ := V.bind_ok h2
            obtain ⟨hn, ρ1, ag1, le1, A1, wg, leg, hd, G⟩ := generalize_sound E pl e2 c'.holds c'.wf
            have T1 : ReliedQ world ctx p s0 seen first.nvars ρ1 := T'.carried le1 ag1
            have all : ∀ (n : Nat) (ρx : Nat → Int) (stx : State), AtPlace ctx pl s0 first ρ1 ρx stx → stx.rip = p.base + pl.pc →
                MarksOk ctx s0 { regq := placeQuiet ctx pl s'.q.regq, fq := s'.q.fq } stx →
                Value ctx.defs (placeVals ctx pl s0 stx) pl.decreases (.int (n : Int)) →
                Runs world (ctx.contract.perm ctx.pieces s0) p (runsPost ctx.contract ctx.defs s0) stx := by
              intro n
              induction n using Nat.strongRecOn with
              | ind n ih =>
                intro ρx stx A hripx Mx val
                obtain ⟨ρ'', Hg, agx, pos, val'⟩ := G ρx stx A
                have same := Value.unique val val'
                injection same with same
                have a1 : Agree first.nvars ρ1 ρ'' := Agree.trans (Nat.le_refl _) A.outer agx
                have Tinner : ReliedQ world ctx p s0 (⟨pl, d, { first with q := { regq := placeQuiet ctx pl s'.q.regq, fq := s'.q.fq } }⟩ :: seen) g.nvars ρ'' := by
                  intro e me
                  cases me with
                  | head =>
                    refine ⟨hn, leg, hd, ?_⟩
                    intro ρy sty Ay hripy My ⟨k, valy, lty⟩
                    have Ay1 : AtPlace ctx pl s0 first ρ1 ρy sty :=
                      ⟨Agree.trans (Nat.le_refl _) a1 Ay.outer, Ay.entry, Ay.data, Ay.kept, Ay.small, Ay.frame, Ay.mem, Ay.facts, Ay.lanes, Ay.cells, Ay.wrote, Ay.vecIntact⟩
                    obtain ⟨ρz, _, _, posz, valz⟩ := G ρy sty Ay1
                    have samez := Value.unique valy valz
                    injection samez with samez
                    have lty : k + 1 ≤ ev ρ'' d := lty
                    have small : k.toNat < n := by omega
                    exact ih k.toNat small ρy sty Ay1 hripy My (by rw [Int.toNat_of_nonneg (by omega)]; exact valy)
                  | tail _ me => exact (T1.carried leg a1) e me
                exact (explore_runsQ E W Kc he hcap fuel hgo (Hg.q _) (wg.q _) Tinner (fun _ m => nomatch m)).2
                  ρ'' stx (Nat.le_refl _) (Agree.refl _ _) (Hg.q _) (wg.q _) (by rw [← epc]; exact hripx) Mx
            obtain ⟨ρ'', _, _, pos, val⟩ := G ρ1 st' A1
            exact all (ev ρ'' d).toNat ρ1 st' A1 (by rw [epc]; exact hrip')
              (M'.fewer (placeQuiet_all ctx pl s'.q.regq) (List.all_eq_true.mpr fun _ hm => List.contains_iff_mem.mpr hm))
              (by rw [Int.toNat_of_nonneg pos]; exact val)

theorem verifyOne_runsQ_at (world : List Program) (ctx : Ctx) (p : Program) (proof : List Item) (hcode : p.code = ctx.code)
    (he : ctx.contract.traceExprs.isEmpty = true) (hcap : hasSelect ctx.code = true ∨ hasCallOrTail ctx.code = false)
    (h : verdictOne ctx proof = none) (s0 : State) (W : CalleesRunsAt world ctx s0)
    (loaded : Loaded ctx.pieces s0) (clear : ctx.contract.clear world ctx.pieces s0) (pre : ctx.contract.pre p s0)
    (quiet : ctx.contract.quietAt s0)
    (dq : ∀ k pc, ctx.pieces[k]? = some pc → ∀ j, j < pc.bytes.length → s0.marks.mem (s0.data k + j) = false) :
    Runs world (ctx.contract.perm ctx.pieces s0) p (runsPost ctx.contract ctx.defs s0) s0 := by
  have E : Setting ctx p s0 := ⟨hcode, pre, quiet, loaded, dq, fun a ha => ⟨(clear a (Or.inl ha)).1, (clear a (Or.inl ha)).2.1⟩⟩
  obtain ⟨_, _, _, r, hv⟩ := verdictOne_ok h
  unfold verify at hv
  obtain ⟨_, r1, e1, _⟩ := V.bind_ok hv
  obtain ⟨ρ0, H, wf⟩ := entry_holds E
  have Mreg : ∀ r ∈ ctx.contract.cleanAtEntry ++ ctx.contract.link.toList, s0.marks.reg r = false := by
    intro r hr
    rcases List.mem_append.mp hr with h1 | h2
    · exact quiet.1 r h1
    · have hb := quiet.2.1; unfold Contract.backQuiet at hb; unfold Contract.link at h2
      cases ha : ctx.contract.arm64 with
      | false => simp [ha] at h2
      | true =>
        simp only [ha, ↓reduceIte] at hb h2
        have e : r = LINK := by simpa using h2
        rw [e]; exact hb
  exact (explore_runsQ E W clear he hcap PATH e1 H wf (fun e m => nomatch m) (fun e m => nomatch m)).2
    ρ0 s0 (Nat.le_refl _) (Agree.refl _ _) H wf (by rw [E.rip]; rfl)
    (by rw [entrySym_q]; exact ⟨Mreg, (fun x => by cases x), (fun x => by cases x), (fun _ _ _ => rfl), CellsOk.nil, (fun _ m => nomatch m)⟩)

theorem verifyOne_runsQ_rec (world : List Program) (pieces : List Piece) (defs : List Def)
    (runsOk : List String) (done : List (String × Contract)) (f : Fn) (p : Program) (c : Contract) (rp : Bool)
    (hp : findProgram world f.name = some p) (hc : p.code = f.code) (hf : p.fits)
    (hceq : c.decreases = f.contract.decreases ∧ ∀ x, c.regOf x = f.contract.regOf x)
    (he : c.traceExprs.isEmpty = true) (hcap : hasSelect f.code = true ∨ hasCallOrTail f.code = false)
    (I : ∀ name c', done.lookup name = some c' → name ∈ runsOk →
      ∃ q, findProgram world name = some q ∧ q.fits ∧ RunsOk world pieces c' defs q)
    (hpass : verdictOne
      { code := f.code, contract := c, defs := defs, places := f.places,
        callees := if f.contract.decreases.isSome then (f.name, f.contract) :: done else done,
        selfName := if f.contract.decreases.isSome then some f.name else none,
        pieces := pieces, piece := f.piece, resultPass := rp, runsCallees := runsOk } f.proof = none)
    (hrself : f.contract.decreases.isSome = true → c = f.contract ∨ RunsOk world pieces f.contract defs p) :
    RunsOk world pieces c defs p := by
  let ctx : Ctx :=
    { code := f.code, contract := c, defs := defs, places := f.places,
      callees := if f.contract.decreases.isSome then (f.name, f.contract) :: done else done,
      selfName := if f.contract.decreases.isSome then some f.name else none,
      pieces := pieces, piece := f.piece, resultPass := rp, runsCallees := runsOk }
  cases hdec : f.contract.decreases with
  | none =>
    have W : ∀ s0, CalleesRunsAt world ctx s0 := fun s0 name c' hl hmem => by
      simp only [ctx, hdec, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hl hmem
      rcases hmem with hm | hs
      · obtain ⟨q, hq, fitq, Rq⟩ := I name c' hl (List.contains_iff_mem.mp hm)
        exact ⟨q, hq, fitq, Rq.below _⟩
      · cases hs
    exact fun s0 hl hcl hpre hq hdq => verifyOne_runsQ_at world ctx p f.proof hc he hcap hpass s0 (W s0) hl hcl hpre hq hdq
  | some d =>
    have hdok := (verdictOne_ok hpass).2.1
    simp only [ctx, Contract.decreasesOk, hceq.1, hdec] at hdok
    cases hr : f.contract.regOf d with
    | none => rw [hceq.2 d, hr] at hdok; simp at hdok
    | some rDec =>
      have all : ∀ n s0, s0.reg rDec = n →
          Loaded pieces s0 → c.clear world pieces s0 → c.pre p s0 → c.quietAt s0 →
          (∀ k pc, pieces[k]? = some pc → ∀ j, j < pc.bytes.length → s0.marks.mem (s0.data k + j) = false) →
          Runs world (c.perm pieces s0) p (runsPost c defs s0) s0 := by
        intro n
        refine Nat.strongRecOn n fun n ih => ?_
        intro s0 heq loaded clear pre quiet dq
        have W : CalleesRunsAt world ctx s0 := by
          intro name c' hl hmem
          simp only [ctx, hdec, Option.isSome_some, ↓reduceIte, List.lookup_cons] at hl
          cases hn : (name == f.name) with
          | true =>
            rw [hn] at hl; injection hl with hl
            have e : name = f.name := by simpa using hn
            subst hl e
            rcases hrself (by simp [hdec]) with hce | Rmain
            · refine ⟨p, hp, hf, fun sc hbd hl' hc' hp' hq' hdq' => ?_⟩
              have hlt : sc.reg rDec < s0.reg rDec := hbd rDec (s0.reg rDec) (by simp [Ctx.recBound, ctx, hdec, hr])
              rw [← hce]; exact ih (sc.reg rDec) (by omega) sc rfl hl' (hce ▸ hc') (hce ▸ hp') (hce ▸ hq') hdq'
            · exact ⟨p, hp, hf, Rmain.below _⟩
          | false =>
            rw [hn] at hl
            have hm : name ∈ runsOk := by
              rcases hmem with hm | hs
              · exact List.contains_iff_mem.mp hm
              · simp only [ctx, hdec, Option.isSome_some, ↓reduceIte, Option.some.injEq] at hs
                subst hs; simp at hn
            obtain ⟨q, hq, fitq, Rq⟩ := I name c' hl hm
            exact ⟨q, hq, fitq, Rq.below _⟩
        exact verifyOne_runsQ_at world ctx p f.proof hc he hcap hpass s0 W loaded clear pre quiet dq
      exact fun s0 hl hc' hp' hq' hdq' => all (s0.reg rDec) s0 rfl hl hc' hp' hq' hdq'

theorem runsOk_traceOk {world : List Program} {pieces : List Piece} {c : Contract} {defs : List Def} {p : Program}
    (R : RunsOk world pieces c defs p) : TraceOk world pieces c defs p := by
  intro a0 b0 la ka pa lb kb pb ta a' b' Epa Epb
  let mk := initMarks c pieces a0
  let a0m : State := { a0 with marks := mk }
  let b0m : State := { b0 with marks := mk }
  have A0 : Alike a0m b0m := initMarks_alike la lb ta
  obtain ⟨qa, qb⟩ := initMarks_quiet (pieces := pieces) ta
  have dqa : ∀ k pc, pieces[k]? = some pc → ∀ j, j < pc.bytes.length → a0m.marks.mem (a0m.data k + j) = false :=
    initMarks_dataQuiet (c := c) (pieces := pieces) (a0 := a0)
  have dqb : ∀ k pc, pieces[k]? = some pc → ∀ j, j < pc.bytes.length → b0m.marks.mem (b0m.data k + j) = false := by
    intro k pc hk j hj; show mk.mem (b0.data k + j) = false; rw [← ta.2.1]; exact dqa k pc hk j hj
  have Ra := R a0m la ka pa qa dqa
  have Rb := R b0m lb kb pb qb dqb
  obtain ⟨ra, Ea, Qa, ha⟩ := runs_endsP Ra Epa
  obtain ⟨rb, Eb, Qb, hb⟩ := runs_endsP Rb Epb
  have Alr := ends_alike Ea A0 Eb
  subst ha hb
  refine ⟨Alr.trace, fun hrf => ?_⟩
  have hmk0 : ra.marks.reg 0 = false := by
    have := Qa.2.2.1 hrf; rw [retReg_of_resultFollowsTrace hrf] at this; exact this
  exact Alr.reg 0 hmk0

theorem verdictFrom_trace_sound (world : List Program) (pieces : List Piece) (defs : List Def) :
    ∀ (fns : List Fn) (runsOk : List String) (done : List (String × Contract)),
    (∀ name ∈ runsOk, ∃ c, done.lookup name = some c) →
    (∀ name c, done.lookup name = some c →
      ∃ q, findProgram world name = some q ∧ q.fits ∧
        c.stackBitsOk = true ∧
        Meets world pieces c defs q ∧
        TraceOk world pieces c defs q ∧
        (∀ rh, c.resultHidden = some rh → c.result.isSome = true ∧ TraceOk world pieces (c.forResult rh) defs q) ∧
        (name ∈ runsOk → RunsOk world pieces c defs q)) →
    Linked world fns → verdictFrom.go pieces defs runsOk done fns = none →
    ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧
      Meets world pieces f.contract defs p ∧
      TraceOk world pieces f.contract defs p ∧
      (∀ rh, f.contract.resultHidden = some rh → f.contract.result.isSome = true ∧ TraceOk world pieces (f.contract.forResult rh) defs p)
  | [], _, _, _, _, _, _ => fun f m => nomatch m
  | f :: more, runsOk, done, hsub, I, L, h => by
    simp only [verdictFrom.go] at h
    split at h
    · cases h
    next hnodup =>
      let ctx : Ctx :=
        { code := f.code, contract := f.contract, defs := defs, places := f.places,
          callees := if f.contract.decreases.isSome then (f.name, f.contract) :: done else done,
          selfName := if f.contract.decreases.isSome then some f.name else none,
          pieces := pieces, piece := f.piece, runsCallees := runsOk }
      cases hv : verdict ctx f.proof with
      | some why => simp [ctx, hv] at h
      | none =>
        simp only [ctx, hv] at h
        obtain ⟨p, hp, hc, hf⟩ := L f (List.mem_cons_self ..)
        have hpass1 : verdictOne ctx f.proof = none := by
          unfold verdict at hv; cases hv1 : verdictOne ctx f.proof with
          | none => rfl
          | some _ => rw [hv1] at hv; cases hv
        have hsbok1 : f.contract.stackBitsOk = true := (verdictOne_ok hpass1).1
        have hdok1 : f.contract.decreasesOk = true := (verdictOne_ok hpass1).2.1
        have hsel_emp : hasSelect f.code = true → f.contract.traceExprs.isEmpty = true := (verdictOne_ok hpass1).2.2.1
        have IM : ∀ name c, done.lookup name = some c → ∃ q, findProgram world name = some q ∧ q.fits ∧ Meets world pieces c defs q :=
          fun name c hl => let ⟨q, hq, fitq, _, Mq, _, _, _⟩ := I name c hl; ⟨q, hq, fitq, Mq⟩
        have IR : ∀ name c, done.lookup name = some c → name ∈ runsOk →
            ∃ q, findProgram world name = some q ∧ q.fits ∧ RunsOk world pieces c defs q :=
          fun name c hl hm => let ⟨q, hq, fitq, _, _, _, _, Rq⟩ := I name c hl; ⟨q, hq, fitq, Rq hm⟩
        have M : Meets world pieces f.contract defs p := verifyOne_sound_rec world pieces defs runsOk done f p hp hc hf IM hpass1
        have hpass2 : ∀ rh, f.contract.resultHidden = some rh →
            f.contract.result.isSome = true ∧
            verdictOne { ctx with contract := f.contract.forResult rh, resultPass := true } f.proof = none := by
          intro rh hrh
          unfold verdict at hv
          rw [hpass1] at hv
          have hrh' : ctx.contract.resultHidden = some rh := hrh
          simp only [hrh'] at hv
          split at hv
          · cases hv
          · split at hv
            next => cases hv
            next hres =>
              have hres' : f.contract.result.isSome = true := by
                cases h0 : f.contract.result <;> simp [ctx, h0] at hres ⊢
              cases hv2 : verdictOne { ctx with contract := f.contract.forResult rh, resultPass := true } f.proof with
              | some _ =>
                have hv2' : verdictOne { ctx with contract := ctx.contract.forResult rh, resultPass := true } f.proof = some _ := hv2
                rw [hv2'] at hv; cases hv
              | none => exact ⟨hres', rfl⟩
        have hR : fnRunsCapable f = true → RunsOk world pieces f.contract defs p := by
          intro hcap_f
          unfold fnRunsCapable at hcap_f
          obtain ⟨he, hsc⟩ := Bool.and_eq_true _ _ |>.mp hcap_f
          have hcap' : hasSelect f.code = true ∨ hasCallOrTail f.code = false := by
            rcases Bool.or_eq_true _ _ |>.mp hsc with h1 | h2
            · exact Or.inl h1
            · exact Or.inr (by simpa using h2)
          exact verifyOne_runsQ_rec world pieces defs runsOk done f p f.contract false hp hc hf ⟨rfl, fun _ => rfl⟩ he hcap' IR hpass1 (fun _ => Or.inl rfl)
        have hTT : TraceOk world pieces f.contract defs p ∧
            (∀ rh, f.contract.resultHidden = some rh → f.contract.result.isSome = true ∧
              TraceOk world pieces (f.contract.forResult rh) defs p) := by
          cases hsel : hasSelect f.code with
          | true =>
            have he : f.contract.traceExprs.isEmpty = true := hsel_emp hsel
            have R1 : RunsOk world pieces f.contract defs p := hR (by simp [fnRunsCapable, he, hsel])
            refine ⟨runsOk_traceOk R1, fun rh hrh => ?_⟩
            obtain ⟨hres', hv2⟩ := hpass2 rh hrh
            have he2 : (f.contract.forResult rh).traceExprs.isEmpty = true := he
            have R2 : RunsOk world pieces (f.contract.forResult rh) defs p :=
              verifyOne_runsQ_rec world pieces defs runsOk done f p (f.contract.forResult rh) true hp hc hf
                ⟨rfl, fun x => forResult_regOf f.contract rh x⟩ he2 (Or.inl hsel) IR
                (by exact hv2) (fun _ => Or.inr R1)
            exact ⟨hres', runsOk_traceOk R2⟩
          | false =>
          cases hdec : f.contract.decreases with
          | none =>
            have W1 : ∀ a0, CalleesTrace world ctx a0 := fun a0 name c hl => by
              simp only [ctx, hdec, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hl
              obtain ⟨q, hq, fitq, hsb, Mq, Tq, Tq2, _⟩ := I name c hl
              exact ⟨q, hq, fitq, hsb, fun hs => by simp [ctx, hdec] at hs, Mq.below _, Tq.below _,
                fun rh hrh => ⟨(Tq2 rh hrh).1, (Tq2 rh hrh).2.below _⟩⟩
            have T1 : TraceOk world pieces f.contract defs p :=
              fun a0 b0 la ka pa lb kb pb ta a' b' Epa Epb =>
                verifyOne_trace_sound_at world ctx p f.proof hc hsel hpass1 a0 b0 (W1 a0) la ka pa lb kb pb ta a' b' Epa Epb
            have T2 : ∀ rh, f.contract.resultHidden = some rh → f.contract.result.isSome = true ∧
                TraceOk world pieces (f.contract.forResult rh) defs p := by
              intro rh hrh
              obtain ⟨hres', hv2⟩ := hpass2 rh hrh
              have W2 : ∀ a0, CalleesTrace world { ctx with contract := f.contract.forResult rh, resultPass := true } a0 :=
                fun a0 name c hl => by
                  simp only [ctx, hdec, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hl
                  obtain ⟨q, hq, fitq, hsb, Mq, Tq, Tq2, _⟩ := I name c hl
                  exact ⟨q, hq, fitq, hsb, fun hs => by simp [ctx, hdec] at hs, Mq.below _, Tq.below _,
                    fun rh' hrh' => ⟨(Tq2 rh' hrh').1, (Tq2 rh' hrh').2.below _⟩⟩
              exact ⟨hres', fun a0 b0 la ka pa lb kb pb ta a' b' Epa Epb =>
                verifyOne_trace_sound_at world { ctx with contract := f.contract.forResult rh, resultPass := true }
                  p f.proof hc hsel hv2 a0 b0 (W2 a0) la ka pa lb kb pb ta a' b' Epa Epb⟩
            exact ⟨T1, T2⟩
          | some d =>
            simp only [Contract.decreasesOk, hdec] at hdok1
            cases hr : f.contract.regOf d with
            | none => simp [hr] at hdok1
            | some rDec =>
              have all : ∀ n,
                  (∀ a0 b0, a0.reg rDec = n →
                    Loaded pieces a0 → f.contract.clear world pieces a0 → f.contract.pre p a0 →
                    Loaded pieces b0 → f.contract.clear world pieces b0 → f.contract.pre p b0 →
                    f.contract.traceAgree defs a0 b0 →
                    ∀ a' b', EndsP world p a0.plain a' → EndsP world p b0.plain b' →
                      a'.trace = b'.trace ∧ (f.contract.resultFollowsTrace = true → a'.reg 0 = b'.reg 0)) ∧
                  (∀ rh, f.contract.resultHidden = some rh →
                    ∀ a0 b0, a0.reg rDec = n →
                    Loaded pieces a0 → (f.contract.forResult rh).clear world pieces a0 → (f.contract.forResult rh).pre p a0 →
                    Loaded pieces b0 → (f.contract.forResult rh).clear world pieces b0 → (f.contract.forResult rh).pre p b0 →
                    (f.contract.forResult rh).traceAgree defs a0 b0 →
                    ∀ a' b', EndsP world p a0.plain a' → EndsP world p b0.plain b' →
                      a'.trace = b'.trace ∧ ((f.contract.forResult rh).resultFollowsTrace = true → a'.reg 0 = b'.reg 0)) := by
                intro n
                refine Nat.strongRecOn n fun n ih => ?_
                have mkW : ∀ (ct : Contract), ct.decreases = f.contract.decreases → (∀ x, ct.regOf x = f.contract.regOf x) →
                    ∀ a0, a0.reg rDec = n → CalleesTrace world { ctx with contract := ct } a0 := by
                  intro ct hdeq hreq a0 heq name c hl
                  simp only [ctx, hdec, Option.isSome_some, ↓reduceIte, List.lookup_cons] at hl
                  cases hn : (name == f.name) with
                  | true =>
                    rw [hn] at hl; injection hl with hl
                    have e : name = f.name := by simpa using hn
                    subst hl e
                    refine ⟨p, hp, hf, hsbok1, fun _ => ⟨hdeq.symm, fun x => (hreq x).symm⟩, M.below _, ?_, ?_⟩
                    · intro sa sb hbd la ka pa lb kb pb ta a' b' Epa Epb
                      have hlt : sa.reg rDec < a0.reg rDec := hbd rDec (a0.reg rDec) (by
                        simp [Ctx.recBound, ctx, hdec, hr])
                      exact (ih (sa.reg rDec) (by omega)).1 sa sb rfl la ka pa lb kb pb ta a' b' Epa Epb
                    · intro rh hrh
                      refine ⟨(hpass2 rh hrh).1, fun sa sb hbd la ka pa lb kb pb ta a' b' Epa Epb => ?_⟩
                      have hlt : sa.reg rDec < a0.reg rDec := hbd rDec (a0.reg rDec) (by
                        simp [Ctx.recBound, ctx, hdec, hr])
                      exact (ih (sa.reg rDec) (by omega)).2 rh hrh sa sb rfl la ka pa lb kb pb ta a' b' Epa Epb
                  | false =>
                    rw [hn] at hl
                    obtain ⟨q, hq, fitq, hsb, Mq, Tq, Tq2, _⟩ := I name c hl
                    refine ⟨q, hq, fitq, hsb, fun hs => by
                        simp only [ctx, hdec, Option.isSome_some, ↓reduceIte, Option.some.injEq] at hs
                        subst hs; simp at hn,
                      Mq.below _, Tq.below _, fun rh hrh => ⟨(Tq2 rh hrh).1, (Tq2 rh hrh).2.below _⟩⟩
                refine ⟨?_, ?_⟩
                · intro a0 b0 heq la ka pa lb kb pb ta a' b' Epa Epb
                  exact verifyOne_trace_sound_at world ctx p f.proof hc hsel hpass1 a0 b0
                    (mkW f.contract rfl (fun _ => rfl) a0 heq) la ka pa lb kb pb ta a' b' Epa Epb
                · intro rh hrh a0 b0 heq la ka pa lb kb pb ta a' b' Epa Epb
                  have W2 : CalleesTrace world { ctx with contract := f.contract.forResult rh, resultPass := true } a0 :=
                    mkW (f.contract.forResult rh) rfl (fun x => forResult_regOf f.contract rh x) a0 heq
                  exact verifyOne_trace_sound_at world { ctx with contract := f.contract.forResult rh, resultPass := true }
                    p f.proof hc hsel (hpass2 rh hrh).2 a0 b0 W2 la ka pa lb kb pb ta a' b' Epa Epb
              exact ⟨fun a0 b0 la ka pa lb kb pb ta a' b' Epa Epb =>
                  (all (a0.reg rDec)).1 a0 b0 rfl la ka pa lb kb pb ta a' b' Epa Epb,
                fun rh hrh => ⟨(hpass2 rh hrh).1, fun a0 b0 la ka pa lb kb pb ta a' b' Epa Epb =>
                  (all (a0.reg rDec)).2 rh hrh a0 b0 rfl la ka pa lb kb pb ta a' b' Epa Epb⟩⟩
        obtain ⟨T1, T2⟩ := hTT
        let runsOk' := if fnRunsCapable f then f.name :: runsOk else runsOk
        have hnot_in_runs : f.name ∉ runsOk := by
          intro hm
          obtain ⟨c0, hlk0⟩ := hsub f.name hm
          have hmem0 : (f.name, c0) ∈ done := lookup_mem hlk0
          exact hnodup (List.any_eq_true.mpr ⟨(f.name, c0), hmem0, by simp⟩)
        have hsub' : ∀ name ∈ runsOk', ∃ c, ((f.name, f.contract) :: done).lookup name = some c := by
          intro name hm
          dsimp only [runsOk'] at hm
          by_cases hnf : name = f.name
          · subst hnf; exact ⟨f.contract, by simp [List.lookup_cons]⟩
          · have hm' : name ∈ runsOk := by
              split at hm
              · rcases List.mem_cons.mp hm with rfl | h2
                · exact absurd rfl hnf
                · exact h2
              · exact hm
            obtain ⟨c0, hlk0⟩ := hsub name hm'
            exact ⟨c0, by rw [List.lookup_cons, beq_false_of_ne hnf]; exact hlk0⟩
        have I' : ∀ name c, ((f.name, f.contract) :: done).lookup name = some c →
            ∃ q, findProgram world name = some q ∧ q.fits ∧
              c.stackBitsOk = true ∧
              Meets world pieces c defs q ∧ TraceOk world pieces c defs q ∧
              (∀ rh, c.resultHidden = some rh → c.result.isSome = true ∧ TraceOk world pieces (c.forResult rh) defs q) ∧
              (name ∈ runsOk' → RunsOk world pieces c defs q) := by
          intro name c hl
          rw [List.lookup_cons] at hl
          cases hn : (name == f.name) with
          | true =>
            rw [hn] at hl; injection hl with hl
            have e : name = f.name := by simpa using hn
            subst hl e
            refine ⟨p, hp, hf, hsbok1, M, T1, T2, fun hmem => ?_⟩
            by_cases hcap_f : fnRunsCapable f = true
            · exact hR hcap_f
            · dsimp only [runsOk'] at hmem
              rw [if_neg hcap_f] at hmem
              exact (hnot_in_runs hmem).elim
          | false =>
            rw [hn] at hl
            obtain ⟨q, hq, fitq, hsb, Mq, Tq, Tq2, Rq⟩ := I name c hl
            refine ⟨q, hq, fitq, hsb, Mq, Tq, Tq2, fun hmem => Rq ?_⟩
            dsimp only [runsOk'] at hmem
            split at hmem
            · rcases List.mem_cons.mp hmem with rfl | hmem'
              · simp at hn
              · exact hmem'
            · exact hmem
        intro g m
        cases m with
        | head => exact ⟨p, hp, M, T1, T2⟩
        | tail _ m => exact verdictFrom_trace_sound world pieces defs more runsOk' _ hsub' I' (fun g m => L g (List.mem_cons_of_mem _ m)) h g m

/-- **Constant time, of what the verifier says yes of — stated directly on entry agreement (`traceAgree`),
with no mention of marks.** Take any two states at the function's entry where the program is loaded,
nothing the function may write overlaps the program's own bytes, the contract's preconditions hold, and
both states agree on everything the contract's `trace depends on` line lists (addresses, non-hidden
arguments, and computed values in `trace depends on`). Then any two runs of the plain machine (`EndsP`),
one from each state to the function's return, produce the exact same observable trace. -/
theorem verify_all_trace (world : List Program) (pieces : List Piece) (defs : List Def) (fns : List Fn) (L : Linked world fns)
    (h : verdictAll pieces defs fns = none) :
    ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧
      ∀ a b : State,
        Loaded pieces a → f.contract.clear world pieces a → f.contract.pre p a →
        Loaded pieces b → f.contract.clear world pieces b → f.contract.pre p b →
        f.contract.traceAgree defs a b →
        ∀ a' b' : State, EndsP world p a.plain a' → EndsP world p b.plain b' → a'.trace = b'.trace := by
  intro f m
  obtain ⟨p, hp, _, T1, _⟩ := verdictFrom_trace_sound world pieces defs fns [] [] (fun _ m => nomatch m) (fun name c hl => by simp [List.lookup] at hl) L h f m
  exact ⟨p, hp, fun a b la ka pa lb kb pb ta a' b' Epa Epb => (T1 a b la ka pa lb kb pb ta a' b' Epa Epb).1⟩

/-- **Return-value independence (`result depends on`), stated directly on entry agreement (`traceAgree`).**
For any verified function:
1. If it returns a named result with no `result depends on` line (`resultFollowsTrace = true`), two runs
   agreeing on `trace depends on` return the same value in register 0.
2. If it has a `result depends on` line (`resultHidden = some rh`), two runs agreeing on `trace depends on`
   and `result depends on` (`forResult rh`) return the same value in register 0. -/
theorem verify_all_result (world : List Program) (pieces : List Piece) (defs : List Def) (fns : List Fn) (L : Linked world fns)
    (h : verdictAll pieces defs fns = none) :
    ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧
      (f.contract.resultFollowsTrace = true →
        ∀ a b : State,
          Loaded pieces a → f.contract.clear world pieces a → f.contract.pre p a →
          Loaded pieces b → f.contract.clear world pieces b → f.contract.pre p b →
          f.contract.traceAgree defs a b →
          ∀ a' b' : State, EndsP world p a.plain a' → EndsP world p b.plain b' → a'.reg 0 = b'.reg 0) ∧
      (∀ rh, f.contract.resultHidden = some rh →
        ∀ a b : State,
          Loaded pieces a → f.contract.clear world pieces a → f.contract.pre p a →
          Loaded pieces b → f.contract.clear world pieces b → f.contract.pre p b →
          (f.contract.forResult rh).traceAgree defs a b →
          ∀ a' b' : State, EndsP world p a.plain a' → EndsP world p b.plain b' → a'.reg 0 = b'.reg 0) := by
  intro f m
  obtain ⟨p, hp, _, T1, T2⟩ := verdictFrom_trace_sound world pieces defs fns [] [] (fun _ m => nomatch m) (fun name c hl => by simp [List.lookup] at hl) L h f m
  refine ⟨p, hp, fun hrf a b la ka pa lb kb pb ta a' b' Epa Epb => (T1 a b la ka pa lb kb pb ta a' b' Epa Epb).2 hrf, ?_⟩
  intro rh hrh a b la ka pa lb kb pb ta a' b' Epa Epb
  obtain ⟨hres, Tr⟩ := T2 rh hrh
  have hrf_r : (f.contract.forResult rh).resultFollowsTrace = true := by
    simp [Contract.forResult, Contract.resultFollowsTrace, hres]
  exact (Tr a b la ((forResult_clear f.contract rh _ _ _).mpr ka) ((forResult_pre f.contract rh _ _).mpr pa)
    lb ((forResult_clear f.contract rh _ _ _).mpr kb) ((forResult_pre f.contract rh _ _).mpr pb) ta a' b' Epa Epb).2 hrf_r

end Ode
