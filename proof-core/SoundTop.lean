import SoundCall
import SoundCallW
import SoundSpecW
import SoundWide
import SoundList
/-!
# Why the verifier's yes is right, 4: instructions, paths, and the theorem
-/
namespace Ode
open Arithmetic

theorem Holds.rip {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (x : Nat) :
    Holds ctx s0 ρ s { st with rip := x } :=
  ⟨H.entry, H.reg, H.small, H.zf, H.cf, H.frame, H.facts, H.bytes, H.spec, H.mem, H.wrote, H.words, H.known⟩

/-- The statements of an effect, one after another. -/
theorem stmts_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) (base : Nat) (u : Nat → Nat) :
    ∀ (stmts : List Stmt) (k : Nat) {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State},
    fold (symStmt ctx bind) s stmts items = .ok (s', rest) → Holds ctx s0 ρ s st → WF s →
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧
      execAll (ctx.contract.perm s0) bind base u k st stmts = some (.next st') ∧ st'.rip = st.rip
  | [], k, s, s', items, rest, ρ, st, h, H, wf => by
    simp only [fold] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, st, Carried.here H wf, rfl, rfl⟩
  | stmt :: more, k, s, s', items, rest, ρ, st, h, H, wf => by
    simp only [fold] at h
    obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨ρ1, st1, c1, x1, rip1⟩ := symStmt_sound E bind e1 H wf base (u k)
    obtain ⟨ρ2, st2, c2, x2, rip2⟩ := stmts_sound E bind base u more (k + 1) h c1.holds c1.wf
    refine ⟨ρ2, st2, c1.then c2, ?_, rip2.trans rip1⟩
    cases stmt with
    | ret => simp only [symStmt] at e1; exact (refuse_ok e1).elim
    | nothing => simp only [execAll, x1]; exact x2
    | set _ _ => simp only [execAll, x1]; exact x2
    | vset _ _ => simp only [execAll, x1]; exact x2
    | vset512 _ _ => simp only [execAll, x1]; exact x2
    | jump _ _ => simp only [execAll, x1]; exact x2
    | call _ => simp only [execAll, x1]; exact x2

theorem stackGoals_bounded {ctx : Ctx} {s : Sym} (wf : WF s) {g : Row} (m : g ∈ stackGoals ctx s) : bounded s.nvars g := by
  have off := bounded_sub (wf.reg RSP (by decide)) (bounded_var (x := RSP) (Nat.lt_of_lt_of_le (by decide) wf.base))
  simp only [stackGoals, List.mem_cons, List.mem_append, List.mem_map, Option.mem_toList] at m
  rcases m with rfl | rfl | ⟨⟨o, _⟩, _, rfl⟩ | ⟨⟨o, ids⟩, hs, rfl⟩
  · exact bounded_add off (bounded_const _ _)
  · exact bounded_scale (-1) off
  · exact bounded_sub (bounded_const _ _) off
  · exact bounded_sub (wf.words.spill o ids hs).1 off

theorem settle_sound {ctx : Ctx} {s0 : State} {s s' : Sym} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : settle ctx s items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) : Carried ctx s0 ρ s ρ s' st := by
  cases hsp : s.sp with
  | none =>
    simp only [settle, hsp] at h
    obtain ⟨q, _, hc, he⟩ := V.bind_ok h
    cases q
    have hs := V.pure_ok he
    injection hs with heq _; subst s'
    exact ⟨Agree.refl _ _, Nat.le_refl _,
      ⟨H.entry, H.reg, H.small, H.zf, H.cf, H.frame,
       fun g m => (List.mem_append.mp m).elim (entails_sound H.facts hc g) (H.facts g),
       H.bytes, H.spec, H.mem, H.wrote, H.words, H.known⟩,
      ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame,
       fun _ m => (List.mem_append.mp m).elim (fun mg => stackGoals_bounded wf (List.mem_filter.mp mg).1) (wf.facts _),
       wf.bytes, wf.spec, wf.wrote, wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known⟩⟩
  | some sp =>
    simp only [settle, hsp] at h
    split at h
    next =>
      have := V.pure_ok h
      injection this with h1 _
      subst h1
      exact ⟨Agree.refl _ _, Nat.le_refl _,
        ⟨H.entry, H.reg, H.small, H.zf, H.cf, fun o v m => H.frame o v (List.mem_filter.mp m).1, H.facts, H.bytes, H.spec, H.mem, H.wrote,
         ⟨H.words.vec, H.words.intact, H.words.wrote, fun _ _ h => nomatch h⟩, H.known⟩,
        ⟨wf.base, wf.reg, wf.zf, wf.cf, fun o v m => wf.frame o v (List.mem_filter.mp m).1, wf.facts, wf.bytes, wf.spec, wf.wrote,
         wf.words.mono rfl rfl rfl (Nat.le_refl _), wf.known⟩⟩
    next => exact (refuse_ok h).elim

/-! ## A jump on a flag -/

/-- The way the flag is in fact set is among the ways gone. -/
theorem ways_sound {ctx : Ctx} {s0 : State} {s : Sym} {want : Bool} {target next : Nat} {ρ : Nat → Int} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF s) (b : Bool) :
    ∀ (w : List (Bool × List Row)) {nexts : List (Sym × Next)} {items rest : Items},
    ways s want target next w items = .ok (nexts, rest) →
    (∀ sr ∈ w, ∀ r ∈ sr.2, bounded s.nvars r) →
    (∃ sr ∈ w, sr.1 = b ∧ ∀ r ∈ sr.2, r.holds ρ) →
    ∃ s', (s', Next.at (if b == want then target else next)) ∈ nexts ∧ Carried ctx s0 ρ s ρ s' st
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
        · exact Carried.here H wf
        · exact ⟨Agree.refl _ _, Nat.le_refl _, H.more rows hrows, wf.more rows (hb (set, rows) (List.mem_cons_self ..))⟩
    | tail _ m =>
      obtain ⟨s', m', hs'⟩ := ways_sound H wf b more e2 (fun sr m => hb sr (List.mem_cons_of_mem _ m)) ⟨sr, m, hset, hrows⟩
      cases now with
      | none =>
        simp only at h
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        exact ⟨s', m', hs'⟩
      | some s1 =>
        simp only at h
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        exact ⟨s', List.mem_cons_of_mem _ m', hs'⟩

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

theorem calleeSaved_spec {r : Nat} (h : r ∈ calleeSaved) : r < 16 ∧ r ≠ RSP := by
  simp only [calleeSaved, List.mem_cons, List.mem_nil_iff, or_false] at h
  unfold RSP
  omega

/-- At a return the verifier has passed: the machine's return is allowed, and leaves what the contract
promises. -/
theorem symReturn_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s : Sym} {items : Items}
    {r : Unit × Items} {ρ : Nat → Int} {st : State}
    (h : symReturn ctx s items = .ok r) (H : Holds ctx s0 ρ s st) (wf : WF s) :
    allowed (ctx.contract.perm s0).read (st.reg RSP) 8 = true ∧
    ctx.contract.post ctx.defs s0 (setReg { st with rip := load st.mem (st.reg RSP) 8 } RSP (st.reg RSP + 8)) := by
  unfold symReturn at h
  split at h
  next => exact (refuse_ok h).elim
  next hsp =>
    split at h
    next => exact (refuse_ok h).elim
    next hcs =>
      -- every `ensures` of a whole run of words: of this state's memory, which the return leaves as it is
      obtain ⟨_, rW, enW, h⟩ := V.bind_ok h
      have hensW : ∀ e ∈ ctx.contract.ensuresW,
          e.holds ctx.contract ctx.defs s0 (setReg { st with rip := load st.mem (st.reg RSP) 8 } RSP (st.reg RSP + 8)) := by
        intro e me
        obtain ⟨items', r', hr⟩ := each_mem enW e me
        exact symEnsureW_sound E hr H wf rfl
      -- every `ensures` first: of the state the return leaves, whose memory and rax are this state's
      obtain ⟨sE, rE, en, h⟩ := V.bind_ok h
      have henvB : EnvB s.nvars (symEnvAfter ctx.contract s) := by
        have hsym := (symEnv_bounded ctx.contract).mono wf.base
        unfold symEnvAfter
        split
        · intro nv m
          rcases List.mem_cons.mp m with rfl | m
          · exact wf.reg 0 (by decide)
          · exact hsym nv m
        · exact hsym
      have henv : ∀ ρ', Agree s.nvars ρ ρ' → semEnv ctx s0 ρ' (symEnvAfter ctx.contract s) =
          ctx.contract.envAfter s0 (setReg { st with rip := load st.mem (st.reg RSP) 8 } RSP (st.reg RSP + 8)) := by
        intro ρ' a
        have hsym := semEnv_symEnv ctx s0 ρ' (fun r hr => by rw [← a r (Nat.lt_of_lt_of_le hr wf.base)]; exact H.entry r hr)
        have hrax : ev ρ' (s.reg 0) = (st.reg 0 : Int) := by rw [← ev_agree (wf.reg 0 (by decide)) a]; exact (H.reg 0 (by decide)).symm
        cases hres : ctx.contract.result with
        | none => simp only [symEnvAfter, Contract.envAfter, hres]; exact hsym
        | some name =>
          simp only [symEnvAfter, Contract.envAfter, hres]
          show (name, semv ctx s0 ρ' (.lin (s.reg 0))) :: semEnv ctx s0 ρ' (symEnv ctx.contract) = _
          rw [hsym]
          simp only [semv, hrax]
          simp [setReg, RSP]
      obtain ⟨ρE, cE, hens⟩ := symEnsures_sound E en H wf henvB henv rfl
      have hsp' : s.sp = some 0 := by simpa using hsp
      have hcs' : ∀ r ∈ calleeSaved, s.reg r = Lin.var r := by simpa using hcs
      have e := ev_isConst (ρ := ρ) hsp'
      simp only [ev_sub, ev_var] at e
      have h1 := H.reg RSP (by decide)
      have h2 := H.entry RSP (by decide)
      have hrsp : st.reg RSP = s0.reg RSP := by omega
      have hstack := E.stack
      have habove := E.above
      refine ⟨allowed_of _ _ _ ?_, ?_, ?_, ?_, ?_, ?_, ?_, hens, hensW⟩
      · intro x hx1 hx2
        simp only [Contract.perm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        left; left; right; omega
      · show load st.mem (st.reg RSP) 8 = load s0.mem (s0.reg RSP) 8
        rw [hrsp]
        apply load_congr
        intro x hx1 hx2
        apply H.mem
        · simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        · exact E.frame_notOut (by omega) (by omega)
      · show (if RSP = RSP then (st.reg RSP + 8) % M64 else st.reg RSP) = s0.reg RSP + 8
        rw [if_pos rfl, hrsp, Nat.mod_eq_of_lt habove]
      · intro r hr
        obtain ⟨lt, ne⟩ := calleeSaved_spec hr
        show (if r = RSP then (st.reg RSP + 8) % M64 else st.reg r) = s0.reg r
        rw [if_neg ne]
        have := H.reg r lt
        rw [hcs' r hr, ev_var, H.entry r lt] at this
        omega
      · intro a ha ho
        exact H.mem a ha ho
      · intro e he
        simp only [he] at h
        obtain ⟨⟨res, s1⟩, r1, e1, h⟩ := V.bind_ok h
        obtain ⟨ρ1, c1, sem, bd⟩ := seval_sound E _ e e1 cE.holds cE.wf ((symEnv_bounded ctx.contract).mono cE.wf.base)
        rw [semEnv_symEnv ctx s0 ρ1 c1.holds.entry] at sem
        show Value ctx.defs (ctx.contract.env s0) e (.int ((if 0 = RSP then (st.reg RSP + 8) % M64 else st.reg 0 : Nat)))
        rw [if_neg (by decide)]
        have hrax := c1.holds.reg 0 (by decide)
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
            have : ev ρ1 v = (st.reg 0 : Int) := by omega
            rw [this] at sem
            exact sem
        | tail c =>
          simp only at h
          obtain ⟨s2, r2, g1, h⟩ := V.bind_ok h
          obtain ⟨ρ2, c2, gh⟩ := specGoal_sound E 16 g1 c1.holds c1.wf ⟨bd, c1.wf.reg 0 (by decide)⟩
          simp only [SFact.holds] at gh
          rw [← ev_agree (c1.wf.reg 0 (by decide)) c2.agree, ← hrax] at gh
          exact (sem _).mpr ((CallValue_agree bd c2.agree _).mpr gh)
      · intro r
        show (if r = RSP then (st.reg RSP + 8) % M64 else st.reg r) < M64
        split
        · exact Nat.mod_lt _ (by unfold M64; omega)
        · exact H.small r

/-! ## An instruction -/

theorem shape_ret : ∀ {l : List Stmt}, shape l = .ret → l = [.ret]
  | [], h => by simp [shape] at h
  | [s], h => by cases s <;> simp [shape] at h ⊢
  | _ :: _ :: _, h => by simp [shape] at h

theorem shape_jump {target : Expr} {cond : Option (String × Bool)} : ∀ {l : List Stmt}, shape l = .jump target cond → l = [.jump target cond]
  | [], h => by simp [shape] at h
  | [s], h => by cases s <;> simp [shape] at h ⊢; exact h
  | _ :: _ :: _, h => by simp [shape] at h

/-- An instruction the verifier has gone through, of the machine: whatever the unknowns turn out to be it
does not fault; if it returns, the contract's promise holds; if it goes on, it goes on at one of the places
the verifier went on at, in a state of which what the verifier holds there is so. -/
theorem symInstr_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s : Sym} {i : Instr}
    {nexts : List (Sym × Next)} {items rest : Items} {ρ : Nat → Int} {st : State}
    (h : symInstr ctx s i items = .ok (nexts, rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (u : Nat → Nat) :
    ∃ o, exec (ctx.contract.perm s0) p i u st = some o ∧
      match o with
      | .next st' => ∃ s' pc ρ', (s', Next.at pc) ∈ nexts ∧ st'.rip = p.base + pc ∧ Carried ctx s0 ρ s ρ' s' st'
      | .returned st' => ctx.contract.post ctx.defs s0 st' := by
  cases hs : shape i.effect with
  | ret =>
    have heff := shape_ret hs
    simp only [symInstr, hs] at h
    obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨al, post⟩ := symReturn_sound E e1 (H.rip (p.base + i.next)) wf
    refine ⟨_, by simp only [exec, heff, execAll]; rw [if_pos al], post⟩
  | jump target cond =>
    have heff := shape_jump hs
    simp only [symInstr, hs] at h
    cases ht : jumpTarget i.bind target with
    | none => simp only [ht] at h; exact (refuse_ok h).elim
    | some t =>
      simp only [ht] at h
      have hv := jumpTarget_value ht (ctx.contract.perm s0) { st with rip := p.base + i.next }
      cases cond with
      | none =>
        simp only at h
        have := V.pure_ok h
        injection this with h1 _
        subst h1
        refine ⟨.next { st with rip := p.base + t }, by simp [exec, heff, execAll, execStmt, hv], s, t, ρ, List.mem_cons_self .., rfl, Carried.here (H.rip _) wf⟩
      | some fw =>
        obtain ⟨flag, want⟩ := fw
        simp only at h
        cases hz : (flag == "zf") with
        | true =>
          simp only [hz, if_true] at h
          cases hw : flagWays s.zf with
          | none => simp only [hw] at h; exact (refuse_ok h).elim
          | some w =>
            simp only [hw] at h
            obtain ⟨bd, ex⟩ := flagWays_spec hw H.zf wf.zf
            obtain ⟨s', m, c'⟩ := ways_sound H wf st.zf w h bd ex
            by_cases taken : (st.zf == want) = true
            · rw [if_pos taken] at m
              exact ⟨.next { st with rip := p.base + t }, by simp only [exec, heff, execAll, execStmt, hz, if_true, Bool.false_eq_true, if_false, taken, hv, Option.map], s', t, ρ, m, rfl, c'.agree, c'.mono, c'.holds.rip _, c'.wf⟩
            · rw [if_neg taken] at m
              exact ⟨.next { st with rip := p.base + i.next }, by simp only [exec, heff, execAll, execStmt, hz, if_true, Bool.false_eq_true, if_false, taken], s', i.next, ρ, m, rfl, c'.agree, c'.mono, c'.holds.rip _, c'.wf⟩
        | false =>
          simp only [hz, Bool.false_eq_true, if_false] at h
          cases hw : flagWays s.cf with
          | none => simp only [hw] at h; exact (refuse_ok h).elim
          | some w =>
            simp only [hw] at h
            obtain ⟨bd, ex⟩ := flagWays_spec hw H.cf wf.cf
            obtain ⟨s', m, c'⟩ := ways_sound H wf st.cf w h bd ex
            by_cases taken : (st.cf == want) = true
            · rw [if_pos taken] at m
              exact ⟨.next { st with rip := p.base + t }, by simp only [exec, heff, execAll, execStmt, hz, if_true, Bool.false_eq_true, if_false, taken, hv, Option.map], s', t, ρ, m, rfl, c'.agree, c'.mono, c'.holds.rip _, c'.wf⟩
            · rw [if_neg taken] at m
              exact ⟨.next { st with rip := p.base + i.next }, by simp only [exec, heff, execAll, execStmt, hz, if_true, Bool.false_eq_true, if_false, taken], s', i.next, ρ, m, rfl, c'.agree, c'.mono, c'.holds.rip _, c'.wf⟩
  | plain =>
    simp only [symInstr, hs] at h
    obtain ⟨s1, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨s2, r2, e2, h⟩ := V.bind_ok h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    obtain ⟨ρ1, st1, c1, x1, rip1⟩ := stmts_sound E i.bind p.base u i.effect 0 e1 (H.rip (p.base + i.next)) wf
    have c2 := settle_sound e2 c1.holds c1.wf
    exact ⟨.next st1, x1, s2, i.next, ρ1, List.mem_cons_self .., rip1, c1.then c2⟩

/-! ## Paths -/

/-- One instruction, in general: if from every state the machine can go on in, at a place the verifier
went on at, the machine runs to its return and leaves what the contract promises, so it does from here.
At a call, the called function runs by its contract, which it meets, and the machine goes on after it. -/
theorem step_runs {world : List Program} {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (W : CalleesMeet world ctx)
    {s : Sym} {pc : Nat} {i : Instr}
    {nexts : List (Sym × Next)} {items rest : Items} {ρ : Nat → Int} {st : State}
    (hl : ctx.code.lookup pc = some i) (h : symNext ctx s i items = .ok (nexts, rest))
    (H : Holds ctx s0 ρ s st) (wf : WF s) (hrip : st.rip = p.base + pc)
    (K : ∀ s' pc' ρ' st', (s', Next.at pc') ∈ nexts → st'.rip = p.base + pc' → Carried ctx s0 ρ s ρ' s' st' →
      Runs world (ctx.contract.perm s0) p (ctx.contract.post ctx.defs s0) st') :
    Runs world (ctx.contract.perm s0) p (ctx.contract.post ctx.defs s0) st := by
  have hfetch : p.fetch st.rip = some i := by
    unfold Program.fetch
    rw [hrip, if_neg (by omega), E.code, Nat.add_sub_cancel_left]
    exact hl
  cases hc : callTarget i with
  | none =>
    simp only [symNext, hc] at h
    apply Runs.step _ p _ st i hfetch
    · intro u hn
      obtain ⟨o, ho, _⟩ := symInstr_sound E h H wf u
      rw [ho] at hn
      cases hn
    · intro u st' hx
      obtain ⟨o, ho, hmatch⟩ := symInstr_sound E h H wf u
      rw [hx] at ho
      injection ho with ho
      subst ho
      obtain ⟨s', pc', ρ', m, hrip', c'⟩ := hmatch
      exact K s' pc' ρ' st' m hrip' c'
    · intro u st' hx
      obtain ⟨o, ho, hmatch⟩ := symInstr_sound E h H wf u
      rw [hx] at ho
      injection ho with ho
      subst ho
      exact hmatch
  | some name =>
    simp only [symNext, hc] at h
    cases hl2 : ctx.callees.lookup name with
    | none => simp only [hl2] at h; exact (refuse_ok h).elim
    | some c =>
      simp only [hl2] at h
      obtain ⟨_, _, _, h⟩ := V.bind_ok h
      obtain ⟨s', r1, e1, h⟩ := V.bind_ok h
      have := V.pure_ok h
      injection this with hn _
      subst hn
      obtain ⟨q, hq, fitq, meets⟩ := W name c hl2
      have hcode : (pc, i) ∈ p.code := by rw [E.code]; exact lookup_mem hl
      obtain ⟨h8, hw, hpre, hread, hwrite, hpost⟩ := symCall_sound E e1 H wf q fitq i (E.fits hcode)
      exact Runs.call _ p _ st i name q (c.perm (afterCall p q i st)) (c.post ctx.defs (afterCall p q i st))
        hfetch hc hq h8 hw hread hwrite (meets _ hpre)
        (fun s2 post => by
          obtain ⟨hrip2, ρ', c'⟩ := hpost s2 post
          exact K s' i.next ρ' s2 (List.mem_cons_self ..) hrip2 c')

/-- What the verifier relies on along a path, of each place the path has come to, `n` being the unknowns
in use and `ρ` what they are: from every state of the machine at that place of which the place says what
it says, whose number is less than the number of the place's general state on this path, the machine runs
to the function's return and leaves what the contract promises. -/
def Relied (world : List Program) (ctx : Ctx) (p : Program) (s0 : State) (seen : List Seen) (n : Nat) (ρ : Nat → Int) : Prop :=
  ∀ e ∈ seen, (∀ nr ∈ e.place.names, nr.2 < 16) ∧ e.first.nvars ≤ n ∧ bounded n e.d ∧
    ∀ ρ' st', AtPlace ctx e.place s0 e.first ρ ρ' st' → st'.rip = p.base + e.place.pc →
      (∃ m : Int, Value ctx.defs (placeVals ctx e.place s0 st') e.place.decreases (.int m) ∧ m + 1 ≤ ev ρ e.d) →
      Runs world (ctx.contract.perm s0) p (ctx.contract.post ctx.defs s0) st'

theorem Relied.carried {world : List Program} {ctx : Ctx} {p : Program} {s0 : State} {seen : List Seen} {n n' : Nat} {ρ ρ' : Nat → Int}
    (T : Relied world ctx p s0 seen n ρ) (le : n ≤ n') (a : Agree n ρ ρ') : Relied world ctx p s0 seen n' ρ' := by
  intro e m
  obtain ⟨hn, hf, hd, run⟩ := T e m
  refine ⟨hn, Nat.le_trans hf le, bounded_mono le hd, ?_⟩
  intro ρx stx A hrip ⟨k, val, lt⟩
  refine run ρx stx ⟨Agree.trans (Nat.le_refl _) (Agree.mono hf a) A.outer, A.entry, A.kept, A.small, A.frame, A.mem, A.facts⟩ hrip ⟨k, val, ?_⟩
  rw [ev_agree hd a]
  exact lt

/-- The paths from a state of which what the verifier holds is so: the machine runs to the function's
return and leaves what the contract promises. Where a path first comes to a place, by induction on the
place's number, which every way round to it makes less and which is never below zero. -/
theorem explore_sound {world : List Program} {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (W : CalleesMeet world ctx) :
    ∀ (fuel : Nat) {seen : List Seen} {s : Sym} {pc : Nat} {items : Items} {r : Unit × Items} {ρ : Nat → Int} {st : State},
    explore ctx fuel seen s pc items = .ok r → Holds ctx s0 ρ s st → WF s → st.rip = p.base + pc →
    Relied world ctx p s0 seen s.nvars ρ →
    Runs world (ctx.contract.perm s0) p (ctx.contract.post ctx.defs s0) st
  | 0, seen, s, pc, items, r, ρ, st, h, H, wf, hrip, T => by
    simp only [explore] at h
    exact (refuse_ok h).elim
  | fuel + 1, seen, s, pc, items, r, ρ, st, h, H, wf, hrip, T => by
    cases hl : ctx.code.lookup pc with
    | none => simp only [explore, hl] at h; exact (refuse_ok h).elim
    | some i =>
      simp only [explore, hl] at h
      obtain ⟨nexts, r1, e1, h⟩ := V.bind_ok h
      apply step_runs E W hl e1 H wf hrip
      intro s' pc' ρ' st' m hrip' c'
      obtain ⟨items', r', hbody⟩ := each_mem h (s', Next.at pc') m
      have T' := T.carried c'.mono c'.agree
      simp only [onward] at hbody
      cases hp : ctx.places.find? (fun p => p.pc == pc') with
      | none =>
        simp only [hp] at hbody
        exact explore_sound E W fuel hbody c'.holds c'.wf hrip' T'
      | some pl =>
        simp only [hp] at hbody
        have epc : pl.pc = pc' := by simpa using List.find?_some hp
        cases hs : seen.find? (fun e => e.place.pc == pc') with
        | some e =>
          simp only [hs] at hbody
          have em : e ∈ seen := List.mem_of_find?_eq_some hs
          have eq : e.place.pc = pc' := by simpa using List.find?_some hs
          obtain ⟨hn, hf, hd, run⟩ := T' e em
          obtain ⟨A, k, val, lt⟩ := arrive_sound E e.place hn hbody c'.holds c'.wf hd
          exact run ρ' st' A (by rw [eq]; exact hrip') ⟨k, val, lt⟩
        | none =>
          simp only [hs] at hbody
          obtain ⟨⟨g, d, first⟩, r2, e2, hgo⟩ := V.bind_ok hbody
          obtain ⟨hn, ρ1, ag1, le1, A1, wg, leg, hd, G⟩ := generalize_sound E pl e2 c'.holds c'.wf
          have T1 : Relied world ctx p s0 seen first.nvars ρ1 := T'.carried le1 ag1
          have all : ∀ (n : Nat) (ρx : Nat → Int) (stx : State), AtPlace ctx pl s0 first ρ1 ρx stx → stx.rip = p.base + pl.pc →
              Value ctx.defs (placeVals ctx pl s0 stx) pl.decreases (.int (n : Int)) →
              Runs world (ctx.contract.perm s0) p (ctx.contract.post ctx.defs s0) stx := by
            intro n
            induction n using Nat.strongRecOn with
            | ind n ih =>
              intro ρx stx A hripx val
              obtain ⟨ρ'', Hg, agx, pos, val'⟩ := G ρx stx A
              have same := Value.unique val val'
              injection same with same
              have a1 : Agree first.nvars ρ1 ρ'' := Agree.trans (Nat.le_refl _) A.outer agx
              apply explore_sound E W fuel hgo Hg wg (by rw [← epc]; exact hripx)
              intro e me
              cases me with
              | head =>
                refine ⟨hn, leg, hd, ?_⟩
                intro ρy sty Ay hripy ⟨k, valy, lty⟩
                have Ay1 : AtPlace ctx pl s0 first ρ1 ρy sty :=
                  ⟨Agree.trans (Nat.le_refl _) a1 Ay.outer, Ay.entry, Ay.kept, Ay.small, Ay.frame, Ay.mem, Ay.facts⟩
                obtain ⟨ρz, _, _, posz, valz⟩ := G ρy sty Ay1
                have samez := Value.unique valy valz
                injection samez with samez
                have lty : k + 1 ≤ ev ρ'' d := lty
                have small : k.toNat < n := by omega
                exact ih k.toNat small ρy sty Ay1 hripy (by rw [Int.toNat_of_nonneg (by omega)]; exact valy)
              | tail _ me => exact (T1.carried leg a1) e me
          obtain ⟨ρ'', _, _, pos, val⟩ := G ρ1 st' A1
          exact all (ev ρ'' d).toNat ρ1 st' A1 (by rw [epc]; exact hrip') (by rw [Int.toNat_of_nonneg pos]; exact val)

/-! ## The entry, and the theorem -/

/-- At entry, what the verifier starts from is so (the unknowns being what the registers hold). -/
theorem entry_holds {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) :
    Holds ctx s0 (fun k => (s0.reg k : Int)) (entrySym ctx) s0 ∧ WF (entrySym ctx) := by
  have hstack := E.stack
  have habove := E.above
  unfold M64 at habove
  refine ⟨⟨fun _ _ => rfl, fun r _ => by simp [entrySym], E.small, trivial, trivial, ?_, ?_, ?_, ?_, (fun _ _ _ => rfl),
           (fun _ _ _ m => nomatch m),
           ⟨(fun x ids h => by simp [entrySym] at h), (fun _ _ _ _ _ _ _ _ => rfl),
            (fun w j i m => by simp [entrySym] at m), fun _ _ h => nomatch h⟩,
           (fun k m => by simp [entrySym] at m)⟩,
          ⟨Nat.le_refl _, fun r hr => bounded_var hr, trivial, trivial, ?_, ?_, ?_, ?_, (fun _ _ _ m => nomatch m),
           ⟨fun i n h => by simp [entrySym] at h, fun j r h => by simp [entrySym] at h, fun x ids h => by simp [entrySym] at h,
            (fun j a n h => by simp [entrySym] at h), (fun w j i h => by simp [entrySym] at h), fun _ _ h => nomatch h⟩,
           (fun k m => by simp [entrySym] at m)⟩⟩
  · intro o v m; cases m
  · intro f m
    simp only [entrySym, entryFacts, List.mem_append] at m
    rcases m with ((((m | m) | m) | m) | m) | m
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
  · intro v r o m; cases m
  · intro f m; cases m
  · intro o v m; cases m
  · intro f m
    simp only [entrySym, entryFacts, List.mem_append] at m
    rcases m with ((((m | m) | m) | m) | m) | m
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      have hr := List.mem_range.mp hr
      simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · exact bounded_var hr
      · exact bounded_sub (bounded_const _ _) (bounded_var hr)
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at m
      rcases m with rfl | rfl
      · exact bounded_sub (bounded_var (show RSP < 16 by decide)) (bounded_const _ _)
      · exact bounded_sub (bounded_const _ _) (bounded_var (show RSP < 16 by decide))
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
        exact bounded_sub (bounded_const _ _) (bounded_var (argRegs_lt (regOfIn_mem x ctx.contract.args argRegs r hr)))
    · obtain ⟨⟨x, b, n⟩, hm, rfl⟩ := List.mem_map.mp m
      exact bounded_sub (bounded_const _ _) (bounded_var (fixeds_lt hm))
  · intro v r o m; cases m
  · intro f m; cases m

/-- **What the verifier's yes stands for.** If the verifier says yes of a proof, whatever the proof is, and
every function this one calls meets the contract its call was taken by, then the function's code meets its
contract (`Meets`): from every state at entry of which the caller has seen to what the contract asks, the
machine runs on instructions of the function and of those it calls, touches only memory the contract
allows, and after finitely many instructions returns to its caller with the stack pointer, the registers a
callee keeps and all memory outside its frame as they were, and in rax the value the contract's `returns`
has by the specification's definitions. -/
theorem verify_sound (world : List Program) (ctx : Ctx) (p : Program) (proof : List Item) (hcode : p.code = ctx.code)
    (W : CalleesMeet world ctx) (h : verdict ctx proof = none) : Meets world ctx.contract ctx.defs p := by
  intro s0 pre
  have E : Setting ctx p s0 := ⟨hcode, pre⟩
  cases hv : verify ctx (Items.ofList proof) with
  | error why => simp [verdict, hv] at h
  | ok r =>
    unfold verify at hv
    obtain ⟨_, r1, e1, _⟩ := V.bind_ok hv
    obtain ⟨H, wf⟩ := entry_holds E
    exact explore_sound E W PATH e1 H wf (by rw [E.rip]; rfl) (fun e m => nomatch m)

/-! ## The functions of a statement, together -/

/-- The functions there are have, under each function's name, the instructions the statement gives for it,
lying in memory. -/
def Linked (world : List Program) (fns : List Fn) : Prop :=
  ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧ p.code = f.code ∧ p.fits

theorem verdictFrom_sound (world : List Program) (defs : List Def) :
    ∀ (fns : List Fn) (done : List (String × Contract)),
    (∀ name c, done.lookup name = some c → ∃ q, findProgram world name = some q ∧ q.fits ∧ Meets world c defs q) →
    Linked world fns → verdictFrom defs done fns = none →
    ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧ Meets world f.contract defs p
  | [], _, _, _, _ => fun f m => nomatch m
  | f :: more, done, I, L, h => by
    simp only [verdictFrom] at h
    split at h
    · cases h
    · cases hv : verdict { code := f.code, contract := f.contract, defs := defs, places := f.places, callees := done } f.proof with
      | some why => simp [hv] at h
      | none =>
        simp only [hv] at h
        obtain ⟨p, hp, hc, hf⟩ := L f (List.mem_cons_self ..)
        have M : Meets world f.contract defs p :=
          verify_sound world { code := f.code, contract := f.contract, defs := defs, places := f.places, callees := done } p f.proof hc I hv
        have I' : ∀ name c, ((f.name, f.contract) :: done).lookup name = some c →
            ∃ q, findProgram world name = some q ∧ q.fits ∧ Meets world c defs q := by
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
        | tail _ m => exact verdictFrom_sound world defs more _ I' (fun g m => L g (List.mem_cons_of_mem _ m)) h g m

/-- **What the verifier's yes of a statement stands for.** If the verifier says yes of the functions of a
statement, whatever the proofs are, then every one of them meets its contract: given only that the
functions there are have, under each name, the instructions the statement gives, lying in memory. Nothing
is assumed of any function: each one called is itself in the statement, and is shown before its caller. -/
theorem verify_all_sound (world : List Program) (defs : List Def) (fns : List Fn) (L : Linked world fns)
    (h : verdictAll defs fns = none) :
    ∀ f ∈ fns, ∃ p, findProgram world f.name = some p ∧ Meets world f.contract defs p :=
  verdictFrom_sound world defs fns [] (fun name c hl => by simp [List.lookup] at hl) L h

end Ode
