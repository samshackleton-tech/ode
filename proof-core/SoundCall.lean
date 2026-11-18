import SoundPlace
/-!
# Why the verifier's yes is right, 7: a call, by the called function's contract

At a call the verifier shows what the called function's contract asks of its caller, and goes on from what
the contract leaves. Here: that the machine's call then goes as `Runs` says a call goes, given that the
called function meets that contract (`CalleesMeet`).
-/
namespace Ode
open Arithmetic

theorem Holds.more {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (rows : List Row) (hr : ∀ r ∈ rows, r.holds ρ) : Holds ctx s0 ρ { s with facts := rows ++ s.facts } st :=
  ⟨H.entry, H.reg, H.small, H.zf, H.cf, H.frame,
   fun f m => (List.mem_append.mp m).elim (hr f) (H.facts f), H.bytes, H.spec, H.mem⟩

theorem WF.more {s : Sym} (wf : WF s) (rows : List Row) (hb : ∀ r ∈ rows, bounded s.nvars r) : WF { s with facts := rows ++ s.facts } :=
  ⟨wf.base, wf.reg, wf.zf, wf.cf, wf.frame, fun f m => (List.mem_append.mp m).elim (hb f) (wf.facts f), wf.bytes, wf.spec⟩

/-- Every function this one calls is among the functions there are, lies in memory, and meets the contract
its call is taken by. -/
def CalleesMeet (world : List Program) (ctx : Ctx) : Prop :=
  ∀ name c, ctx.callees.lookup name = some c →
    ∃ q, findProgram world name = some q ∧ q.fits ∧ Meets world c ctx.defs q

theorem findRun_spec {s : Sym} {b l : Nat} : ∀ {regs : List (Nat × Nat)} {k j : Nat}, findRun s b l regs k = some j →
    ∃ b0 l0, k ≤ j ∧ regs[j - k]? = some (b0, l0) ∧ s.reg b = Lin.var b0 ∧ s.reg l = Lin.var l0
  | [], _, _, h => by simp [findRun] at h
  | (b0, l0) :: more, k, j, h => by
    simp only [findRun] at h
    split at h
    next hc =>
      injection h with h; subst h
      have hc' : s.reg b = Lin.var b0 ∧ s.reg l = Lin.var l0 := by simpa using hc
      exact ⟨b0, l0, Nat.le_refl _, by simp, hc'.1, hc'.2⟩
    next =>
      obtain ⟨b1, l1, hk, hr, e1, e2⟩ := findRun_spec h
      refine ⟨b1, l1, by omega, ?_, e1, e2⟩
      have : j - k = (j - (k + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]; exact hr

theorem regions_args {c : Contract} {b l : Nat} (h : (b, l) ∈ c.regions) : b ∈ argRegs ∧ l ∈ argRegs := by
  obtain ⟨hb, len, hl⟩ := regionsIn_mem c c.args argRegs b l h
  exact ⟨hb, regOfIn_mem len c.args argRegs l hl⟩

theorem argRegs_not_rsp {r : Nat} (h : r ∈ argRegs) : r < 16 ∧ r ≠ RSP := by
  simp only [argRegs, List.mem_cons, List.mem_nil_iff, or_false] at h
  unfold RSP
  omega

/-- Each run of bytes a called function is given is one of this function's own, whole. -/
theorem calleeEnv_regions {ctx : Ctx} {c : Contract} {s : Sym} : ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × SVal)},
    calleeEnv ctx c s args regs = some env → ∀ r l, (r, l) ∈ regionsIn c args regs →
    ∃ (j b0 l0 : Nat), ctx.contract.regions[j]? = some (b0, l0) ∧ s.reg r = Lin.var b0 ∧ s.reg l = Lin.var l0
  | [], _, _, _, r, l, m => by simp [regionsIn] at m
  | _ :: _, [], _, _, r, l, m => by simp [regionsIn] at m
  | (n, .number) :: args, x :: regs, env, h, r, l, m => by
    simp only [calleeEnv] at h
    cases hrec : calleeEnv ctx c s args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [regionsIn] at m
      exact calleeEnv_regions args regs hrec r l m
  | (n, .bytes len) :: args, x :: regs, env, h, r, l, m => by
    simp only [calleeEnv] at h
    cases hl : c.regOf len with
    | none =>
      simp only [hl] at h
      simp only [regionsIn, hl] at m
      exact calleeEnv_regions args regs h r l m
    | some l1 =>
      simp only [hl] at h
      cases hf : findRun s x l1 ctx.contract.regions 0 with
      | none => simp [hf] at h
      | some j =>
        cases hrec : calleeEnv ctx c s args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [regionsIn, hl, List.mem_cons] at m
          rcases m with m | m
          · injection m with m1 m2
            subst m1 m2
            obtain ⟨b0, l0, _, hr, e1, e2⟩ := findRun_spec hf
            exact ⟨j, b0, l0, by simpa using hr, e1, e2⟩
          · exact calleeEnv_regions args regs hrec r l m

theorem calleeEnv_bounded {ctx : Ctx} {c : Contract} {s : Sym} (wf : WF s) : ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × SVal)},
    (∀ r ∈ regs, r < 16) → calleeEnv ctx c s args regs = some env → EnvB s.nvars env
  | [], _, env, _, h => by
    simp only [calleeEnv] at h; injection h with h; subst h; exact fun nv m => nomatch m
  | _ :: _, [], env, _, h => by
    simp only [calleeEnv] at h; injection h with h; subst h; exact fun nv m => nomatch m
  | (n, .number) :: args, x :: regs, env, hr, h => by
    simp only [calleeEnv] at h
    cases hrec : calleeEnv ctx c s args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map] at h
      injection h with h
      subst h
      intro nv m
      cases m with
      | head => exact wf.reg x (hr x (List.mem_cons_self ..))
      | tail _ m => exact calleeEnv_bounded wf args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) hrec nv m
  | (n, .bytes len) :: args, x :: regs, env, hr, h => by
    simp only [calleeEnv] at h
    cases hl : c.regOf len with
    | none =>
      simp only [hl] at h
      exact calleeEnv_bounded wf args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) h
    | some l1 =>
      simp only [hl] at h
      cases hf : findRun s x l1 ctx.contract.regions 0 with
      | none => simp [hf] at h
      | some j =>
        cases hrec : calleeEnv ctx c s args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [hf, hrec] at h
          injection h with h
          subst h
          intro nv m
          cases m with
          | head => trivial
          | tail _ m => exact calleeEnv_bounded wf args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) hrec nv m

/-- A called function's names on symbols mean its names in the state it starts in. -/
theorem semEnv_calleeEnv {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {c : Contract} {s1 : State}
    (hentry : ∀ r, r < 16 → ρ r = s0.reg r)
    (hreg : ∀ r ∈ argRegs, (s1.reg r : Int) = ev ρ (s.reg r))
    (hmem : ∀ b0 l0, (b0, l0) ∈ ctx.contract.regions → ∀ k, k < s0.reg l0 → s1.mem (s0.reg b0 + k) = s0.mem (s0.reg b0 + k)) :
    ∀ (args : List (String × Kind)) (regs : List Nat) {env : List (String × SVal)}, (∀ r ∈ regs, r ∈ argRegs) →
    calleeEnv ctx c s args regs = some env → semEnv ctx s0 ρ env = envIn c s1 args regs
  | [], _, env, _, h => by
    simp only [calleeEnv] at h; injection h with h; subst h; simp [semEnv, envIn]
  | _ :: _, [], env, _, h => by
    simp only [calleeEnv] at h; injection h with h; subst h; simp [semEnv, envIn]
  | (n, .number) :: args, x :: regs, env, hr, h => by
    simp only [calleeEnv] at h
    cases hrec : calleeEnv ctx c s args regs with
    | none => simp [hrec] at h
    | some env' =>
      simp only [hrec, Option.map] at h
      injection h with h
      subst h
      have ih := semEnv_calleeEnv hentry hreg hmem args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) hrec
      simp only [semEnv, List.map_cons, envIn, semv] at ih ⊢
      rw [ih, hreg x (hr x (List.mem_cons_self ..))]
  | (n, .bytes len) :: args, x :: regs, env, hr, h => by
    simp only [calleeEnv] at h
    cases hl : c.regOf len with
    | none =>
      simp only [hl] at h
      have ih := semEnv_calleeEnv hentry hreg hmem args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) h
      simp only [envIn, hl]
      exact ih
    | some l1 =>
      simp only [hl] at h
      cases hf : findRun s x l1 ctx.contract.regions 0 with
      | none => simp [hf] at h
      | some j =>
        cases hrec : calleeEnv ctx c s args regs with
        | none => simp [hf, hrec] at h
        | some env' =>
          simp only [hf, hrec] at h
          injection h with h
          subst h
          have ih := semEnv_calleeEnv hentry hreg hmem args regs (fun r m => hr r (List.mem_cons_of_mem _ m)) hrec
          obtain ⟨b0, l0, _, hreg0, e1, e2⟩ := findRun_spec hf
          have hreg0' : ctx.contract.regions[j]? = some (b0, l0) := by simpa using hreg0
          have hm := List.mem_of_getElem? hreg0'
          have lt := regions_lt hm
          have hl1 : l1 ∈ argRegs := regOfIn_mem len c.args argRegs l1 hl
          have rx : s1.reg x = s0.reg b0 := by
            have := hreg x (hr x (List.mem_cons_self ..))
            rw [e1, ev_var, hentry b0 lt.1] at this
            omega
          have rl : s1.reg l1 = s0.reg l0 := by
            have := hreg l1 hl1
            rw [e2, ev_var, hentry l0 lt.2] at this
            omega
          have hbytes : (List.range (s0.reg l0)).map (fun k => s1.mem (s0.reg b0 + k)) = (List.range (s0.reg l0)).map (fun k => s0.mem (s0.reg b0 + k)) :=
            List.map_congr_left fun k hk => hmem b0 l0 hm k (List.mem_range.mp hk)
          simp only [semEnv, List.map_cons, envIn, hl, semv, hreg0', runBytes] at ih ⊢
          rw [ih, rx, rl, hbytes]

/-! ## The state after a call -/

/-- What the unknowns are after a call: those made for the registers are what the registers then hold. -/
def afterRho (n : Nat) (ρ : Nat → Int) (s2 : State) : Nat → Int :=
  fun k => if n ≤ k ∧ k < n + 16 then (s2.reg (k - n) : Int) else ρ k

theorem afterRho_agree (n : Nat) (ρ : Nat → Int) (s2 : State) : Agree n ρ (afterRho n ρ s2) := by
  intro k hk
  show ρ k = if n ≤ k ∧ k < n + 16 then (s2.reg (k - n) : Int) else ρ k
  rw [if_neg (by omega)]

theorem afterRho_new (n : Nat) (ρ : Nat → Int) (s2 : State) {r : Nat} (hr : r < 16) : afterRho n ρ s2 (n + r) = s2.reg r := by
  show (if n ≤ n + r ∧ n + r < n + 16 then (s2.reg (n + r - n) : Int) else ρ (n + r)) = s2.reg r
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

theorem callerSaved_lt {r : Nat} (h : r ∈ callerSaved) : r < 16 := by
  simp only [callerSaved, List.mem_cons, List.mem_nil_iff, or_false] at h
  omega

theorem afterCall_wf {s : Sym} (wf : WF s) (sp : Int) : WF (s.afterCall sp) := by
  refine ⟨Nat.le_trans wf.base (Nat.le_add_right _ _), ?_, trivial, trivial, ?_, ?_, ?_, ?_⟩
  · intro r hr
    show bounded (s.nvars + 16) (if callerSaved.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    split
    · exact bounded_var (by omega)
    · exact bounded_mono (Nat.le_add_right _ _) (wf.reg r hr)
  · intro o v m
    exact bounded_mono (Nat.le_add_right _ _) (wf.frame o v (List.mem_filter.mp m).1)
  · intro f m
    simp only [Sym.afterCall, List.mem_append] at m
    rcases m with m | m
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      have hr := callerSaved_lt hr
      simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · exact bounded_var (show s.nvars + r < s.nvars + 16 by omega)
      · exact bounded_sub (bounded_const _ _) (bounded_var (show s.nvars + r < s.nvars + 16 by omega))
    · exact bounded_mono (Nat.le_add_right _ _) (wf.facts f m)
  · intro v r o m
    have := wf.bytes v r o m
    exact ⟨Nat.lt_of_lt_of_le this.1 (Nat.le_add_right _ _), bounded_mono (Nat.le_add_right _ _) this.2⟩
  · intro f m
    exact SFact.bounded_mono (Nat.le_add_right _ _) (wf.spec f m)

/-- Of the machine's state when the called function has returned, what the verifier holds after the call is
so: given that the registers a callee keeps and the stack pointer are as before the call, and memory is as
before but in the called function's frame and at the address it returned to. -/
theorem afterCall_holds {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st s2 : State} {sp : Int} (cs : Nat)
    (H : Holds ctx s0 ρ s st) (wf : WF s)
    (hsp : (st.reg RSP : Int) = s0.reg RSP + sp) (hlow : -(ctx.contract.stack : Int) ≤ sp - 8 - cs) (hsp0 : sp ≤ 0)
    (hstack : ctx.contract.stack ≤ s0.reg RSP)
    (hkeep : ∀ r, r < 16 → callerSaved.contains r = false → s2.reg r = st.reg r)
    (hsmall : ∀ r, s2.reg r < M64)
    (hmem : ∀ a, a + 8 + cs < st.reg RSP ∨ st.reg RSP ≤ a → s2.mem a = st.mem a) :
    Holds ctx s0 (afterRho s.nvars ρ s2) (s.afterCall sp) s2 := by
  have ag := afterRho_agree s.nvars ρ s2
  have H' := H.agree wf ag
  refine ⟨H'.entry, ?_, hsmall, trivial, trivial, ?_, ?_, H'.bytes, H'.spec, ?_⟩
  · intro r hr
    show (s2.reg r : Int) = ev _ (if callerSaved.contains r = true then Lin.var (s.nvars + r) else s.reg r)
    cases hc : callerSaved.contains r with
    | true => rw [if_pos rfl, ev_var, afterRho_new _ _ _ hr]
    | false =>
      rw [if_neg (by decide), hkeep r hr hc]
      exact H'.reg r hr
  · intro o v m
    obtain ⟨m1, m2⟩ := List.mem_filter.mp m
    have m2' : sp ≤ o := by simpa using m2
    obtain ⟨h1, h2, h3⟩ := H'.frame o v m1
    refine ⟨h1, h2, ?_⟩
    rw [← h3]
    congr 1
    apply load_congr
    intro x hx1 hx2
    apply hmem
    right
    omega
  · intro f m
    simp only [Sym.afterCall, List.mem_append] at m
    rcases m with m | m
    · obtain ⟨l, hl, hf⟩ := List.mem_flatten.mp m
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
      have hr := callerSaved_lt hr
      have sm := hsmall r
      unfold M64 at sm
      have val := afterRho_new s.nvars ρ s2 hr
      simp only [ranged, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl
      · rw [holds_iff, ev_var, val]; omega
      · rw [holds_iff, ev_sub, ev_const, ev_var, val]; simp only [top]; omega
    · exact H'.facts f m
  · intro a ha
    have hfr : a + 8 + cs < st.reg RSP ∨ st.reg RSP ≤ a := by
      simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at ha
      omega
    rw [hmem a hfr]
    exact H.mem a ha

/-- **A call, by contract.** If the verifier has gone through a call, then of the machine at the call: the
address to come back to can be written; the state the called function starts in is one its contract's
caller has seen to; what the called function may touch, this function may touch; and of every state the
contract lets it return in, what the verifier holds after the call is so, at the next instruction. -/
theorem symCall_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {c : Contract}
    {items rest : List Item} {ρ : Nat → Int} {st : State}
    (h : symCall ctx s c items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s)
    (q : Program) (hq : q.fits) (i : Instr) (hret : p.base + i.next < M64) :
    8 ≤ st.reg RSP ∧ allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true ∧
    c.pre q (afterCall p q i st) ∧
    (∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true) ∧
    (∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true) ∧
    ∀ s2, c.post ctx.defs (afterCall p q i st) s2 → s2.rip = p.base + i.next ∧ ∃ ρ', Carried ctx s0 ρ s ρ' s' s2 := by
  cases hsp : s.sp with
  | none => simp only [symCall, hsp] at h; exact (refuse_ok h).elim
  | some sp =>
    simp only [symCall, hsp] at h
    split at h
    next => exact (refuse_ok h).elim
    next hguard =>
      have hg : sp ≤ 0 ∧ -(ctx.contract.stack : Int) ≤ sp - 8 - c.stack := by simpa using hguard
      cases henv : calleeEnv ctx c s c.args argRegs with
      | none => simp only [henv] at h; exact (refuse_ok h).elim
      | some env =>
        simp only [henv] at h
        have e := ev_isConst (ρ := ρ) hsp
        simp only [ev_sub, ev_var] at e
        have h1 := H.reg RSP (by decide)
        have h2 := H.entry RSP (by decide)
        have hrsp : (st.reg RSP : Int) = s0.reg RSP + sp := by omega
        have hstack := E.stack
        have habove := E.above
        have hsmallsp := H.small RSP
        have h8 : 8 ≤ st.reg RSP := by omega
        have s1rsp : (afterCall p q i st).reg RSP = st.reg RSP - 8 := by simp [afterCall]
        have s1reg : ∀ r, r ≠ RSP → (afterCall p q i st).reg r = st.reg r := fun r hr => by simp [afterCall, hr]
        have s1mem : ∀ x, x < st.reg RSP - 8 ∨ st.reg RSP ≤ x → (afterCall p q i st).mem x = st.mem x := fun x hx => by
          show store st.mem (st.reg RSP - 8) (p.base + i.next) 8 x = st.mem x
          exact store_other _ _ _ _ _ (by omega)
        have hregion : ∀ r l, (r, l) ∈ c.regions → ∃ b0 l0, (b0, l0) ∈ ctx.contract.regions ∧
            (afterCall p q i st).reg r = s0.reg b0 ∧ (afterCall p q i st).reg l = s0.reg l0 := by
          intro r l m
          obtain ⟨j, b0, l0, hj, e1, e2⟩ := calleeEnv_regions c.args argRegs henv r l m
          have hm := List.mem_of_getElem? hj
          have lt := regions_lt hm
          obtain ⟨ar, al⟩ := regions_args m
          obtain ⟨r16, rne⟩ := argRegs_not_rsp ar
          obtain ⟨l16, lne⟩ := argRegs_not_rsp al
          refine ⟨b0, l0, hm, ?_, ?_⟩
          · rw [s1reg r rne]
            have := H.reg r r16
            rw [e1, ev_var, H.entry b0 lt.1] at this
            omega
          · rw [s1reg l lne]
            have := H.reg l l16
            rw [e2, ev_var, H.entry l0 lt.2] at this
            omega
        have hpre : c.pre q (afterCall p q i st) := by
          refine ⟨rfl, ?_, ?_, ?_, hq, ?_⟩
          · intro r
            by_cases hr : r = RSP
            · rw [hr, s1rsp]; omega
            · rw [s1reg r hr]; exact H.small r
          · rw [s1rsp]; omega
          · rw [s1rsp]; omega
          · intro r l m
            obtain ⟨b0, l0, hm, er, el⟩ := hregion r l m
            obtain ⟨fit, apart⟩ := E.region hm
            rw [er, el, s1rsp]
            refine ⟨fit, by omega, ?_⟩
            intro k hk
            have hx : (afterCall p q i st).mem (s0.reg b0 + k) = st.mem (s0.reg b0 + k) := s1mem _ (by omega)
            rw [hx, H.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)]
            exact E.byte hm k hk
        have hread : ∀ a, (c.perm (afterCall p q i st)).read a = true → (ctx.contract.perm s0).read a = true := by
          intro a ha
          simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          rcases ha with (ha | ha) | ha
          · left; left; omega
          · left; left; omega
          · right
            obtain ⟨⟨r, l⟩, m, hin⟩ := List.any_eq_true.mp ha
            obtain ⟨b0, l0, hm, er, el⟩ := hregion r l m
            simp only [Bool.and_eq_true, decide_eq_true_eq, er, el] at hin
            exact List.any_eq_true.mpr ⟨(b0, l0), hm, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hin⟩
        have hwrite : ∀ a, (c.perm (afterCall p q i st)).write a = true → (ctx.contract.perm s0).write a = true := by
          intro a ha
          simp only [Contract.perm, Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq, s1rsp] at ha ⊢
          omega
        have hw : allowed (ctx.contract.perm s0).write (st.reg RSP - 8) 8 = true := by
          apply allowed_of
          intro x hx1 hx2
          simp only [Contract.perm, Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
          omega
        refine ⟨h8, hw, hpre, hread, hwrite, ?_⟩
        intro s2 post
        obtain ⟨prip, prsp, psaved, pmem, pret, psmall⟩ := post
        have hrip : s2.rip = p.base + i.next := by
          rw [prip, s1rsp]
          show load (store st.mem (st.reg RSP - 8) (p.base + i.next) 8) (st.reg RSP - 8) 8 = p.base + i.next
          exact load_store_same _ _ _ _ (by unfold M64 at hret; omega)
        have hkeep : ∀ r, r < 16 → callerSaved.contains r = false → s2.reg r = st.reg r := by
          intro r hr hc
          by_cases h4 : r = RSP
          · rw [h4, prsp, s1rsp]; omega
          · have hmemr : r ∈ calleeSaved := by
              unfold RSP at h4
              simp [callerSaved] at hc
              simp only [calleeSaved, List.mem_cons, List.mem_nil_iff, or_false]
              omega
            rw [psaved r hmemr, s1reg r h4]
        have hmem2 : ∀ a, a + 8 + c.stack < st.reg RSP ∨ st.reg RSP ≤ a → s2.mem a = st.mem a := by
          intro a ha
          rw [pmem a (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not, s1rsp]; omega)]
          exact s1mem a (by omega)
        have Hafter := afterCall_holds c.stack H wf hrsp hg.2 hg.1 hstack hkeep psmall hmem2
        have wafter := afterCall_wf wf sp
        have ag := afterRho_agree s.nvars ρ s2
        cases hret' : c.returns with
        | none =>
          simp only [hret'] at h
          have := V.pure_ok h
          injection this with h1 _
          subst h1
          exact ⟨hrip, _, ag, Nat.le_add_right _ _, Hafter, wafter⟩
        | some e =>
          simp only [hret'] at h
          obtain ⟨⟨res, s3⟩, r1, e1, h⟩ := V.bind_ok h
          have envb : EnvB s.nvars env := calleeEnv_bounded wf c.args argRegs (fun r m => (argRegs_not_rsp m).1) henv
          obtain ⟨ρ3, c3, sem, bd⟩ := seval_sound E env e e1 Hafter wafter (envb.mono (Nat.le_add_right _ _))
          have ag3 : Agree s.nvars ρ ρ3 := Agree.trans (Nat.le_add_right _ _) ag c3.agree
          have henv3 : semEnv ctx s0 ρ3 env = c.env (afterCall p q i st) := by
            rw [← semEnv_agree envb ag3]
            exact semEnv_calleeEnv H.entry
              (fun r m => by rw [s1reg r (argRegs_not_rsp m).2]; exact H.reg r (argRegs_not_rsp m).1)
              (fun b0 l0 hm k hk => by
                obtain ⟨fit, apart⟩ := E.region hm
                rw [s1mem _ (by omega)]
                exact H.mem _ (by simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega))
              c.args argRegs (fun r m => m) henv
          rw [henv3] at sem
          have val := pret e hret'
          have hnew : ev ρ3 (Lin.var s.nvars) = s2.reg 0 := by
            rw [ev_var, ← c3.agree s.nvars (show s.nvars < s.nvars + 16 by omega)]
            exact afterRho_new s.nvars ρ s2 (r := 0) (by decide)
          have bvar : bounded s3.nvars (Lin.var s.nvars) :=
            bounded_var (Nat.lt_of_lt_of_le (show s.nvars < s.nvars + 16 by omega) c3.mono)
          cases res with
          | list _ => exact (refuse_ok h).elim
          | tail call =>
            simp only at h
            have := V.pure_ok h
            injection this with h1 _
            subst h1
            have hv : SFact.holds ctx s0 ρ3 (.value call (Lin.var s.nvars)) := by
              show CallValue ctx s0 ρ3 call (.int (ev ρ3 (Lin.var s.nvars)))
              rw [hnew]
              exact (sem _).mp val
            exact ⟨hrip, ρ3, ag3, Nat.le_trans (Nat.le_add_right _ _) c3.mono, c3.holds.withSpec _ hv, c3.wf.withSpec _ ⟨bd, bvar⟩⟩
          | val v =>
            cases v with
            | region _ => exact (refuse_ok h).elim
            | bool _ => exact (refuse_ok h).elim
            | lin v =>
              simp only at h
              have := V.pure_ok h
              injection this with h1 _
              subst h1
              have same := Value.unique sem val
              simp only [semv] at same
              injection same with same
              exact ⟨hrip, ρ3, ag3, Nat.le_trans (Nat.le_add_right _ _) c3.mono,
                c3.holds.more _ (all_two (by rw [holds_iff, ev_sub, hnew]; omega) (by rw [holds_iff, ev_sub, hnew]; omega)),
                c3.wf.more _ (all_two (bounded_sub bd bvar) (bounded_sub bvar bd))⟩

end Ode
