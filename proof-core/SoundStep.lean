import SoundState
/-!
# Why the verifier's yes is right, 3: an instruction on symbols and the instruction on the machine
-/
namespace Ode
open Arithmetic

/-- The setting of every lemma here: the verifier's `ctx` is of the program `p`, and `s0` is a state at the
function's entry of which the caller has seen to what the contract asks. -/
structure Setting (ctx : Ctx) (p : Program) (s0 : State) : Prop where
  code : p.code = ctx.code
  pre : ctx.contract.pre p s0

namespace Setting
variable {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0)
include E
theorem rip : s0.rip = p.base := E.pre.1
theorem small (r : Nat) : s0.reg r < M64 := E.pre.2.1 r
theorem stack : ctx.contract.stack ≤ s0.reg RSP := E.pre.2.2.1
theorem above : s0.reg RSP + 8 < M64 := E.pre.2.2.2.1
theorem fits {o : Nat} {i : Instr} (h : (o, i) ∈ p.code) : p.base + i.next < M64 := E.pre.2.2.2.2.1 (o, i) h
theorem region {r l : Nat} (h : (r, l) ∈ ctx.contract.regions) :
    s0.reg r + s0.reg l ≤ M64 ∧ (s0.reg r + s0.reg l ≤ s0.reg RSP - ctx.contract.stack ∨ s0.reg RSP + 8 ≤ s0.reg r) :=
  ⟨(E.pre.2.2.2.2.2 r l h).1, (E.pre.2.2.2.2.2 r l h).2.1⟩
theorem byte {r l : Nat} (h : (r, l) ∈ ctx.contract.regions) (k : Nat) (hk : k < s0.reg l) : s0.mem (s0.reg r + k) < 256 :=
  (E.pre.2.2.2.2.2 r l h).2.2 k hk
end Setting

theorem indexOf_lt (name : String) : ∀ (l : List String) (k r : Nat), indexOf name l k = some r → r < k + l.length
  | [], _, _, h => by simp [indexOf] at h
  | n :: ns, k, r, h => by
    simp only [indexOf] at h
    split at h
    · injection h with h; subst h; simp
    · have := indexOf_lt name ns (k + 1) r h
      simp only [List.length_cons]; omega

theorem regIndex_lt {name : String} {r : Nat} (h : regIndex name = some r) : r < 16 := by
  have := indexOf_lt name regNames 0 r h
  simpa [regNames] using this

theorem regOf_lt {bind : Bind} {n : String} {r : Nat} (h : regOf bind n = some r) : r < 16 := by
  unfold regOf at h
  split at h
  · cases hb : bind.lookup n with
    | none => simp [hb] at h
    | some x => simp [hb] at h; exact regIndex_lt h
  · exact regIndex_lt h

theorem regOfIn_mem (name : String) : ∀ (args : List (String × Kind)) (regs : List Nat) (r : Nat),
    regOfIn name args regs = some r → r ∈ regs
  | [], _, _, h => by simp [regOfIn] at h
  | _ :: _, [], _, h => by simp [regOfIn] at h
  | (n, _) :: args, x :: regs, r, h => by
    simp only [regOfIn] at h
    split at h
    · injection h with h; subst h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (regOfIn_mem name args regs r h)

theorem regionsIn_mem (c : Contract) : ∀ (args : List (String × Kind)) (regs : List Nat) (b l : Nat),
    (b, l) ∈ regionsIn c args regs → b ∈ regs ∧ ∃ len, c.regOf len = some l
  | [], _, _, _, h => by simp [regionsIn] at h
  | _ :: _, [], _, _, h => by simp [regionsIn] at h
  | (_, .number) :: args, x :: regs, b, l, h => by
    simp only [regionsIn] at h
    have := regionsIn_mem c args regs b l h
    exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
  | (_, .bytes len) :: args, x :: regs, b, l, h => by
    simp only [regionsIn] at h
    split at h
    next l' hl =>
      cases h with
      | head => exact ⟨List.mem_cons_self .., len, hl⟩
      | tail _ h =>
        have := regionsIn_mem c args regs b l h
        exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    next =>
      have := regionsIn_mem c args regs b l h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem argRegs_lt {r : Nat} (h : r ∈ argRegs) : r < 16 := by
  simp [argRegs] at h; omega

theorem regions_lt {c : Contract} {b l : Nat} (h : (b, l) ∈ c.regions) : b < 16 ∧ l < 16 := by
  obtain ⟨hb, len, hl⟩ := regionsIn_mem c c.args argRegs b l h
  exact ⟨argRegs_lt hb, argRegs_lt (regOfIn_mem len c.args argRegs l hl)⟩

theorem signed_ev (ρ : Nat → Int) (r : Row) : ev ρ (signed r) = ev ρ r ∨ ev ρ (signed r) = ev ρ r - 2 ^ 64 := by
  unfold signed
  split
  next k hk =>
    split
    · right; rw [ev_isConst hk]; simp
    · left; rfl
  next => left; rfl

theorem lookupByte_mem {r : Nat} {o : Row} : ∀ {l : List (Nat × Nat × Row)} {v : Nat}, lookupByte r o l = some v → (v, r, o) ∈ l
  | [], _, h => by simp [lookupByte] at h
  | (v', r', o') :: rest, v, h => by
    simp only [lookupByte] at h
    split at h
    next e => injection h with h; subst h; rw [e.1, e.2]; exact List.mem_cons_self ..
    next => exact List.mem_cons_of_mem _ (lookupByte_mem h)

/-- From one state of the verifier to a later one: the unknowns in use keep their values, and what the
later state holds is so. -/
structure Carried (ctx : Ctx) (s0 : State) (ρ : Nat → Int) (s : Sym) (ρ' : Nat → Int) (s' : Sym) (st' : State) : Prop where
  agree : Agree s.nvars ρ ρ'
  mono : s.nvars ≤ s'.nvars
  holds : Holds ctx s0 ρ' s' st'
  wf : WF s'

theorem Carried.here {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) (wf : WF s) :
    Carried ctx s0 ρ s ρ s st := ⟨Agree.refl _ _, Nat.le_refl _, H, wf⟩

theorem Carried.then {ctx : Ctx} {s0 : State} {ρ ρ1 ρ2 : Nat → Int} {s s1 s2 : Sym} {st1 st2 : State}
    (a : Carried ctx s0 ρ s ρ1 s1 st1) (b : Carried ctx s0 ρ1 s1 ρ2 s2 st2) : Carried ctx s0 ρ s ρ2 s2 st2 :=
  ⟨Agree.trans a.mono a.agree b.agree, Nat.le_trans a.mono b.mono, b.holds, b.wf⟩

theorem readByte_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {r : Nat} {o v : Row}
    {items rest : List Item} {ρ : Nat → Int} {st : State}
    (h : readByte ctx s r o items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (hb : bounded s.nvars o) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ bounded s'.nvars v ∧
      ∃ base len, ctx.contract.regions[r]? = some (base, len) ∧ 0 ≤ ev ρ' o ∧ ev ρ' o < s0.reg len ∧
        ev ρ' v = s0.mem (s0.reg base + (ev ρ' o).toNat) := by
  cases hreg : ctx.contract.regions[r]? with
  | none => simp only [readByte, hreg] at h; exact (refuse_ok h).elim
  | some bl =>
    obtain ⟨base, len⟩ := bl
    simp only [readByte, hreg] at h
    obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨_, r2, e2, h⟩ := V.bind_ok h
    have g1 := entail_sound e1 ρ H.facts
    have g2 := entail_sound e2 ρ H.facts
    have hlen : len < 16 := (regions_lt (List.mem_of_getElem? hreg)).2
    simp only [ev_sub, ev_var, ev_const] at g2
    rw [H.entry len hlen] at g2
    cases hv : lookupByte r o s.bytes with
    | some v0 =>
      simp only [hv] at h
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      have m := lookupByte_mem hv
      obtain ⟨base', len', hr', _, _, h4⟩ := H.bytes v0 r o m
      rw [hreg] at hr'
      injection hr' with hr'
      injection hr' with hb1 hb2
      subst hb1 hb2
      refine ⟨ρ, Carried.here H wf, bounded_var (wf.bytes v0 r o m).1, base, len, rfl, g1, by omega, ?_⟩
      rw [ev_var]; exact h4
    | none =>
      simp only [hv] at h
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      let ρ' : Nat → Int := fun k => if k = s.nvars then (s0.mem (s0.reg base + (ev ρ o).toNat) : Int) else ρ k
      have ag : Agree s.nvars ρ ρ' := fun k hk => by
        show ρ k = if k = s.nvars then _ else ρ k
        rw [if_neg (by omega)]
      have H' := H.agree wf ag
      have eo : ev ρ' o = ev ρ o := (ev_agree hb ag).symm
      have new : ρ' s.nvars = (s0.mem (s0.reg base + (ev ρ o).toNat) : Int) := by
        show (if s.nvars = s.nvars then _ else ρ s.nvars) = _
        rw [if_pos rfl]
      have le : s.nvars ≤ s.nvars + 1 := Nat.le_succ _
      refine ⟨ρ', ⟨ag, le, ?_, ?_⟩, bounded_var (Nat.lt_succ_self _), base, len, rfl, by rw [eo]; exact g1, by rw [eo]; omega, ?_⟩
      · exact {
          entry := H'.entry, reg := H'.reg, small := H'.small, zf := H'.zf, cf := H'.cf, frame := H'.frame,
          spec := H'.spec, mem := H'.mem,
          facts := by
            intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | rfl | hf
            · rw [holds_iff, ev_var, new]; exact Int.natCast_nonneg _
            · rw [holds_iff, ev_sub, ev_const, ev_var, new]
              have := E.byte (List.mem_of_getElem? hreg) (ev ρ o).toNat (by omega)
              omega
            · exact H'.facts f hf
          bytes := by
            intro v1 r1 o1 hm
            simp only [List.mem_cons] at hm
            rcases hm with heq | hm
            · injection heq with h1 h2
              injection h2 with h2 h3
              subst h1 h2 h3
              exact ⟨base, len, hreg, by rw [eo]; exact g1, by rw [eo]; omega, by rw [new, eo]⟩
            · exact H'.bytes v1 r1 o1 hm }
      · exact {
          base := Nat.le_trans wf.base le
          reg := fun r hr => bounded_mono le (wf.reg r hr)
          zf := Flag.bounded_mono le wf.zf
          cf := Flag.bounded_mono le wf.cf
          frame := fun o v m => bounded_mono le (wf.frame o v m)
          spec := fun f m => SFact.bounded_mono le (wf.spec f m)
          facts := by
            intro f hf
            simp only [List.mem_cons] at hf
            rcases hf with rfl | rfl | hf
            · exact bounded_var (Nat.lt_succ_self _)
            · exact bounded_sub (bounded_const _ _) (bounded_var (Nat.lt_succ_self _))
            · exact bounded_mono le (wf.facts f hf)
          bytes := by
            intro v1 r1 o1 hm
            simp only [List.mem_cons] at hm
            rcases hm with heq | hm
            · injection heq with h1 h2
              injection h2 with h2 h3
              subst h1 h2 h3
              exact ⟨Nat.lt_succ_self _, bounded_mono le hb⟩
            · exact ⟨Nat.lt_of_lt_of_le (wf.bytes v1 r1 o1 hm).1 le, bounded_mono le (wf.bytes v1 r1 o1 hm).2⟩ }
      · rw [ev_var, new, eo]

/-! ## The value of an effect's expression -/

/-- What a value on symbols says of the number `x` the machine works out. -/
def EV.sem (ρ : Nat → Int) (n : Nat) (x : Nat) : EV → Prop
  | .lin r => x < M64 ∧ (x : Int) = ev ρ r ∧ bounded n r
  | .equal a b => x = (if ev ρ a = ev ρ b then 1 else 0) ∧ bounded n a ∧ bounded n b
  | .below a b => x = (if ev ρ a < ev ρ b then 1 else 0) ∧ bounded n a ∧ bounded n b

theorem EV.sem_agree {ρ ρ' : Nat → Int} {n m x : Nat} {v : EV} (h : EV.sem ρ n x v) (a : Agree n ρ ρ') (le : n ≤ m) : EV.sem ρ' m x v := by
  cases v with
  | lin r => exact ⟨h.1, by rw [← ev_agree h.2.2 a]; exact h.2.1, bounded_mono le h.2.2⟩
  | equal x y => exact ⟨by rw [← ev_agree h.2.1 a, ← ev_agree h.2.2 a]; exact h.1, bounded_mono le h.2.1, bounded_mono le h.2.2⟩
  | below x y => exact ⟨by rw [← ev_agree h.2.1 a, ← ev_agree h.2.2 a]; exact h.1, bounded_mono le h.2.1, bounded_mono le h.2.2⟩

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] : ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (a', b') :: rest, a, b, h => by
    simp only [List.lookup] at h
    split at h
    next e =>
      injection h with h; subst h
      have : a = a' := by simpa using e
      subst this
      exact List.mem_cons_self ..
    next => exact List.mem_cons_of_mem _ (lookup_mem h)

theorem findRegion_spec {addr : Row} : ∀ {l : List (Nat × Nat)} {k : Nat} {w : Where}, findRegion addr l k = some w →
    ∃ r o base len, w = .region r o ∧ k ≤ r ∧ l[r - k]? = some (base, len) ∧ o = Lin.sub addr (Lin.var base)
  | [], _, _, h => by simp [findRegion] at h
  | (base, len) :: more, k, w, h => by
    simp only [findRegion] at h
    split at h
    next =>
      injection h with h; subst h
      exact ⟨k, _, base, len, rfl, Nat.le_refl _, by simp, rfl⟩
    next =>
      obtain ⟨r, o, b, l, hw, hk, hr, ho⟩ := findRegion_spec h
      refine ⟨r, o, b, l, hw, by omega, ?_, ho⟩
      have : r - k = (r - (k + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]; exact hr

theorem locate_frame {ctx : Ctx} {addr : Row} {c : Int} (h : locate ctx addr = some (.frame c)) :
    Lin.isConst (Lin.sub addr (Lin.var RSP)) = some c := by
  cases hk : Lin.isConst (Lin.sub addr (Lin.var RSP)) with
  | some c' => simp only [locate, hk] at h; injection h with h; injection h with h; rw [h]
  | none =>
    simp only [locate, hk] at h
    obtain ⟨r, o, b, l, hw, _⟩ := findRegion_spec h
    cases hw

theorem locate_region {ctx : Ctx} {addr : Row} {r : Nat} {o : Row} (h : locate ctx addr = some (.region r o)) :
    ∃ base len, ctx.contract.regions[r]? = some (base, len) ∧ o = Lin.sub addr (Lin.var base) := by
  cases hk : Lin.isConst (Lin.sub addr (Lin.var RSP)) with
  | some c' => simp only [locate, hk] at h; injection h with h; cases h
  | none =>
    simp only [locate, hk] at h
    obtain ⟨r', o', b, l, hw, _, hr, ho⟩ := findRegion_spec h
    injection hw with h1 h2
    subst h1 h2
    exact ⟨b, l, by simpa using hr, ho⟩

theorem inFrame_spec {ctx : Ctx} {s : Sym} {c : Int} (h : inFrame ctx s c = true) :
    ∃ sp, s.sp = some sp ∧ sp ≤ c ∧ c + 8 ≤ 0 ∧ -(ctx.contract.stack : Int) ≤ c := by
  unfold inFrame at h
  split at h
  next sp hsp =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨sp, hsp, h.1.1, h.1.2, h.2⟩
  next => contradiction

theorem pow8 : (256 : Nat) ^ 8 = M64 := by decide

/-- Eight bytes of the frame, at `c` from where the stack pointer was at entry: where they are, and that the
function may read and write them. -/
theorem frame_address {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {c : Int}
    (h1 : -(ctx.contract.stack : Int) ≤ c) (h2 : c + 8 ≤ 0) (a : Nat) (ha : (a : Int) = (s0.reg RSP : Int) + c) :
    allowed (ctx.contract.perm s0).read a 8 = true ∧ allowed (ctx.contract.perm s0).write a 8 = true ∧
    ((s0.reg RSP : Int) + c).toNat = a := by
  have hs := E.stack
  refine ⟨allowed_of _ _ _ ?_, allowed_of _ _ _ ?_, by omega⟩
  · intro x hx1 hx2
    simp only [Contract.perm, Contract.inFrame, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    left; left; omega
  · intro x hx1 hx2
    simp only [Contract.perm, Contract.inFrame, Bool.and_eq_true, decide_eq_true_eq]
    omega

theorem symLoad_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {s s' : Sym} {addr : Row} {size : Nat} {v : EV}
    {items rest : List Item} {ρ : Nat → Int} {st : State}
    (h : symLoad ctx s addr size items = .ok ((v, s'), rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (hb : bounded s.nvars addr)
    (a : Nat) (hlt : a < M64) (ha : (a : Int) % 2 ^ 64 = ev ρ addr % 2 ^ 64) :
    ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ allowed (ctx.contract.perm s0).read a size = true ∧ EV.sem ρ' s'.nvars (load st.mem a size) v := by
  have hstack := E.stack
  have habove := E.above
  have hrsp : ρ RSP = s0.reg RSP := H.entry RSP (by decide)
  unfold M64 at hlt habove
  cases hl : locate ctx addr with
  | none => simp only [symLoad, hl] at h; exact (refuse_ok h).elim
  | some w =>
    cases w with
    | frame c =>
      simp only [symLoad, hl] at h
      split at h
      next hc =>
        obtain ⟨hsize, hin⟩ := hc
        subst hsize
        obtain ⟨sp, _, _, h8, hst⟩ := inFrame_spec hin
        have e := ev_isConst (ρ := ρ) (locate_frame hl)
        simp only [ev_sub, ev_var, hrsp] at e
        have hadr : (a : Int) = (s0.reg RSP : Int) + c := by omega
        obtain ⟨hr, _, hn⟩ := frame_address E hst h8 a hadr
        cases hf : s.frame.lookup c with
        | none => simp only [hf] at h; exact (refuse_ok h).elim
        | some v0 =>
          simp only [hf] at h
          have := V.pure_ok h
          injection this with hp _
          injection hp with h1 h2
          subst h1 h2
          have m := lookup_mem hf
          obtain ⟨_, _, hv⟩ := H.frame c v0 m
          rw [hn] at hv
          have lt := load_lt st.mem a 8
          rw [pow8] at lt
          exact ⟨ρ, Carried.here H wf, hr, lt, hv, wf.frame c v0 m⟩
      next => exact (refuse_ok h).elim
    | region r o =>
      simp only [symLoad, hl] at h
      obtain ⟨base, len, hreg, ho⟩ := locate_region hl
      have hmem := List.mem_of_getElem? hreg
      have hbl := regions_lt hmem
      split at h
      next hsize =>
        subst hsize
        obtain ⟨⟨v0, s1⟩, r1, e1, h⟩ := V.bind_ok h
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        have hbo : bounded s.nvars o := by
          rw [ho]; exact bounded_sub hb (bounded_var (Nat.lt_of_lt_of_le hbl.1 wf.base))
        obtain ⟨ρ', c1, bv, base', len', hreg', g1, g2, g3⟩ := readByte_sound E e1 H wf hbo
        rw [hreg] at hreg'
        injection hreg' with hreg'
        injection hreg' with hb1 hb2
        subst hb1 hb2
        have eo : ev ρ' o = ev ρ addr - s0.reg base := by
          rw [← ev_agree hbo c1.agree, ho, ev_sub, ev_var, H.entry base hbl.1]
        obtain ⟨hfit, hapart⟩ := E.region hmem
        unfold M64 at hfit
        have hadr : a = s0.reg base + (ev ρ' o).toNat := by omega
        have hmem0 : st.mem a = s0.mem a := by
          apply c1.holds.mem
          simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        have hbyte := E.byte hmem (ev ρ' o).toNat (by omega)
        rw [← hadr] at hbyte
        refine ⟨ρ', c1, ?_, ?_, ?_, bv⟩
        · simp only [allowed, Bool.and_true, Contract.perm, Bool.or_eq_true]
          right
          exact List.any_eq_true.mpr ⟨(base, len), hmem, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩
        · simp only [load]; unfold M64; omega
        · rw [g3, ← hadr]; simp only [load, hmem0]; omega
      next => exact (refuse_ok h).elim

theorem symPrim_sound {f : String} {s s' : Sym} {x y : Row} {v : EV} {items rest : List Item} {ρ : Nat → Int}
    (h : symPrim f s x y items = .ok ((v, s'), rest)) (hf : ∀ g ∈ s.facts, g.holds ρ)
    (xa xb : Nat) (hx : EV.sem ρ s.nvars xa (.lin x)) (hy : EV.sem ρ s.nvars xb (.lin y)) :
    s' = s ∧ ∃ z, prim f [xa, xb] = some z ∧ EV.sem ρ s.nvars z v := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  have sx := signed_ev ρ x
  have sy := signed_ev ρ y
  unfold M64 at hx1 hy1
  unfold symPrim at h
  split at h
  next hc =>
    obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
    unfold inRange at e1
    obtain ⟨_, r2, e2, e3⟩ := V.bind_ok e1
    have g1 := entail_sound e2 ρ hf
    have g2 := entail_sound e3 ρ hf
    simp only [ev_sub, ev_add, ev_const, top] at g1 g2
    have := V.pure_ok h
    injection this with hp _
    injection hp with h1 h2
    subst h1 h2
    refine ⟨rfl, (xa + xb) % M64, by simp only [prim]; rw [if_pos hc], ?_, ?_, bounded_add (bounded_signed hx3) (bounded_signed hy3)⟩
    · exact Nat.mod_lt _ (by decide)
    · rw [ev_add]; unfold M64; omega
  next hc =>
    split at h
    next hc2 =>
      obtain ⟨_, r1, e1, h⟩ := V.bind_ok h
      unfold inRange at e1
      obtain ⟨_, r2, e2, e3⟩ := V.bind_ok e1
      have g1 := entail_sound e2 ρ hf
      have g2 := entail_sound e3 ρ hf
      simp only [ev_sub, ev_const, top] at g1 g2
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      refine ⟨rfl, (xa + (M64 - xb % M64)) % M64, by simp only [prim]; rw [if_neg hc, if_pos hc2], ?_, ?_, bounded_sub (bounded_signed hx3) (bounded_signed hy3)⟩
      · exact Nat.mod_lt _ (by decide)
      · rw [ev_sub]; unfold M64; omega
    next hc2 =>
      split at h
      next hc3 =>
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        have fe : f = "equal" := by simpa using hc3
        subst fe
        refine ⟨rfl, (if xa % M64 = xb % M64 then 1 else 0), by simp [prim], ?_, hx3, hy3⟩
        unfold M64
        rw [Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hy1, ← hx2, ← hy2]
        simp only [Int.natCast_inj]
      next hc3 =>
        split at h
        next hc4 =>
          have := V.pure_ok h
          injection this with hp _
          injection hp with h1 h2
          subst h1 h2
          have fe : f = "below" := by simpa using hc4
          subst fe
          refine ⟨rfl, (if xa % M64 < xb % M64 then 1 else 0), by simp [prim], ?_, hx3, hy3⟩
          unfold M64
          rw [Nat.mod_eq_of_lt hx1, Nat.mod_eq_of_lt hy1, ← hx2, ← hy2]
          simp only [Int.ofNat_lt]
        next => exact (refuse_ok h).elim

theorem M64_cast : (M64 : Int) = 2 ^ 64 := by decide

theorem symValue_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) :
    ∀ (e : Expr) {s s' : Sym} {v : EV} {items rest : List Item} {ρ : Nat → Int} {st : State},
    symValue ctx bind s e items = .ok ((v, s'), rest) → Holds ctx s0 ρ s st → WF s →
    ∃ ρ' x, Carried ctx s0 ρ s ρ' s' st ∧ value (ctx.contract.perm s0) bind st e = some x ∧ EV.sem ρ' s'.nvars x v
  | .number n, s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    split at h
    next hn =>
      have := V.pure_ok h
      injection this with hp _
      injection hp with h1 h2
      subst h1 h2
      exact ⟨ρ, n, Carried.here H wf, by simp [value], by unfold M64; exact hn, by simp, bounded_const _ _⟩
    next => exact (refuse_ok h).elim
  | .lane _ _, s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    exact (refuse_ok h).elim
  | .name n, s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    split at h
    next hletter =>
      cases hb : (bind.lookup n).bind readInt with
      | none => simp only [hb] at h; exact (refuse_ok h).elim
      | some i =>
        simp only [hb] at h
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        refine ⟨ρ, (i % (M64 : Int)).toNat, Carried.here H wf, by simp [value, hletter, hb], ?_, ?_, bounded_const _ _⟩
        · rw [M64_cast]; unfold M64; omega
        · rw [ev_const, M64_cast]; omega
    next hletter =>
      cases hr : regOf bind n with
      | none => simp only [hr] at h; exact (refuse_ok h).elim
      | some r =>
        simp only [hr] at h
        have := V.pure_ok h
        injection this with hp _
        injection hp with h1 h2
        subst h1 h2
        have lt := regOf_lt hr
        exact ⟨ρ, st.reg r, Carried.here H wf, by simp [value, hletter, hr], H.small r, H.reg r lt, wf.reg r lt⟩
  | .call f [a, b], s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    obtain ⟨⟨x, s1⟩, r1, e1, h⟩ := V.bind_ok h
    obtain ⟨⟨y, s2⟩, r2, e2, h⟩ := V.bind_ok h
    obtain ⟨ρ1, xa, c1, va, sa⟩ := symValue_sound E bind a e1 H wf
    obtain ⟨ρ2, xb, c2, vb, sb⟩ := symValue_sound E bind b e2 c1.holds c1.wf
    have sa2 := EV.sem_agree sa c2.agree c2.mono
    cases x with
    | equal _ _ => exact (refuse_ok h).elim
    | below _ _ => exact (refuse_ok h).elim
    | lin x =>
      cases y with
      | equal _ _ => exact (refuse_ok h).elim
      | below _ _ => exact (refuse_ok h).elim
      | lin y =>
        simp only at h
        cases hm : memSize f with
        | some size =>
          simp only [hm] at h
          have sx := signed_ev ρ2 x
          have sy := signed_ev ρ2 y
          have hx1 := sa2.1
          have hy1 := sb.1
          unfold M64 at hx1 hy1
          have hmod : (((xa + (xb + 0)) % M64 : Nat) : Int) % 2 ^ 64 = ev ρ2 (Lin.add (signed x) (signed y)) % 2 ^ 64 := by
            rw [ev_add]; unfold M64; have := sa2.2.1; have := sb.2.1; omega
          obtain ⟨ρ3, c3, al, sv⟩ := symLoad_sound E h c2.holds c2.wf (bounded_add (bounded_signed sa2.2.2) (bounded_signed sb.2.2))
            ((xa + (xb + 0)) % M64) (Nat.mod_lt _ (by decide)) hmod
          exact ⟨ρ3, _, (c1.then c2).then c3, by simp only [value, values, va, vb, hm, sumList, al, if_true], sv⟩
        | none =>
          simp only [hm] at h
          obtain ⟨hs, z, hz, sz⟩ := symPrim_sound h c2.holds.facts xa xb sa2 sb
          subst hs
          exact ⟨ρ2, z, c1.then c2, by simp only [value, values, va, vb, hm, hz], sz⟩
  | .call f [], s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    exact (refuse_ok h).elim
  | .call f [_], s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    exact (refuse_ok h).elim
  | .call f (_ :: _ :: _ :: _), s, s', v, items, rest, ρ, st, h, H, wf => by
    simp only [symValue] at h
    exact (refuse_ok h).elim

/-! ## A statement of an effect -/

theorem Holds.setZf {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (f : Flag) (b : Bool) (hf : f.holds ρ b) : Holds ctx s0 ρ { s with zf := f } { st with zf := b } :=
  ⟨H.entry, H.reg, H.small, hf, H.cf, H.frame, H.facts, H.bytes, H.spec, H.mem⟩

theorem Holds.setCf {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (f : Flag) (b : Bool) (hf : f.holds ρ b) : Holds ctx s0 ρ { s with cf := f } { st with cf := b } :=
  ⟨H.entry, H.reg, H.small, H.zf, hf, H.frame, H.facts, H.bytes, H.spec, H.mem⟩

theorem WF.setZf {s : Sym} (wf : WF s) (f : Flag) (hb : f.bounded s.nvars) : WF { s with zf := f } :=
  ⟨wf.base, wf.reg, hb, wf.cf, wf.frame, wf.facts, wf.bytes, wf.spec⟩

theorem WF.setCf {s : Sym} (wf : WF s) (f : Flag) (hb : f.bounded s.nvars) : WF { s with cf := f } :=
  ⟨wf.base, wf.reg, wf.zf, hb, wf.frame, wf.facts, wf.bytes, wf.spec⟩

theorem Holds.put {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (r x : Nat) (xr : Row) (hx : x < M64) (hxr : (x : Int) = ev ρ xr) : Holds ctx s0 ρ (s.put r xr) (setReg st r x) where
  entry := H.entry
  reg r' hr' := by
    simp only [Sym.put, setReg]
    split
    · rw [Nat.mod_eq_of_lt hx]; exact hxr
    · exact H.reg r' hr'
  small r' := by
    simp only [setReg]
    split
    · exact Nat.mod_lt _ (by decide)
    · exact H.small r'
  zf := H.zf
  cf := H.cf
  frame := H.frame
  facts := H.facts
  bytes := H.bytes
  spec := H.spec
  mem := H.mem

theorem WF.put {s : Sym} (wf : WF s) (r : Nat) (xr : Row) (hb : bounded s.nvars xr) : WF (s.put r xr) where
  base := wf.base
  reg r' hr' := by
    simp only [Sym.put]
    split
    · exact hb
    · exact wf.reg r' hr'
  zf := wf.zf
  cf := wf.cf
  frame := wf.frame
  facts := wf.facts
  bytes := wf.bytes
  spec := wf.spec

theorem Flag.equal_holds {ρ : Nat → Int} {a b : Row} {x : Nat} (h : x = if ev ρ a = ev ρ b then 1 else 0) :
    (Flag.equal a b).holds ρ (x != 0) := by
  simp only [Flag.holds]
  by_cases e : ev ρ a = ev ρ b <;> simp [h, e]

theorem Flag.below_holds {ρ : Nat → Int} {a b : Row} {x : Nat} (h : x = if ev ρ a < ev ρ b then 1 else 0) :
    (Flag.below a b).holds ρ (x != 0) := by
  simp only [Flag.holds]
  by_cases e : ev ρ a < ev ρ b <;> simp [h, e]

/-- Eight bytes of the frame written. -/
theorem Holds.write {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (c : Int) (h1 : -(ctx.contract.stack : Int) ≤ c) (h2 : c + 8 ≤ 0)
    (a : Nat) (ha : (a : Int) = (s0.reg RSP : Int) + c) (x : Nat) (xr : Row) (hx : x < M64) (hxr : (x : Int) = ev ρ xr) :
    Holds ctx s0 ρ { s with frame := (c, xr) :: s.frame.filter fun (o, _) => decide (o + 8 ≤ c) || decide (c + 8 ≤ o) }
      { st with mem := store st.mem a x 8 } where
  entry := H.entry
  reg := H.reg
  small := H.small
  zf := H.zf
  cf := H.cf
  facts := H.facts
  bytes := H.bytes
  spec := H.spec
  frame o v m := by
    have hs := E.stack
    simp only [List.mem_cons] at m
    rcases m with heq | m
    · injection heq with e1 e2
      subst e1 e2
      refine ⟨h1, h2, ?_⟩
      have : ((s0.reg RSP : Int) + o).toNat = a := by omega
      rw [this, load_store_same _ _ _ _ (by rw [pow8]; exact hx)]
      exact hxr
    · obtain ⟨m, hk⟩ := List.mem_filter.mp m
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
      obtain ⟨g1, g2, g3⟩ := H.frame o v m
      refine ⟨g1, g2, ?_⟩
      rw [load_store_other _ _ _ _ _ _ (by omega)]
      exact g3
  mem x' hx' := by
    have hs := E.stack
    simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hx'
    show store st.mem a x 8 x' = s0.mem x'
    rw [store_other _ _ _ _ _ (by omega)]
    apply H.mem
    simp only [Contract.inFrame, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact hx'

theorem WF.write {s : Sym} (wf : WF s) (c : Int) (xr : Row) (hb : bounded s.nvars xr) :
    WF { s with frame := (c, xr) :: s.frame.filter fun (o, _) => decide (o + 8 ≤ c) || decide (c + 8 ≤ o) } where
  base := wf.base
  reg := wf.reg
  zf := wf.zf
  cf := wf.cf
  facts := wf.facts
  bytes := wf.bytes
  spec := wf.spec
  frame o v m := by
    simp only [List.mem_cons] at m
    rcases m with heq | m
    · injection heq with e1 e2; subst e2; exact hb
    · exact wf.frame o v (List.mem_filter.mp m).1

theorem values_two {perm : Perm} {bind : Bind} {st : State} {a b : Expr} {xa xb : Nat}
    (h1 : value perm bind st a = some xa) (h2 : value perm bind st b = some xb) : values perm bind st [a, b] = some [xa, xb] := by
  simp [values, h1, h2]

theorem symStmt_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) (bind : Bind) {s s' : Sym} {stmt : Stmt}
    {items rest : List Item} {ρ : Nat → Int} {st : State}
    (h : symStmt ctx bind s stmt items = .ok (s', rest)) (H : Holds ctx s0 ρ s st) (wf : WF s) (base u : Nat) :
    ∃ ρ' st', Carried ctx s0 ρ s ρ' s' st' ∧ execStmt (ctx.contract.perm s0) bind base u st stmt = some st' ∧ st'.rip = st.rip := by
  cases stmt with
  | nothing =>
    simp only [symStmt] at h
    have := V.pure_ok h
    injection this with h1 _
    subst h1
    exact ⟨ρ, st, Carried.here H wf, rfl, rfl⟩
  | ret => simp only [symStmt] at h; exact (refuse_ok h).elim
  | call t => simp only [symStmt] at h; exact (refuse_ok h).elim
  | jump t c => simp only [symStmt] at h; exact (refuse_ok h).elim
  | set place v =>
    simp only [symStmt] at h
    split at h
    next hu =>
      cases place with
      | number _ => exact (refuse_ok h).elim
      | lane _ _ => exact (refuse_ok h).elim
      | call _ _ => exact (refuse_ok h).elim
      | name n =>
        simp only at h
        split at h
        next hz =>
          have := V.pure_ok h
          injection this with h1 _
          subst h1
          exact ⟨ρ, { st with zf := u != 0 }, ⟨Agree.refl _ _, Nat.le_refl _, H.setZf .unknown _ trivial, wf.setZf .unknown trivial⟩,
            by simp [execStmt, hu, hz], rfl⟩
        next hz =>
          split at h
          next hc =>
            have := V.pure_ok h
            injection this with h1 _
            subst h1
            exact ⟨ρ, { st with cf := u != 0 }, ⟨Agree.refl _ _, Nat.le_refl _, H.setCf .unknown _ trivial, wf.setCf .unknown trivial⟩,
              by simp [execStmt, hu, hz, hc], rfl⟩
          next => exact (refuse_ok h).elim
    next hu =>
      obtain ⟨⟨ev, s1⟩, r1, e1, h⟩ := V.bind_ok h
      obtain ⟨ρ1, x, c1, vx, sx⟩ := symValue_sound E bind v e1 H wf
      cases place with
      | number _ => exact (refuse_ok h).elim
      | lane _ _ => exact (refuse_ok h).elim
      | name n =>
        simp only at h
        split at h
        next hz =>
          cases ev with
          | lin _ => exact (refuse_ok h).elim
          | equal a b =>
            have := V.pure_ok h
            injection this with h1 _
            subst h1
            exact ⟨ρ1, { st with zf := x != 0 }, ⟨c1.agree, c1.mono, c1.holds.setZf _ _ (Flag.equal_holds sx.1), c1.wf.setZf _ sx.2⟩,
              by simp [execStmt, hu, hz, vx], rfl⟩
          | below a b =>
            have := V.pure_ok h
            injection this with h1 _
            subst h1
            exact ⟨ρ1, { st with zf := x != 0 }, ⟨c1.agree, c1.mono, c1.holds.setZf _ _ (Flag.below_holds sx.1), c1.wf.setZf _ sx.2⟩,
              by simp [execStmt, hu, hz, vx], rfl⟩
        next hz =>
          split at h
          next hc =>
            cases ev with
            | lin _ => exact (refuse_ok h).elim
            | equal a b =>
              have := V.pure_ok h
              injection this with h1 _
              subst h1
              exact ⟨ρ1, { st with cf := x != 0 }, ⟨c1.agree, c1.mono, c1.holds.setCf _ _ (Flag.equal_holds sx.1), c1.wf.setCf _ sx.2⟩,
                by simp [execStmt, hu, hz, hc, vx], rfl⟩
            | below a b =>
              have := V.pure_ok h
              injection this with h1 _
              subst h1
              exact ⟨ρ1, { st with cf := x != 0 }, ⟨c1.agree, c1.mono, c1.holds.setCf _ _ (Flag.below_holds sx.1), c1.wf.setCf _ sx.2⟩,
                by simp [execStmt, hu, hz, hc, vx], rfl⟩
          next hc =>
            cases hr : regOf bind n with
            | none => simp only [hr] at h; exact (refuse_ok h).elim
            | some r =>
              cases ev with
              | equal _ _ => simp only [hr] at h; exact (refuse_ok h).elim
              | below _ _ => simp only [hr] at h; exact (refuse_ok h).elim
              | lin xr =>
                simp only [hr] at h
                have := V.pure_ok h
                injection this with h1 _
                subst h1
                exact ⟨ρ1, setReg st r x, ⟨c1.agree, c1.mono, c1.holds.put r x xr sx.1 sx.2.1, c1.wf.put r xr sx.2.2⟩,
                  by simp [execStmt, hu, hz, hc, vx, hr], rfl⟩
      | call f args =>
        cases args with
        | nil => exact (refuse_ok h).elim
        | cons a more =>
          cases more with
          | nil => exact (refuse_ok h).elim
          | cons b more2 =>
            cases more2 with
            | cons _ _ => exact (refuse_ok h).elim
            | nil =>
              simp only at h
              obtain ⟨⟨ea, s2⟩, r2, e2, h⟩ := V.bind_ok h
              obtain ⟨⟨eb, s3⟩, r3, e3, h⟩ := V.bind_ok h
              obtain ⟨ρ2, xa, c2, va, sa⟩ := symValue_sound E bind a e2 c1.holds c1.wf
              obtain ⟨ρ3, xb, c3, vb, sb⟩ := symValue_sound E bind b e3 c2.holds c2.wf
              have sx3 := EV.sem_agree (EV.sem_agree sx c2.agree c2.mono) c3.agree c3.mono
              have sa3 := EV.sem_agree sa c3.agree c3.mono
              cases ev with
              | equal _ _ => exact (refuse_ok h).elim
              | below _ _ => exact (refuse_ok h).elim
              | lin xr =>
                cases ea with
                | equal _ _ => exact (refuse_ok h).elim
                | below _ _ => exact (refuse_ok h).elim
                | lin ar =>
                  cases eb with
                  | equal _ _ => exact (refuse_ok h).elim
                  | below _ _ => exact (refuse_ok h).elim
                  | lin br =>
                    simp only at h
                    cases hl : locate ctx (Lin.add (signed ar) (signed br)) with
                    | none => simp only [hl] at h; exact (refuse_ok h).elim
                    | some w =>
                      cases w with
                      | region _ _ => simp only [hl] at h; exact (refuse_ok h).elim
                      | frame c =>
                        simp only [hl] at h
                        split at h
                        next hc =>
                          obtain ⟨hsize, hin⟩ := hc
                          have := V.pure_ok h
                          injection this with h1 _
                          subst h1
                          obtain ⟨sp, _, _, h8, hst⟩ := inFrame_spec hin
                          have hstack := E.stack
                          have habove := E.above
                          have hrsp : ρ3 RSP = s0.reg RSP := c3.holds.entry RSP (by decide)
                          have e := ev_isConst (ρ := ρ3) (locate_frame hl)
                          simp only [ev_sub, ev_add, ev_var, hrsp] at e
                          have sgx := signed_ev ρ3 ar
                          have sgy := signed_ev ρ3 br
                          have hx1 := sa3.1
                          have hy1 := sb.1
                          have hx2 := sa3.2.1
                          have hy2 := sb.2.1
                          unfold M64 at hx1 hy1 habove
                          have hadr : (((xa + xb) % M64 : Nat) : Int) = (s0.reg RSP : Int) + c := by unfold M64; omega
                          obtain ⟨_, hw, _⟩ := frame_address E hst h8 _ hadr
                          refine ⟨ρ3, { st with mem := store st.mem ((xa + xb) % M64) x 8 },
                            ⟨Agree.trans c1.mono c1.agree (Agree.trans c2.mono c2.agree c3.agree),
                             Nat.le_trans c1.mono (Nat.le_trans c2.mono c3.mono),
                             c3.holds.write E c hst h8 _ hadr x xr sx3.1 sx3.2.1, c3.wf.write c xr sx3.2.2⟩, ?_, rfl⟩
                          simp [execStmt, hu, vx, hsize, values_two va vb, sumList, hw]
                        next => exact (refuse_ok h).elim

end Ode
