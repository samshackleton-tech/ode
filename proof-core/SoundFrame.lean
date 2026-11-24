import SoundSpecW

/-! # A part of the frame as words

A word of the frame is a half of a cell: the cell's number modulo 2^32, or its quotient by 2^32. -/

namespace Ode
open Arithmetic

/-- Eight bytes are two words: the low one and 2^32 times the high one. -/
theorem load_halves (mem : Nat → Byte) (a : Nat) : load mem a 8 = load mem a 4 + 4294967296 * load mem (a + 4) 4 := by
  simp only [load, Nat.add_assoc, Nat.reduceAdd]
  omega

theorem highHalf_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st) {x q : Row}
    (h : highHalf s x = some q) : ev ρ q = ev ρ x / W32i := by
  unfold highHalf at h
  split at h
  next hk =>
    have hk' : knownNonneg s (Lin.word x) = true ∧ plain s.facts (Lin.sub (Lin.const (W32i - 1)) (Lin.word x)) = true := by simpa using hk
    injection h with h; subst h
    have h0 := knownNonneg_sound H hk'.1
    have h1 := plain_sound hk'.2 ρ H.facts
    simp only [ev_sub, ev_const] at h1
    have e := ev_high ρ x
    unfold W32i at h1 e ⊢
    omega
  next => exact highOf_sound H h

/-- A word of the frame read from a cell is the four bytes there: the atom of the row is that word. -/
theorem frameWord_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (hst : ctx.contract.stackAt s0 ≤ s0.reg RSP) {o : Int} {x : Row} (h : frameWord s o = some x) :
    -(ctx.contract.stackAt s0 : Int) ≤ o ∧ o + 4 ≤ 0 ∧
    (load st.mem ((s0.reg RSP : Int) + o).toNat 4 : Int) = ev ρ x % W32i := by
  have h4 : (256 : Nat) ^ 4 = 4294967296 := by decide
  unfold frameWord at h
  split at h
  next o' x' hf =>
    injection h with h; subst h
    have hm := List.mem_of_find?_eq_some hf
    have ho : o' = o := by have := List.find?_some hf; simpa using this
    subst ho
    obtain ⟨g1, g2, g3⟩ := H.frame _ _ hm
    refine ⟨g1, by omega, ?_⟩
    have e := load_halves st.mem ((s0.reg RSP : Int) + o').toNat
    have lt := load_lt st.mem ((s0.reg RSP : Int) + o').toNat 4
    rw [h4] at lt
    rw [e] at g3
    rw [← g3]
    unfold W32i
    omega
  next =>
    split at h
    next o' x' hf =>
      have hm := List.mem_of_find?_eq_some hf
      have ho : o' + 4 = o := by have := List.find?_some hf; simpa using this
      subst ho
      obtain ⟨g1, g2, g3⟩ := H.frame _ _ hm
      have hq := highHalf_sound H h
      refine ⟨by omega, by omega, ?_⟩
      have e := load_halves st.mem ((s0.reg RSP : Int) + o').toNat
      have lt := load_lt st.mem ((s0.reg RSP : Int) + o').toNat 4
      have lt2 := load_lt st.mem (((s0.reg RSP : Int) + o').toNat + 4) 4
      rw [h4] at lt lt2
      have ea : ((s0.reg RSP : Int) + (o' + 4)).toNat = ((s0.reg RSP : Int) + o').toNat + 4 := by omega
      rw [ea, hq, ← g3, e]
      unfold W32i
      omega
    next => cases h

/-- The words of a part of the frame, read from cells: each is the four bytes at its place. -/
theorem frameRows_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State} (H : Holds ctx s0 ρ s st)
    (hst : ctx.contract.stackAt s0 ≤ s0.reg RSP) (c : Int) :
    ∀ (count k : Nat) {rows : List Row}, frameRows s c count k = some rows →
      rows.length = count ∧ ∀ j, j < count →
        -(ctx.contract.stackAt s0 : Int) ≤ c + 4 * ((k + j : Nat) : Int) ∧ c + 4 * ((k + j : Nat) : Int) + 4 ≤ 0 ∧
        (load st.mem ((s0.reg RSP : Int) + (c + 4 * ((k + j : Nat) : Int))).toNat 4 : Int) = ev ρ (rows.getD j (Lin.const 0)) % W32i
  | 0, k, rows, h => by
    simp only [frameRows, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | count + 1, k, rows, h => by
    simp only [frameRows] at h
    cases hw : frameWord s (c + 4 * (k : Int)) with
    | none => simp [hw] at h
    | some x =>
      cases hr : frameRows s c count (k + 1) with
      | none => simp [hw, hr] at h
      | some rest =>
        simp only [hw, hr, Option.some.injEq] at h; subst h
        obtain ⟨hl, ih⟩ := frameRows_sound H hst c count (k + 1) hr
        refine ⟨by simp [hl], fun j hj => ?_⟩
        cases j with
        | zero =>
          have := frameWord_sound H hst hw
          simpa using this
        | succ j =>
          have := ih j (by omega)
          have e : ((k + 1 + j : Nat) : Int) = ((k + (j + 1) : Nat) : Int) := by omega
          rw [e] at this
          simpa using this

/-- The terms found for rows are the atoms of those rows: each is that row's number modulo 2^32. -/
theorem frameIds_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} (wf : WF ctx s) :
    ∀ (rows : List Row) {ids : List Nat}, frameIds s rows = some ids →
      ids.length = rows.length ∧ ∀ j, j < rows.length → ids.getD j 0 < s.terms.length ∧
        (den (inpOf ctx s0) ρ s.terms (ids.getD j 0) : Int) = ev ρ (rows.getD j (Lin.const 0)) % W32i
  | [], ids, h => by
    simp only [frameIds, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | x :: rest, ids, h => by
    simp only [frameIds] at h
    cases hf : s.tab.find (.atom (Lin.word x)) with
    | none => simp [hf] at h
    | some i =>
      cases hr : frameIds s rest with
      | none => simp [hf, hr] at h
      | some more =>
        simp only [hf, hr, Option.some.injEq] at h; subst h
        obtain ⟨hl, ih⟩ := frameIds_sound (ctx := ctx) (s0 := s0) (ρ := ρ) wf rest hr
        refine ⟨by simp [hl], fun j hj => ?_⟩
        cases j with
        | zero =>
          have hget : s.terms[i]? = some (Node.atom (Lin.word x)) := Looks.found (look := s.tab.find) hf
          obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hget
          have hd := den_node (inp := inpOf ctx s0) (ρ := ρ) wf.words.table hget
          have hnn : 0 ≤ ev ρ (Lin.word x) % W32i := Int.emod_nonneg _ (by unfold W32i; decide)
          refine ⟨by simpa using hi, ?_⟩
          simp only [List.getD_cons_zero]
          rw [hd]
          show (((ev ρ (Lin.word x) % W32i).toNat : Nat) : Int) = _
          rw [Int.toNat_of_nonneg hnn, ev_word]
        | succ j =>
          have := ih j (by simpa using hj)
          simpa using this

/-- The quotient by 2^32 that `highOf` finds speaks of unknowns in use. -/
theorem highOf_bounded {s : Sym} (wf : WF ctx s) {r q : Row} (hb : bounded s.nvars r) (h : highOf s r = some q) : bounded s.nvars q := by
  have dv : ∀ {q : Row}, (divided s r W32i).map Lin.var = some q → bounded s.nvars q := by
    intro q hq
    cases hd : divided s r W32i with
    | none => simp [hd] at hq
    | some v =>
      simp only [hd, Option.map_some, Option.some.injEq] at hq; subst hq
      have hk := wf.known _ (divided_known hd)
      exact bounded_var (Nat.lt_of_succ_lt hk.2)
  unfold highOf at h
  split at h
  · exact dv h
  · split at h
    · injection h with h; subst h; exact bounded_high hb
    · exact dv h

/-- A word of the frame read from a cell is a row of unknowns in use. -/
theorem frameWord_bounded {s : Sym} (wf : WF ctx s) {o : Int} {x : Row} (h : frameWord s o = some x) : bounded s.nvars x := by
  unfold frameWord at h
  split at h
  next o' x' hf =>
    injection h with h; subst h
    exact wf.frame _ _ (List.mem_of_find?_eq_some hf)
  next =>
    split at h
    next o' x' hf =>
      have hb := wf.frame _ _ (List.mem_of_find?_eq_some hf)
      unfold highHalf at h
      split at h
      · injection h with h; subst h; exact bounded_high hb
      · exact highOf_bounded wf hb h
    next => cases h

theorem frameRows_bounded {s : Sym} (wf : WF ctx s) (c : Int) :
    ∀ (count k : Nat) {rows : List Row}, frameRows s c count k = some rows → ∀ x ∈ rows, bounded s.nvars x
  | 0, k, rows, h => by
    simp only [frameRows, Option.some.injEq] at h; subst h
    intro x m; cases m
  | count + 1, k, rows, h => by
    simp only [frameRows] at h
    cases hw : frameWord s (c + 4 * (k : Int)) with
    | none => simp [hw] at h
    | some x =>
      cases hr : frameRows s c count (k + 1) with
      | none => simp [hw, hr] at h
      | some rest =>
        simp only [hw, hr, Option.some.injEq] at h; subst h
        intro y m
        rcases List.mem_cons.mp m with rfl | m
        · exact frameWord_bounded wf hw
        · exact frameRows_bounded wf c count (k + 1) hr y m

/-- A frame word term ID found by `frameWordId` lies in `s.terms`, its offset lies in the frame, and its
denotation equals the 4-byte word in memory there. -/
theorem frameWordId_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hst : ctx.contract.stackAt s0 ≤ s0.reg RSP)
    {o : Int} {id : Nat} (h : frameWordId s o = some id) :
    id < s.terms.length ∧ -(ctx.contract.stackAt s0 : Int) ≤ o ∧ o + 4 ≤ 0 ∧
      load st.mem ((s0.reg RSP : Int) + o).toNat 4 = den (inpOf ctx s0) ρ s.terms id := by
  unfold frameWordId at h
  cases hf : s.frameW.find? (fun cell => cell.1 == o) with
  | some cell =>
    simp only [hf, Option.some.injEq] at h; subst h
    have hm := List.mem_of_find?_eq_some hf
    have ho : cell.1 = o := by have := List.find?_some hf; simpa using this
    have hi := wf.frameW cell.1 cell.2 hm
    obtain ⟨g1, g2, g3⟩ := H.frameW cell.1 cell.2 hm
    rw [ho] at g1 g2 g3
    exact ⟨hi, g1, g2, g3⟩
  | none =>
    simp only [hf] at h
    cases hw : frameWord s o with
    | none => simp [hw] at h
    | some x =>
      simp only [hw, Option.bind_some] at h
      have hget : s.terms[id]? = some (Node.atom (Lin.word x)) := Looks.found (look := s.tab.find) h
      obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hget
      have hd := den_node (inp := inpOf ctx s0) (ρ := ρ) wf.words.table hget
      have hnn : 0 ≤ ev ρ (Lin.word x) % W32i := Int.emod_nonneg _ (by unfold W32i; decide)
      obtain ⟨g1, g2, g3⟩ := frameWord_sound H hst hw
      refine ⟨hi, g1, g2, ?_⟩
      rw [hd]
      show load st.mem ((s0.reg RSP : Int) + o).toNat 4 = (ev ρ (Lin.word x) % W32i).toNat
      have : ((load st.mem ((s0.reg RSP : Int) + o).toNat 4 : Nat) : Int) = ((ev ρ (Lin.word x) % W32i).toNat : Int) := by
        rw [Int.toNat_of_nonneg hnn, ev_word]; exact g3
      omega

theorem frameRunIds_sound {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) (hst : ctx.contract.stackAt s0 ≤ s0.reg RSP) (c : Int) :
    ∀ (count k : Nat) {ids : List Nat}, frameRunIds s c count k = some ids →
      ids.length = count ∧ ∀ j, j < count → ids.getD j 0 < s.terms.length ∧
        -(ctx.contract.stackAt s0 : Int) ≤ c + 4 * ((k + j : Nat) : Int) ∧
        c + 4 * ((k + j : Nat) : Int) + 4 ≤ 0 ∧
        load st.mem ((s0.reg RSP : Int) + (c + 4 * ((k + j : Nat) : Int))).toNat 4 =
          den (inpOf ctx s0) ρ s.terms (ids.getD j 0)
  | 0, k, ids, h => by
    simp only [frameRunIds, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | count + 1, k, ids, h => by
    simp only [frameRunIds] at h
    cases hw : frameWordId s (c + 4 * (k : Int)) with
    | none => simp [hw] at h
    | some id =>
      cases hr : frameRunIds s c count (k + 1) with
      | none => simp [hw, hr] at h
      | some rest =>
        simp only [hw, hr, Option.some.injEq] at h; subst h
        obtain ⟨hl, ih⟩ := frameRunIds_sound H wf hst c count (k + 1) hr
        refine ⟨by simp [hl], fun j hj => ?_⟩
        cases j with
        | zero =>
          simp only [Nat.add_zero, List.getD_cons_zero]
          exact frameWordId_sound H wf hst hw
        | succ j =>
          have hkj : k + 1 + j = k + (j + 1) := by omega
          have := ih j (by omega)
          rw [hkj] at this
          simpa [List.getD_cons_succ] using this

theorem touchFrameRange_carried {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {st : State} (c : Int) :
    ∀ (count k : Nat) {s : Sym}, Holds ctx s0 ρ s st → WF ctx s →
      Carried ctx s0 ρ s ρ { s with tab := touchFrameRange s c count k } st
  | 0, k, s, H, wf => Carried.here H wf
  | count + 1, k, s, H, wf => by
    simp only [touchFrameRange]
    cases hfw : s.frameW.find? (fun cell => cell.1 == c + 4 * (k : Int)) with
    | some _ => exact touchFrameRange_carried c count (k + 1) H wf
    | none =>
      cases hw : frameWord s (c + 4 * (k : Int)) with
      | none => exact touchFrameRange_carried c count (k + 1) H wf
      | some x =>
        obtain ⟨ext, ok, _, _⟩ := wAtom_step (inp := inpOf ctx s0) (ρ := ρ) wf.words.ok (frameWord_bounded wf hw)
        have C1 := Carried.terms H wf ext ok
        have C2 := touchFrameRange_carried c count (k + 1) C1.holds C1.wf
        exact ⟨C2.agree, C2.mono, C2.holds, C2.wf⟩

/-- Before a call, putting the frame's words into the table changes nothing the verifier holds. -/
theorem callFrameTouch_carried {ctx : Ctx} {s0 : State} {ρ : Nat → Int} {st : State} (c : Contract) :
    ∀ (runs : List (String × Nat × Nat)) {s : Sym}, Holds ctx s0 ρ s st → WF ctx s →
      Carried ctx s0 ρ s ρ (runs.foldl (fun s (x : String × Nat × Nat) =>
        match frameAt s x.2.1 with
        | some k => { s with tab := touchFrameRange s k (x.2.2 / 4) 0 }
        | none => s) s) st
  | [], s, H, wf => Carried.here H wf
  | x :: runs, s, H, wf => by
    simp only [List.foldl_cons]
    cases hf : frameAt s x.2.1 with
    | none => exact callFrameTouch_carried c runs H wf
    | some k =>
      have C1 := touchFrameRange_carried k (x.2.2 / 4) 0 H wf
      have C2 := callFrameTouch_carried c runs C1.holds C1.wf
      exact ⟨C2.agree, C2.mono, C2.holds, C2.wf⟩

/-- A part of the frame a called function is given: the register points there, the part lies in the frame
at or above the stack pointer, in whole cells, and each of its words is the term found for it. -/
theorem frameRun_sound {ctx : Ctx} {p : Program} {s0 : State} (E : Setting ctx p s0) {ρ : Nat → Int} {s : Sym} {st : State}
    (H : Holds ctx s0 ρ s st) (wf : WF ctx s) {r n : Nat} (hr : r < ctx.nreg) {c : Int} {ids : List Nat}
    (h : frameRun s r n = some (c, ids)) :
    (∃ sp, s.sp = some sp ∧ sp ≤ c) ∧ c + n ≤ 0 ∧ n % 8 = 0 ∧ (st.reg r : Int) = s0.reg RSP + c ∧ ids.length = n / 4 ∧
      ∀ j, j < n / 4 → ids.getD j 0 < s.terms.length ∧ -(ctx.contract.stackAt s0 : Int) ≤ c + 4 * (j : Int) ∧
        load st.mem (((s0.reg RSP : Int) + c).toNat + 4 * j) 4 = den (inpOf ctx s0) ρ s.terms (ids.getD j 0) := by
  unfold frameRun at h
  cases hf : frameAt s r with
  | none => simp [hf] at h
  | some c' =>
    cases hsp : s.sp with
    | none => simp [hf, hsp] at h
    | some sp =>
      simp only [hf, hsp] at h
      split at h
      next hc =>
        cases hids : frameRunIds s c' (n / 4) 0 with
        | none => simp [hids] at h
        | some ids' =>
          simp only [hids, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hl, hw⟩ := frameRunIds_sound H wf E.stackAt c' (n / 4) 0 hids
          have hreg : (st.reg r : Int) = s0.reg RSP + c' := by
            have e := ev_isConst (ρ := ρ) (show Lin.isConst (Lin.sub (s.reg r) (Lin.var RSP)) = some c' from hf)
            rw [ev_sub, ev_var] at e
            have h1 := H.reg r hr
            have h2 := H.entry RSP ctx.rsp_lt
            omega
          refine ⟨⟨sp, rfl, hc.1⟩, hc.2.1, hc.2.2, hreg, hl, fun j hj => ?_⟩
          have hwj := hw j hj
          have hw0 := hw 0 (by omega)
          simp only [Nat.zero_add] at hwj hw0
          have hs := E.stackAt
          have ea : ((s0.reg RSP : Int) + (c' + 4 * (j : Int))).toNat = ((s0.reg RSP : Int) + c').toNat + 4 * j := by
            have := hw0.2.1
            omega
          rw [ea] at hwj
          exact ⟨hwj.1, hwj.2.1, hwj.2.2.2⟩
      next => cases h

/-- Where a part of the frame lies is where its register points. -/
theorem frameRun_at {s : Sym} {r n : Nat} {c : Int} {ids : List Nat} (h : frameRun s r n = some (c, ids)) : frameAt s r = some c := by
  unfold frameRun at h
  cases hf : frameAt s r with
  | none => simp [hf] at h
  | some c' =>
    cases hsp : s.sp with
    | none => simp [hf, hsp] at h
    | some sp =>
      simp only [hf, hsp] at h
      split at h
      · cases hx : frameRunIds s c' (n / 4) 0 with
        | none => simp [hx] at h
        | some ids' => simp only [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
      · cases h

/-- Filling `count` 4-byte words of a writable frame buffer at `cw`: every missing word allocates a fresh
variable whose value equals the real 4-byte word already in memory there. Preserves all other fields of `s`. -/
theorem frameFill_sound {ctx : Ctx} {s0 : State} {st : State} (hst : ctx.contract.stackAt s0 ≤ s0.reg RSP) (cw : Int) :
    ∀ (count k : Nat) {ρ : Nat → Int} {s : Sym},
      -(ctx.contract.stackAt s0 : Int) ≤ cw + 4 * (k : Int) →
      Holds ctx s0 ρ s st → WF ctx s →
      let (ids, s') := frameFill s cw count k
      ∃ ρ', Carried ctx s0 ρ s ρ' s' st ∧ Ext s.terms s'.terms ∧
        s'.reg = s.reg ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧ s'.frame = s.frame ∧ s'.frameW = s.frameW ∧
        s'.facts = s.facts ∧ s'.bytes = s.bytes ∧ s'.spec = s.spec ∧ s'.wrote = s.wrote ∧
        s'.vec = s.vec ∧ s'.intact = s.intact ∧ s'.wroteW = s.wroteW ∧ s'.spill = s.spill ∧
        s'.known = s.known ∧ s'.range = s.range ∧
        ids.length = count ∧
        ∀ j, j < count → ids.getD j 0 < s'.terms.length ∧
          load st.mem (((s0.reg RSP : Int) + (cw + 4 * ((k + j : Nat) : Int))).toNat) 4 =
            den (inpOf ctx s0) ρ' s'.terms (ids.getD j 0)
  | 0, k, ρ, s, _, H, wf =>
    ⟨ρ, Carried.here H wf, Ext.refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | count + 1, k, ρ, s, hlo, H, wf => by
    simp only [frameFill]
    cases hw : frameWordId s (cw + 4 * (k : Int)) with
    | some id =>
      obtain ⟨hid, _, _, hmem⟩ := frameWordId_sound H wf hst hw
      obtain ⟨ρ', C, hext, hreg, hzf, hcf, hfr, hfw, hfa, hby, hsp, hwr, hvc, hin, hww, hspl, hkn, hrg, hlen, hj⟩ :=
        frameFill_sound hst cw count (k + 1) (by omega) H wf
      refine ⟨ρ', C, hext, hreg, hzf, hcf, hfr, hfw, hfa, hby, hsp, hwr, hvc, hin, hww, hspl, hkn, hrg,
        by simp [hlen], fun j hlt => ?_⟩
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getD_cons_zero]
        refine ⟨Nat.lt_of_lt_of_le hid hext.le, ?_⟩
        rw [hmem]
        have hda := den_agree (inp := inpOf ctx s0) wf.words.table
          (fun m r hr => ev_agree (wf.words.atoms m r hr) C.agree) hid
        have hde := den_ext (inp := inpOf ctx s0) (ρ := ρ') wf.words.table hext hid
        exact (hde.trans hda.symm).symm
      | succ j =>
        have hkj : k + 1 + j = k + (j + 1) := by omega
        have := hj j (by omega)
        rw [hkj] at this
        simpa [List.getD_cons_succ] using this
    | none =>
      let v := s.nvars
      let val : Nat := load st.mem ((s0.reg RSP : Int) + (cw + 4 * (k : Int))).toNat 4
      let ρ1 : Nat → Int := fun u => if u = v then (val : Int) else ρ u
      have hag1 : Agree s.nvars ρ ρ1 := fun u hu => by simp [ρ1, v, Nat.ne_of_lt hu]
      have hH1 : Holds ctx s0 ρ1 { s with nvars := v + 1 } st := by
        have hH0 := H.agree wf hag1
        exact ⟨hH0.entry, hH0.data, hH0.reg, hH0.small, hH0.zf, hH0.cf, hH0.frame, hH0.frameW,
          hH0.facts, hH0.bytes, hH0.spec, hH0.mem, hH0.wrote, hH0.words, hH0.known, hH0.range⟩
      have le : s.nvars ≤ v + 1 := Nat.le_succ _
      have hwf1 : WF ctx { s with nvars := v + 1 } :=
        ⟨Nat.le_trans wf.base le, fun r hr => bounded_mono le (wf.reg r hr),
         Flag.bounded_mono le wf.zf, Flag.bounded_mono le wf.cf,
         fun o r hm => bounded_mono le (wf.frame o r hm), wf.frameW,
         fun f hm => bounded_mono le (wf.facts f hm),
         fun r o x hm => ⟨Nat.lt_of_lt_of_le (wf.bytes r o x hm).1 le, bounded_mono le (wf.bytes r o x hm).2⟩,
         fun f hm => SFact.bounded_mono le (wf.spec f hm),
         fun w o x hm => ⟨bounded_mono le (wf.wrote w o x hm).1, bounded_mono le (wf.wrote w o x hm).2⟩,
         wf.words.mono rfl rfl rfl le,
         fun k' hm => Known.wf_mono le (Nat.le_refl _) (wf.known k' hm),
         fun rg hr => ⟨bounded_mono le (wf.range rg hr).1, fun v' hv' => SVal.bounded_mono le ((wf.range rg hr).2 v' hv')⟩⟩
      have hbv : bounded (v + 1) (Lin.var v) := bounded_var (Nat.lt_succ_self v)
      obtain ⟨hext1, hok1, hid, hden1⟩ := wAtom_step (inp := inpOf ctx s0) (ρ := ρ1) hwf1.words.ok hbv
      let s1 : Sym := { s with nvars := v + 1, tab := (wAtom (Lin.var v) s.tab).2 }
      have C1 := Carried.terms hH1 hwf1 hext1 hok1
      obtain ⟨ρ', C2, hext2, hreg, hzf, hcf, hfr, hfw, hfa, hby, hsp, hwr, hvc, hin, hww, hspl, hkn, hrg, hlen, hj⟩ :=
        frameFill_sound hst cw count (k + 1) (by omega) C1.holds C1.wf
      have hC : Carried ctx s0 ρ s ρ' (frameFill s1 cw count (k + 1)).2 st :=
        ⟨fun u hu => (hag1 u hu).trans (C2.agree u (Nat.lt_trans hu (Nat.lt_succ_self _))),
         Nat.le_trans (Nat.le_succ _) C2.mono, C2.holds, C2.wf⟩
      refine ⟨ρ', hC, hext1.trans hext2, hreg, hzf, hcf, hfr, hfw, hfa, hby, hsp, hwr, hvc, hin, hww, hspl, hkn, hrg,
        by simp only [List.length_cons]; exact congrArg (· + 1) hlen, fun j hlt => ?_⟩
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getD_cons_zero]
        refine ⟨Nat.lt_of_lt_of_le hid hext2.le, ?_⟩
        have hlt_w32 : val < W32 := by
          have := load_lt st.mem ((s0.reg RSP : Int) + (cw + 4 * (k : Int))).toNat 4
          unfold W32; omega
        have hden1' : den (inpOf ctx s0) ρ1 (wAtom (Lin.var v) s.tab).2.list (wAtom (Lin.var v) s.tab).1 = val := by
          rw [hden1, ev_var]
          simp only [ρ1, ↓reduceIte]
          rw [Int.emod_eq_of_lt (Int.natCast_nonneg val) (by unfold W32i; unfold W32 at hlt_w32; omega)]
          exact Int.toNat_natCast val
        have hda := den_agree (inp := inpOf ctx s0) C1.wf.words.table
          (fun m r hr => ev_agree (C1.wf.words.atoms m r hr) C2.agree) hid
        have hde := den_ext (inp := inpOf ctx s0) (ρ := ρ') C1.wf.words.table hext2 hid
        show val = den (inpOf ctx s0) ρ' (frameFill s1 cw count (k + 1)).2.terms (wAtom (Lin.var v) s.tab).1
        rw [hde, hda.symm]; exact hden1'.symm
      | succ j =>
        have hkj : k + 1 + j = k + (j + 1) := by omega
        have := hj j (by omega)
        rw [hkj] at this
        simpa [List.getD_cons_succ] using this

/-- Four bytes that are the bytes of a word are that word. -/
theorem load4_of_bytes (mem : Nat → Byte) (a v : Nat) (hv : v < 4294967296)
    (h : ∀ bb, bb < 4 → (mem (a + bb)).val = v / 256 ^ bb % 256) : load mem a 4 = v := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  simp only [Nat.add_zero, Nat.pow_zero, Nat.div_one, Nat.pow_one, Nat.reducePow] at h0 h1 h2 h3
  simp only [load, Nat.add_assoc, Nat.reduceAdd]
  omega

end Ode
