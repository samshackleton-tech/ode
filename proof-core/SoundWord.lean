import SoundLin
/-!
# Why the verifier's yes is right: words as terms

What a term of the verifier's table of words is (`den`): a number below nothing in particular, worked out
from the terms it is made of, which stand before it in the table. The lemmas here say that a term keeps what
it is when the table grows, and what the terms the verifier makes (`wAtom`, `wAdd`, `wXor`, `wRotr`) are.
-/
namespace Ode
open Arithmetic

/-- What a term is, the terms it is made of being what `g` says: `inp` is what the words of the runs given
to read were at entry, `ρ` the unknowns. -/
def Node.value (inp : Nat → Nat → Nat) (ρ : Nat → Int) (g : Nat → Nat) : Node → Nat
  | .atom r => (ev ρ r % W32i).toNat
  | .input j k => inp j k
  | .add xs => sumList (xs.map g) % W32
  | .xor a b => g a ^^^ g b
  | .band a b => g a &&& g b
  | .rotr a n => Ode.rotr (g a) n
  | .shl a n => (g a <<< n) % W32
  | .shr a n => g a >>> n
  | .ult a b => if g a < g b then 1 else 0
  | .sel m a b => if g m = 0 then g b else g a

def denF (inp : Nat → Nat → Nat) (ρ : Nat → Int) (T : List Node) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, i =>
    match T[i]? with
    | none => 0
    | some n => n.value inp ρ (denF inp ρ T f)

/-- What the term of number `i` is. -/
def den (inp : Nat → Nat → Nat) (ρ : Nat → Int) (T : List Node) (i : Nat) : Nat := denF inp ρ T T.length i

/-- Every term of the table is made of terms before it. -/
@[reducible] def WFT (T : List Node) : Prop := ∀ (i : Nat) (n : Node), T[i]? = some n → ∀ j ∈ n.parts, j < i

theorem Node.value_congr {inp : Nat → Nat → Nat} {ρ ρ' : Nat → Int} {g g' : Nat → Nat} (n : Node)
    (hg : ∀ j ∈ n.parts, g' j = g j) (ha : ∀ r, n = .atom r → ev ρ' r = ev ρ r) :
    n.value inp ρ' g' = n.value inp ρ g := by
  cases n with
  | atom r => simp only [Node.value, ha r rfl]
  | input j k => rfl
  | add xs =>
    simp only [Node.value]
    have : xs.map g' = xs.map g := List.map_congr_left (fun j m => hg j m)
    rw [this]
  | xor a b =>
    simp only [Node.value]
    rw [hg a (by simp [Node.parts]), hg b (by simp [Node.parts])]
  | band a b =>
    simp only [Node.value]
    rw [hg a (by simp [Node.parts]), hg b (by simp [Node.parts])]
  | rotr a k =>
    simp only [Node.value]
    rw [hg a (by simp [Node.parts])]
  | shl a k =>
    simp only [Node.value]
    rw [hg a (by simp [Node.parts])]
  | shr a k =>
    simp only [Node.value]
    rw [hg a (by simp [Node.parts])]
  | ult a b =>
    simp only [Node.value]
    rw [hg a (by simp [Node.parts]), hg b (by simp [Node.parts])]
  | sel m a b =>
    simp only [Node.value]
    rw [hg m (by simp [Node.parts]), hg a (by simp [Node.parts]), hg b (by simp [Node.parts])]

/-- Two tables alike below `m`, with unknowns under which the rows of their terms are the same numbers: a
term below `m` is the same in both, whatever more is counted. -/
theorem denF_congr {inp : Nat → Nat → Nat} {ρ ρ' : Nat → Int} {T T' : List Node} {m : Nat} (hw : WFT T)
    (hp : ∀ j, j < m → T'[j]? = T[j]?) (ha : ∀ (j : Nat) (r : Row), j < m → T[j]? = some (Node.atom r) → ev ρ' r = ev ρ r) :
    ∀ i, i < m → ∀ f f', i < f → i < f' → denF inp ρ' T' f i = denF inp ρ T f' i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi f f' hf hf'
    cases f with
    | zero => omega
    | succ f =>
      cases f' with
      | zero => omega
      | succ f' =>
        simp only [denF, hp i hi]
        cases h : T[i]? with
        | none => rfl
        | some n =>
          apply Node.value_congr
          · intro j mj
            have lt := hw i n h j mj
            exact ih j lt (by omega) f f' (by omega) (by omega)
          · intro r e
            subst e
            exact ha i r hi h

theorem den_stable {inp : Nat → Nat → Nat} {ρ : Nat → Int} {T : List Node} (hw : WFT T) {i f : Nat} (hi : i < T.length) (hf : i < f) :
    denF inp ρ T f i = den inp ρ T i :=
  denF_congr hw (fun _ _ => rfl) (fun _ _ _ _ => rfl) i hi f T.length hf hi

/-- `T'` is `T` with more terms after it. -/
structure Ext (T T' : List Node) : Prop where
  le : T.length ≤ T'.length
  same : ∀ j, j < T.length → T'[j]? = T[j]?

theorem Ext.refl (T : List Node) : Ext T T := ⟨Nat.le_refl _, fun _ _ => rfl⟩
theorem Ext.trans {T T' T'' : List Node} (a : Ext T T') (b : Ext T' T'') : Ext T T'' :=
  ⟨Nat.le_trans a.le b.le, fun j h => (b.same j (Nat.lt_of_lt_of_le h a.le)).trans (a.same j h)⟩

theorem den_ext {inp : Nat → Nat → Nat} {ρ : Nat → Int} {T T' : List Node} (hw : WFT T) (e : Ext T T') {i : Nat} (hi : i < T.length) :
    den inp ρ T' i = den inp ρ T i :=
  denF_congr hw e.same (fun _ _ _ _ => rfl) i hi T'.length T.length (Nat.lt_of_lt_of_le hi e.le) hi

/-- Other unknowns, under which the rows of the table's terms are the same numbers: every term is the same. -/
theorem den_agree {inp : Nat → Nat → Nat} {ρ ρ' : Nat → Int} {T : List Node} (hw : WFT T)
    (ha : ∀ (j : Nat) (r : Row), T[j]? = some (Node.atom r) → ev ρ' r = ev ρ r) {i : Nat} (hi : i < T.length) :
    den inp ρ' T i = den inp ρ T i :=
  denF_congr hw (fun _ _ => rfl) (fun j r _ h => ha j r h) i hi T.length T.length hi hi

/-- A term of the table is what its node says of the terms it is made of. -/
theorem den_node {inp : Nat → Nat → Nat} {ρ : Nat → Int} {T : List Node} (hw : WFT T) {i : Nat} {n : Node} (h : T[i]? = some n) :
    den inp ρ T i = n.value inp ρ (den inp ρ T) := by
  have hi : i < T.length := by
    cases Nat.lt_or_ge i T.length with
    | inl lt => exact lt
    | inr ge => rw [List.getElem?_eq_none ge] at h; cases h
  show denF inp ρ T T.length i = _
  cases hl : T.length with
  | zero => omega
  | succ L =>
    simp only [denF, h]
    apply Node.value_congr
    · intro j mj
      have lt := hw i n h j mj
      have := den_stable (inp := inp) (ρ := ρ) hw (i := j) (f := L) (by omega) (by omega)
      rw [this]
    · intro r _; rfl

/-! ## Putting a term into the table -/

/-- A way of looking a term up that is right where it finds one: the term stands at the number given. -/
class Looks (look : Node → Option Nat) (T : List Node) : Prop where
  found : ∀ {n : Node} {i : Nat}, look n = some i → T[i]? = some n

/-- The table's own index, as `Tab.find` reads it, is such a way. -/
instance Tab.find_looks (t : Tab) : Looks t.find t.list where
  found := by
    intro n i h
    unfold Tab.find at h
    split at h
    next j hj =>
      split at h
      next e => injection h with h; subst h; simpa [Tab.list] using e
      next => cases h
    next => cases h

/-- A term put into the table: it stands at the number given; what was there is there still; and where its
parts are terms of the table before, the table is still made of terms that stand after their parts. -/
theorem interned_spec {n : Node} {T T' : List Node} {i : Nat}
    (h : (T' = T ∧ T[i]? = some n) ∨ (T' = T ++ [n] ∧ i = T.length)) :
    T'[i]? = some n ∧ Ext T T' ∧ i < T'.length ∧ (WFT T → (∀ j ∈ n.parts, j < T.length) → WFT T') := by
  rcases h with ⟨e, at_⟩ | ⟨e, ei⟩
  · subst T'
    have lt : i < T.length := by
      cases Nat.lt_or_ge i T.length with
      | inl lt => exact lt
      | inr ge => rw [List.getElem?_eq_none ge] at at_; cases at_
    exact ⟨at_, Ext.refl _, lt, fun w _ => w⟩
  · subst T'; subst i
    refine ⟨by simp, ⟨by simp, fun j hj => List.getElem?_append_left hj⟩, by simp, ?_⟩
    intro w hp j m hm
    cases Nat.lt_or_ge j T.length with
    | inl lt => rw [List.getElem?_append_left lt] at hm; exact w j m hm
    | inr ge =>
      cases Nat.eq_or_lt_of_le ge with
      | inl e =>
        subst e
        simp at hm; subst hm
        exact hp
      | inr gt =>
        rw [List.getElem?_eq_none (by simp; omega)] at hm; cases hm

/-- What putting a term into the table does to the list of its terms: the list is as it was and the term
stands at the number given, or the term is at the list's end and its number is that place. (Whether the
number is the first place the term stands at is not said: the advice the table keeps is relied on for
nothing.) -/
theorem intern_list {n : Node} {t t' : Tab} {i : Nat} (h : intern n t = (i, t')) :
    (t'.list = t.list ∧ t.list[i]? = some n) ∨ (t'.list = t.list ++ [n] ∧ i = t.list.length) := by
  unfold intern at h
  split at h
  next k _ =>
    split at h
    next hat =>
      injection h with h1 h2; subst h1; subst h2
      exact Or.inl ⟨rfl, by simpa [Tab.list] using hat⟩
    next =>
      injection h with h1 h2; subst h1; subst h2
      exact Or.inr ⟨by simp [Tab.list], by simp [Tab.list]⟩
  next =>
    injection h with h1 h2; subst h1; subst h2
    exact Or.inr ⟨by simp [Tab.list], by simp [Tab.list]⟩

theorem intern_spec {n : Node} {t t' : Tab} {i : Nat} (h : intern n t = (i, t')) :
    t'.list[i]? = some n ∧ Ext t.list t'.list ∧ i < t'.list.length ∧
      (WFT t.list → (∀ j ∈ n.parts, j < t.list.length) → WFT t'.list) :=
  interned_spec (intern_list h)

/-- What a new term is: what its node says of the terms of the table before. -/
theorem intern_den {inp : Nat → Nat → Nat} {ρ : Nat → Int} {n : Node} {t t' : Tab} {i : Nat} (h : intern n t = (i, t'))
    (hw : WFT t.list) (hp : ∀ j ∈ n.parts, j < t.list.length) :
    den inp ρ t'.list i = n.value inp ρ (den inp ρ t.list) := by
  obtain ⟨at_, e, _, w⟩ := intern_spec h
  rw [den_node (w hw hp) at_]
  apply Node.value_congr
  · intro j mj; exact den_ext hw e (hp j mj)
  · intro r _; rfl

/-! ## What the verifier's terms are -/

theorem sumList_insertSorted (g : Nat → Nat) (a : Nat) : ∀ (l : List Nat), sumList ((insertSorted a l).map g) = g a + sumList (l.map g)
  | [] => rfl
  | b :: l => by
    unfold insertSorted
    split
    · rfl
    · simp only [List.map_cons, sumList]
      rw [sumList_insertSorted g a l]
      omega

theorem sumList_sorted (g : Nat → Nat) : ∀ (l : List Nat), sumList ((l.foldr insertSorted []).map g) = sumList (l.map g)
  | [] => rfl
  | a :: l => by
    simp only [List.foldr_cons, List.map_cons, sumList]
    rw [sumList_insertSorted, sumList_sorted g l]

theorem sumList_append (g : Nat → Nat) : ∀ (l l' : List Nat), sumList ((l ++ l').map g) = sumList (l.map g) + sumList (l'.map g)
  | [], l' => by simp [sumList]
  | a :: l, l' => by
    simp only [List.cons_append, List.map_cons, sumList]
    rw [sumList_append g l l']
    omega

theorem mem_insertSorted {j a : Nat} : ∀ {l : List Nat}, j ∈ insertSorted a l → j = a ∨ j ∈ l
  | [], h => by simp [insertSorted] at h; exact Or.inl h
  | b :: l, h => by
    unfold insertSorted at h
    split at h
    · simp only [List.mem_cons] at h ⊢; exact h
    · simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · rcases mem_insertSorted h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem mem_sorted {j : Nat} : ∀ {l : List Nat}, j ∈ l.foldr insertSorted [] → j ∈ l
  | [], h => by simp at h
  | a :: l, h => by
    simp only [List.foldr_cons] at h
    rcases mem_insertSorted h with h | h
    · exact h ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_sorted h)

/-- What a term is a sum of: summed and wrapped they are the term, wrapped; and they are terms of the table. -/
theorem addends_spec {inp : Nat → Nat → Nat} {ρ : Nat → Int} {t : Tab} (hw : WFT t.list) {a : Nat} (ha : a < t.list.length) :
    sumList ((addends t a).map (den inp ρ t.list)) % W32 = den inp ρ t.list a % W32 ∧ ∀ j ∈ addends t a, j < t.list.length := by
  unfold addends
  have at_list : t.arr[a]? = t.list[a]? := by simp [Tab.list]
  rw [at_list]
  generalize t.list = T at *
  cases h : T[a]? with
  | none => rw [List.getElem?_eq_none_iff] at h; omega
  | some n =>
    cases n with
    | add xs =>
      refine ⟨?_, fun j m => Nat.lt_trans (hw a _ h j m) ha⟩
      rw [den_node hw h]
      simp only [Node.value, Nat.mod_mod]
    | atom r => exact ⟨by simp [sumList], fun j m => by simp at m; omega⟩
    | input r k => exact ⟨by simp [sumList], fun j m => by simp at m; omega⟩
    | xor x y => exact ⟨by simp [sumList], fun j m => by simp at m; omega⟩
    | band x y => exact ⟨by simp [sumList], fun j m => by simp at m; omega⟩
    | rotr x k => exact ⟨by simp [sumList], fun j m => by simp at m; omega⟩
    | shl x k => exact ⟨by simp [sumList], fun j m => by simp at m; omega⟩
    | shr x k => exact ⟨by simp [sumList], fun j m => by simp at m; omega⟩
    | ult x y => exact ⟨by simp [sumList], fun j m => by simp at m; omega⟩
    | sel c x y => exact ⟨by simp [sumList], fun j m => by simp at m; omega⟩

/-- What each term the verifier makes is, the table having grown by it at most. -/
structure Made (inp : Nat → Nat → Nat) (ρ : Nat → Int) (T T' : List Node) (i : Nat) (v : Nat) : Prop where
  ext : Ext T T'
  wf : WFT T'
  lt : i < T'.length
  den : den inp ρ T' i = v

theorem made {inp : Nat → Nat → Nat} {ρ : Nat → Int} {n : Node} {t t' : Tab} {i : Nat} (h : intern n t = (i, t'))
    (hw : WFT t.list) (hp : ∀ j ∈ n.parts, j < t.list.length) : Made inp ρ t.list t'.list i (n.value inp ρ (Ode.den inp ρ t.list)) :=
  ⟨(intern_spec h).2.1, (intern_spec h).2.2.2 hw hp, (intern_spec h).2.2.1, intern_den h hw hp⟩

theorem wAdd_made {inp : Nat → Nat → Nat} {ρ : Nat → Int} {t t' : Tab} {a b i : Nat} (h : wAdd a b t = (i, t'))
    (hw : WFT t.list) (ha : a < t.list.length) (hb : b < t.list.length) :
    Made inp ρ t.list t'.list i ((den inp ρ t.list a + den inp ρ t.list b) % W32) := by
  obtain ⟨sa, la⟩ := addends_spec (inp := inp) (ρ := ρ) hw ha
  obtain ⟨sb, lb⟩ := addends_spec (inp := inp) (ρ := ρ) hw hb
  have m := made (inp := inp) (ρ := ρ) h hw (by
    intro j mj
    simp only [Node.parts] at mj
    rcases List.mem_append.mp (mem_sorted mj) with mj | mj
    · exact la j mj
    · exact lb j mj)
  refine ⟨m.ext, m.wf, m.lt, ?_⟩
  rw [m.den]
  simp only [Node.value]
  rw [sumList_sorted, sumList_append, Nat.add_mod, sa, sb, ← Nat.add_mod]

theorem wXor_made {inp : Nat → Nat → Nat} {ρ : Nat → Int} {t t' : Tab} {a b i : Nat} (h : wXor a b t = (i, t'))
    (hw : WFT t.list) (ha : a < t.list.length) (hb : b < t.list.length) :
    Made inp ρ t.list t'.list i (den inp ρ t.list a ^^^ den inp ρ t.list b) := by
  have m := made (inp := inp) (ρ := ρ) h hw (by
    intro j mj
    simp only [Node.parts, List.mem_cons, List.mem_nil_iff, or_false] at mj
    rcases mj with mj | mj <;> (rw [mj]; omega))
  refine ⟨m.ext, m.wf, m.lt, ?_⟩
  rw [m.den]
  simp only [Node.value]
  cases Nat.le_total a b with
  | inl le => rw [Nat.min_eq_left le, Nat.max_eq_right le]
  | inr le => rw [Nat.min_eq_right le, Nat.max_eq_left le, Nat.xor_comm]

theorem wAnd_made {inp : Nat → Nat → Nat} {ρ : Nat → Int} {t t' : Tab} {a b i : Nat} (h : wAnd a b t = (i, t'))
    (hw : WFT t.list) (ha : a < t.list.length) (hb : b < t.list.length) :
    Made inp ρ t.list t'.list i (den inp ρ t.list a &&& den inp ρ t.list b) := by
  have m := made (inp := inp) (ρ := ρ) h hw (by
    intro j mj
    simp only [Node.parts, List.mem_cons, List.mem_nil_iff, or_false] at mj
    rcases mj with mj | mj <;> (rw [mj]; omega))
  refine ⟨m.ext, m.wf, m.lt, ?_⟩
  rw [m.den]
  simp only [Node.value]
  cases Nat.le_total a b with
  | inl le => rw [Nat.min_eq_left le, Nat.max_eq_right le]
  | inr le => rw [Nat.min_eq_right le, Nat.max_eq_left le, Nat.and_comm]

theorem wRotr_made {inp : Nat → Nat → Nat} {ρ : Nat → Int} {t t' : Tab} {a n i : Nat} (h : wRotr a n t = (i, t'))
    (hw : WFT t.list) (ha : a < t.list.length) : Made inp ρ t.list t'.list i (rotr (den inp ρ t.list a) n) := by
  have m := made (inp := inp) (ρ := ρ) h hw (by
    intro j mj
    simp only [Node.parts, List.mem_cons, List.mem_nil_iff, or_false] at mj
    rw [mj]; exact ha)
  exact ⟨m.ext, m.wf, m.lt, m.den⟩

/-! ## A row all of whose multiples are multiples of one number -/

theorem dot_exact (m : Int) (cs : List Int) : ∀ (ρ : Nat → Int), (cs.all fun c => c % m == 0) = true →
    dot cs ρ = m * dot (cs.map (· / m)) ρ := by
  induction cs with
  | nil => intro ρ _; simp [dot]
  | cons c cs ih =>
    intro ρ h
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, dot]
    rw [ih (fun n => ρ (n + 1)) h.2, Int.mul_add]
    have e := Int.emod_add_mul_ediv c m
    rw [h.1, Int.zero_add] at e
    rw [← Int.mul_assoc, e]

theorem ev_low_exact {ρ : Nat → Int} {x : Row} {m : Int} (h : (x.coeff.all fun c => c % m == 0) = true) :
    ev ρ x % m = x.constant % m := by
  simp only [ev]
  rw [dot_exact m x.coeff ρ h, Int.add_comm, Int.add_mul_emod_self_left]

theorem ev_quot_exact {ρ : Nat → Int} {x : Row} {m : Int} (pos : 0 < m) (h : (x.coeff.all fun c => c % m == 0) = true) :
    ev ρ ⟨Lin.strip (x.coeff.map (· / m)), x.constant / m⟩ = ev ρ x / m := by
  simp only [ev, dot_strip]
  rw [dot_exact m x.coeff ρ h, Int.add_comm (m * _), Int.add_mul_ediv_left _ _ (Int.ne_of_gt pos)]
  exact Int.add_comm _ _

/-! ## A row as a word -/

theorem dot_word (cs : List Int) : ∀ (ρ : Nat → Int), dot (cs.map (· % W32i)) ρ % W32i = dot cs ρ % W32i := by
  induction cs with
  | nil => intro ρ; rfl
  | cons c cs ih =>
    intro ρ
    simp only [List.map_cons, dot]
    rw [Int.add_emod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, ih, ← Int.add_emod]

theorem ev_word (ρ : Nat → Int) (r : Row) : ev ρ (Lin.word r) % W32i = ev ρ r % W32i := by
  simp only [ev, Lin.word, dot_strip]
  rw [Int.add_emod, dot_word, Int.emod_emod, ← Int.add_emod]

theorem dot_high (cs : List Int) : ∀ (ρ : Nat → Int), dot cs ρ = dot (cs.map (· % W32i)) ρ + W32i * dot (cs.map (· / W32i)) ρ := by
  induction cs with
  | nil => intro ρ; simp [dot]
  | cons c cs ih =>
    intro ρ
    simp only [List.map_cons, dot]
    rw [ih (fun n => ρ (n + 1))]
    have e : c * ρ 0 = c % W32i * ρ 0 + W32i * (c / W32i * ρ 0) := by
      rw [← Int.mul_assoc, ← Int.add_mul, Int.emod_add_mul_ediv]
    rw [e, Int.mul_add]
    omega

/-- A row is its word and 2^32 times its high part. -/
theorem ev_high (ρ : Nat → Int) (r : Row) : ev ρ r = ev ρ (Lin.word r) + W32i * ev ρ (Lin.high r) := by
  simp only [ev, Lin.word, Lin.high, dot_strip]
  rw [dot_high r.coeff ρ, Int.mul_add]
  have := Int.emod_add_mul_ediv r.constant W32i
  omega

theorem wAtom_made {inp : Nat → Nat → Nat} {ρ : Nat → Int} {t t' : Tab} {r : Row} {i : Nat} (h : wAtom r t = (i, t'))
    (hw : WFT t.list) : Made inp ρ t.list t'.list i (ev ρ r % W32i).toNat := by
  have m := made (inp := inp) (ρ := ρ) h hw (by intro j mj; simp [Node.parts] at mj)
  refine ⟨m.ext, m.wf, m.lt, ?_⟩
  rw [m.den]
  simp only [Node.value, ev_word]

theorem rotr_lt {w n : Nat} (hw : w < W32) (hn : n ≤ 32) : Ode.rotr w n < W32 := by
  have hp : 2 ^ n * 2 ^ (32 - n) = W32 := by
    rw [← Nat.pow_add]
    have e : n + (32 - n) = 32 := by omega
    rw [e]; rfl
  have h1 : w / 2 ^ n < 2 ^ (32 - n) := by
    apply Nat.div_lt_of_lt_mul; rw [hp]; exact hw
  have h2 : w % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have h3 : (w % 2 ^ n + 1) * 2 ^ (32 - n) ≤ 2 ^ n * 2 ^ (32 - n) := Nat.mul_le_mul_right _ h2
  rw [Nat.add_mul, Nat.one_mul] at h3
  unfold Ode.rotr
  omega

theorem den_out {inp : Nat → Nat → Nat} {ρ : Nat → Int} {T : List Node} {i : Nat} (h : T[i]? = none) : den inp ρ T i = 0 := by
  unfold den
  cases T.length with
  | zero => rfl
  | succ f => simp [denF, h]

/-- Every term is a word: a number below 2^32. -/
theorem den_lt {inp : Nat → Nat → Nat} {ρ : Nat → Int} {T : List Node} (hw : WFT T) (hinp : ∀ j k, inp j k < W32)
    (hrot : ∀ (i a n : Nat), T[i]? = some (Node.rotr a n) → n ≤ 32) : ∀ i, den inp ρ T i < W32 := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    cases h : T[i]? with
    | none => rw [den_out h]; decide
    | some n =>
      rw [den_node hw h]
      cases n with
      | atom r =>
        simp only [Node.value]
        have h1 := Int.emod_lt_of_pos (ev ρ r) (show (0 : Int) < W32i by decide)
        have h2 := Int.emod_nonneg (ev ρ r) (show W32i ≠ 0 by decide)
        unfold W32i at h1 h2 ⊢
        unfold W32
        omega
      | input j k => exact hinp j k
      | add xs => exact Nat.mod_lt _ (by decide)
      | xor a b =>
        simp only [Node.value]
        exact Nat.xor_lt_two_pow (ih a (hw i _ h a (by simp [Node.parts]))) (ih b (hw i _ h b (by simp [Node.parts])))
      | band a b =>
        simp only [Node.value]
        exact Nat.lt_of_le_of_lt Nat.and_le_left (ih a (hw i _ h a (by simp [Node.parts])))
      | rotr a n => exact rotr_lt (ih a (hw i _ h a (by simp [Node.parts]))) (hrot i a n h)
      | shl a n => exact Nat.mod_lt _ (by decide)
      | shr a n => exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ih a (hw i _ h a (by simp [Node.parts])))
      | ult a b =>
        simp only [Node.value]
        split <;> decide
      | sel m a b =>
        simp only [Node.value]
        split
        · exact ih b (hw i _ h b (by simp [Node.parts]))
        · exact ih a (hw i _ h a (by simp [Node.parts]))

/-! ## Shifts, and the or of two shifts that is a turn -/

theorem wShl_made {inp : Nat → Nat → Nat} {ρ : Nat → Int} {t t' : Tab} {a n i : Nat} (h : wShl a n t = (i, t'))
    (hw : WFT t.list) (ha : a < t.list.length) : Made inp ρ t.list t'.list i ((den inp ρ t.list a <<< n) % W32) := by
  have m := made (inp := inp) (ρ := ρ) h hw (by
    intro j mj
    simp only [Node.parts, List.mem_cons, List.mem_nil_iff, or_false] at mj
    rw [mj]; exact ha)
  exact ⟨m.ext, m.wf, m.lt, m.den⟩

theorem wShr_made {inp : Nat → Nat → Nat} {ρ : Nat → Int} {t t' : Tab} {a n i : Nat} (h : wShr a n t = (i, t'))
    (hw : WFT t.list) (ha : a < t.list.length) : Made inp ρ t.list t'.list i (den inp ρ t.list a >>> n) := by
  have m := made (inp := inp) (ρ := ρ) h hw (by
    intro j mj
    simp only [Node.parts, List.mem_cons, List.mem_nil_iff, or_false] at mj
    rw [mj]; exact ha)
  exact ⟨m.ext, m.wf, m.lt, m.den⟩

/-- A word shifted left by `k` bits, or the same word shifted right by `n`, the two shifts making up 32
bits: the word turned right by `n`. -/
theorem shl_or_shr {w k n : Nat} (hw : w < W32) (hkn : k + n = 32) :
    (w <<< k) % W32 ||| w >>> n = Ode.rotr w n := by
  have full : 2 ^ n * 2 ^ k = W32 := by rw [← Nat.pow_add, show n + k = 32 by omega]; rfl
  have e1 : (w <<< k) % W32 = (w % 2 ^ n) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, ← full, Nat.mul_mod_mul_right]
  have small : w >>> n < 2 ^ k := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [full]; exact hw)
  rw [e1, ← Nat.shiftLeft_add_eq_or_of_lt small]
  unfold Ode.rotr
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, show 32 - n = k by omega, Nat.add_comm]

/-- What `orTurn` finds is so: the term it names is in the table before the two, the turn is by 32 bits at
most, and the or of the two terms is that term turned. -/
theorem orTurn_sound {inp : Nat → Nat → Nat} {ρ : Nat → Int} {T : List Node} {a b : Nat} {t : Nat × Nat} (hw : WFT T)
    (hlt : ∀ i, den inp ρ T i < W32) (h : orTurn T a b = some t) :
    t.1 < T.length ∧ t.2 ≤ 32 ∧ den inp ρ T a ||| den inp ρ T b = Ode.rotr (den inp ρ T t.1) t.2 := by
  unfold orTurn at h
  cases ha : T[a]? with
  | none => simp [ha] at h
  | some na =>
    cases hb : T[b]? with
    | none => cases na <;> simp [ha, hb] at h
    | some nb =>
      have alt : a < T.length := by
        refine Decidable.by_contra fun c => ?_
        rw [List.getElem?_eq_none_iff.mpr (by omega)] at ha; cases ha
      have blt : b < T.length := by
        refine Decidable.by_contra fun c => ?_
        rw [List.getElem?_eq_none_iff.mpr (by omega)] at hb; cases hb
      cases na with
      | shl x k =>
        cases nb with
        | shr y n =>
          simp only [ha, hb] at h
          split at h
          next hc =>
            obtain ⟨rfl, hkn, n0, k0⟩ := hc
            injection h with h; subst h
            have xlt : x < a := hw a _ ha x (by simp [Node.parts])
            refine ⟨by show x < T.length; omega, by show n ≤ 32; omega, ?_⟩
            rw [den_node hw ha, den_node hw hb]
            exact shl_or_shr (hlt x) hkn
          next => cases h
        | _ => simp [ha, hb] at h
      | shr y n =>
        cases nb with
        | shl x k =>
          simp only [ha, hb] at h
          split at h
          next hc =>
            obtain ⟨rfl, hkn, n0, k0⟩ := hc
            injection h with h; subst h
            have xlt : x < b := hw b _ hb x (by simp [Node.parts])
            refine ⟨by show x < T.length; omega, by show n ≤ 32; omega, ?_⟩
            rw [den_node hw ha, den_node hw hb, Nat.or_comm]
            exact shl_or_shr (hlt x) hkn
          next => cases h
        | _ => simp [ha, hb] at h
      | _ => simp [ha, hb] at h

end Ode
