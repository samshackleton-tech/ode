import Contract
/-!
# Why the verifier's yes is right, 2b: a value of the specification as one number

The verifier may give a use of a definition a number of its own, without working the use out (`Known.use` of
Core.lean): the called function's contract says the use has a value, and the verifier follows the use by its
number. In the proofs the unknown of that number stands for the value. An unknown is a whole number, so here
every value of the specification is given a number of its own (`Val.code`), and a number is read back as the
value it is the number of (`Val.decode`). Nothing here is run: it is used in the soundness proofs alone.
-/

namespace Ode

/-- Two numbers as one, above zero: `2^a * (2 * b + 1)`. -/
def pair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

theorem pair_zero (b : Nat) : pair 0 b = 2 * b + 1 := by simp [pair]

theorem pair_succ (a b : Nat) : pair (a + 1) b = 2 * pair a b := by
  rw [pair, pair, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]

theorem pair_pos (a b : Nat) : 0 < pair a b := by
  induction a with
  | zero => rw [pair_zero]; omega
  | succ a ih => rw [pair_succ]; omega

/-- The two numbers can be read back. -/
theorem pair_inj {a b c d : Nat} (h : pair a b = pair c d) : a = c ∧ b = d := by
  induction a generalizing c with
  | zero =>
    cases c with
    | zero => rw [pair_zero, pair_zero] at h; exact ⟨rfl, by omega⟩
    | succ c => rw [pair_zero, pair_succ] at h; omega
  | succ a ih =>
    cases c with
    | zero => rw [pair_zero, pair_succ] at h; omega
    | succ c =>
      rw [pair_succ, pair_succ] at h
      obtain ⟨rfl, rfl⟩ := ih (c := c) (by omega)
      exact ⟨rfl, rfl⟩

/-- A whole number as a number not below zero. -/
def codeInt (n : Int) : Nat := if 0 ≤ n then 2 * n.toNat else 2 * (-n).toNat + 1

theorem codeInt_inj {a b : Int} (h : codeInt a = codeInt b) : a = b := by
  unfold codeInt at h
  split at h <;> split at h <;> omega

/-- A name as a number. -/
def codeChars : List Char → Nat
  | [] => 0
  | c :: rest => pair c.toNat (codeChars rest)

theorem codeChars_inj : ∀ {a b : List Char}, codeChars a = codeChars b → a = b
  | [], [], _ => rfl
  | [], d :: r', h => by
    have := pair_pos d.toNat (codeChars r')
    simp only [codeChars] at h; omega
  | c :: r, [], h => by
    have := pair_pos c.toNat (codeChars r)
    simp only [codeChars] at h; omega
  | c :: r, d :: r', h => by
    simp only [codeChars] at h
    obtain ⟨h1, h2⟩ := pair_inj h
    rw [Char.toNat_inj.mp h1, codeChars_inj h2]

/-- The number of a value: the kind of thing it is, and the number of what it holds. A list is 0 where it
is empty, else its first thing's number and the rest's. -/
noncomputable def Val.code : Val → Nat :=
  @Val.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun n => pair 0 (codeInt n)) (fun b => pair 1 (if b then 1 else 0)) (fun w => pair 2 w) (fun n => pair 3 n)
    (fun _ cl => pair 4 cl) (fun _ cf => pair 5 cf)
    0 (fun _ _ ch ct => pair ch ct)
    0 (fun _ _ ch ct => pair ch ct)
    (fun x _ cv => pair (codeChars x.toList) cv)

/-- The number of a list of values. -/
noncomputable def codeVals : List Val → Nat :=
  @Val.rec_1 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun n => pair 0 (codeInt n)) (fun b => pair 1 (if b then 1 else 0)) (fun w => pair 2 w) (fun n => pair 3 n)
    (fun _ cl => pair 4 cl) (fun _ cf => pair 5 cf)
    0 (fun _ _ ch ct => pair ch ct)
    0 (fun _ _ ch ct => pair ch ct)
    (fun x _ cv => pair (codeChars x.toList) cv)

/-- The number of a record's names with their things. -/
noncomputable def codeFields : List (String × Val) → Nat :=
  @Val.rec_2 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun n => pair 0 (codeInt n)) (fun b => pair 1 (if b then 1 else 0)) (fun w => pair 2 w) (fun n => pair 3 n)
    (fun _ cl => pair 4 cl) (fun _ cf => pair 5 cf)
    0 (fun _ _ ch ct => pair ch ct)
    0 (fun _ _ ch ct => pair ch ct)
    (fun x _ cv => pair (codeChars x.toList) cv)

/-- The number of a name with its thing. -/
noncomputable def codeField : String × Val → Nat :=
  @Val.rec_3 (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) (fun _ => Nat)
    (fun n => pair 0 (codeInt n)) (fun b => pair 1 (if b then 1 else 0)) (fun w => pair 2 w) (fun n => pair 3 n)
    (fun _ cl => pair 4 cl) (fun _ cf => pair 5 cf)
    0 (fun _ _ ch ct => pair ch ct)
    0 (fun _ _ ch ct => pair ch ct)
    (fun x _ cv => pair (codeChars x.toList) cv)

theorem Val.code_int (n : Int) : (Val.int n).code = pair 0 (codeInt n) := rfl
theorem Val.code_bool (b : Bool) : (Val.bool b).code = pair 1 (if b then 1 else 0) := rfl
theorem Val.code_word (w : Nat) : (Val.word w).code = pair 2 w := rfl
theorem Val.code_counter (n : Nat) : (Val.counter n).code = pair 3 n := rfl
theorem Val.code_list (l : List Val) : (Val.list l).code = pair 4 (codeVals l) := rfl
theorem Val.code_record (fs : List (String × Val)) : (Val.record fs).code = pair 5 (codeFields fs) := rfl
theorem codeVals_nil : codeVals [] = 0 := rfl
theorem codeVals_cons (v : Val) (rest : List Val) : codeVals (v :: rest) = pair v.code (codeVals rest) := rfl
theorem codeFields_nil : codeFields [] = 0 := rfl
theorem codeFields_cons (f : String × Val) (rest : List (String × Val)) : codeFields (f :: rest) = pair (codeField f) (codeFields rest) := rfl
theorem codeField_mk (x : String) (v : Val) : codeField (x, v) = pair (codeChars x.toList) v.code := rfl

set_option linter.unusedSimpArgs false in
/-- No two values have one number. -/
theorem Val.code_inj (a : Val) : ∀ b : Val, a.code = b.code → a = b := by
  refine @Val.rec (fun a => ∀ b : Val, a.code = b.code → a = b)
    (fun l => ∀ l' : List Val, codeVals l = codeVals l' → l = l')
    (fun fs => ∀ fs' : List (String × Val), codeFields fs = codeFields fs' → fs = fs')
    (fun f => ∀ f' : String × Val, codeField f = codeField f' → f = f')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a
  · intro n b h
    cases b with
    | int m =>
      simp only [Val.code_int] at h
      have h2 := (pair_inj h).2
      rw [codeInt_inj h2]
    | _ =>
      simp only [Val.code_int, Val.code_bool, Val.code_word, Val.code_counter, Val.code_list, Val.code_record] at h
      exact absurd (pair_inj h).1 (by decide)
  · intro x b h
    cases b with
    | bool y =>
      simp only [Val.code_bool] at h
      have h2 := (pair_inj h).2
      cases x <;> cases y <;> first | rfl | exact absurd h2 (by decide)
    | _ =>
      simp only [Val.code_int, Val.code_bool, Val.code_word, Val.code_counter, Val.code_list, Val.code_record] at h
      exact absurd (pair_inj h).1 (by decide)
  · intro w b h
    cases b with
    | word w' =>
      simp only [Val.code_word] at h
      have h2 := (pair_inj h).2
      rw [h2]
    | _ =>
      simp only [Val.code_int, Val.code_bool, Val.code_word, Val.code_counter, Val.code_list, Val.code_record] at h
      exact absurd (pair_inj h).1 (by decide)
  · intro n b h
    cases b with
    | counter m =>
      simp only [Val.code_counter] at h
      have h2 := (pair_inj h).2
      rw [h2]
    | _ =>
      simp only [Val.code_int, Val.code_bool, Val.code_word, Val.code_counter, Val.code_list, Val.code_record] at h
      exact absurd (pair_inj h).1 (by decide)
  · intro l ih b h
    cases b with
    | list l' =>
      simp only [Val.code_list] at h
      have h2 := (pair_inj h).2
      rw [ih _ h2]
    | _ =>
      simp only [Val.code_int, Val.code_bool, Val.code_word, Val.code_counter, Val.code_list, Val.code_record] at h
      exact absurd (pair_inj h).1 (by decide)
  · intro fs ih b h
    cases b with
    | record fs' =>
      simp only [Val.code_record] at h
      have h2 := (pair_inj h).2
      rw [ih _ h2]
    | _ =>
      simp only [Val.code_int, Val.code_bool, Val.code_word, Val.code_counter, Val.code_list, Val.code_record] at h
      exact absurd (pair_inj h).1 (by decide)
  · intro l' h
    cases l' with
    | nil => rfl
    | cons v rest =>
      have := pair_pos v.code (codeVals rest)
      rw [codeVals_nil, codeVals_cons] at h; omega
  · intro v rest ihv ihr l' h
    cases l' with
    | nil =>
      have := pair_pos v.code (codeVals rest)
      rw [codeVals_nil, codeVals_cons] at h; omega
    | cons v' rest' =>
      rw [codeVals_cons, codeVals_cons] at h
      obtain ⟨h1, h2⟩ := pair_inj h
      rw [ihv _ h1, ihr _ h2]
  · intro fs' h
    cases fs' with
    | nil => rfl
    | cons f rest =>
      have := pair_pos (codeField f) (codeFields rest)
      rw [codeFields_nil, codeFields_cons] at h; omega
  · intro f rest ihf ihr fs' h
    cases fs' with
    | nil =>
      have := pair_pos (codeField f) (codeFields rest)
      rw [codeFields_nil, codeFields_cons] at h; omega
    | cons f' rest' =>
      rw [codeFields_cons, codeFields_cons] at h
      obtain ⟨h1, h2⟩ := pair_inj h
      rw [ihf _ h1, ihr _ h2]
  · intro x v ihv f' h
    obtain ⟨x', v'⟩ := f'
    rw [codeField_mk, codeField_mk] at h
    obtain ⟨h1, h2⟩ := pair_inj h
    rw [String.toList_inj.mp (codeChars_inj h1), ihv _ h2]

/-- The value a number is the number of (a number of no value: some value). -/
noncomputable def Val.decode (n : Nat) : Val := Classical.epsilon fun v : Val => v.code = n

theorem Val.decode_code (v : Val) : Val.decode v.code = v :=
  Val.code_inj _ _ (Classical.epsilon_spec (p := fun w : Val => w.code = v.code) ⟨v, rfl⟩)

end Ode
