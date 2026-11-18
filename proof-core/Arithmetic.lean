/-!
# The arithmetic rule

A verifier of proofs that some whole-number inequalities cannot all hold, and the theorem that what it
accepts is so. It searches for nothing: a prover found the rows and the steps, and is relied on for nothing.

A row says `c₀·x₀ + c₁·x₁ + … + constant ≥ 0`, the `x` standing for whole numbers (a name is its place in
the list; places past the list's end have the multiple zero).

A proof is the rows it starts from, then steps. A step `(i, a, j, b, d)`, with `a`, `b`, `d` above zero,
adds the row

    (a · row i + b · row j) / d      every multiple divided exactly by d, the constant rounded down

The last row must have every multiple zero and a constant below zero.

`refutes_sound` is the whole of what is shown here. Not covered by it: that the text of a proof is read as
written (`Main.lean`), that the compiled program does what this function does, and that the rows given are
the facts of the place where the proof is used (the caller's).
-/
namespace Ode.Arithmetic

structure Row where
  coeff : List Int
  constant : Int
  deriving Repr, DecidableEq, Inhabited

structure Step where
  i : Nat
  a : Nat
  j : Nat
  b : Nat
  d : Nat
  deriving Repr, Inhabited

/-- `x₀` is `v 0`, `x₁` is `v 1`, … -/
def dot : List Int → (Nat → Int) → Int
  | [], _ => 0
  | c :: cs, v => c * v 0 + dot cs (fun n => v (n + 1))

/-- What a row says, of the whole numbers `v`. -/
def Row.holds (v : Nat → Int) (r : Row) : Prop := 0 ≤ dot r.coeff v + r.constant

def scale (n : Int) : List Int → List Int
  | [] => []
  | c :: cs => n * c :: scale n cs

def quotient (d : Int) : List Int → List Int
  | [] => []
  | c :: cs => c / d :: quotient d cs

def sum : List Int → List Int → List Int
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: sum xs ys

def allZero : List Int → Bool
  | [] => true
  | c :: cs => c == 0 && allZero cs

def combine (a : Int) (p : Row) (b : Int) (q : Row) : Row :=
  ⟨sum (scale a p.coeff) (scale b q.coeff), a * p.constant + b * q.constant⟩

/-- The row divided by `d`, where `d` divides every multiple. -/
def divide (d : Int) (r : Row) : Option Row :=
  if scale d (quotient d r.coeff) = r.coeff then some ⟨quotient d r.coeff, r.constant / d⟩ else none

def derive (rows : Array Row) (s : Step) : Option Row :=
  match rows[s.i]?, rows[s.j]? with
  | some p, some q =>
    if s.a = 0 ∨ s.b = 0 ∨ s.d = 0 then none else divide s.d (combine s.a p s.b q)
  | _, _ => none

/-- Do the steps, from these rows, end in a row that cannot hold? -/
def verify (rows : Array Row) : List Step → Bool
  | [] => match rows[rows.size - 1]? with
    | some r => allZero r.coeff && decide (r.constant < 0)
    | none => false
  | s :: rest => match derive rows s with
    | some r => verify (rows.push r) rest
    | none => false

def among (r : Row) : List Row → Bool
  | [] => false
  | g :: gs => decide (r = g) || among r gs

def allAmong (given : List Row) : List Row → Bool
  | [] => true
  | r :: rs => among r given && allAmong given rs

/-- The verifier: every row the proof starts from is one of the rows given, and its steps end in a row
that cannot hold. -/
def refutes (given starts : List Row) (steps : List Step) : Bool :=
  allAmong given starts && verify starts.toArray steps

/-! ## Why its yes is right -/

theorem dot_scale (n : Int) (cs : List Int) (v : Nat → Int) : dot (scale n cs) v = n * dot cs v := by
  induction cs generalizing v with
  | nil => simp [scale, dot]
  | cons c cs ih => simp only [scale, dot, ih, Int.mul_add, Int.mul_assoc]

theorem dot_sum (xs ys : List Int) (v : Nat → Int) : dot (sum xs ys) v = dot xs v + dot ys v := by
  induction xs generalizing ys v with
  | nil => simp [sum, dot]
  | cons x xs ih =>
    cases ys with
    | nil => simp [sum, dot]
    | cons y ys => simp only [sum, dot, ih, Int.add_mul]; omega

theorem dot_allZero (cs : List Int) (v : Nat → Int) (h : allZero cs = true) : dot cs v = 0 := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [allZero, Bool.and_eq_true, beq_iff_eq] at h
    simp [dot, h.1, ih _ h.2]

theorem combine_holds (v : Nat → Int) (a b : Int) (p q : Row) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : p.holds v) (hq : q.holds v) : (combine a p b q).holds v := by
  unfold Row.holds at *
  have h1 := Int.mul_nonneg ha hp
  have h2 := Int.mul_nonneg hb hq
  rw [Int.mul_add] at h1 h2
  simp only [combine, dot_sum, dot_scale]
  omega

theorem divide_holds (v : Nat → Int) (d : Int) (r r' : Row) (hd : 0 < d) (hr : r.holds v)
    (h : divide d r = some r') : r'.holds v := by
  unfold divide at h
  split at h
  next exact =>
    injection h with h
    subst h
    unfold Row.holds at *
    have e : dot r.coeff v = d * dot (quotient d r.coeff) v := by rw [← dot_scale, exact]
    rw [e] at hr
    have le : -dot (quotient d r.coeff) v * d ≤ r.constant := by
      rw [Int.neg_mul, Int.mul_comm]; omega
    have := Int.le_ediv_of_mul_le hd le
    show 0 ≤ dot (quotient d r.coeff) v + r.constant / d
    omega
  next => contradiction

theorem indexed {rows : Array Row} {i : Nat} {r : Row} (h : rows[i]? = some r) : r ∈ rows.toList := by
  apply List.mem_of_getElem? (i := i)
  simpa using h

theorem derive_holds (v : Nat → Int) (rows : Array Row) (s : Step) (r : Row)
    (valid : ∀ p ∈ rows.toList, p.holds v) (h : derive rows s = some r) : r.holds v := by
  unfold derive at h
  split at h
  next p q hp hq =>
    split at h
    next => contradiction
    next nz =>
      have hc := combine_holds v s.a s.b p q (Int.natCast_nonneg _) (Int.natCast_nonneg _)
        (valid p (indexed hp)) (valid q (indexed hq))
      exact divide_holds v s.d _ r (by omega) hc h
  next => contradiction

theorem verify_sound (v : Nat → Int) (steps : List Step) (rows : Array Row)
    (valid : ∀ r ∈ rows.toList, r.holds v) (h : verify rows steps = true) : False := by
  induction steps generalizing rows with
  | nil =>
    unfold verify at h
    split at h
    next r hr =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have hv := valid r (indexed hr)
      unfold Row.holds at hv
      rw [dot_allZero _ _ h.1] at hv
      omega
    next => contradiction
  | cons s rest ih =>
    unfold verify at h
    split at h
    next r hr =>
      apply ih (rows.push r) _ h
      intro p hp
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
      cases hp with
      | inl old => exact valid p old
      | inr new => rw [new]; exact derive_holds v rows s r valid hr
    next => contradiction

theorem among_mem (r : Row) (given : List Row) (h : among r given = true) : r ∈ given := by
  induction given with
  | nil => contradiction
  | cons g gs ih =>
    simp only [among, Bool.or_eq_true, decide_eq_true_eq] at h
    cases h with
    | inl e => rw [e]; exact List.mem_cons_self ..
    | inr e => exact List.mem_cons_of_mem _ (ih e)

theorem allAmong_mem (given starts : List Row) (h : allAmong given starts = true) :
    ∀ r ∈ starts, r ∈ given := by
  induction starts with
  | nil => intro r hr; contradiction
  | cons s ss ih =>
    simp only [allAmong, Bool.and_eq_true] at h
    intro r hr
    cases hr with
    | head => exact among_mem _ _ h.1
    | tail _ hr => exact ih h.2 r hr

/-- Whatever the proof is: if the verifier says yes, no whole numbers make every row given hold. -/
theorem refutes_sound (given starts : List Row) (steps : List Step)
    (h : refutes given starts steps = true) (v : Nat → Int) : ¬ ∀ r ∈ given, r.holds v := by
  intro all
  simp only [refutes, Bool.and_eq_true] at h
  apply verify_sound v steps starts.toArray _ h.2
  intro r hr
  exact all r (allAmong_mem given starts h.1 r (by simpa using hr))

end Ode.Arithmetic
