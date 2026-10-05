import Mathlib

/-!
# Conjecture 00000005402 (Moebius divisor recursion): a disproof

The conjecture: the Moebius conversion recovering the primitive (exactly periodic) orbit counts
from the counts of all periodic orbits is, at low order, an explicit divisor-sum recursion whose
coefficients are the integers `μ(d) * d`; its matrix is triangular with diagonal `1`; and the
inverse (cumulative) conversion has nonnegative coefficients.

We refute the first clause (hence the conjunction) for finite dynamical systems `f : β → β`
(`β` a finite type), at order `n = 2`, under three readings of the counts:

* (R1) total = `perPts f n = #{x | f^[n] x = x}` (periodic points of period `n`),
  primitive = `primOrbits f n` (number of periodic orbits of least period `n`);
* (R2) total = `perPts`, primitive = `exactPts f n = #{x | minimalPeriod f x = n}`;
* (R3) total = `divOrbits f n` (number of periodic orbits whose length divides `n`),
  primitive = `primOrbits`.

Orbits are Mathlib's `Function.periodicOrbit` cycles. We also treat the cumulative variants
R1', R2', R3' in which the total count is an ordinary partial sum over least periods `≤ n`
(`cumPts`, `cumOrbits`). Convention: Mathlib's `minimalPeriod f x` is `0` when `x` is not periodic.

The witness is the permutation `(0)(1)(2 3)` of `Fin 4`. In addition we prove that under R1 no
order-2 divisor-sum conversion with integer coefficients exists, and that under R2 and R3 the
order-2 coefficients are forced to be `1` and `-1 = μ(2)`, so `μ(2) * 2 = -2` fits in neither slot.
-/

open Function Finset

namespace C5402

section Counts

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Number of periodic points of period `n`: `#{x | f^[n] x = x}`. -/
noncomputable def perPts (f : β → β) (n : ℕ) : ℕ :=
  (univ.filter fun x => IsPeriodicPt f n x).card

/-- Number of points of least period `n`: `#{x | minimalPeriod f x = n}`. -/
noncomputable def exactPts (f : β → β) (n : ℕ) : ℕ :=
  (univ.filter fun x => minimalPeriod f x = n).card

/-- Number of primitive periodic orbits of length `n`: the distinct orbits
`periodicOrbit f x` of the points `x` of least period `n`. -/
noncomputable def primOrbits (f : β → β) (n : ℕ) : ℕ :=
  ((univ.filter fun x => minimalPeriod f x = n).image (periodicOrbit f)).card

/-- Number of periodic orbits whose length divides `n` (for `n ≥ 1`): the distinct orbits of the
points `x` with `f^[n] x = x`. -/
noncomputable def divOrbits (f : β → β) (n : ℕ) : ℕ :=
  ((univ.filter fun x => IsPeriodicPt f n x).image (periodicOrbit f)).card

/-- Cumulative count of points: `#{x | 1 ≤ minimalPeriod f x ≤ n}` (periodic points of least
period at most `n`, i.e. the ordinary partial sums of `exactPts`). -/
noncomputable def cumPts (f : β → β) (n : ℕ) : ℕ :=
  (univ.filter fun x => 1 ≤ minimalPeriod f x ∧ minimalPeriod f x ≤ n).card

/-- Cumulative count of orbits: number of periodic orbits of length at most `n` (the ordinary
partial sums of `primOrbits`). -/
noncomputable def cumOrbits (f : β → β) (n : ℕ) : ℕ :=
  ((univ.filter fun x => 1 ≤ minimalPeriod f x ∧ minimalPeriod f x ≤ n).image
    (periodicOrbit f)).card

/-- At orders `1` and `2`, "period divides `n`" and "least period at most `n`" coincide. -/
lemma filter_per_eq_cum (f : β → β) {n : ℕ} (hn : n = 1 ∨ n = 2) :
    (univ.filter fun x => IsPeriodicPt f n x) =
      univ.filter fun x => 1 ≤ minimalPeriod f x ∧ minimalPeriod f x ≤ n := by
  ext x
  simp only [mem_filter, mem_univ, true_and]
  rw [isPeriodicPt_iff_minimalPeriod_dvd]
  rcases hn with rfl | rfl
  · rw [Nat.dvd_one]; omega
  · rw [Nat.dvd_prime Nat.prime_two]; omega

lemma perPts_eq_cumPts (f : β → β) {n : ℕ} (hn : n = 1 ∨ n = 2) : perPts f n = cumPts f n := by
  unfold perPts cumPts; rw [filter_per_eq_cum f hn]

lemma divOrbits_eq_cumOrbits (f : β → β) {n : ℕ} (hn : n = 1 ∨ n = 2) :
    divOrbits f n = cumOrbits f n := by
  unfold divOrbits cumOrbits; rw [filter_per_eq_cum f hn]

end Counts

/-- The conjectured divisor-sum conversion with coefficients `μ(d) * d`:
`H(a)(n) = ∑_{d ∣ n} μ(d) * d * a(n / d)` (its diagonal coefficient, `d = 1`, is `1`). -/
def muDConv (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) * d * a (n / d)

/-- The first clause of the conjecture for a choice `T` of total counts and `B` of primitive
counts: for every finite dynamical system and every order `1 ≤ n ≤ N`,
`B f n = ∑_{d ∣ n} μ(d) * d * T f (n / d)`. -/
def ConjecturedConversion (T B : ∀ {β : Type} [Fintype β] [DecidableEq β], (β → β) → ℕ → ℕ)
    (N : ℕ) : Prop :=
  ∀ (β : Type) [Fintype β] [DecidableEq β] (f : β → β) (n : ℕ), 1 ≤ n → n ≤ N →
    (B f n : ℤ) = muDConv (fun k => (T f k : ℤ)) n

lemma muDConv_two (a : ℕ → ℤ) : muDConv a 2 = a 2 - 2 * a 1 := by
  have h : Nat.divisors 2 = {1, 2} := by decide
  rw [muDConv, h, Finset.sum_pair (by norm_num)]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

/-! ### Involutions: least periods and orbits -/

section Invol

variable {β : Type*} [DecidableEq β] {f : β → β}

lemma minimalPeriod_invol (hf : ∀ x, f (f x) = x) (x : β) :
    minimalPeriod f x = if f x = x then 1 else 2 := by
  split_ifs with h
  · exact minimalPeriod_eq_one_iff_isFixedPt.mpr h
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact minimalPeriod_eq_prime (show f (f x) = x from hf x) h

lemma periodicOrbit_invol (hf : ∀ x, f (f x) = x) (x : β) :
    periodicOrbit f x =
      if f x = x then (([x] : List β) : Cycle β) else (([x, f x] : List β) : Cycle β) := by
  rw [periodicOrbit_def, minimalPeriod_invol hf]
  split_ifs <;> rfl

variable [Fintype β]

lemma exactPts_invol (hf : ∀ x, f (f x) = x) (n : ℕ) :
    exactPts f n = (univ.filter fun x => (if f x = x then 1 else 2) = n).card := by
  simp only [exactPts, minimalPeriod_invol hf]

lemma primOrbits_invol (hf : ∀ x, f (f x) = x) (n : ℕ) :
    primOrbits f n = ((univ.filter fun x => (if f x = x then 1 else 2) = n).image
      (fun x => if f x = x then (([x] : List β) : Cycle β) else (([x, f x] : List β) : Cycle β))).card := by
  simp only [primOrbits, minimalPeriod_invol hf]
  congr 2
  exact funext (periodicOrbit_invol hf)

lemma divOrbits_invol (hf : ∀ x, f (f x) = x) (n : ℕ) :
    divOrbits f n = ((univ.filter fun x => IsPeriodicPt f n x).image
      (fun x => if f x = x then (([x] : List β) : Cycle β) else (([x, f x] : List β) : Cycle β))).card := by
  simp only [divOrbits]
  congr 2
  exact funext (periodicOrbit_invol hf)

end Invol

/-! ### The non-degenerate witness: two fixed points and one 2-cycle on `Fin 4` -/

/-- The permutation `(0)(1)(2 3)` of `Fin 4`. -/
def g : Fin 4 → Fin 4 := ![0, 1, 3, 2]

lemma g_invol : ∀ x, g (g x) = x := by decide

lemma g_perPts_one : perPts g 1 = 2 := by unfold perPts; decide
lemma g_perPts_two : perPts g 2 = 4 := by unfold perPts; decide
lemma g_exactPts_two : exactPts g 2 = 2 := by rw [exactPts_invol g_invol]; decide
lemma g_primOrbits_two : primOrbits g 2 = 1 := by rw [primOrbits_invol g_invol]; decide
lemma g_divOrbits_one : divOrbits g 1 = 2 := by rw [divOrbits_invol g_invol]; decide
lemma g_divOrbits_two : divOrbits g 2 = 3 := by rw [divOrbits_invol g_invol]; decide

/-- The `μ(d)·d` conversion fails at order `2` on the permutation `(0)(1)(2 3)` under all three
readings R1, R2, R3: it predicts `0`, `0`, `-1` where the true values are `1`, `2`, `1`. -/
theorem g_counterexample :
    (primOrbits g 2 : ℤ) ≠ muDConv (fun k => (perPts g k : ℤ)) 2 ∧
    (exactPts g 2 : ℤ) ≠ muDConv (fun k => (perPts g k : ℤ)) 2 ∧
    (primOrbits g 2 : ℤ) ≠ muDConv (fun k => (divOrbits g k : ℤ)) 2 := by
  simp only [muDConv_two, g_perPts_one, g_perPts_two, g_exactPts_two, g_primOrbits_two,
    g_divOrbits_one, g_divOrbits_two]
  norm_num

lemma muDConv_cumPts_g : muDConv (fun k => (cumPts g k : ℤ)) 2 = muDConv (fun k => (perPts g k : ℤ)) 2 := by
  simp only [muDConv_two, perPts_eq_cumPts g (n := 1) (by norm_num),
    perPts_eq_cumPts g (n := 2) (by norm_num)]

lemma muDConv_cumOrbits_g :
    muDConv (fun k => (cumOrbits g k : ℤ)) 2 = muDConv (fun k => (divOrbits g k : ℤ)) 2 := by
  simp only [muDConv_two, divOrbits_eq_cumOrbits g (n := 1) (by norm_num),
    divOrbits_eq_cumOrbits g (n := 2) (by norm_num)]

/-- **Main theorem.** For every `N ≥ 2`, the conjectured `μ(d)·d` divisor-sum conversion from
total to primitive counts fails under readings R1, R2, R3, and under their cumulative
(ordinary partial-sum) variants R1', R2', R3' in which the total count is `cumPts` / `cumOrbits`. -/
theorem conjecture_5402_false (N : ℕ) (hN : 2 ≤ N) :
    ¬ ConjecturedConversion perPts primOrbits N ∧
    ¬ ConjecturedConversion perPts exactPts N ∧
    ¬ ConjecturedConversion divOrbits primOrbits N ∧
    ¬ ConjecturedConversion cumPts primOrbits N ∧
    ¬ ConjecturedConversion cumPts exactPts N ∧
    ¬ ConjecturedConversion cumOrbits primOrbits N := by
  obtain ⟨h1, h2, h3⟩ := g_counterexample
  refine ⟨fun h => h1 (h (Fin 4) g 2 (by norm_num) hN),
    fun h => h2 (h (Fin 4) g 2 (by norm_num) hN),
    fun h => h3 (h (Fin 4) g 2 (by norm_num) hN), fun h => h1 ?_, fun h => h2 ?_, fun h => h3 ?_⟩
  · rw [← muDConv_cumPts_g]; exact h (Fin 4) g 2 (by norm_num) hN
  · rw [← muDConv_cumPts_g]; exact h (Fin 4) g 2 (by norm_num) hN
  · rw [← muDConv_cumOrbits_g]; exact h (Fin 4) g 2 (by norm_num) hN

/-! ### The order-2 coefficients are forced (so no placement of `μ(d)·d` can work)

Two further systems: the identity of `Unit` and the swap `not` of `Bool`. -/

lemma unit_perPts (n : ℕ) : perPts (id : Unit → Unit) n = 1 := by
  have h : ∀ x : Unit, IsPeriodicPt id n x := fun _ => Subsingleton.elim _ _
  simp [perPts, h]
lemma unit_exactPts_two : exactPts (id : Unit → Unit) 2 = 0 := by
  rw [exactPts_invol (fun _ => rfl)]; decide
lemma unit_primOrbits_two : primOrbits (id : Unit → Unit) 2 = 0 := by
  rw [primOrbits_invol (fun _ => rfl)]; decide
lemma unit_divOrbits (n : ℕ) : divOrbits (id : Unit → Unit) n = 1 := by
  have h : ∀ x : Unit, IsPeriodicPt id n x := fun _ => Subsingleton.elim _ _
  simp [divOrbits, h, Finset.univ_unique]

lemma not_invol : ∀ b, (!(!b)) = b := Bool.not_not
lemma bool_perPts_one : perPts (not : Bool → Bool) 1 = 0 := by unfold perPts; decide
lemma bool_perPts_two : perPts (not : Bool → Bool) 2 = 2 := by unfold perPts; decide
lemma bool_exactPts_two : exactPts (not : Bool → Bool) 2 = 2 := by
  rw [exactPts_invol not_invol]; decide
lemma bool_primOrbits_two : primOrbits (not : Bool → Bool) 2 = 1 := by
  rw [primOrbits_invol not_invol]; decide
lemma bool_divOrbits_one : divOrbits (not : Bool → Bool) 1 = 0 := by
  rw [divOrbits_invol not_invol]; decide
lemma bool_divOrbits_two : divOrbits (not : Bool → Bool) 2 = 1 := by
  rw [divOrbits_invol not_invol]; decide

/-- R1: no order-2 conversion `B_2 = x * T_2 + y * T_1` with integer coefficients exists at all. -/
theorem R1_no_integer_conversion :
    ¬ ∃ x y : ℤ, ∀ (β : Type) [Fintype β] [DecidableEq β] (f : β → β),
      (primOrbits f 2 : ℤ) = x * perPts f 2 + y * perPts f 1 := by
  rintro ⟨x, y, h⟩
  have h1 := h Unit id
  have h2 := h Bool not
  rw [unit_primOrbits_two, unit_perPts, unit_perPts] at h1
  rw [bool_primOrbits_two, bool_perPts_one, bool_perPts_two] at h2
  push_cast at h1 h2
  omega

/-- R2: any order-2 conversion `B_2 = x * T_2 + y * T_1` has `x = 1` and `y = -1 = μ(2)`. -/
theorem R2_coefficients_forced (x y : ℤ)
    (h : ∀ (β : Type) [Fintype β] [DecidableEq β] (f : β → β),
      (exactPts f 2 : ℤ) = x * perPts f 2 + y * perPts f 1) : x = 1 ∧ y = -1 := by
  have h1 := h Unit id
  have h2 := h Bool not
  rw [unit_exactPts_two, unit_perPts, unit_perPts] at h1
  rw [bool_exactPts_two, bool_perPts_one, bool_perPts_two] at h2
  push_cast at h1 h2
  omega

/-- R3: any order-2 conversion `B_2 = x * T_2 + y * T_1` has `x = 1` and `y = -1 = μ(2)`. -/
theorem R3_coefficients_forced (x y : ℤ)
    (h : ∀ (β : Type) [Fintype β] [DecidableEq β] (f : β → β),
      (primOrbits f 2 : ℤ) = x * divOrbits f 2 + y * divOrbits f 1) : x = 1 ∧ y = -1 := by
  have h1 := h Unit id
  have h2 := h Bool not
  rw [unit_primOrbits_two, unit_divOrbits, unit_divOrbits] at h1
  rw [bool_primOrbits_two, bool_divOrbits_one, bool_divOrbits_two] at h2
  push_cast at h1 h2
  omega

/-- The order-2 coefficients `μ(1)·1 = 1` and `μ(2)·2 = -2` of the conjecture. Whichever of the two
slots receives `μ(2)·2`, the resulting order-2 conversion is not valid under R1, R2 or R3. -/
theorem no_placement_of_muD :
    ∀ x y : ℤ, ({x, y} : Finset ℤ) = {(ArithmeticFunction.moebius 1 : ℤ) * 1,
        (ArithmeticFunction.moebius 2 : ℤ) * 2} →
      (¬ ∀ (β : Type) [Fintype β] [DecidableEq β] (f : β → β),
          (primOrbits f 2 : ℤ) = x * perPts f 2 + y * perPts f 1) ∧
      (¬ ∀ (β : Type) [Fintype β] [DecidableEq β] (f : β → β),
          (exactPts f 2 : ℤ) = x * perPts f 2 + y * perPts f 1) ∧
      (¬ ∀ (β : Type) [Fintype β] [DecidableEq β] (f : β → β),
          (primOrbits f 2 : ℤ) = x * divOrbits f 2 + y * divOrbits f 1) := by
  intro x y hxy
  have hm : ({x, y} : Finset ℤ) = {1, -2} := by
    rw [hxy]; simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have hy : y ≠ -1 := by
    intro hy; subst hy
    have : (-2 : ℤ) ∈ ({x, -1} : Finset ℤ) := by rw [hm]; simp
    have hx : x = -2 := by simp at this; omega
    have : (1 : ℤ) ∈ ({x, -1} : Finset ℤ) := by rw [hm]; simp
    simp [hx] at this
  refine ⟨fun h => R1_no_integer_conversion ⟨x, y, h⟩, fun h => hy (R2_coefficients_forced x y h).2,
    fun h => hy (R3_coefficients_forced x y h).2⟩

end C5402
