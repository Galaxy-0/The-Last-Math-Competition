import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-!
# A counterexample to conjecture 00000007767

We use complex coefficients and positive composition iterates. The complex projective
line is represented by its usual affine chart together with one point at infinity:
`some z` represents `[z : 1]`, and `none` represents `[1 : 0]`.
The polynomials are `X ^ 2` and `X ^ 3`. Primitive roots of orders `5 ^ (k + 1)`
give distinct points that are periodic for both projective polynomial maps.
-/

namespace Conjecture7767

/-- The standard affine-chart model of the complex projective line. -/
abbrev ProjectiveLine := Option ℂ

/-- The affine chart inclusion, sending `z` to the homogeneous point `[z : 1]`. -/
def affine (z : ℂ) : ProjectiveLine := some z

/-- The point `[1 : 0]` at infinity. -/
def infinity : ProjectiveLine := none

theorem affine_injective : Function.Injective affine := Option.some_injective ℂ

theorem affine_ne_infinity (z : ℂ) : affine z ≠ infinity := by
  simp [affine, infinity]

/-- A nonconstant polynomial acts by evaluation on the affine chart and fixes infinity.
The definition is also given for constant polynomials; only degree-at-least-two
polynomials enter the assertion below. -/
noncomputable def projectiveMap (p : Polynomial ℂ) : ProjectiveLine → ProjectiveLine :=
  Option.map p.eval

theorem projectiveMap_affine (p : Polynomial ℂ) (z : ℂ) :
    projectiveMap p (affine z) = affine (p.eval z) := rfl

theorem projectiveMap_infinity (p : Polynomial ℂ) :
    projectiveMap p infinity = infinity := rfl

/-- Periodicity requires a strictly positive compositional return time. -/
def Periodic (F : ProjectiveLine → ProjectiveLine) (P : ProjectiveLine) : Prop :=
  ∃ r : ℕ, 0 < r ∧ F^[r] P = P

def CommonPeriodicSet (F G : ProjectiveLine → ProjectiveLine) : Set ProjectiveLine :=
  {P | Periodic F P ∧ Periodic G P}

/-- Equality here is equality of the actual self-maps, with both indices positive. -/
def CommonIterate (F G : ProjectiveLine → ProjectiveLine) : Prop :=
  ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ F^[m] = G^[n]

noncomputable def powerPolynomial (d : ℕ) : Polynomial ℂ := Polynomial.X ^ d

noncomputable def powerMap (d : ℕ) : ProjectiveLine → ProjectiveLine :=
  projectiveMap (powerPolynomial d)

theorem powerPolynomial_degree (d : ℕ) : (powerPolynomial d).natDegree = d := by
  simp [powerPolynomial]

theorem powerMap_affine (d : ℕ) (z : ℂ) :
    powerMap d (affine z) = affine (z ^ d) := by
  simp [powerMap, projectiveMap_affine, powerPolynomial]

theorem powerMap_infinity (d : ℕ) : powerMap d infinity = infinity := rfl

theorem powerMap_iterate_affine (d r : ℕ) (z : ℂ) :
    (powerMap d)^[r] (affine z) = affine (z ^ (d ^ r)) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, powerMap_affine, ← pow_mul, pow_succ]

theorem powerMap_commute (d e : ℕ) : Function.Commute (powerMap d) (powerMap e) := by
  intro P
  cases P with
  | none => rfl
  | some z =>
      change powerMap d (powerMap e (affine z)) = powerMap e (powerMap d (affine z))
      simp only [powerMap_affine, ← pow_mul, Nat.mul_comm]

/-- A primitive root whose order is coprime to the degree is periodic, not merely
preperiodic: Euler's theorem supplies the positive return time `N.totient`. -/
theorem primitiveRoot_periodic {z : ℂ} {N d : ℕ} (hN : 0 < N)
    (hz : IsPrimitiveRoot z N) (hd : Nat.Coprime d N) :
    Periodic (powerMap d) (affine z) := by
  refine ⟨N.totient, Nat.totient_pos.mpr hN, ?_⟩
  rw [powerMap_iterate_affine]
  apply congrArg affine
  have hmod : d ^ N.totient ≡ 1 [MOD orderOf z] := by
    rw [← hz.eq_orderOf]
    exact Nat.ModEq.pow_totient hd
  have hfin : IsOfFinOrder z := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨N, hN, hz.pow_eq_one⟩
  simpa using (hfin.pow_eq_pow_iff_modEq.mpr hmod : z ^ (d ^ N.totient) = z ^ 1)

/-- An explicit primitive root of order `5 ^ (k + 1)`. -/
noncomputable def root (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (5 ^ (k + 1) : ℕ))

theorem root_primitive (k : ℕ) : IsPrimitiveRoot (root k) (5 ^ (k + 1)) := by
  exact Complex.isPrimitiveRoot_exp _ (by positivity)

theorem root_injective : Function.Injective root := by
  intro j k h
  have horder : 5 ^ (j + 1) = 5 ^ (k + 1) := by
    apply (root_primitive j).unique
    rw [h]
    exact root_primitive k
  have hexp := Nat.pow_right_injective (by decide : 2 ≤ 5) horder
  omega

theorem root_periodic_two (k : ℕ) : Periodic (powerMap 2) (affine (root k)) := by
  exact primitiveRoot_periodic (by positivity) (root_primitive k)
    ((by decide : Nat.Coprime 2 5).pow_right (k + 1))

theorem root_periodic_three (k : ℕ) : Periodic (powerMap 3) (affine (root k)) := by
  exact primitiveRoot_periodic (by positivity) (root_primitive k)
    ((by decide : Nat.Coprime 3 5).pow_right (k + 1))

/-- The chart inclusion transfers the distinct affine roots to distinct projective points. -/
theorem common_periodic_infinite :
    (CommonPeriodicSet (powerMap 2) (powerMap 3)).Infinite := by
  have hinj : Function.Injective (fun k : ℕ => affine (root k)) :=
    affine_injective.comp root_injective
  apply (Set.infinite_range_of_injective hinj).mono
  rintro P ⟨k, rfl⟩
  exact ⟨root_periodic_two k, root_periodic_three k⟩

/-- Actual map equality would imply `2 ^ m = 3 ^ n`, by evaluation at the affine
point `2`. Parity rules this out for every positive `m`. -/
theorem no_positive_common_iterate : ¬ CommonIterate (powerMap 2) (powerMap 3) := by
  rintro ⟨m, n, hm, _hn, h⟩
  have heval := congrFun h (affine 2)
  rw [powerMap_iterate_affine, powerMap_iterate_affine] at heval
  have hcomplex : (2 : ℂ) ^ (2 ^ m) = (2 : ℂ) ^ (3 ^ n) :=
    affine_injective heval
  have hnat : (2 : ℕ) ^ (2 ^ m) = (2 : ℕ) ^ (3 ^ n) := by
    exact_mod_cast hcomplex
  have hdegrees : (2 : ℕ) ^ m = (3 : ℕ) ^ n :=
    Nat.pow_right_injective (by decide) hnat
  have hparity := congrArg (fun a : ℕ => a % 2) hdegrees
  norm_num [Nat.pow_mod, Nat.ne_of_gt hm] at hparity

/-- The explicit leading equivalence in the conjecture, under the disclosed
complex-field and positive-iterate conventions. -/
def LeadingAssertion : Prop :=
  ∀ f g : Polynomial ℂ, 2 ≤ f.natDegree → 2 ≤ g.natDegree →
    Function.Commute (projectiveMap f) (projectiveMap g) →
    ((CommonPeriodicSet (projectiveMap f) (projectiveMap g)).Infinite ↔
      CommonIterate (projectiveMap f) (projectiveMap g))

theorem counterexample :
    2 ≤ (powerPolynomial 2).natDegree ∧
    2 ≤ (powerPolynomial 3).natDegree ∧
    Function.Commute (projectiveMap (powerPolynomial 2))
      (projectiveMap (powerPolynomial 3)) ∧
    (CommonPeriodicSet (projectiveMap (powerPolynomial 2))
      (projectiveMap (powerPolynomial 3))).Infinite ∧
    ¬ CommonIterate (projectiveMap (powerPolynomial 2))
      (projectiveMap (powerPolynomial 3)) := by
  exact ⟨by simp [powerPolynomial_degree], by simp [powerPolynomial_degree],
    powerMap_commute 2 3, common_periodic_infinite, no_positive_common_iterate⟩

/-- Refuting this necessary part already refutes the conjecture in the stated setting. -/
theorem conjecture_false : ¬ LeadingAssertion := by
  intro h
  obtain ⟨hf, hg, hcomm, hinf, hnot⟩ := counterexample
  exact hnot ((h _ _ hf hg hcomm).mp hinf)

end Conjecture7767
