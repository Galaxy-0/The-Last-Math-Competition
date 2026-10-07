/-
# TLMC conjecture 00000007713: internal inconsistency

Conjecture (verbatim): "Definition: For the regular tiling {p,q} of the
hyperbolic plane, the vertex corona count C_k is the number of vertices at
graph distance at most k from a fixed vertex. Conjecture: For the
two-parameter family with p,q both tending to infinity, the growth rate of
C_k is given by a quadratic form in 2cosh, with exponential growth rate
lambda(p,q) satisfying the transcendental equation
lambda+lambda^{-1}=(p-2)(q-2)-2, and lambda is a quadratic irrational only
when (p-2)(q-2) lies in {4,5,6,10}. (transcendental corona growth equation)"

Reading: the displayed equation is an exact equality and "only when" is a
necessary condition. We refute their conjunction for any real-valued
function on hyperbolic tiling parameters, both globally and on every tail
where both parameters are at least an arbitrary K. No assumption about the
actual corona growth rate is required. Hyperbolic includes p,q >= 3.
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
This module disproves TLMC conjecture 00000007713 as stated verbatim in the
opening documentation. Both global and simultaneous-tail readings are covered.
-/

namespace CoronaGrowth

/-- Irrational and a root of a genuine integer quadratic. -/
def IsQuadraticIrrational (x : ℝ) : Prop :=
  Irrational x ∧ ∃ a b c : ℤ, a ≠ 0 ∧
    (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0

/-- The usual parameter range for a regular hyperbolic tiling. -/
def Hyperbolic (p q : ℕ) : Prop :=
  3 ≤ p ∧ 3 ≤ q ∧ 1 / (p : ℝ) + 1 / (q : ℝ) < 1 / 2

def EquationClause (lam : ℕ → ℕ → ℝ) : Prop :=
  ∀ p q, Hyperbolic p q →
    lam p q + (lam p q)⁻¹ = ((p : ℝ) - 2) * ((q : ℝ) - 2) - 2

def OnlyWhenClause (lam : ℕ → ℕ → ℝ) : Prop :=
  ∀ p q, Hyperbolic p q → IsQuadraticIrrational (lam p q) →
    (p - 2) * (q - 2) ∈ ({4, 5, 6, 10} : Finset ℕ)

/-- The discriminant lies strictly between two consecutive squares. -/
theorem discriminant_not_square (N : ℤ) (hN : 3 ≤ N) :
    ¬ IsSquare (N ^ 2 - 4) := by
  rintro ⟨m, hm⟩
  have ha : 0 ≤ |m| := abs_nonneg m
  have hs : |m| ^ 2 = N ^ 2 - 4 := by
    rw [sq_abs]
    nlinarith [hm]
  have hupper : |m| < N := by
    by_contra h
    have : N ≤ |m| := le_of_not_gt h
    nlinarith
  have hlower : N - 1 < |m| := by
    by_contra h
    have : |m| ≤ N - 1 := le_of_not_gt h
    nlinarith
  omega

/-- Lean's total inverse introduces no exceptional zero solution. -/
theorem equation_nonzero (N : ℤ) (hN : 3 ≤ N) (x : ℝ)
    (heq : x + x⁻¹ = (N : ℝ)) : x ≠ 0 := by
  intro hx
  have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : (0 : ℤ) < N)
  simp [hx] at heq
  linarith

/-- Every real solution of the claimed equation with integer N >= 3
is quadratic irrational, whichever root is chosen. -/
theorem equation_quadratic_irrational (N : ℤ) (hN : 3 ≤ N) (x : ℝ)
    (heq : x + x⁻¹ = (N : ℝ)) : IsQuadraticIrrational x := by
  have hx := equation_nonzero N hN x heq
  have hp : x ^ 2 - (N : ℝ) * x + 1 = 0 := by
    have hm := congrArg (fun y : ℝ => y * x) heq
    simp only [add_mul, inv_mul_cancel₀ hx] at hm
    nlinarith
  refine ⟨?_, 1, -N, 1, by norm_num, ?_⟩
  · rintro ⟨r, hr⟩
    have hd : (2 * x - (N : ℝ)) ^ 2 = ((N ^ 2 - 4 : ℤ) : ℝ) := by
      push_cast
      nlinarith
    have hrat : (2 * r - (N : ℚ)) ^ 2 = ((N ^ 2 - 4 : ℤ) : ℚ) := by
      apply Rat.cast_injective (α := ℝ)
      simpa only [Rat.cast_pow, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
        Rat.cast_intCast, hr] using hd
    apply discriminant_not_square N hN
    apply Rat.isSquare_intCast_iff.mp
    exact ⟨2 * r - (N : ℚ), by nlinarith [hrat]⟩
  · push_cast
    nlinarith

theorem hyperbolic_four_six : Hyperbolic 4 6 := by
  norm_num [Hyperbolic]

/-- Main refutation: no positivity or nonzero hypothesis is needed. -/
theorem conjecture_00000007713_false (lam : ℕ → ℕ → ℝ) :
    ¬ (EquationClause lam ∧ OnlyWhenClause lam) := by
  rintro ⟨hA, hB⟩
  have heq : lam 4 6 + (lam 4 6)⁻¹ = (6 : ℤ) := by
    have := hA 4 6 hyperbolic_four_six
    norm_num at this ⊢
    exact this
  have hi := equation_quadratic_irrational 6 (by norm_num) (lam 4 6) heq
  have hmem := hB 4 6 hyperbolic_four_six hi
  norm_num at hmem

/-- Exact quantitative clauses on an arbitrary simultaneous tail. -/
def TailClauses (K : ℕ) (lam : ℕ → ℕ → ℝ) : Prop :=
  (∀ p q, K ≤ p → K ≤ q → Hyperbolic p q →
    lam p q + (lam p q)⁻¹ = ((p : ℝ) - 2) * ((q : ℝ) - 2) - 2) ∧
  (∀ p q, K ≤ p → K ≤ q → Hyperbolic p q →
    IsQuadraticIrrational (lam p q) →
    (p - 2) * (q - 2) ∈ ({4, 5, 6, 10} : Finset ℕ))

theorem diagonal_hyperbolic (t : ℕ) (ht : 6 ≤ t) : Hyperbolic t t := by
  have htR : (6 : ℝ) ≤ t := by exact_mod_cast ht
  have hpos : (0 : ℝ) < t := by linarith
  refine ⟨by omega, by omega, ?_⟩
  have hbound : 1 / (t : ℝ) < 1 / 4 := by
    apply (div_lt_iff₀ hpos).mpr
    linarith
  linarith

/-- The contradiction persists however far out both parameters are taken. -/
theorem conjecture_00000007713_false_on_every_tail
    (K : ℕ) (lam : ℕ → ℕ → ℝ) : ¬ TailClauses K lam := by
  rintro ⟨hA, hB⟩
  let t := max K 6
  have htK : K ≤ t := le_max_left _ _
  have ht : 6 ≤ t := le_max_right _ _
  have hh := diagonal_hyperbolic t ht
  let M : ℕ := (t - 2) * (t - 2)
  have hM : 16 ≤ M := by
    dsimp [M]
    have : 4 ≤ t - 2 := by omega
    nlinarith
  have hN : (3 : ℤ) ≤ (M : ℤ) - 2 := by
    have : (16 : ℤ) ≤ M := by exact_mod_cast hM
    omega
  have hcast : (((M : ℤ) - 2 : ℤ) : ℝ) =
      ((t : ℝ) - 2) * ((t : ℝ) - 2) - 2 := by
    have hmR : (M : ℝ) = ((t : ℝ) - 2) * ((t : ℝ) - 2) := by
      dsimp [M]
      rw [Nat.cast_mul]
      simp only [Nat.cast_sub (by omega : 2 ≤ t), Nat.cast_ofNat]
    push_cast
    rw [hmR]
  have heq := hA t t htK htK hh
  have hi := equation_quadratic_irrational ((M : ℤ) - 2) hN (lam t t)
    (by rw [hcast]; exact heq)
  have hmem := hB t t htK htK hh hi
  change M ∈ ({4, 5, 6, 10} : Finset ℕ) at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

/-- Even existentially choosing a cutoff cannot repair the exact clauses. -/
theorem no_eventual_quantitative_clauses (lam : ℕ → ℕ → ℝ) :
    ¬ ∃ K : ℕ, TailClauses K lam := by
  rintro ⟨K, hK⟩
  exact conjecture_00000007713_false_on_every_tail K lam hK

end CoronaGrowth

#print axioms CoronaGrowth.discriminant_not_square
#print axioms CoronaGrowth.equation_quadratic_irrational
#print axioms CoronaGrowth.conjecture_00000007713_false
#print axioms CoronaGrowth.conjecture_00000007713_false_on_every_tail
#print axioms CoronaGrowth.no_eventual_quantitative_clauses
