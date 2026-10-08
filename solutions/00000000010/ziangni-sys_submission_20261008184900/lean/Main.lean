import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
open Polynomial Filter Topology
namespace LinearBatemanHorn
def f : ℤ[X] := X
theorem f_squarefree : Squarefree f := Polynomial.prime_X.squarefree
theorem f_degree : f.natDegree = 1 := by simp [f]

-- Standard root-product discriminant of a split degree-n polynomial.
def rootDiscriminant (p : ℂ[X]) (n : ℕ) (r : Fin n → ℂ) : ℂ :=
  p.leadingCoeff ^ (2*n-2) *
    ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (r i-r j)^2
def complexPolynomial : ℂ[X] := f.map (Int.castRingHom ℂ)
def roots : Fin 1 → ℂ := fun _ => 0
theorem actual_root_factorization :
    complexPolynomial = ∏ i : Fin 1, (X-C (roots i)) := by
  simp [complexPolynomial, f, roots, Fin.prod_univ_succ]
def discriminant : ℂ := rootDiscriminant complexPolynomial 1 roots
theorem discriminant_one : discriminant = 1 := by
  simp only [discriminant, rootDiscriminant, show 2*1-2 = 0 by decide,
    pow_zero, one_mul]
  apply Finset.prod_eq_one
  intro i hi
  have he : Finset.univ.filter (fun j : Fin 1 => i < j) = ∅ := by
    ext j
    fin_cases i
    fin_cases j
    decide
  rw [he]
  simp
def D : ℝ := ‖discriminant‖
theorem D_one : D = 1 := by simp [D, discriminant_one]

abbrev PrimeIndex := {p : ℕ // p.Prime}
instance (p : PrimeIndex) : NeZero p.val := ⟨p.property.ne_zero⟩
def rootCount (p : PrimeIndex) : ℕ :=
  (Finset.univ.filter (fun a : ZMod p.val =>
    Polynomial.eval a (f.map (Int.castRingHom (ZMod p.val))) = 0)).card
theorem roots_mod_prime (p : PrimeIndex) : rootCount p = 1 := by
  simp only [rootCount, f, Polynomial.map_X, Polynomial.eval_X]
  have he : Finset.univ.filter (fun a : ZMod p.val => a = 0) = {0} := by
    ext a
    simp
  rw [he]
  simp
def localFactor (p : PrimeIndex) : ℝ :=
  (1-(rootCount p : ℝ)/(p.val : ℝ)) / (1-1/(p.val : ℝ))
theorem localFactor_one (p : PrimeIndex) : localFactor p = 1 := by
  have hp : (2:ℝ) ≤ (p.val:ℝ) := by exact_mod_cast p.property.two_le
  have hpos : 0 < (p.val:ℝ) := by linarith
  have hne : 1-1/(p.val:ℝ) ≠ 0 := by
    have hlt : 1/(p.val:ℝ) < 1 := (div_lt_iff₀ hpos).mpr (by linarith)
    linarith
  rw [localFactor, roots_mod_prime]
  simp only [Nat.cast_one]
  exact div_self hne

-- Genuine prime partial products, taken in increasing prime order.
def partialProduct (N : ℕ) : ℝ :=
  ∏ p ∈ Finset.range (N+1), if h : p.Prime then localFactor ⟨p,h⟩ else 1
theorem partialProduct_one (N : ℕ) : partialProduct N = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  split_ifs with h
  · exact localFactor_one ⟨p,h⟩
  · rfl
theorem product_limit : Tendsto partialProduct atTop (𝓝 1) := by
  have he : partialProduct = fun _ => (1:ℝ) := funext partialProduct_one
  rw [he]
  exact tendsto_const_nhds
def BHconstant : ℝ := limUnder atTop partialProduct
theorem BHconstant_one : BHconstant = 1 := product_limit.limUnder_eq
theorem upper_bound_false : ¬ BHconstant ≤ 2*Real.log D := by
  rw [BHconstant_one, D_one, Real.log_one]
  norm_num

#print axioms f_squarefree
#print axioms actual_root_factorization
#print axioms discriminant_one
#print axioms roots_mod_prime
#print axioms product_limit
#print axioms upper_bound_false
end LinearBatemanHorn
