import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

namespace TensorHomogeneity
abbrev Tensor := Fin 1 → Fin 1 → Fin 1 → ℝ
def tensor : Tensor := fun _ _ _ => 1
def contraction (A : Tensor) (x : Fin 1 → ℝ) (i : Fin 1) : ℝ :=
  ∑ j, ∑ k, A i j k * x j * x k

def ZPair (z : Fin 2 → ℝ) : Prop :=
  (∀ i, contraction tensor (fun _ => z 1) i = z 0 * z 1) ∧
    (∑ i : Fin 1, (z 1)^2) = 1

theorem contraction_formula (x : Fin 1 → ℝ) (i : Fin 1) :
    contraction tensor x i = (x 0)^2 := by
  simp [contraction, tensor, Fin.sum_univ_one, pow_two]

theorem normalized_eigenpair_formula (z : Fin 2 → ℝ) :
    ZPair z ↔ (z 1)^2 = z 0 * z 1 ∧ (z 1)^2 = 1 := by
  simp [ZPair, contraction_formula, Fin.sum_univ_one]

theorem unit_pair : ZPair (fun _ => 1) := by
  rw [normalized_eigenpair_formula]
  norm_num

theorem doubled_pair_invalid : ¬ ZPair (fun _ => 2) := by
  rw [normalized_eigenpair_formula]
  norm_num

/-- The genuine normalization polynomial is nonhomogeneous. -/
noncomputable def normalization : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1 ^ 2 - 1

/-- Ordinary homogeneity implies scalar covariance of polynomial evaluation. -/
theorem homogeneous_scaling (p : MvPolynomial (Fin 2) ℝ) (n : ℕ)
    (hp : p.IsHomogeneous n) (c : ℝ) (z : Fin 2 → ℝ) :
    MvPolynomial.eval (fun i => c * z i) p = c^n * MvPolynomial.eval z p := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  conv_rhs => rw [← p.support_sum_monomial_coeff]
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d 0 + d 1 = n := by
    have h := hp (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using h
  simp only [MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype _ _ (by intro i; simp),
    Finsupp.prod_fintype _ _ (by intro i; simp)]
  simp only [Fin.prod_univ_two, mul_pow]
  rw [← hdeg, pow_add]
  ring

/-- Any family of homogeneous polynomial equations has a scaling-invariant zero set. -/
theorem homogeneous_zero_scaling {ι : Type*} (P : ι → MvPolynomial (Fin 2) ℝ)
    (degree : ι → ℕ) (hP : ∀ i, (P i).IsHomogeneous (degree i))
    (z : Fin 2 → ℝ) (hz : ∀ i, MvPolynomial.eval z (P i) = 0) (c : ℝ) :
    ∀ i, MvPolynomial.eval (fun j => c * z j) (P i) = 0 := by
  intro i
  rw [homogeneous_scaling (P i) (degree i) (hP i) c z, hz i, mul_zero]

/-- No arbitrary homogeneous family in the original eigenpair variables defines the Z system. -/
theorem conjecture_false {ι : Type*} :
    ¬ ∃ P : ι → MvPolynomial (Fin 2) ℝ, ∃ degree : ι → ℕ,
      (∀ i, (P i).IsHomogeneous (degree i)) ∧
      ∀ z, ZPair z ↔ ∀ i, MvPolynomial.eval z (P i) = 0 := by
  rintro ⟨P, degree, hP, hEq⟩
  have hz := (hEq (fun _ => 1)).mp unit_pair
  have hd := homogeneous_zero_scaling P degree hP (fun _ => 1) hz 2
  have hbad : ZPair (fun _ => 2) := (hEq (fun _ => 2)).mpr (by simpa using hd)
  exact doubled_pair_invalid hbad

end TensorHomogeneity
#print axioms TensorHomogeneity.contraction_formula
#print axioms TensorHomogeneity.normalized_eigenpair_formula
#print axioms TensorHomogeneity.homogeneous_scaling
#print axioms TensorHomogeneity.homogeneous_zero_scaling
#print axioms TensorHomogeneity.conjecture_false
