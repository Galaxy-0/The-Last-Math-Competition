import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators TensorProduct
open Filter
namespace TensorPI
variable (A : Type*) [CommRing A] [Algebra ℚ A] [Nontrivial A]
abbrev Coeff (n : ℕ) := Equiv.Perm (Fin n) → ℚ
abbrev Values (n : ℕ) := (Fin n → A) → A

def productFunction (n : ℕ) : Values A n := fun x => ∏ i, x i

def wordEval (n : ℕ) (σ : Equiv.Perm (Fin n)) : Values A n :=
  fun x => ∏ i, x (σ i)

lemma wordEval_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    wordEval A n σ = productFunction A n := by
  funext x
  exact Equiv.prod_comp σ x

/-- Evaluate the genuine formal multilinear words on every tuple in A. -/
def evalMap (n : ℕ) : Coeff n →ₗ[ℚ] Values A n where
  toFun c x := ∑ σ, c σ • wordEval A n σ x
  map_add' c d := by
    ext x
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext x
    simp [smul_smul, Finset.smul_sum]

lemma eval_formula (n : ℕ) (c : Coeff n) :
    evalMap A n c = (∑ σ, c σ) • productFunction A n := by
  ext x
  simp [evalMap, wordEval_eq, Finset.sum_smul]

lemma product_nonzero (n : ℕ) : productFunction A n ≠ 0 := by
  intro h
  have := congrFun h (fun _ => 1)
  simpa [productFunction] using this

lemma product_mem_range (n : ℕ) : productFunction A n ∈ LinearMap.range (evalMap A n) := by
  refine ⟨Pi.single (Equiv.refl (Fin n)) 1, ?_⟩
  rw [eval_formula]
  simp

lemma range_eq_span (n : ℕ) :
    LinearMap.range (evalMap A n) = Submodule.span ℚ {productFunction A n} := by
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    rw [eval_formula]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro y hy
    have : y = productFunction A n := Set.mem_singleton_iff.mp hy
    subst y
    exact product_mem_range A n

/-- Quotient by identities, identified with the actual evaluation image. -/
def identityQuotientEquiv (n : ℕ) :
    (Coeff n ⧸ LinearMap.ker (evalMap A n)) ≃ₗ[ℚ] LinearMap.range (evalMap A n) :=
  (evalMap A n).quotKerEquivRange

def codimension (n : ℕ) : ℕ := Module.finrank ℚ (LinearMap.range (evalMap A n))

lemma codimension_one (n : ℕ) : codimension A n = 1 := by
  unfold codimension
  rw [range_eq_span]
  exact finrank_span_singleton (product_nonzero A n)

def piExponent : ℝ :=
  limUnder atTop (fun n : ℕ => (codimension A n : ℝ) ^ (1 / (n : ℝ)))

lemma exponent_limit : Tendsto
    (fun n : ℕ => (codimension A n : ℝ) ^ (1 / (n : ℝ))) atTop (nhds 1) := by
  simpa [codimension_one] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))

lemma exponent_one : piExponent A = 1 := exponent_limit A |>.limUnder_eq

abbrev ScalarTensor := ℚ ⊗[ℚ] ℚ

def tensorEquiv : ScalarTensor ≃ₐ[ℚ] ℚ := Algebra.TensorProduct.lid ℚ ℚ

instance tensorNontrivial : Nontrivial ScalarTensor := tensorEquiv.toEquiv.nontrivial

lemma actual_tensor_multiplication (x y : ℚ) : tensorEquiv (x ⊗ₜ[ℚ] y) = x * y := by
  simp [tensorEquiv, Algebra.TensorProduct.lid_tmul, smul_eq_mul]

lemma tensor_codimension_one (n : ℕ) : codimension ScalarTensor n = 1 :=
  codimension_one ScalarTensor n

lemma tensor_exponent_one : piExponent ScalarTensor = 1 := exponent_one ScalarTensor

theorem conjectured_sum_false : piExponent ScalarTensor ≠ piExponent ℚ + piExponent ℚ := by
  rw [tensor_exponent_one, exponent_one ℚ]
  norm_num

end TensorPI
#print axioms TensorPI.identityQuotientEquiv
#print axioms TensorPI.codimension_one
#print axioms TensorPI.exponent_limit
#print axioms TensorPI.tensorEquiv
#print axioms TensorPI.actual_tensor_multiplication
#print axioms TensorPI.tensor_codimension_one
#print axioms TensorPI.tensor_exponent_one
#print axioms TensorPI.conjectured_sum_false
