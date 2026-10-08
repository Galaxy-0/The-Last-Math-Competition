import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Filter
namespace ScalarCapelli
abbrev Coeff (n : ℕ) := Equiv.Perm (Fin n) → ℚ
abbrev Values (n : ℕ) := (Fin n → ℚ) → ℚ

def productFunction (n : ℕ) : Values n := fun x => ∏ i, x i

def wordEval (n : ℕ) (σ : Equiv.Perm (Fin n)) : Values n :=
  fun x => ∏ i, x (σ i)

lemma wordEval_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    wordEval n σ = productFunction n := by
  funext x
  exact Equiv.prod_comp σ x

/-- Evaluation of the formal multilinear words indexed by permutations. -/
def evalMap (n : ℕ) : Coeff n →ₗ[ℚ] Values n where
  toFun c x := ∑ σ, c σ * wordEval n σ x
  map_add' c d := by
    ext x
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext x
    simp [smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma eval_formula (n : ℕ) (c : Coeff n) :
    evalMap n c = (∑ σ, c σ) • productFunction n := by
  ext x
  simp [evalMap, wordEval_eq, Finset.sum_mul, smul_eq_mul]

lemma product_nonzero (n : ℕ) : productFunction n ≠ 0 := by
  intro h
  have := congrFun h (fun _ => 1)
  simpa [productFunction] using this

lemma product_mem_range (n : ℕ) : productFunction n ∈ LinearMap.range (evalMap n) := by
  refine ⟨Pi.single (Equiv.refl (Fin n)) 1, ?_⟩
  rw [eval_formula]
  simp

lemma range_eq_span (n : ℕ) :
    LinearMap.range (evalMap n) = Submodule.span ℚ {productFunction n} := by
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    rw [eval_formula]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro y hy
    have : y = productFunction n := Set.mem_singleton_iff.mp hy
    subst y
    exact product_mem_range n

/-- The kernel is exactly the multilinear identities of the scalar algebra. -/
def identityQuotientEquiv (n : ℕ) :
    (Coeff n ⧸ LinearMap.ker (evalMap n)) ≃ₗ[ℚ] LinearMap.range (evalMap n) :=
  (evalMap n).quotKerEquivRange

def codimension (n : ℕ) : ℕ := Module.finrank ℚ (LinearMap.range (evalMap n))

lemma codimension_one (n : ℕ) : codimension n = 1 := by
  unfold codimension
  rw [range_eq_span]
  exact finrank_span_singleton (product_nonzero n)

/-- The usual PI exponent is the limit of the nth roots of actual codimensions. -/
def piExponent : ℝ :=
  limUnder atTop (fun n : ℕ => (codimension n : ℝ) ^ (1 / (n : ℝ)))

lemma exponent_limit : Tendsto
    (fun n : ℕ => (codimension n : ℝ) ^ (1 / (n : ℝ))) atTop (nhds 1) := by
  simpa [codimension_one] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))

lemma exponent_one : piExponent = 1 := by
  exact exponent_limit.limUnder_eq

/-- The standard Capelli polynomial with one alternating variable is X. -/
def capelliOneIdentity : Prop := ∀ x : ℚ, Polynomial.eval x (Polynomial.X : Polynomial ℚ) = 0

lemma capelli_one_fails : ¬ capelliOneIdentity := by
  intro h
  have := h 1
  norm_num at this

theorem conjectured_equivalence_false : ¬ (capelliOneIdentity ↔ piExponent ≤ 1) := by
  intro h
  apply capelli_one_fails
  apply h.mpr
  rw [exponent_one]

end ScalarCapelli
#print axioms ScalarCapelli.range_eq_span
#print axioms ScalarCapelli.identityQuotientEquiv
#print axioms ScalarCapelli.codimension_one
#print axioms ScalarCapelli.exponent_limit
#print axioms ScalarCapelli.exponent_one
#print axioms ScalarCapelli.capelli_one_fails
#print axioms ScalarCapelli.conjectured_equivalence_false
