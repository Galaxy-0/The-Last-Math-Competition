import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace YosidaCounterexample
noncomputable section

def scalarMap (a : ℝ) : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ
def A : ℝ →L[ℝ] ℝ := scalarMap 4
def lambda : ℝ := 1/4
def shifted (T : ℝ →L[ℝ] ℝ) (l : ℝ) := ContinuousLinearMap.id ℝ ℝ + l • T
def J : ℝ →L[ℝ] ℝ := scalarMap (1/2)
-- Standard Yosida definition, using the resolvent proved below.
def yosida (R : ℝ →L[ℝ] ℝ) (l : ℝ) := l⁻¹ • (ContinuousLinearMap.id ℝ ℝ - R)
def approximation : ℝ →L[ℝ] ℝ := yosida J lambda

theorem scalarMap_apply (a x : ℝ) : scalarMap a x = a*x := rfl

theorem shifted_apply (x : ℝ) : shifted A lambda x = 2*x := by
  norm_num [shifted, A, lambda, scalarMap, smul_eq_mul]
  ring

theorem resolvent_left : J.comp (shifted A lambda) = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro x
  change J (shifted A lambda x) = x
  rw [shifted_apply]
  simp [J, scalarMap, smul_eq_mul]

theorem resolvent_right : (shifted A lambda).comp J = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro x
  change shifted A lambda (J x) = x
  rw [shifted_apply]
  simp [J, scalarMap, smul_eq_mul]

theorem resolvent_unique (p x : ℝ) : shifted A lambda x = p ↔ x = J p := by
  rw [shifted_apply]
  simp [J, scalarMap, smul_eq_mul]
  constructor <;> intro h <;> linarith

theorem approximation_eq : approximation = scalarMap 2 := by
  apply ContinuousLinearMap.ext
  intro x
  simp [approximation, yosida, lambda, J, scalarMap, smul_eq_mul]
  ring

theorem error_eq : A - approximation = scalarMap 2 := by
  rw [approximation_eq]
  apply ContinuousLinearMap.ext
  intro x
  simp [A, scalarMap, smul_eq_mul]
  ring

theorem scalarMap_norm (a : ℝ) : ‖scalarMap a‖ = |a| := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a)
    intro x
    simp [scalarMap_apply, Real.norm_eq_abs, abs_mul]
  · have h := ContinuousLinearMap.le_opNorm (scalarMap a) 1
    simpa [scalarMap_apply, Real.norm_eq_abs] using h

theorem actual_norms : ‖A‖ = 4 ∧ ‖A-approximation‖ = 2 := by
  constructor
  · norm_num [A, scalarMap_norm]
  · rw [error_eq, scalarMap_norm]
    norm_num

def MonotoneOperator (T : ℝ → Set ℝ) : Prop :=
  ∀ x y u v, u ∈ T x → v ∈ T y → 0 ≤ (u-v)*(x-y)
def MaximalMonotone (T : ℝ → Set ℝ) : Prop :=
  MonotoneOperator T ∧ ∀ B, MonotoneOperator B →
    (∀ x, T x ⊆ B x) → ∀ x, B x ⊆ T x
def graphOperator (T : ℝ →L[ℝ] ℝ) (x : ℝ) : Set ℝ := {T x}

theorem A_monotone : MonotoneOperator (graphOperator A) := by
  intro x y u v hu hv
  have hu0 : u = 4*x := hu
  have hv0 : v = 4*y := hv
  rw [hu0, hv0]
  nlinarith [sq_nonneg (x-y)]

theorem A_maximal_monotone : MaximalMonotone (graphOperator A) := by
  refine ⟨A_monotone, ?_⟩
  intro B hB hAB x u hu
  let y : ℝ := x + (u-4*x)/8
  have hv : 4*y ∈ B y := hAB y rfl
  have he := hB x y u (4*y) hu hv
  dsimp [y] at he
  have heq : u = 4*x := by nlinarith [sq_nonneg (u-4*x)]
  exact heq

theorem error_exceeds_claim : lambda*‖A‖ < ‖A-approximation‖ := by
  rw [actual_norms.1, actual_norms.2]
  norm_num [lambda]

theorem unit_vector_error : ‖A 1 - approximation 1‖ = 2 ∧ lambda*‖A‖ = 1 := by
  rw [approximation_eq, actual_norms.1]
  norm_num [A, scalarMap, lambda, smul_eq_mul]

theorem conjecture_00000008839_error_false :
    MaximalMonotone (graphOperator A) ∧ 0 < lambda ∧
    J.comp (shifted A lambda) = ContinuousLinearMap.id ℝ ℝ ∧
    (shifted A lambda).comp J = ContinuousLinearMap.id ℝ ℝ ∧
    approximation = yosida J lambda ∧ ¬ (‖A-approximation‖ ≤ lambda*‖A‖) := by
  exact ⟨A_maximal_monotone, by norm_num [lambda], resolvent_left,
    resolvent_right, rfl, not_le_of_gt error_exceeds_claim⟩

#print axioms resolvent_left
#print axioms resolvent_right
#print axioms actual_norms
#print axioms A_maximal_monotone
#print axioms unit_vector_error
#print axioms conjecture_00000008839_error_false
end
end YosidaCounterexample
