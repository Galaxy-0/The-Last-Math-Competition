import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

noncomputable section
open Filter
namespace SpecialLinearTopDegree
variable (G : Type) [Group G]
-- Inhomogeneous group cochains with trivial rational coefficients.
abbrev C0 := ℚ
abbrev C1 := G → ℚ
def trivialAction (_ : G) : ℚ →ₗ[ℚ] ℚ := LinearMap.id
def d0 : C0 →ₗ[ℚ] C1 G where
  toFun q g := trivialAction G g q - q
  map_add' := by intros; ext; simp [trivialAction]
  map_smul' := by intros; ext; simp [trivialAction]
lemma d0_zero : d0 G = 0 := by ext q g; simp [d0, trivialAction]
def cocycles : Submodule ℚ (C0) := LinearMap.ker (d0 G)
lemma cocycles_top : cocycles G = ⊤ := by simp [cocycles, d0_zero]
-- Negative-degree cochains are zero in the ordinary group cochain complex.
abbrev Cminus1 := Fin 0 → ℚ
def dminus1 : Cminus1 →ₗ[ℚ] cocycles G := 0
def boundaries : Submodule ℚ (cocycles G) := LinearMap.range (dminus1 G)
lemma boundaries_bot : boundaries G = ⊥ := by simp [boundaries, dminus1]
abbrev H0 := (cocycles G) ⧸ boundaries G
def H0Equiv : H0 G ≃ₗ[ℚ] ℚ :=
  (boundaries G).quotEquivOfEqBot (boundaries_bot G) ≪≫ₗ
    (LinearEquiv.ofEq (cocycles G) ⊤ (cocycles_top G)) ≪≫ₗ Submodule.topEquiv

theorem actual_dimension : Module.finrank ℚ (H0 G) = 1 := by
  rw [(H0Equiv G).finrank_eq]
  simp


abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ
-- The predicted degree is an integer, so subtraction is not truncated.
def predicted (n : ℕ) : ℤ := ⌊(((n : ℚ)^2-1)/4)⌋ - 1
lemma predicted_two : predicted 2 = -1 := by norm_num [predicted]
def nonzeroClass : H0 SL2Z := (H0Equiv SL2Z).symm 1
lemma class_nonzero : nonzeroClass ≠ 0 := by
  intro h
  have hh := congrArg (H0Equiv SL2Z) h
  simpa [nonzeroClass] using hh

theorem actual_SL2_H0_dimension : Module.finrank ℚ (H0 SL2Z) = 1 := actual_dimension SL2Z
-- An actual nonzero cohomology class in a degree strictly larger than the
-- asserted top nonzero degree suffices, irrespective of higher degrees.
theorem cohomology_above_predicted_top :
    ∃ c : H0 SL2Z, c ≠ 0 ∧ predicted 2 < (0 : ℤ) := by
  exact ⟨nonzeroClass, class_nonzero, by rw [predicted_two]; norm_num⟩
-- Every putative top nonzero degree must bound degree zero, since H0 is nonzero.
theorem no_top_degree_equal_prediction :
    ¬ ∃ d : ℤ, d = predicted 2 ∧ (∀ c : H0 SL2Z, c ≠ 0 → (0 : ℤ) ≤ d) := by
  rintro ⟨d, hd, hb⟩
  have h := hb nonzeroClass class_nonzero
  rw [hd, predicted_two] at h
  omega

#print axioms d0_zero
#print axioms boundaries_bot
#print axioms actual_SL2_H0_dimension
#print axioms class_nonzero
#print axioms predicted_two
#print axioms cohomology_above_predicted_top
#print axioms no_top_degree_equal_prediction
end SpecialLinearTopDegree
