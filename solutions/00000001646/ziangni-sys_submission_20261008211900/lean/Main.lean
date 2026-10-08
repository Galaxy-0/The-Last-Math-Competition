import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

noncomputable section
open Filter
namespace RationalCohomologyNondecay
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

def dimensionSequence (groups : ℕ → Type) [∀ g, Group (groups g)] (g : ℕ) : ℝ :=
  Module.finrank ℚ (H0 (groups g))
theorem sequence_constant (groups : ℕ → Type) [∀ g, Group (groups g)] :
    dimensionSequence groups = fun _ => 1 := by
  funext g
  simp [dimensionSequence, actual_dimension]

theorem degree_zero_in_stable_range (g : ℕ) (hg : 1 ≤ g) :
    (0 : ℝ) ≤ (2*(g : ℝ)-2)/3 := by
  have : (1:ℝ) ≤ g := by exact_mod_cast hg
  linarith

theorem no_decay (groups : ℕ → Type) [∀ g, Group (groups g)] :
    ¬ Tendsto (dimensionSequence groups) atTop (nhds 0) := by
  rw [sequence_constant]
  intro hz
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have bad := tendsto_nhds_unique hz hone
  norm_num at bad

-- A formulation that only assumes the asserted ordinary H0 dimensions on
-- the stable tail, allowing arbitrary values at the finitely many small genera.
theorem stable_tail_cannot_decay (groups : ℕ → Type) [∀ g, Group (groups g)]
    (f : ℕ → ℝ) (hf : ∀ g, 1 ≤ g → f g = Module.finrank ℚ (H0 (groups g))) :
    ¬ Tendsto f atTop (nhds 0) := by
  intro hz
  have he : (fun _ : ℕ => (1:ℝ)) =ᶠ[atTop] f := by
    filter_upwards [eventually_ge_atTop 1] with g hg
    rw [hf g hg, actual_dimension]
    norm_num
  have hone : Tendsto f atTop (nhds 1) := tendsto_const_nhds.congr' he
  have bad := tendsto_nhds_unique hz hone
  norm_num at bad

#print axioms d0_zero
#print axioms cocycles_top
#print axioms boundaries_bot
#print axioms actual_dimension
#print axioms degree_zero_in_stable_range
#print axioms no_decay
#print axioms stable_tail_cannot_decay
end RationalCohomologyNondecay
