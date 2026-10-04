import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

open Set MeasureTheory Metric
open scoped RealInnerProductSpace
noncomputable section
namespace Counterexample

def K : Set ℝ := Icc (-1) 1
def L : Set ℝ := Icc (-2) 2

theorem bodies : IsCompact K ∧ Convex ℝ K ∧ IsCompact L ∧ Convex ℝ L :=
  ⟨isCompact_Icc, convex_Icc _ _, isCompact_Icc, convex_Icc _ _⟩

theorem interiors : (interior K).Nonempty ∧ (interior L).Nonempty := by
  constructor
  · exact ⟨0, by norm_num [K, interior_Icc]⟩
  · exact ⟨0, by norm_num [L, interior_Icc]⟩

theorem symmetric_neighborhood : Ioo (-1) 1 ⊆ K ∧ Ioo (-1) 1 ⊆ L ∧
    Ioo (-1:ℝ) 1 ∈ nhds 0 ∧ (∀ x:ℝ, x ∈ Ioo (-1) 1 ↔ -x ∈ Ioo (-1) 1) := by
  refine ⟨?_, ?_, Ioo_mem_nhds (by norm_num) (by norm_num), ?_⟩
  · intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  · intro x hx; constructor <;> linarith [hx.1,hx.2]
  · intro x; constructor <;> intro hx <;> constructor <;> linarith [hx.1,hx.2]

-- This is the genuine inner-product orthogonal hyperplane.
def perp (theta : ℝ) : Submodule ℝ ℝ :=
  LinearMap.ker (theta • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))

instance (theta : ℝ) : BorelSpace (perp theta) := Subtype.borelSpace _

theorem mem_perp (theta x : ℝ) : x ∈ perp theta ↔ (@inner ℝ ℝ _ theta x) = 0 := by
  simp [perp, RCLike.inner_apply, or_comm]

theorem perp_zero (theta : ℝ) (h : theta ≠ 0) (x : perp theta) : (x:ℝ) = 0 := by
  have hx := x.property
  change theta * (x:ℝ) = 0 at hx
  exact (mul_eq_zero.mp hx).resolve_left h

abbrev Z := Fin 0 → ℝ

def coordinateMap (theta : ℝ) : Z →ₗᵢ[ℝ] perp theta where
  toLinearMap := 0
  norm_map' := by
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    change ‖(0 : perp theta)‖ = ‖(0 : Z)‖
    rw [norm_zero, norm_zero]

def chart (theta : ℝ) (h : theta ≠ 0) : Z ≃ₗᵢ[ℝ] perp theta :=
  LinearIsometryEquiv.ofSurjective (coordinateMap theta) (by
    intro x
    refine ⟨0, ?_⟩
    apply Subtype.ext
    change 0 = (x:ℝ)
    exact (perp_zero theta h x).symm)

-- Intrinsic zero-dimensional Lebesgue volume, transported by an isometric chart.
def orthVolume (theta : ℝ) (h : theta ≠ 0) : Measure (perp theta) :=
  Measure.map (chart theta h) (volume : Measure Z)

def sectionSet (B : Set ℝ) (theta : ℝ) : Set (perp theta) :=
  {x | (x:ℝ) ∈ B}

def sectionVolume (B : Set ℝ) (theta : ℝ) (h : theta ≠ 0) : ENNReal :=
  orthVolume theta h (sectionSet B theta)

theorem chart_volume_one : (volume : Measure Z) univ = 1 := by
  rw [Measure.volume_pi_eq_dirac (0:Z)]
  simp

theorem section_eq_univ (B : Set ℝ) (hB : 0 ∈ B) (theta : ℝ) (h : theta ≠ 0) :
    sectionSet B theta = univ := by
  ext x
  simp only [sectionSet, mem_setOf_eq, mem_univ, iff_true]
  rw [perp_zero theta h x]
  exact hB

theorem section_volume_one (B : Set ℝ) (hB : 0 ∈ B) (theta : ℝ) (h : theta ≠ 0) :
    sectionVolume B theta h = 1 := by
  unfold sectionVolume orthVolume
  rw [section_eq_univ B hB theta h]
  rw [Measure.map_apply (chart theta h).continuous.measurable MeasurableSet.univ]
  simpa using chart_volume_one

theorem same_sphere_data (theta : ℝ) (ht : ‖theta‖ = 1) :
    ∃ h : theta ≠ 0, sectionVolume K theta h = 1 ∧
      sectionVolume L theta h = 1 := by
  have h : theta ≠ 0 := by intro hz; simp [hz] at ht
  exact ⟨h, section_volume_one K (by norm_num [K]) theta h,
    section_volume_one L (by norm_num [L]) theta h⟩

theorem different_diameters : diam K = 2 ∧ diam L = 4 := by
  norm_num [K,L,Real.diam_Icc]

theorem no_congruence (f g : ℝ → ℝ) (hf : Isometry f) (hg : Isometry g) :
    f '' K ≠ g '' L := by
  intro heq
  have hd := congrArg diam heq
  rw [hf.diam_image, hg.diam_image, different_diameters.1,
    different_diameters.2] at hd
  norm_num at hd

end Counterexample
#print axioms Counterexample.bodies
#print axioms Counterexample.symmetric_neighborhood
#print axioms Counterexample.mem_perp
#print axioms Counterexample.chart_volume_one
#print axioms Counterexample.same_sphere_data
#print axioms Counterexample.no_congruence
