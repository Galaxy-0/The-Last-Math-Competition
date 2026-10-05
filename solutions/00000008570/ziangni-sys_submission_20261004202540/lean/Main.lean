import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open scoped Topology
namespace FredholmComponents
abbrev H := lp (fun _ : ℕ => ℂ) 2
abbrev Op := H →L[ℂ] H

def standardBasis : HilbertBasis ℕ ℂ H :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ H)

theorem infinite_dimension : ¬ FiniteDimensional ℂ H := by
  intro h
  letI := h
  have hc := standardBasis.orthonormal.linearIndependent.lt_aleph0_of_finiteDimensional
  simp at hc

/-- The full standard bounded-operator Fredholm criterion. -/
def Fredholm (A : Op) : Prop :=
  IsClosed (Set.range A) ∧
  FiniteDimensional ℂ (LinearMap.ker A.toLinearMap) ∧
  FiniteDimensional ℂ (H ⧸ LinearMap.range A.toLinearMap)

/-- The integer index, used below only on Fredholm operators. -/
def index (A : Op) : ℤ :=
  (Module.finrank ℂ (LinearMap.ker A.toLinearMap) : ℤ) -
  (Module.finrank ℂ (H ⧸ LinearMap.range A.toLinearMap) : ℤ)

/-- The Fredholm essential spectrum, not a prescribed spectral table. -/
def essentialSpectrum (A : Op) : Set ℂ :=
  {z | ¬ Fredholm (A - z • (1 : Op))}

def scalar (a : ℂ) : Op := a • (1 : Op)

@[simp] theorem scalar_apply (a : ℂ) (x : H) : scalar a x = a • x := rfl

theorem scalar_injective (a : ℂ) (ha : a ≠ 0) : Function.Injective (scalar a) := by
  intro x y h
  have hh := congrArg (fun z : H => a⁻¹ • z) h
  simpa [scalar_apply, smul_smul, ha] using hh

theorem scalar_surjective (a : ℂ) (ha : a ≠ 0) : Function.Surjective (scalar a) := by
  intro y
  exact ⟨a⁻¹ • y, by simp [smul_smul, ha]⟩

theorem scalar_kernel (a : ℂ) (ha : a ≠ 0) :
    LinearMap.ker (scalar a).toLinearMap = ⊥ :=
  LinearMap.ker_eq_bot.mpr (scalar_injective a ha)

theorem scalar_range (a : ℂ) (ha : a ≠ 0) :
    LinearMap.range (scalar a).toLinearMap = ⊤ :=
  LinearMap.range_eq_top.mpr (scalar_surjective a ha)

theorem scalar_fredholm (a : ℂ) (ha : a ≠ 0) : Fredholm (scalar a) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.range_eq_univ.mpr (scalar_surjective a ha)]
    exact isClosed_univ
  · rw [scalar_kernel a ha]
    infer_instance
  · rw [scalar_range a ha]
    infer_instance

theorem scalar_index (a : ℂ) (ha : a ≠ 0) : index (scalar a) = 0 := by
  unfold index
  rw [scalar_kernel a ha, scalar_range a ha]
  simp [Module.finrank_zero_of_subsingleton]

theorem zero_not_fredholm : ¬ Fredholm (0 : Op) := by
  intro h
  have ht : FiniteDimensional ℂ (⊤ : Submodule ℂ H) := by
    have hh := h.2.1
    change FiniteDimensional ℂ (LinearMap.ker (0 : H →ₗ[ℂ] H)) at hh
    rw [LinearMap.ker_zero] at hh
    exact hh
  letI := ht
  have hh : FiniteDimensional ℂ H :=
    FiniteDimensional.of_surjective (Submodule.subtype (⊤ : Submodule ℂ H))
      (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
  exact infinite_dimension hh

theorem scalar_zero : scalar 0 = (0 : Op) := by simp [scalar]

theorem scalar_sub (a z : ℂ) : scalar a - z • (1 : Op) = scalar (a-z) := by
  simp only [scalar, sub_smul]

theorem essential_scalar (a : ℂ) : essentialSpectrum (scalar a) = {a} := by
  ext z
  change (¬ Fredholm (scalar a - z • (1 : Op))) ↔ z = a
  rw [scalar_sub]
  constructor
  · intro h
    by_contra hn
    exact h (scalar_fredholm (a-z) (sub_ne_zero.mpr (Ne.symm hn)))
  · intro hz
    subst z
    simpa [scalar] using zero_not_fredholm

abbrev Domain := {A : Op // Fredholm A}
def first : Domain := ⟨scalar 1, scalar_fredholm 1 one_ne_zero⟩
def second : Domain := ⟨scalar 2, scalar_fredholm 2 (by norm_num)⟩

def joiningPath : Path first second where
  toFun t := ⟨scalar (Complex.ofReal ((1 : ℝ) + (t : ℝ))),
    scalar_fredholm _ (by
      apply Complex.ofReal_ne_zero.mpr
      have ht := t.property.1
      linarith)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun t : unitInterval =>
      Complex.ofReal ((1 : ℝ) + (t : ℝ)) • (1 : Op))
    exact (Complex.continuous_ofReal.comp (continuous_const.add continuous_subtype_val)).smul continuous_const
  source' := by apply Subtype.ext; simp [first]
  target' := by apply Subtype.ext; norm_num [second]

theorem same_component : second ∈ connectedComponent first :=
  pathComponent_subset_component first ⟨joiningPath⟩

theorem equal_indices : index first.val = 0 ∧ index second.val = 0 :=
  ⟨scalar_index 1 one_ne_zero, scalar_index 2 (by norm_num)⟩

theorem different_essential_spectra :
    essentialSpectrum first.val ≠ essentialSpectrum second.val := by
  change essentialSpectrum (scalar 1) ≠ essentialSpectrum (scalar 2)
  rw [essential_scalar, essential_scalar]
  intro h
  have hh := Set.singleton_injective h
  norm_num at hh

theorem classification_fails :
    ∃ A B : Domain, B ∈ connectedComponent A ∧
      index A.val = index B.val ∧ essentialSpectrum A.val ≠ essentialSpectrum B.val := by
  exact ⟨first, second, same_component, equal_indices.1.trans equal_indices.2.symm,
    different_essential_spectra⟩

#print axioms infinite_dimension
#print axioms scalar_kernel
#print axioms scalar_range
#print axioms scalar_fredholm
#print axioms scalar_index
#print axioms zero_not_fredholm
#print axioms essential_scalar
#print axioms same_component
#print axioms different_essential_spectra
#print axioms classification_fails
end FredholmComponents
