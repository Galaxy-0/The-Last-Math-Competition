import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic.NormNum

open Module

namespace Conjecture928

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The actual point spectrum, using Mathlib's nonzero-eigenvector definition. -/
def pointSpectrum (T : H →L[ℂ] H) : Set ℂ :=
  {z | Module.End.HasEigenvalue T.toLinearMap z}

/-- A nonzero, proper, closed, invariant linear subspace. -/
def HasClosedInvariantSubspace (T : H →L[ℂ] H) : Prop :=
  ∃ S : Submodule ℂ H, IsClosed (S : Set H) ∧ S ≠ ⊥ ∧ S ≠ ⊤ ∧
    ∀ x ∈ S, T x ∈ S

/-- The unit circle is contained in the closure of the point spectrum.
This is weaker than requiring the point spectrum to be a dense subset of it. -/
def DensePointSpectrumOnCircle (T : H →L[ℂ] H) : Prop :=
  {z : ℂ | ‖z‖ = 1} ⊆ closure (pointSpectrum T)

theorem no_invariant_subspace_point_spectrum_subsingleton (T : H →L[ℂ] H)
    (hno : ¬ HasClosedInvariantSubspace T) : (pointSpectrum T).Subsingleton := by
  have eigTop (z : ℂ) (hz : Module.End.HasEigenvalue T.toLinearMap z) :
      Module.End.eigenspace T.toLinearMap z = ⊤ := by
    by_contra htop
    apply hno
    refine ⟨Module.End.eigenspace T.toLinearMap z, ContinuousLinearMap.isClosed_eigenspace T z,
      hz, htop, ?_⟩
    intro x hx
    exact Module.End.eigenspace_mem_invtSubmodule T.toLinearMap z hx
  intro a ha b hb
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  have hbv : T v = b • v := by
    apply Module.End.mem_eigenspace_iff.mp
    rw [eigTop b hb]
    trivial
  exact smul_left_injective ℂ hv.2 (hv.apply_eq_smul.symm.trans hbv)

/-- The density conjunct alone forces a nontrivial closed invariant subspace. -/
theorem dense_point_spectrum_forces_invariant_subspace (T : H →L[ℂ] H)
    (hd : DensePointSpectrumOnCircle T) : HasClosedInvariantSubspace T := by
  by_contra hno
  have hs := (no_invariant_subspace_point_spectrum_subsingleton T hno).closure
  have hone : (1 : ℂ) ∈ closure (pointSpectrum T) := hd (by simp)
  have hneg : (-1 : ℂ) ∈ closure (pointSpectrum T) := hd (by simp)
  have hbad : (1 : ℂ) = -1 := hs hone hneg
  norm_num at hbad

theorem conjecture_928_false (T : H →L[ℂ] H) :
    ¬ (DensePointSpectrumOnCircle T ∧ ¬ HasClosedInvariantSubspace T) := by
  rintro ⟨hd, hno⟩
  exact hno (dense_point_spectrum_forces_invariant_subspace T hd)

end Conjecture928
