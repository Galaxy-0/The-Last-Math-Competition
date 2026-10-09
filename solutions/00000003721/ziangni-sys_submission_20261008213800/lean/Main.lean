import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
namespace MagneticStarDegeneracy
abbrev V := Fin 4
def graph : SimpleGraph V where
  Adj i j := i ≠ j ∧ (i = 0 ∨ j = 0)
  symm i j h := ⟨Ne.symm h.1,h.2.symm⟩
  loopless i h := h.1 rfl
instance : DecidableRel graph.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (i=0 ∨ j=0)))
theorem graph_connected : graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨0, fun w => ?_⟩
  by_cases h : w = 0
  · subst w; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ⟨Ne.symm h, Or.inl rfl⟩
lemma degree_values : ∀ i : V, graph.degree i = ![3,1,1,1] i := by decide

-- Unit-modulus edge phases, equivalently unitary complex scalars.
def UnitPhases (z : Fin 3 → ℂ) : Prop := ∀ i, z i * star (z i) = 1
lemma phase_star_nonzero (z : Fin 3 → ℂ) (hz : UnitPhases z) (i : Fin 3) :
    star (z i) ≠ 0 := by
  intro h
  have hh := hz i
  rw [h, mul_zero] at hh
  exact zero_ne_one hh

def magneticAdj (z : Fin 3 → ℂ) : Matrix V V ℂ :=
  !![0,z 0,z 1,z 2; star (z 0),0,0,0;
     star (z 1),0,0,0; star (z 2),0,0,0]
def D : Matrix V V ℂ := Matrix.diagonal fun i => graph.degree i
def L (z : Fin 3 → ℂ) : Matrix V V ℂ :=
  !![3,-z 0,-z 1,-z 2; -star (z 0),1,0,0;
     -star (z 1),0,1,0; -star (z 2),0,0,1]
theorem actual_laplacian (z : Fin 3 → ℂ) : L z = D - magneticAdj z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [L,D,magneticAdj,Matrix.diagonal,degree_values]
theorem hermitian (z : Fin 3 → ℂ) : (L z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [L]

def v (z : Fin 3 → ℂ) : V → ℂ := ![0,star (z 0),-star (z 1),0]
def w (z : Fin 3 → ℂ) : V → ℂ := ![0,star (z 0),0,-star (z 2)]
theorem eigen_v (z : Fin 3 → ℂ) (hz : UnitPhases z) : (L z).mulVec (v z) = v z := by
  have hc : ∀ i, z i * (starRingEnd ℂ) (z i) = 1 := hz
  funext i
  fin_cases i <;> simp [L,v,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hc 0,hc 1,hc 2]
theorem eigen_w (z : Fin 3 → ℂ) (hz : UnitPhases z) : (L z).mulVec (w z) = w z := by
  have hc : ∀ i, z i * (starRingEnd ℂ) (z i) = 1 := hz
  funext i
  fin_cases i <;> simp [L,w,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hc 0,hc 1,hc 2]
abbrev eigenspaceOne (z : Fin 3 → ℂ) := Module.End.eigenspace (L z).mulVecLin (1 : ℂ)
def eigenPair (z : Fin 3 → ℂ) (hz : UnitPhases z) : Fin 2 → eigenspaceOne z :=
  ![⟨v z, by rw [Module.End.mem_eigenspace_iff]; simpa using eigen_v z hz⟩,
    ⟨w z, by rw [Module.End.mem_eigenspace_iff]; simpa using eigen_w z hz⟩]
theorem independent (z : Fin 3 → ℂ) (hz : UnitPhases z) :
    LinearIndependent ℂ (eigenPair z hz) := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have hh := congrArg (fun x : eigenspaceOne z => x.val 3) h
    have hn := phase_star_nonzero z hz 2
    simp [eigenPair,w] at hh
    exact hn (by simpa using congrArg star hh)
  · intro a h
    have hh := congrArg (fun x : eigenspaceOne z => x.val 2) h
    have hn := phase_star_nonzero z hz 1
    simp [eigenPair,v,w] at hh
    exact hn (by simpa using congrArg star hh)

theorem persistent_degeneracy (z : Fin 3 → ℂ) (hz : UnitPhases z) :
    2 ≤ Module.finrank ℂ (eigenspaceOne z) := by
  simpa using (independent z hz).fintype_card_le_finrank
-- No phase tuple has a simple eigenvalue-one eigenspace, so no generic
-- subset of admissible phases can have an entirely nondegenerate spectrum.
theorem no_phase_removes_degeneracy :
    ¬ ∃ z : Fin 3 → ℂ, UnitPhases z ∧ Module.finrank ℂ (eigenspaceOne z) ≤ 1 := by
  rintro ⟨z,hz,h⟩
  have := persistent_degeneracy z hz
  omega

#print axioms graph_connected
#print axioms actual_laplacian
#print axioms hermitian
#print axioms eigen_v
#print axioms eigen_w
#print axioms independent
#print axioms persistent_degeneracy
#print axioms no_phase_removes_degeneracy
end MagneticStarDegeneracy
