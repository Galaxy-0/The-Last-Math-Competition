import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

noncomputable section
namespace FourthMoment
abbrev V := Fin 5

def star : SimpleGraph V where
  Adj i j := i ≠ j ∧ (i = 0 ∨ j = 0)
  symm i j h := ⟨Ne.symm h.1, h.2.symm⟩
  loopless i h := h.1 rfl

/-- Canonical clique-plus-partial-vertex quasi-complete construction,
with any remaining vertices isolated. -/
def quasiComplete (k r : ℕ) : SimpleGraph V where
  Adj i j := i ≠ j ∧ ((i.val < k ∧ j.val < k) ∨
    (i.val = k ∧ j.val < r) ∨ (j.val = k ∧ i.val < r))
  symm i j h := by
    refine ⟨Ne.symm h.1, ?_⟩
    rcases h.2 with h | h | h
    · exact Or.inl ⟨h.2,h.1⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless i h := h.1 rfl

abbrev qc := quasiComplete 3 1
instance starDecidable : DecidableRel star.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ (i = 0 ∨ j = 0)))
instance qcDecidable : DecidableRel qc.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ((i.val < 3 ∧ j.val < 3) ∨
    (i.val = 3 ∧ j.val < 1) ∨ (j.val = 3 ∧ i.val < 1))))

lemma canonical_parameters : Nat.choose 3 2 ≤ 4 ∧ 4 < Nat.choose 4 2 ∧
    4 = Nat.choose 3 2 + 1 ∧ 1 < 3 := by decide

lemma star_edges : star.edgeFinset = {s(0,1),s(0,2),s(0,3),s(0,4)} := by
  ext e
  induction e using Sym2.inductionOn with
  | hf i j =>
    fin_cases i <;> fin_cases j <;>
      decide

lemma qc_edges : qc.edgeFinset = {s(0,1),s(0,2),s(1,2),s(0,3)} := by
  ext e
  induction e using Sym2.inductionOn with
  | hf i j =>
    fin_cases i <;> fin_cases j <;>
      decide

lemma same_size : Fintype.card V = 5 ∧ star.edgeFinset.card = 4 ∧ qc.edgeFinset.card = 4 := by
  rw [star_edges,qc_edges]
  decide

def starMatrix : Matrix V V ℝ :=
  ![![0,1,1,1,1], ![1,0,0,0,0], ![1,0,0,0,0], ![1,0,0,0,0], ![1,0,0,0,0]]
def qcMatrix : Matrix V V ℝ :=
  ![![0,1,1,1,0], ![1,0,1,0,0], ![1,1,0,0,0], ![1,0,0,0,0], ![0,0,0,0,0]]

lemma star_adjacency : star.adjMatrix ℝ = starMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SimpleGraph.adjMatrix, star, starMatrix]

lemma qc_adjacency : qc.adjMatrix ℝ = qcMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SimpleGraph.adjMatrix, quasiComplete, qcMatrix]

/-- Standard kth adjacency spectral moment, expressed as the genuine
trace of a matrix power (equivalently sum of kth powers of eigenvalues). -/
def moment (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℝ :=
  Matrix.trace ((G.adjMatrix ℝ)^k)

lemma star_fourth : moment star 4 = 32 := by
  rw [moment, star_adjacency]
  norm_num [starMatrix, Matrix.trace, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

lemma qc_fourth : moment qc 4 = 28 := by
  rw [moment, qc_adjacency]
  norm_num [qcMatrix, Matrix.trace, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem quasi_complete_not_extremal : ¬ ∀ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    G.edgeFinset.card = 4 → moment G 4 ≤ moment qc 4 := by
  intro h
  have hh := h star starDecidable same_size.2.1
  rw [star_fourth,qc_fourth] at hh
  norm_num at hh

end FourthMoment
#print axioms FourthMoment.canonical_parameters
#print axioms FourthMoment.star_edges
#print axioms FourthMoment.qc_edges
#print axioms FourthMoment.same_size
#print axioms FourthMoment.star_adjacency
#print axioms FourthMoment.qc_adjacency
#print axioms FourthMoment.star_fourth
#print axioms FourthMoment.qc_fourth
#print axioms FourthMoment.quasi_complete_not_extremal
