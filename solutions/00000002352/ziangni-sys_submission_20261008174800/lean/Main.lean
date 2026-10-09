import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open Matrix
open scoped ComplexOrder
noncomputable section
namespace FreePickCounterexample

-- All matrix sizes, with the genuine operator norm on C^n.
abbrev Space (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Operator (n : ℕ) := Space n →L[ℂ] Space n
def freePolynomial (n : ℕ) (X : Operator n) : Operator n := X
def matrixBall (n : ℕ) : Set (Operator n) := {X | ‖X‖ < 1}

theorem graded_analytic (n : ℕ) (X : Operator n) :
    AnalyticAt ℂ (freePolynomial n) X := analyticAt_id

theorem graded_strictly_contractive (n : ℕ) (X : Operator n)
    (hX : X ∈ matrixBall n) : ‖freePolynomial n X‖ < 1 := hX

-- Intertwining is the defining nc compatibility, including similarities
-- and the canonical inclusions of block direct sums.
theorem respects_intertwiners (m n : ℕ) (X : Operator m) (Y : Operator n)
    (S : Space m →L[ℂ] Space n) (h : S.comp X = Y.comp S) :
    S.comp (freePolynomial m X) = (freePolynomial n Y).comp S := h

-- Level-one Szego kernel: the sum over free words in one generator.
def szego (z w : ℂ) : ℂ := (1 - z * star w)⁻¹
theorem szego_series (z w : ℂ) (h : ‖z * star w‖ < 1) :
    (∑' k : ℕ, (z * star w)^k) = szego z w :=
  tsum_geometric_of_norm_lt_one h

def node : Fin 2 → ℂ := ![0, 1/2]
def target : Fin 2 → ℂ := node
def pick : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (1 - target i * star (target j)) * szego (node i) (node j)

theorem nodes_in_ball (i : Fin 2) : ‖node i‖ < 1 := by
  fin_cases i <;> norm_num [node, Complex.norm_def]

theorem distinct_nodes : node 0 ≠ node 1 := by norm_num [node]
theorem interpolation (i : Fin 2) : id (node i) = target i := rfl

theorem pick_entries (i j : Fin 2) : pick i j = 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [pick, target, node, szego]

def witness : Fin 2 → ℂ := ![1, -1]
theorem pick_not_positive_definite : ¬ pick.PosDef := by
  intro h
  have hn : witness ≠ 0 := by
    intro he
    have := congrFun he 0
    norm_num [witness] at this
  have hp := h.2 witness hn
  have hz : dotProduct (star witness) (pick *ᵥ witness) = 0 := by
    simp [dotProduct, mulVec, Fin.sum_univ_two, witness, pick_entries]
  rw [hz] at hp
  exact (lt_irrefl (0 : ℂ)) hp

#print axioms graded_analytic
#print axioms graded_strictly_contractive
#print axioms respects_intertwiners
#print axioms szego_series
#print axioms nodes_in_ball
#print axioms interpolation
#print axioms pick_not_positive_definite
end FreePickCounterexample
