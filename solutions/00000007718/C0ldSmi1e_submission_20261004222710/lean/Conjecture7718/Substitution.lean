import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Count
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-! An explicit family of genuine three-letter substitutions and their incidence matrices. -/

namespace Conjecture7718

abbrev Letter := Fin 3

def Substitution := Letter → List Letter

/-- Column j records the letter counts in the substituted word for j. -/
def incidenceCounts (σ : Substitution) : Matrix Letter Letter ℕ :=
  fun i j => (σ j).count i

/-- Complexification of the actual integer incidence matrix. -/
def incidenceMatrix (σ : Substitution) : Matrix Letter Letter ℂ :=
  fun i j => (incidenceCounts σ i j : ℂ)

def familyCounts (m : ℕ) : Matrix Letter Letter ℕ :=
  !![m + 2, m, m + 1; m, m + 3, m; m + 1, m, m + 2]

/-- Each matrix column is realized by an actual word, in increasing letter order. -/
def substitution (m : ℕ) : Substitution := fun j =>
  List.replicate (familyCounts m 0 j) 0 ++
    List.replicate (familyCounts m 1 j) 1 ++
      List.replicate (familyCounts m 2 j) 2

def wordMap (σ : Substitution) (w : List Letter) : List Letter := w.flatMap σ

def iterateWord (σ : Substitution) (k : ℕ) (w : List Letter) : List Letter :=
  (wordMap σ)^[k] w

/-- Every letter occurs in every sufficiently iterated single-letter word. -/
def PrimitiveSubstitution (σ : Substitution) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∀ a b : Letter, a ∈ iterateWord σ k [b]

theorem iterateWord_one (σ : Substitution) (b : Letter) :
    iterateWord σ 1 [b] = σ b := by
  simp [iterateWord, wordMap]

theorem incidenceCounts_substitution (m : ℕ) :
    incidenceCounts (substitution m) = familyCounts m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [incidenceCounts, substitution, familyCounts, List.count_replicate]

theorem incidenceMatrix_substitution (m : ℕ) :
    incidenceMatrix (substitution m) =
      !![(m : ℂ) + 2, (m : ℂ), (m : ℂ) + 1;
         (m : ℂ), (m : ℂ) + 3, (m : ℂ);
         (m : ℂ) + 1, (m : ℂ), (m : ℂ) + 2] := by
  ext i j
  simp only [incidenceMatrix, incidenceCounts_substitution]
  fin_cases i <;> fin_cases j <;> simp [familyCounts]

theorem substitution_length (m : ℕ) (j : Letter) :
    (substitution m j).length = 3 * m + 3 := by
  fin_cases j <;> simp [substitution, familyCounts] <;> omega

theorem substitution_nonempty (m : ℕ) (j : Letter) : substitution m j ≠ [] := by
  intro h
  have hlen := substitution_length m j
  rw [h] at hlen
  simp only [List.length_nil] at hlen
  omega

theorem familyCounts_pos (m : ℕ) (hm : 1 ≤ m) (i j : Letter) :
    0 < familyCounts m i j := by
  fin_cases i <;> fin_cases j <;> simp [familyCounts] <;> omega

theorem every_letter_mem_substitution (m : ℕ) (hm : 1 ≤ m) (a b : Letter) :
    a ∈ substitution m b := by
  apply List.count_pos_iff.mp
  change 0 < incidenceCounts (substitution m) a b
  rw [incidenceCounts_substitution]
  exact familyCounts_pos m hm a b

theorem substitution_primitive (m : ℕ) (hm : 1 ≤ m) :
    PrimitiveSubstitution (substitution m) := by
  refine ⟨1, by norm_num, ?_⟩
  intro a b
  rw [iterateWord_one]
  exact every_letter_mem_substitution m hm a b

/-- Primitivity also has its usual incidence-matrix certificate, already at power one. -/
theorem incidenceCounts_substitution_pow_one_pos (m : ℕ) (hm : 1 ≤ m)
    (i j : Letter) : 0 < ((incidenceCounts (substitution m)) ^ 1) i j := by
  simpa [incidenceCounts_substitution] using familyCounts_pos m hm i j

theorem incidenceCounts_substitution_transpose (m : ℕ) :
    (incidenceCounts (substitution m)).transpose = incidenceCounts (substitution m) := by
  rw [incidenceCounts_substitution]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem incidenceMatrix_substitution_transpose (m : ℕ) :
    (incidenceMatrix (substitution m)).transpose = incidenceMatrix (substitution m) := by
  ext i j
  have h := congrFun (congrFun (incidenceCounts_substitution_transpose m) i) j
  exact congrArg (fun n : ℕ => (n : ℂ)) h

end Conjecture7718
