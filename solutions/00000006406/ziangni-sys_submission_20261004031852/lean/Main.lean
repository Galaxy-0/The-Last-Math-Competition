import Mathlib.Data.Set.SymmDiff
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.InformationTheory.Hamming

namespace ComplementIsometry

open scoped symmDiff

-- Explicit De Morgan identities, proved pointwise.
theorem deMorgan_union {α : Type*} (A B : Set α) :
    (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff]
  exact not_or

theorem deMorgan_intersection {α : Type*} (A B : Set α) :
    (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  classical
  ext x
  simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union]
  exact not_and_or

theorem double_complement {α : Type*} (A : Set α) : Aᶜᶜ = A :=
  compl_compl A

theorem complement_difference {α : Type*} (A B : Set α) :
    Aᶜ \ Bᶜ = B \ A := by
  ext x
  simp only [Set.mem_diff, Set.mem_compl_iff, not_not]
  exact and_comm

theorem complement_symmetric_difference {α : Type*} (A B : Set α) :
    Aᶜ ∆ Bᶜ = A ∆ B := by
  rw [Set.symmDiff_def, complement_difference, complement_difference,
    Set.union_comm, ← Set.symmDiff_def]

def differenceDistance {α β : Type*} (weight : Set α → β)
    (A B : Set α) : β := weight (A ∆ B)

theorem difference_distance_preserved {α β : Type*} (weight : Set α → β)
    (A B : Set α) :
    differenceDistance weight Aᶜ Bᶜ = differenceDistance weight A B := by
  unfold differenceDistance
  rw [complement_symmetric_difference]

theorem complement_isometry {α : Type*} [PseudoMetricSpace (Set α)]
    (weight : Set α → ℝ)
    (h_distance : ∀ A B : Set α, dist A B = differenceDistance weight A B) :
    Isometry (fun A : Set α => Aᶜ) := by
  apply Isometry.of_dist_eq
  intro A B
  rw [h_distance, h_distance, difference_distance_preserved]

theorem complement_involutive (α : Type*) :
    Function.Involutive (fun A : Set α => Aᶜ) :=
  double_complement

theorem composed_complement_is_identity (α : Type*) :
    (fun A : Set α => Aᶜ) ∘ (fun A : Set α => Aᶜ) = id := by
  funext A
  exact double_complement A

theorem composed_complement_involutive (α : Type*) :
    Function.Involutive ((fun A : Set α => Aᶜ) ∘ (fun A : Set α => Aᶜ)) := by
  rw [composed_complement_is_identity]
  exact fun _ => rfl

theorem conjecture_6406 {α : Type*} [PseudoMetricSpace (Set α)]
    (weight : Set α → ℝ)
    (h_distance : ∀ A B : Set α, dist A B = differenceDistance weight A B) :
    Isometry (fun A : Set α => Aᶜ) ∧
      Function.Involutive (fun A : Set α => Aᶜ) ∧
      Function.Involutive ((fun A : Set α => Aᶜ) ∘ (fun A : Set α => Aᶜ)) ∧
      (∀ A B : Set α, (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ ∧ (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ) := by
  exact ⟨complement_isometry weight h_distance, complement_involutive α,
    composed_complement_involutive α, fun A B => ⟨deMorgan_union A B,
      deMorgan_intersection A B⟩⟩

-- Concrete full-power-set metric: finite Boolean characteristic words with
-- the standard Hamming distance (the number of symmetric-difference entries).
def complementWord {ι : Type*} (x : Hamming (fun _ : ι => Bool)) :
    Hamming (fun _ : ι => Bool) :=
  Hamming.toHamming (fun i => !(Hamming.ofHamming x i))

def wordSet {ι : Type*} (x : Hamming (fun _ : ι => Bool)) : Set ι :=
  {i | Hamming.ofHamming x i = true}

theorem word_complement_is_set_complement {ι : Type*}
    (x : Hamming (fun _ : ι => Bool)) :
    wordSet (complementWord x) = (wordSet x)ᶜ := by
  ext i
  change (Bool.not (Hamming.ofHamming x i) = true) ↔ ¬ (Hamming.ofHamming x i = true)
  cases Hamming.ofHamming x i <;> simp

theorem word_mismatch_is_symmetric_difference {ι : Type*}
    (x y : Hamming (fun _ : ι => Bool)) (i : ι) :
    Hamming.ofHamming x i ≠ Hamming.ofHamming y i ↔
      i ∈ wordSet x ∆ wordSet y := by
  change (Hamming.ofHamming x i ≠ Hamming.ofHamming y i) ↔
    ((Hamming.ofHamming x i = true ∧ ¬ Hamming.ofHamming y i = true) ∨
     (Hamming.ofHamming y i = true ∧ ¬ Hamming.ofHamming x i = true))
  cases Hamming.ofHamming x i <;> cases Hamming.ofHamming y i <;> simp

theorem concrete_hamming_isometry (ι : Type*) [Fintype ι] :
    Isometry (complementWord (ι := ι)) := by
  apply Isometry.of_dist_eq
  intro x y
  change (hammingDist (fun i => !(Hamming.ofHamming x i))
    (fun i => !(Hamming.ofHamming y i)) : ℝ) =
    (hammingDist (Hamming.ofHamming x) (Hamming.ofHamming y) : ℝ)
  congr 1
  apply hammingDist_comp (fun _ b => !b)
  intro i a b hab
  cases a <;> cases b <;> simp_all

theorem concrete_complement_involutive (ι : Type*) :
    Function.Involutive (complementWord (ι := ι)) := by
  intro x
  change (fun i => !(!(Hamming.ofHamming x i))) = Hamming.ofHamming x
  funext i
  simp

end ComplementIsometry

#print axioms ComplementIsometry.complement_symmetric_difference
#print axioms ComplementIsometry.difference_distance_preserved
#print axioms ComplementIsometry.conjecture_6406
#print axioms ComplementIsometry.concrete_hamming_isometry
