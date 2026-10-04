import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.NormNum

namespace CommutativityCheckCounterexample

-- The actual symmetry group of the square, with Mathlib's group operations.
abbrev G := DihedralGroup 4

def detectedPairs : Finset (G × G) :=
  Finset.univ.filter (fun p => p.1 * p.2 ≠ p.2 * p.1)

def commutingPairs : Finset (G × G) :=
  Finset.univ.filter (fun p => p.1 * p.2 = p.2 * p.1)

-- Each draw is uniform; the joint mass is the product of the two draw masses.
def drawWeight (_ : G) : ℚ := 1 / (Fintype.card G : ℚ)
def pairWeight (p : G × G) : ℚ := drawWeight p.1 * drawWeight p.2
def detectionProbability : ℚ := ∑ p ∈ detectedPairs, pairWeight p

theorem group_card : Fintype.card G = 8 := by decide
theorem pair_card : Fintype.card (G × G) = 64 := by decide

theorem genuine_noncommuting_witness :
    (DihedralGroup.r 1 : G) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * (DihedralGroup.r 1 : G) := by decide

theorem detected_pair_count : detectedPairs.card = 24 := by decide
theorem commuting_pair_count : commutingPairs.card = 40 := by decide

theorem independent_uniform_pair_weight (p : G × G) : pairWeight p = 1 / 64 := by
  norm_num [pairWeight, drawWeight, group_card]

theorem uniform_draw_total_mass : (∑ x : G, drawWeight x) = 1 := by
  simp only [drawWeight, Finset.sum_const, Finset.card_univ, group_card, nsmul_eq_mul]
  norm_num

theorem uniform_pair_mass_nonnegative (p : G × G) : 0 ≤ pairWeight p := by
  rw [independent_uniform_pair_weight]
  norm_num

theorem uniform_pair_total_mass :
    (∑ p : G × G, pairWeight p) = 1 := by
  simp only [independent_uniform_pair_weight, Finset.sum_const, Finset.card_univ,
    pair_card, nsmul_eq_mul]
  norm_num

theorem actual_detection_probability : detectionProbability = 3 / 8 := by
  simp only [detectionProbability, independent_uniform_pair_weight, Finset.sum_const,
    detected_pair_count, nsmul_eq_mul]
  norm_num

theorem single_check_below_half : detectionProbability < 1 / 2 := by
  rw [actual_detection_probability]
  norm_num

-- Actual noncommutative group, valid sampling distribution, and failed lower bound.
theorem conjecture_5449_counterexample :
    Fintype.card G = 8 ∧
    (∃ x y : G, x * y ≠ y * x) ∧
    (∀ p : G × G, 0 ≤ pairWeight p) ∧
    (∑ p : G × G, pairWeight p) = 1 ∧
    detectionProbability = 3 / 8 ∧ ¬ ((1 / 2 : ℚ) ≤ detectionProbability) :=
  ⟨group_card, ⟨DihedralGroup.r 1, DihedralGroup.sr 0, genuine_noncommuting_witness⟩,
    uniform_pair_mass_nonnegative, uniform_pair_total_mass, actual_detection_probability,
    not_le_of_gt single_check_below_half⟩

end CommutativityCheckCounterexample

#print axioms CommutativityCheckCounterexample.genuine_noncommuting_witness
#print axioms CommutativityCheckCounterexample.detected_pair_count
#print axioms CommutativityCheckCounterexample.uniform_pair_total_mass
#print axioms CommutativityCheckCounterexample.actual_detection_probability
#print axioms CommutativityCheckCounterexample.conjecture_5449_counterexample
