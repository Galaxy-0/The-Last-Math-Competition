import Conjecture9028.Definitions
import Conjecture9028.A2
import Conjecture9028.Diagonal

noncomputable section

namespace Conjecture9028

theorem a2_integral : IntegralLattice A2.lattice := A2.integral_pairing

theorem a2_even : EvenLattice A2.lattice := A2.even_inner

theorem a2_determinant_not_even : ¬ EvenDeterminant A2.realBasis :=
  A2.realGram_det_not_even

/-- Even determinant is not necessary, even among positive-definite integral lattices. -/
theorem determinant_not_necessary : ¬ EvenDeterminantNecessary := by
  intro h
  exact a2_determinant_not_even (h A2.space 2 A2.realBasis a2_integral a2_even)

/-- Even determinant is not sufficient, even among positive-definite integral lattices. -/
theorem determinant_not_sufficient : ¬ EvenDeterminantSufficient := by
  intro h
  exact Diagonal.not_even
    (h Diagonal.plane 2 Diagonal.realBasis Diagonal.integral_pairings
      Diagonal.even_determinant)

/-- Both interpretations of a determinant parity criterion fail. -/
theorem both_directions_fail : ¬ EvenDeterminantNecessary ∧ ¬ EvenDeterminantSufficient :=
  ⟨determinant_not_necessary, determinant_not_sufficient⟩

/-- The explicit lattice-evenness criterion in conjecture 9028 is false. -/
theorem conjecture_false : ¬ ClaimedEvennessCriterion := by
  intro h
  apply determinant_not_necessary
  intro E _ _ n b hi he
  exact (h E n b hi).mp he

end Conjecture9028
