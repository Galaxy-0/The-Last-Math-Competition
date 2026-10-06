import Std

namespace Tlmc8458

variable {Link : Type}
variable (width crossingNumber : Link → Nat)
variable (isAlternating : Link → Prop)

/-- The source definition: quasi-alternating means width exactly one. -/
def IsQuasiAlternating (K : Link) : Prop := width K = 1

def IsNonalternating (K : Link) : Prop := ¬ isAlternating K

/-- “The smallest ... has ...” entails existence, the stated properties,
    and minimality of its crossing number. -/
def StatedSmallestExample : Prop :=
  ∃ K : Link,
    IsQuasiAlternating width K ∧
    IsNonalternating isAlternating K ∧
    crossingNumber K = 11 ∧
    width K = 2 ∧
    ∀ L : Link,
      IsQuasiAlternating width L →
      IsNonalternating isAlternating L →
      crossingNumber K ≤ crossingNumber L

/-- The source's conjunction is false because the second clause is
    inconsistent with the stated definition of quasi-alternating. -/
def SourceClaim : Prop :=
  (∀ K : Link, isAlternating K → IsQuasiAlternating width K) ∧
    StatedSmallestExample width crossingNumber isAlternating

theorem no_stated_smallest_example :
    ¬ StatedSmallestExample width crossingNumber isAlternating := by
  intro h
  rcases h with ⟨K, hQA, _hNonalt, _hCrossing, hWidth, _hMinimal⟩
  change width K = 1 at hQA
  have hOneEqTwo : (1 : Nat) = 2 := hQA.symm.trans hWidth
  have hImpossible : ¬ (1 : Nat) = 2 := by decide
  exact hImpossible hOneEqTwo

theorem source_claim_false : ¬ SourceClaim width crossingNumber isAlternating := by
  intro h
  exact no_stated_smallest_example width crossingNumber isAlternating h.2

end Tlmc8458
