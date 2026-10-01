import Main

/-! Axiom audit: every theorem of the disproof must report
    "does not depend on any axioms" (zero axioms, zero `sorry`). -/

#print axioms lattice_trivial
#print axioms zero_in_lattice
#print axioms no_graver_elements
#print axioms graverBox_empty
#print axioms graverBox_card
#print axioms rhsK2_eq
#print axioms rhsK2_ge
#print axioms conjecture_544_fails

-- Sanity re-checks inside the auditor.
example : graverBox.length = 0 := by decide
example : (0 : Nat) ≠ rhsK2 ∧ (4 : Nat) ≤ rhsK2 ∧ rhsK2 = 8 := by decide
