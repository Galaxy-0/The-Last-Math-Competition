/-!
# TLMC conjecture 00000001672: internal inconsistency

Verbatim statement:
"Definition: The Zarankiewicz formula asserts cr(K_{m,n}) = ⌊m/2⌋⌊(m−1)/2⌋⌊n/2⌋⌊(n−1)/2⌋. Conjecture: cr(K_{7,7}) = 77 (the value of the formula at the smallest open instance); that is, the Zarankiewicz formula holds for min(m,n) ≤ 7."

Reading formalized: the headline value and its asserted restatement are
joint assertions. The formula's value at (7,7) is 81, so these assertions
cannot both hold, for any natural-valued function cr. The crossing number
is left abstract in the formal proof. Separately, Woodall's computer-assisted
theorem gives cr(K_{7,7}) = 81 and cr(K_{7,9}) = 144, so the isolated
headline is false and K_{7,7} is not an open case. The smallest unsettled
cases are K_{7,11} and K_{9,9}. This published result is cited, not formalized:
D. R. Woodall, "Cyclic-order graphs and Zarankiewicz's crossing-number
conjecture", J. Graph Theory 17 (1993), 657–671,
https://doi.org/10.1002/jgt.3190170602.
The positive-parameter reading is also refuted. A bare logical equivalence
can have both sides false, as demonstrated by an abstract zero function;
we do not claim to refute that equivalence for every function.

No imports are needed: the proof uses core natural-number arithmetic.
-/

set_option autoImplicit false

namespace ZarankiewiczConsistency

local notation "ℕ" => Nat

/-- The displayed Zarankiewicz product, using natural division. -/
def Z (m n : ℕ) : ℕ := (m / 2) * ((m - 1) / 2) * (n / 2) * ((n - 1) / 2)

/-- All four factors at (7,7) are 3. -/
theorem Z_seven : Z 7 7 = 81 := by
  decide

/-- Refutation of the explicit parenthetical numerical assertion. -/
theorem not_value_of_formula : Z 7 7 ≠ 77 := by
  decide

/-- Even the local formula equality contradicts the headline. -/
theorem local_inconsistent (cr : ℕ → ℕ → ℕ) :
    ¬ (cr 7 7 = 77 ∧ cr 7 7 = Z 7 7) := by
  intro h
  exact not_value_of_formula (h.2.symm.trans h.1)

/-- The main refutation: the headline and the stated range are inconsistent. -/
theorem conjecture_inconsistent (cr : ℕ → ℕ → ℕ) :
    ¬ (cr 7 7 = 77 ∧ ∀ m n, min m n ≤ 7 → cr m n = Z m n) := by
  intro h
  exact local_inconsistent cr ⟨h.1, h.2 7 7 (by decide)⟩

/-- The claimed restatement implies that the headline is false. -/
theorem formula_range_excludes_77 (cr : ℕ → ℕ → ℕ) :
    (∀ m n, min m n ≤ 7 → cr m n = Z m n) → cr 7 7 ≠ 77 := by
  intro h h77
  exact conjecture_inconsistent cr ⟨h77, h⟩

/-- Restricting the range to positive graph parameters changes nothing. -/
theorem positive_parameters_inconsistent (cr : ℕ → ℕ → ℕ) :
    ¬ (cr 7 7 = 77 ∧
      ∀ m n, 1 ≤ m → 1 ≤ n → min m n ≤ 7 → cr m n = Z m n) := by
  intro h
  exact local_inconsistent cr ⟨h.1, h.2 7 7 (by decide) (by decide) (by decide)⟩

/-- A bare equivalence is satisfiable for an abstract function (both sides false).
This witness is not asserted to model crossing numbers. -/
theorem equivalence_reading_has_abstract_model :
    ∃ cr : ℕ → ℕ → ℕ,
      (cr 7 7 = 77 ↔ ∀ m n, min m n ≤ 7 → cr m n = Z m n) := by
  refine ⟨fun _ _ => 0, ?_⟩
  constructor
  · intro h
    exact False.elim ((by decide : (0 : ℕ) ≠ 77) h)
  · intro h
    have hz : (0 : ℕ) = Z 7 7 := h 7 7 (by decide)
    rw [Z_seven] at hz
    exact False.elim ((by decide : (0 : ℕ) ≠ 81) hz)

end ZarankiewiczConsistency

#print axioms ZarankiewiczConsistency.Z_seven
#print axioms ZarankiewiczConsistency.not_value_of_formula
#print axioms ZarankiewiczConsistency.local_inconsistent
#print axioms ZarankiewiczConsistency.conjecture_inconsistent
#print axioms ZarankiewiczConsistency.formula_range_excludes_77
#print axioms ZarankiewiczConsistency.positive_parameters_inconsistent
#print axioms ZarankiewiczConsistency.equivalence_reading_has_abstract_model
