import Mathlib.Order.Antichain
import Mathlib.Data.Int.Order.Basic
import Lean.Elab.Tactic.Omega

/-!
# Extremal Betti corners form an antichain

Source 00000000508 uses β_{k,k+d}. Positions below are the standard Betti
diagram coordinates (k,d), with signed d. We prove the assertion for every
numerical table β : ℕ → ℤ → ℕ, so no algebraic property of a monomial ideal
or its resolution is needed.

RawExtremal is the definition in Bayer--Charalambous--Popescu (BCP99),
"Extremal Betti Numbers and Applications to Monomial Ideals", p. 1:
https://www.math.columbia.edu/~bayer/papers/Betti_BCP99/Betti_BCP99.pdf
-/

namespace TLMC508

/-- The BCP99 definition in raw indices (homological degree, total degree). -/
def RawExtremal (β : ℕ → ℤ → ℕ) (i : ℕ) (j : ℤ) : Prop :=
  β i j ≠ 0 ∧
    ∀ l r, i ≤ l → j + 1 ≤ r → j - (i : ℤ) ≤ r - (l : ℤ) → β l r = 0

/-- Nonzero support in the signed shifted coordinates (k,d) of β_{k,k+d}. -/
def ShiftedSupport (β : ℕ → ℤ → ℕ) (p : ℕ × ℤ) : Prop :=
  β p.1 ((p.1 : ℤ) + p.2) ≠ 0

/-- Extremal positions in the standard Betti diagram coordinates (k,d). -/
def ExtremalPositions (β : ℕ → ℤ → ℕ) : Set (ℕ × ℤ) :=
  {p | RawExtremal β p.1 ((p.1 : ℤ) + p.2)}

/-- The published vanishing region is exactly maximality in shifted support. -/
theorem rawExtremal_iff_maximal_shiftedSupport
    (β : ℕ → ℤ → ℕ) (p : ℕ × ℤ) :
    RawExtremal β p.1 ((p.1 : ℤ) + p.2) ↔
      Maximal (ShiftedSupport β) p := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro q hq hpq
    have hi : p.1 ≤ q.1 := hpq.1
    have hd : p.2 ≤ q.2 := hpq.2
    by_cases heq : q = p
    · exact heq.le
    · exfalso
      have hj : (p.1 : ℤ) + p.2 + 1 ≤ (q.1 : ℤ) + q.2 := by
        have hdistinct : q.1 ≠ p.1 ∨ q.2 ≠ p.2 := by
          by_cases h1 : q.1 = p.1
          · right
            intro h2
            exact heq (Prod.ext h1 h2)
          · exact Or.inl h1
        omega
      exact hq (h.2 q.1 ((q.1 : ℤ) + q.2) hi hj (by omega))
  · intro h
    refine ⟨h.1, ?_⟩
    intro l r hi hr hd
    by_cases hβ : β l r = 0
    · exact hβ
    · exfalso
      let q : ℕ × ℤ := (l, r - (l : ℤ))
      have hq : ShiftedSupport β q := by
        change β l ((l : ℤ) + (r - (l : ℤ))) ≠ 0
        have hdegree : (l : ℤ) + (r - (l : ℤ)) = r := by omega
        rw [hdegree]
        exact hβ
      have hpq : p ≤ q := by
        refine ⟨hi, ?_⟩
        change p.2 ≤ r - (l : ℤ)
        omega
      have hqp : q ≤ p := h.2 hq hpq
      have hli : l ≤ p.1 := hqp.1
      have hshift : r - (l : ℤ) ≤ p.2 := hqp.2
      omega

/-- A set-level correspondence, using the exact raw definition. -/
theorem extremalPositions_eq_maximal_support (β : ℕ → ℤ → ℕ) :
    ExtremalPositions β = {p | Maximal (ShiftedSupport β) p} := by
  ext p
  exact rawExtremal_iff_maximal_shiftedSupport β p

/-- Source 00000000508: extremal positions of β_{k,k+d} form an antichain. -/
theorem extremal_positions_antichain (β : ℕ → ℤ → ℕ) :
    IsAntichain (· ≤ ·) (ExtremalPositions β) := by
  rw [extremalPositions_eq_maximal_support]
  exact setOfPred_maximal_antichain (ShiftedSupport β)

/-- The source statement with the extremality predicate exposed explicitly. -/
theorem exact_raw_definition_antichain (β : ℕ → ℤ → ℕ) :
    IsAntichain (· ≤ ·)
      {p : ℕ × ℤ | RawExtremal β p.1 ((p.1 : ℤ) + p.2)} :=
  extremal_positions_antichain β

/-- Distinct extremal corners are incomparable in both directions. -/
theorem distinct_extremal_corners_incomparable
    (β : ℕ → ℤ → ℕ) {p q : ℕ × ℤ}
    (hp : p ∈ ExtremalPositions β) (hq : q ∈ ExtremalPositions β)
    (hne : p ≠ q) : ¬p ≤ q ∧ ¬q ≤ p := by
  have hanti := extremal_positions_antichain β
  exact ⟨hanti hp hq hne, hanti hq hp hne.symm⟩

/-- Increasing homological degree forces strictly decreasing shifted degree. -/
theorem shifted_degree_strictly_decreases
    (β : ℕ → ℤ → ℕ) {p q : ℕ × ℤ}
    (hp : p ∈ ExtremalPositions β) (hq : q ∈ ExtremalPositions β)
    (hhom : p.1 < q.1) : q.2 < p.2 := by
  by_contra h
  have hd : p.2 ≤ q.2 := le_of_not_gt h
  have hne : p ≠ q := by
    intro heq
    have hfirst := congrArg Prod.fst heq
    omega
  exact (distinct_extremal_corners_incomparable β hp hq hne).1 ⟨hhom.le, hd⟩

end TLMC508
