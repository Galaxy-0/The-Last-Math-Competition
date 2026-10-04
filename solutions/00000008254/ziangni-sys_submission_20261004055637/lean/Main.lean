import Mathlib.Tactic

namespace ZeroGameCounterexample
noncomputable section
open scoped BigOperators

abbrev Action := Fin 2
abbrev PayoffMatrix := Matrix Action Action ℝ

def ValidStrategy (p : Action → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

def Strategy := {p : Action → ℝ // ValidStrategy p}

def pure (j : Action) : Strategy :=
  ⟨fun i => if i = j then 1 else 0, by
    constructor
    · intro i; dsimp; split_ifs <;> norm_num
    · fin_cases j <;> norm_num [Fin.sum_univ_two]⟩

theorem pure_distinct : pure 0 ≠ pure 1 := by
  intro h
  have he := congrArg (fun p : Strategy => p.val 0) h
  norm_num [pure] at he

theorem distinct_mutant (p : Strategy) : ∃ q : Strategy, q ≠ p := by
  by_cases h : pure 0 = p
  · exact ⟨pure 1, by intro he; exact pure_distinct (h.trans he.symm)⟩
  · exact ⟨pure 0, h⟩

def expectedPayoff (A : PayoffMatrix) (p q : Action → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * A i j * q j

def zeroGame : PayoffMatrix := 0

theorem zero_payoff (p q : Action → ℝ) : expectedPayoff zeroGame p q = 0 := by
  simp [expectedPayoff, zeroGame]

-- The opponent receives the same payoff rule with the two arguments exchanged.
def symmetricGame (A : PayoffMatrix) :
    (Action × Action → ℝ) × (Action × Action → ℝ) :=
  (fun ij => A ij.1 ij.2, fun ij => A ij.2 ij.1)

theorem actual_symmetric_zero_game (i j : Action) :
    (symmetricGame zeroGame).1 (i,j) = 0 ∧
    (symmetricGame zeroGame).2 (i,j) = 0 := by
  simp [symmetricGame, zeroGame]

def mixture (p q : Action → ℝ) (ε : ℝ) : Action → ℝ :=
  fun i => (1-ε)*p i + ε*q i

theorem mixture_valid (p q : Strategy) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ValidStrategy (mixture p.val q.val ε) := by
  constructor
  · intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hε1) (p.property.1 i))
      (mul_nonneg hε (q.property.1 i))
  · simp only [mixture, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [p.property.2, q.property.2]
    ring

-- Standard strict Maynard Smith payoff criterion, including the neutral tie case.
def ESS (A : PayoffMatrix) (p : Strategy) : Prop :=
  ∀ q : Strategy, q ≠ p →
    expectedPayoff A p.val p.val > expectedPayoff A q.val p.val ∨
    (expectedPayoff A p.val p.val = expectedPayoff A q.val p.val ∧
      expectedPayoff A p.val q.val > expectedPayoff A q.val q.val)

-- Direct small-invasion formulation, with actual population mixture.
def InvasionESS (A : PayoffMatrix) (p : Strategy) : Prop :=
  ∀ q : Strategy, q ≠ p → ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → ε < δ → ε ≤ 1 →
      expectedPayoff A p.val (mixture p.val q.val ε) >
        expectedPayoff A q.val (mixture p.val q.val ε)

theorem no_ess (p : Strategy) : ¬ ESS zeroGame p := by
  intro h
  obtain ⟨q, hq⟩ := distinct_mutant p
  have he := h q hq
  simp only [zero_payoff] at he
  rcases he with he | ⟨_, he⟩ <;> linarith

theorem no_invasion_ess (p : Strategy) : ¬ InvasionESS zeroGame p := by
  intro h
  obtain ⟨q, hq⟩ := distinct_mutant p
  obtain ⟨δ, hδ, hfitness⟩ := h q hq
  let ε : ℝ := min δ 1 / 2
  have hmin : 0 < min δ 1 := lt_min hδ (by norm_num)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεlt : ε < δ := by
    have hm := min_le_left δ 1
    dsimp [ε]
    linarith
  have hε1 : ε ≤ 1 := by
    have hm := min_le_right δ 1
    dsimp [ε]
    linarith
  have hvalid := mixture_valid p q ε (le_of_lt hε) hε1
  have he := hfitness ε hε hεlt hε1
  simp only [zero_payoff] at he
  linarith

theorem counterexample :
    Fintype.card Action = 2 ∧
    (∀ p : Strategy, ¬ ESS zeroGame p) ∧
    (∀ p : Strategy, ¬ InvasionESS zeroGame p) :=
  ⟨by simp, no_ess, no_invasion_ess⟩

#print axioms distinct_mutant
#print axioms actual_symmetric_zero_game
#print axioms zero_payoff
#print axioms mixture_valid
#print axioms no_ess
#print axioms no_invasion_ess
#print axioms counterexample
end
end ZeroGameCounterexample
