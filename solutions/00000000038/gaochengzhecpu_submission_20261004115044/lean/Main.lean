import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A density-one obstruction to nontrivial sum-product identities

All entries at least 3 imply product > sum for every list of length at
least 2.  The sets {3,...,N} therefore contradict Conjecture 00000000038,
even when arbitrary repetitions and arbitrarily large N are permitted.
-/

namespace Counterexample38

theorem add_lt_mul_of_three_le {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    a + b < a * b := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hb
  nlinarith [Nat.zero_le (u * v)]

/-- A statement about arbitrary finite lists, not a finite enumeration. -/
theorem sum_lt_prod (xs : List ℕ) (hentries : ∀ x ∈ xs, 3 ≤ x)
    (hlen : 2 ≤ xs.length) : xs.sum < xs.prod := by
  induction xs with
  | nil => simp at hlen
  | cons a tail ih =>
    have ha : 3 ≤ a := hentries a (by simp)
    have ht : ∀ x ∈ tail, 3 ≤ x := fun x hx => hentries x (by simp [hx])
    cases tail with
    | nil => simp at hlen
    | cons b rest =>
      have hb : 3 ≤ b := ht b (by simp)
      cases rest with
      | nil =>
        simpa using add_lt_mul_of_three_le ha hb
      | cons c rest =>
        have htail : (b :: c :: rest).sum < (b :: c :: rest).prod :=
          ih ht (by simp)
        have hsum : 3 ≤ (b :: c :: rest).sum := by
          simp only [List.sum_cons]
          omega
        simpa only [List.sum_cons, List.prod_cons] using
          (add_lt_mul_of_three_le ha hsum).trans_le
            (Nat.mul_le_mul_left a htail.le)

/-- For entries at least 3, every sum-product identity is a singleton identity. -/
theorem only_singleton_solutions (xs : List ℕ) (hentries : ∀ x ∈ xs, 3 ≤ x)
    (heq : xs.sum = xs.prod) : xs.length = 1 := by
  by_cases hlen : 2 ≤ xs.length
  · exact False.elim ((sum_lt_prod xs hentries hlen).ne heq)
  cases xs with
  | nil => simp at heq
  | cons a tail =>
    simp only [List.length_cons] at hlen ⊢
    omega

def counterexampleSet (N : ℕ) : Finset ℕ := Finset.Icc 3 N

noncomputable def density (A : Finset ℕ) (N : ℕ) : ℝ := (A.card : ℝ) / (N : ℝ)

theorem counterexampleSet_subset (N : ℕ) :
    counterexampleSet N ⊆ Finset.Icc 1 N := by
  intro x hx
  have hx' : 3 ≤ x ∧ x ≤ N := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨by omega, hx'.2⟩

theorem counterexampleSet_card {N : ℕ} (hN : 4 ≤ N) :
    (counterexampleSet N).card = N - 2 := by
  simp only [counterexampleSet, Nat.card_Icc]
  omega

theorem counterexampleSet_half_dense {N : ℕ} (hN : 4 ≤ N) :
    (1 / 2 : ℝ) ≤ density (counterexampleSet N) N := by
  have hcount : N ≤ 2 * (counterexampleSet N).card := by
    rw [counterexampleSet_card hN]
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcount' : (N : ℝ) ≤ 2 * ((counterexampleSet N).card : ℝ) := by
    exact_mod_cast hcount
  apply (le_div_iff₀ hNpos).mpr
  linarith

theorem counterexampleSet_has_no_nontrivial_solution (N : ℕ) (xs : List ℕ)
    (hentries : ∀ x ∈ xs, x ∈ counterexampleSet N) (hlen : 2 ≤ xs.length) :
    xs.sum ≠ xs.prod := by
  apply (sum_lt_prod xs ?_ hlen).ne
  intro x hx
  exact (Finset.mem_Icc.mp (hentries x hx)).1

/-- Counterexamples exist above every bound on the ambient interval size. -/
theorem arbitrarily_large_dense_counterexamples (B : ℕ) :
    ∃ N : ℕ, B ≤ N ∧ 0 < N ∧ ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧ (1 / 2 : ℝ) ≤ density A N ∧
      ∀ xs : List ℕ, (∀ x ∈ xs, x ∈ A) → 2 ≤ xs.length → xs.sum ≠ xs.prod := by
  let N := max B 4
  have hN : 4 ≤ N := le_max_right B 4
  refine ⟨N, le_max_left B 4, by omega, counterexampleSet N,
    counterexampleSet_subset N, counterexampleSet_half_dense hN, ?_⟩
  exact counterexampleSet_has_no_nontrivial_solution N

/-- Even the weakened, eventually-in-N assertion at density 1/2 is false.
The original conjecture implies this assertion by taking delta = 1/2. -/
theorem no_uniform_length_even_eventually :
    ¬ ∃ k : ℕ, 2 ≤ k ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → (1 / 2 : ℝ) ≤ density A N →
        ∃ xs : List ℕ, xs.length = k ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = xs.prod := by
  rintro ⟨k, hk, N₀, h⟩
  obtain ⟨N, hN₀, hNpos, A, hA, hdense, hnone⟩ :=
    arbitrarily_large_dense_counterexamples N₀
  obtain ⟨xs, hlen, hentries, heq⟩ := h N hN₀ hNpos A hA hdense
  exact hnone xs hentries (by omega) heq

#print axioms sum_lt_prod
#print axioms only_singleton_solutions
#print axioms counterexampleSet_half_dense
#print axioms arbitrarily_large_dense_counterexamples
#print axioms no_uniform_length_even_eventually

end Counterexample38
