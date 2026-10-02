import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
namespace TLMC587
def S (n : ℕ) : Prop := ∃ a b : ℕ, n = 2*a + 3*b
theorem membership (n : ℕ) : S n ↔ n = 0 ∨ 2 ≤ n := by
  constructor
  · rintro ⟨a,b,h⟩; omega
  · intro h
    rcases h with h | h
    · exact ⟨0,0,by omega⟩
    · by_cases he : n % 2 = 0
      · exact ⟨n/2,0,by omega⟩
      · exact ⟨(n-3)/2,1,by omega⟩
def Apery (n : ℕ) : Prop := S n ∧ ¬ ∃ t, S t ∧ n = 25+t
def ap : Finset ℕ := (Finset.range 27).filter (fun n => (n=0 ∨ 2≤n) ∧ n≠25)
theorem apery_exact (n : ℕ) : Apery n ↔ n ∈ ap := by
  simp only [Apery, membership, ap, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hn, ht⟩
    have hlt : n < 27 := by
      by_contra h
      apply ht
      exact ⟨n-25, Or.inr (by omega), by omega⟩
    have hne : n ≠ 25 := by
      intro heq; apply ht; exact ⟨0,Or.inl rfl,by omega⟩
    exact ⟨hlt, hn, hne⟩
  · rintro ⟨hlt, hn, hne⟩
    refine ⟨hn, ?_⟩
    rintro ⟨t,ht,heq⟩; omega
noncomputable def squareEntries : Finset ℕ := by
  classical
  exact ap.filter IsSquare

theorem square_count : 3 ≤ squareEntries.card := by
  classical
  have hs : ({4,9,16} : Finset ℕ) ⊆ squareEntries := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · apply Finset.mem_filter.mpr
      exact ⟨by norm_num [ap], ⟨2, by decide⟩⟩
    · apply Finset.mem_filter.mpr
      exact ⟨by norm_num [ap], ⟨3, by decide⟩⟩
    · apply Finset.mem_filter.mpr
      exact ⟨by norm_num [ap], ⟨4, by decide⟩⟩
  simpa using Finset.card_mono hs
theorem minimal_generators : S 2 ∧ S 3 ∧
    (¬ ∃ k : ℕ, 2 = 3*k) ∧ (¬ ∃ k : ℕ, 3 = 2*k) := by
  refine ⟨⟨1,0,by decide⟩,⟨0,1,by decide⟩,?_,?_⟩ <;> omega
theorem bound_fails : ¬ (squareEntries.card : ℝ) ≤ Real.sqrt (2*3) := by
  have hc : (3 : ℝ) ≤ squareEntries.card := by exact_mod_cast square_count
  have h : Real.sqrt (2*3) < 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith
#print axioms apery_exact
#print axioms square_count
#print axioms minimal_generators
#print axioms bound_fails
end TLMC587
