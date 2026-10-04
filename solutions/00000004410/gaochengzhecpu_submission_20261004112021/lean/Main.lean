import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Equal finite sampling laws cannot have unequal entropy-rate limits. -/

namespace Conjecture4410

open Filter Topology
open scoped BigOperators

/-- Genuine finite probability distributions, with nonnegative masses summing to one. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

/-- Real.log 0 = 0 implements the usual 0 log 0 = 0 convention. -/
noncomputable def entropy {Ω : Type*} [Fintype Ω] (p : FiniteLaw Ω) : ℝ :=
  - ∑ x, p.mass x * Real.log (p.mass x)

theorem entropy_eq_of_same_masses {Ω : Type*} [Fintype Ω] (p q : FiniteLaw Ω)
    (h : ∀ x, p.mass x = q.mass x) : entropy p = entropy q := by
  unfold entropy
  simp only [h]

/-- Canonical unordered edges of a labeled n-vertex simple graph. -/
abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

/-- A Boolean choice for every unordered edge is an actual labeled simple graph. -/
abbrev GraphSample (n : ℕ) := Edge n → Bool

/-- The n-th law is the law of a nonempty sample of size n+1. -/
abbrev SamplingLaws := (n : ℕ) → FiniteLaw (GraphSample (n + 1))

def SameFiniteDistributions (p q : SamplingLaws) : Prop :=
  ∀ n g, (p n).mass g = (q n).mass g

/-- The two objects must use the same positive normalization convention. -/
structure Normalization where
  denominator : ℕ → ℝ
  positive : ∀ n, 0 < denominator n

noncomputable def perWindow : Normalization where
  denominator n := n + 1
  positive n := by positivity

/-- No particular graph or window encoding is needed: any common finite outcome spaces work. -/
theorem arbitrary_finite_law_rates_equal {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (p q : ∀ n, FiniteLaw (Ω n)) (h : ∀ n x, (p n).mass x = (q n).mass x)
    (c : Normalization) (a b : ℝ)
    (ha : Tendsto (fun n => entropy (p n) / c.denominator n) atTop (𝓝 a))
    (hb : Tendsto (fun n => entropy (q n) / c.denominator n) atTop (𝓝 b)) : a = b := by
  have heq : (fun n => entropy (p n) / c.denominator n) =
      (fun n => entropy (q n) / c.denominator n) := by
    funext n
    rw [entropy_eq_of_same_masses (p n) (q n) (h n)]
  rw [heq] at ha
  exact tendsto_nhds_unique ha hb

noncomputable def normalizedEntropy (p : SamplingLaws) (c : Normalization) (n : ℕ) : ℝ :=
  entropy (p n) / c.denominator n

def HasEntropyRate (p : SamplingLaws) (c : Normalization) (h : ℝ) : Prop :=
  Tendsto (normalizedEntropy p c) atTop (𝓝 h)

theorem normalized_entropies_equal (p q : SamplingLaws) (h : SameFiniteDistributions p q)
    (c : Normalization) : normalizedEntropy p c = normalizedEntropy q c := by
  funext n
  unfold normalizedEntropy
  rw [entropy_eq_of_same_masses (p n) (q n) (h n)]

theorem rates_equal (p q : SamplingLaws) (h : SameFiniteDistributions p q)
    (c : Normalization) (a b : ℝ) (ha : HasEntropyRate p c a)
    (hb : HasEntropyRate q c b) : a = b := by
  unfold HasEntropyRate at ha hb
  rw [normalized_entropies_equal p q h c] at ha
  exact tendsto_nhds_unique ha hb

/-- The source's separation is impossible already for arbitrary graph sampling laws. -/
theorem no_entropy_rate_separation (c : Normalization) :
    ¬ ∃ (p q : SamplingLaws) (a b : ℝ),
      SameFiniteDistributions p q ∧ HasEntropyRate p c a ∧
      HasEntropyRate q c b ∧ a ≠ b := by
  rintro ⟨p, q, a, b, h, ha, hb, hne⟩
  exact hne (rates_equal p q h c a b ha hb)

/-- Applies to any objects producing sampling laws, hence in particular to graphons. -/
theorem no_object_pair_with_positive_gap (W : Type*) (sample : W → SamplingLaws)
    (c : Normalization) :
    ¬ ∃ (U V : W) (a b δ : ℝ), SameFiniteDistributions (sample U) (sample V) ∧
      HasEntropyRate (sample U) c a ∧ HasEntropyRate (sample V) c b ∧
      0 < δ ∧ b - a = δ := by
  rintro ⟨U, V, a, b, δ, h, ha, hb, hδ, heq⟩
  have hab := rates_equal (sample U) (sample V) h c a b ha hb
  rw [hab, sub_self] at heq
  rw [← heq] at hδ
  exact (lt_irrefl 0) hδ

/-- A concrete, nonempty example: the deterministic empty-graph distribution. -/
noncomputable def emptyGraphLaw (n : ℕ) : FiniteLaw (GraphSample (n + 1)) := by
  classical
  exact {
    mass := fun g => if g = (fun _ => false) then 1 else 0
    nonnegative := by intro g; split_ifs <;> norm_num
    total := by simp
  }

theorem emptyGraphLaw_entropy (n : ℕ) : entropy (emptyGraphLaw n) = 0 := by
  classical
  unfold entropy emptyGraphLaw
  simp

theorem empty_graph_entropy_rate : HasEntropyRate emptyGraphLaw perWindow 0 := by
  unfold HasEntropyRate normalizedEntropy
  simp only [emptyGraphLaw_entropy, zero_div]
  exact tendsto_const_nhds

#print axioms entropy_eq_of_same_masses
#print axioms arbitrary_finite_law_rates_equal
#print axioms normalized_entropies_equal
#print axioms rates_equal
#print axioms no_entropy_rate_separation
#print axioms no_object_pair_with_positive_gap
#print axioms empty_graph_entropy_rate

end Conjecture4410
