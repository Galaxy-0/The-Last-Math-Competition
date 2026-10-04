import CycleTrees
import NumberTheory

namespace Conjecture464
open SimpleGraph Filter

/-- An explicit family of actual simple cycle graphs. -/
def cycleFamily (k : ℕ) : SimpleGraph (Fin (vertexCount k)) := cycleGraph (vertexCount k)

instance (k : ℕ) : DecidableRel (cycleFamily k).Adj :=
  inferInstanceAs (DecidableRel (cycleGraph (vertexCount k)).Adj)

lemma cycleFamily_connected (k : ℕ) : (cycleFamily k).Connected := by
  have hn := vertexCount_ge_four k
  obtain ⟨m, hm⟩ : ∃ m, vertexCount k = m + 1 := ⟨vertexCount k - 1, by omega⟩
  unfold cycleFamily
  generalize vertexCount k = n at *
  subst n
  exact cycleGraph_connected

lemma cycle_regular (n : ℕ) (hn : 3 ≤ n) : (cycleGraph n).IsRegularOfDegree 2 := by
  match n with
  | 0 | 1 | 2 => omega
  | m + 3 => exact fun _ ↦ cycleGraph_degree_three_le

lemma cycleFamily_regular (k : ℕ) : (cycleFamily k).IsRegularOfDegree 2 := by
  exact cycle_regular (vertexCount k) (le_trans (by norm_num) (vertexCount_ge_four k))

lemma cycleFamily_order_tendsto :
    Tendsto (fun k ↦ Fintype.card (Fin (vertexCount k))) atTop atTop := by
  simpa only [Fintype.card_fin] using vertexCount_tendsto

lemma cycleFamily_spanningTreeCount (k : ℕ) :
    spanningTreeCount (cycleFamily k) = vertexCount k := by
  exact cycle_spanningTreeCount_of_three_le (vertexCount k)
    (le_trans (by norm_num) (vertexCount_ge_four k))

lemma cycleFamily_largestPrimeFactor (k : ℕ) :
    largestPrimeFactor (spanningTreeCount (cycleFamily k)) = 2 := by
  rw [cycleFamily_spanningTreeCount, largestPrimeFactor_vertexCount]

/-- The deterministic bound fails eventually for every positive real constant. -/
theorem cycleFamily_eventually_violates (c : ℝ) (hc : 0 < c) :
    ∀ᶠ k in atTop,
      (largestPrimeFactor (spanningTreeCount (cycleFamily k)) : ℝ) <
        c * Real.log (Fintype.card (Fin (vertexCount k)) : ℝ) := by
  simpa only [cycleFamily_largestPrimeFactor, Fintype.card_fin, Nat.cast_ofNat] using
    eventually_bound_exceeds_two c hc

/-- No positive lower-bound constant works even after discarding a finite prefix. -/
theorem no_eventual_logarithmic_lower_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      c * Real.log (Fintype.card (Fin (vertexCount k)) : ℝ) ≤
        (largestPrimeFactor (spanningTreeCount (cycleFamily k)) : ℝ) := by
  rintro ⟨c, hc, K, hK⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp (cycleFamily_eventually_violates c hc)
  exact (not_lt_of_ge (hK (max K M) (le_max_left K M)))
    (hM (max K M) (le_max_right K M))

/-- An admissible connected 2-regular family of unbounded order refutes the bound. -/
theorem conjecture464_counterexample :
    (∀ k, (cycleFamily k).Connected ∧ (cycleFamily k).IsRegularOfDegree 2) ∧
    Tendsto (fun k ↦ Fintype.card (Fin (vertexCount k))) atTop atTop ∧
    ¬ (∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      c * Real.log (Fintype.card (Fin (vertexCount k)) : ℝ) ≤
        (largestPrimeFactor (spanningTreeCount (cycleFamily k)) : ℝ)) := by
  exact ⟨fun k ↦ ⟨cycleFamily_connected k, cycleFamily_regular k⟩,
    cycleFamily_order_tendsto, no_eventual_logarithmic_lower_bound⟩

end Conjecture464
