import Std

namespace Conjecture3464
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

structure Graph (n : Nat) where
  adj : Fin n → Fin n → Bool
  loopless : ∀ v, adj v v = false
  symmetric : ∀ v w, adj v w = adj w v

def degree {n} (G : Graph n) (v : Fin n) : Nat :=
  ((List.finRange n).filter (G.adj v)).length

def maxDegree {n} (G : Graph n) : Nat :=
  ((List.finRange n).map (degree G)).foldl max 0

def DistanceTwo {n} (G : Graph n) (v w : Fin n) : Prop :=
  v ≠ w ∧ G.adj v w = false ∧ ∃ u, G.adj v u = true ∧ G.adj u w = true

/-- Absolute difference of two nonnegative integer labels. -/
def separation (a b : Nat) : Nat := (a-b)+(b-a)

def L21 {n} (G : Graph n) (f : Fin n → Nat) : Prop :=
  (∀ v w, G.adj v w = true → 2 ≤ separation (f v) (f w)) ∧
  (∀ v w, DistanceTwo G v w → 1 ≤ separation (f v) (f w))

/-- All labels lie in a translate of [0,R]; equivalent to range at most R. -/
def SpanAtMost {n} (f : Fin n → Nat) (R : Nat) : Prop :=
  ∃ lo, ∀ v, lo ≤ f v ∧ f v ≤ lo + R

def MinimumSpan {n} (G : Graph n) (s : Nat) : Prop :=
  (∃ f, L21 G f ∧ SpanAtMost f s) ∧
  ∀ f R, L21 G f → SpanAtMost f R → s ≤ R

def edgeGraph : Graph 2 where
  adj v w := decide (v ≠ w)
  loopless := by decide
  symmetric := by decide

theorem degree_one : ∀ v, degree edgeGraph v = 1 := by decide
theorem maximum_degree_one : maxDegree edgeGraph = 1 := by decide
theorem no_distance_two : ∀ v w, ¬DistanceTwo edgeGraph v w := by
  intro v w h
  have hh := h.2.1
  simp [edgeGraph, h.1] at hh

def edgeLabels (v : Fin 2) : Nat := if v = 0 then 0 else 2

theorem labels_valid : L21 edgeGraph edgeLabels := by
  constructor
  · decide
  · intro v w h
    exact False.elim (no_distance_two v w h)

theorem labels_span_two : SpanAtMost edgeLabels 2 := by
  exact ⟨0, by decide⟩

/-- This quantifies over all label values and all translations, not a finite
search bounded by the proposed answer. -/
theorem every_valid_span_at_least_two (f : Fin 2 → Nat) (R : Nat)
    (hf : L21 edgeGraph f) (hr : SpanAtMost f R) : 2 ≤ R := by
  have hsep := hf.1 0 1 (by decide)
  obtain ⟨lo, hlo⟩ := hr
  have ha := hlo 0
  have hb := hlo 1
  unfold separation at hsep
  omega

theorem edge_minimum_span : MinimumSpan edgeGraph 2 :=
  ⟨⟨edgeLabels, labels_valid, labels_span_two⟩, every_valid_span_at_least_two⟩

/-- Equivalent range calculation on the two vertices. -/
theorem span_range_equivalence (f : Fin 2 → Nat) (R : Nat) :
    SpanAtMost f R ↔ max (f 0) (f 1) - min (f 0) (f 1) ≤ R := by
  constructor
  · rintro ⟨lo,h⟩
    have h0 := h 0
    have h1 := h 1
    omega
  · intro h
    refine ⟨min (f 0) (f 1), ?_⟩
    intro v
    have hv : v = 0 ∨ v = 1 := by
      have := v.isLt
      omega
    rcases hv with rfl | rfl <;> omega

def ClaimedUniversalBound : Prop :=
  ∀ n (G : Graph n), ∃ f, L21 G f ∧ SpanAtMost f (maxDegree G * maxDegree G)

theorem conjecture3464_false : ¬ClaimedUniversalBound := by
  intro h
  obtain ⟨f,hf,hr⟩ := h 2 edgeGraph
  have hbad := every_valid_span_at_least_two f _ hf hr
  rw [maximum_degree_one] at hbad
  omega

theorem counterexample_parameters :
    maxDegree edgeGraph = 1 ∧ MinimumSpan edgeGraph 2 ∧ 1 * 1 < 2 :=
  ⟨maximum_degree_one, edge_minimum_span, by decide⟩

#print axioms edge_minimum_span
#print axioms span_range_equivalence
#print axioms conjecture3464_false
end Conjecture3464
