import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Conjecture428

/-- The number of parts of an actual partition that are at least `k`. -/
def rowsAtLeast {n : ℕ} (p : Nat.Partition n) (k : ℕ) : ℕ :=
  (p.parts.filter (k ≤ ·)).card

lemma parts_card_le {n : ℕ} (p : Nat.Partition n) : p.parts.card ≤ n := by
  have h := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1)
    (fun a ha => p.parts_pos ha)
  simpa [p.parts_sum] using h

lemma rowsAtLeast_le {n : ℕ} (p : Nat.Partition n) (k : ℕ) : rowsAtLeast p k ≤ n :=
  (Multiset.card_le_card (Multiset.filter_le _ _)).trans (parts_card_le p)

lemma rowsAtLeast_antitone {n : ℕ} (p : Nat.Partition n) : Antitone (rowsAtLeast p) := by
  intro a b hab
  exact Multiset.card_le_card (Multiset.monotone_filter_right p.parts
    (fun c hc => hab.trans hc))

/-- The possible square sides. The finite cutoff is subsequently proved redundant. -/
def squareSides {n : ℕ} (p : Nat.Partition n) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => k ≤ rowsAtLeast p k)

lemma squareSides_nonempty {n : ℕ} (p : Nat.Partition n) : (squareSides p).Nonempty := by
  refine ⟨0, ?_⟩
  simp [squareSides]

lemma mem_squareSides_iff {n : ℕ} (p : Nat.Partition n) (k : ℕ) :
    k ∈ squareSides p ↔ k ≤ rowsAtLeast p k := by
  simp only [squareSides, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨Nat.lt_succ_of_le (h.trans (rowsAtLeast_le p k)), h⟩⟩

/-- The Durfee side is the largest `k` with at least `k` parts of length at least `k`. -/
def durfee {n : ℕ} (p : Nat.Partition n) : ℕ :=
  (squareSides p).max' (squareSides_nonempty p)

lemma durfee_attained {n : ℕ} (p : Nat.Partition n) : durfee p ≤ rowsAtLeast p (durfee p) :=
  (mem_squareSides_iff p _).mp (Finset.max'_mem _ _)

lemma le_durfee_of_square {n : ℕ} (p : Nat.Partition n) {k : ℕ}
    (hk : k ≤ rowsAtLeast p k) : k ≤ durfee p :=
  Finset.le_max' _ _ ((mem_squareSides_iff p k).mpr hk)

lemma square_iff_le_durfee {n : ℕ} (p : Nat.Partition n) (k : ℕ) :
    k ≤ rowsAtLeast p k ↔ k ≤ durfee p := by
  refine ⟨le_durfee_of_square p, fun hk => ?_⟩
  exact hk.trans ((durfee_attained p).trans (rowsAtLeast_antitone p hk))

lemma square_area_le {n : ℕ} (p : Nat.Partition n) {k : ℕ}
    (hk : k ≤ rowsAtLeast p k) : k ^ 2 ≤ n := by
  have hsum : (p.parts.filter (k ≤ ·)).sum ≤ n := by
    have h := congrArg Multiset.sum (Multiset.filter_add_not (k ≤ ·) p.parts)
    rw [Multiset.sum_add, p.parts_sum] at h
    omega
  have hlower := Multiset.card_nsmul_le_sum (s := p.parts.filter (k ≤ ·)) (a := k)
    (fun a ha => (Multiset.mem_filter.mp ha).2)
  simp only [nsmul_eq_mul] at hlower
  calc
    k ^ 2 = k * k := pow_two k
    _ ≤ (p.parts.filter (k ≤ ·)).card * k := Nat.mul_le_mul_right k hk
    _ ≤ (p.parts.filter (k ≤ ·)).sum := hlower
    _ ≤ n := hsum

lemma durfee_sq_le {n : ℕ} (p : Nat.Partition n) : (durfee p) ^ 2 ≤ n :=
  square_area_le p (durfee_attained p)

lemma durfee_le_sqrt {n : ℕ} (p : Nat.Partition n) : (durfee p : ℝ) ≤ Real.sqrt (n : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast durfee_sq_le p

lemma column_index_lt {n : ℕ} (p : Nat.Partition n) {i j : ℕ}
    (h : i < rowsAtLeast p (j + 1)) : j < n := by
  have hpos : 0 < (p.parts.filter (j + 1 ≤ ·)).card := (Nat.zero_le i).trans_lt h
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp hpos)
  obtain ⟨ha, hja⟩ := Multiset.mem_filter.mp ha
  have han : a ≤ n := (Multiset.le_sum_of_mem ha).trans_eq p.parts_sum
  omega

/-- The canonical Ferrers diagram: column `j` has one cell per part at least `j+1`. -/
def ferrers {n : ℕ} (p : Nat.Partition n) : YoungDiagram where
  cells := ((Finset.range n) ×ˢ (Finset.range n)).filter
    (fun c => c.1 < rowsAtLeast p (c.2 + 1))
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hb ⊢
    refine ⟨⟨hab.1.trans_lt hb.1.1, hab.2.trans_lt hb.1.2⟩, ?_⟩
    exact hab.1.trans_lt (hb.2.trans_le (rowsAtLeast_antitone p (Nat.add_le_add_right hab.2 1)))

lemma mem_ferrers_iff {n : ℕ} (p : Nat.Partition n) (i j : ℕ) :
    (i, j) ∈ ferrers p ↔ i < rowsAtLeast p (j + 1) := by
  change ((i, j) ∈ ((Finset.range n) ×ˢ (Finset.range n)).filter
    (fun c => c.1 < rowsAtLeast p (c.2 + 1))) ↔ _
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨⟨h.trans_le (rowsAtLeast_le p _), column_index_lt p h⟩, h⟩⟩

lemma square_subset_ferrers_iff {n : ℕ} (p : Nat.Partition n) (k : ℕ) :
    (Finset.range k) ×ˢ (Finset.range k) ⊆ (ferrers p).cells ↔
      k ≤ rowsAtLeast p k := by
  constructor
  · intro h
    cases k with
    | zero => exact Nat.zero_le _
    | succ k =>
      have hk : (k, k) ∈ (ferrers p).cells := h (by simp)
      exact (mem_ferrers_iff p k k).mp hk
  · intro hk c hc
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hc
    rw [Finset.mem_range] at hi hj
    apply (mem_ferrers_iff p c.1 c.2).mpr
    exact hi.trans_le (hk.trans (rowsAtLeast_antitone p (Nat.succ_le_of_lt hj)))

lemma square_subset_ferrers_iff_le_durfee {n : ℕ} (p : Nat.Partition n) (k : ℕ) :
    (Finset.range k) ×ˢ (Finset.range k) ⊆ (ferrers p).cells ↔ k ≤ durfee p := by
  rw [square_subset_ferrers_iff, square_iff_le_durfee]

/-- Counting cells by column gives the sum of the original part lengths. -/
lemma sum_column_counts (s : Multiset ℕ) (N : ℕ) (hs : ∀ a ∈ s, a ≤ N) :
    (∑ j ∈ Finset.range N, (s.filter (j + 1 ≤ ·)).card) = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha : a ≤ N := hs a (by simp)
    have hs' : ∀ b ∈ s, b ≤ N := fun b hb => hs b (by simp [hb])
    have hterm (j : ℕ) :
        ((a ::ₘ s).filter (j + 1 ≤ ·)).card =
          (if j < a then 1 else 0) + (s.filter (j + 1 ≤ ·)).card := by
      by_cases hj : j < a
      · have hj' : j + 1 ≤ a := hj
        simp [Multiset.filter_cons, hj, hj', add_comm]
      · have hj' : ¬j + 1 ≤ a := hj
        simp [Multiset.filter_cons, hj, hj']
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ih hs']
    have hfilter : (Finset.range N).filter (· < a) = Finset.range a := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨And.right, fun hj => ⟨hj.trans_le ha, hj⟩⟩
    simp [hfilter]

lemma ferrers_card_sum {n : ℕ} (p : Nat.Partition n) :
    (ferrers p).card = ∑ j ∈ Finset.range n, rowsAtLeast p (j + 1) := by
  change (((Finset.range n) ×ˢ (Finset.range n)).filter
    (fun c => c.1 < rowsAtLeast p (c.2 + 1))).card = _
  rw [Finset.card_filter, Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro j hj
  have hfilter : (Finset.range n).filter (· < rowsAtLeast p (j + 1)) =
      Finset.range (rowsAtLeast p (j + 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun hi => ⟨hi.trans_le (rowsAtLeast_le p _), hi⟩⟩
  simp only [Finset.sum_boole, hfilter, Finset.card_range, Nat.cast_id]

lemma ferrers_card {n : ℕ} (p : Nat.Partition n) : (ferrers p).card = n := by
  rw [ferrers_card_sum]
  exact (sum_column_counts p.parts n
    (fun a ha => (Multiset.le_sum_of_mem ha).trans_eq p.parts_sum)).trans p.parts_sum

end Conjecture428
