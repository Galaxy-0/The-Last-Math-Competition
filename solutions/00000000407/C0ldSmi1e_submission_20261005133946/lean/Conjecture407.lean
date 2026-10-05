import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A disproof of the literal equal-size indexing in conjecture 00000000407.
The Littlewood–Richardson coefficients below count conventional LR tableaux. -/

namespace Conjecture407

/-- Integer partitions represented by their standard Young diagrams. -/
def Partition (n : ℕ) := {d : YoungDiagram // d.card = n}

/-- A cell of the skew diagram `nu / lam`. -/
abbrev SkewCell (lam nu : YoungDiagram) := ↥(nu.cells \ lam.cells)

/-- Reading order: top rows first, and right to left within a row. -/
def ReadingLE (a b : ℕ × ℕ) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ b.2 ≤ a.2)

/-- The reading relation is a total order on distinct cell coordinates. -/
theorem readingLE_refl (a : ℕ × ℕ) : ReadingLE a a := by
  simp [ReadingLE]

theorem readingLE_total (a b : ℕ × ℕ) : ReadingLE a b ∨ ReadingLE b a := by
  simp only [ReadingLE]
  omega

theorem readingLE_antisymm {a b : ℕ × ℕ} (h : ReadingLE a b) (h' : ReadingLE b a) : a = b := by
  rcases a with ⟨i,j⟩
  rcases b with ⟨k,l⟩
  simp only [ReadingLE] at h h'
  have hi : i = k := by omega
  have hj : j = l := by omega
  exact Prod.ext hi hj

theorem readingLE_trans {a b c : ℕ × ℕ} (h : ReadingLE a b) (h' : ReadingLE b c) :
    ReadingLE a c := by
  simp only [ReadingLE] at *
  omega

/-- Number of occurrences of the zero-based letter `i` in a filling. -/
noncomputable def entryCount {lam nu : YoungDiagram} (f : SkewCell lam nu → ℕ) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun a => f a = i).card

/-- Occurrences of `i` in the reading prefix ending at cell `b`, inclusive. -/
noncomputable def prefixCount {lam nu : YoungDiagram} (f : SkewCell lam nu → ℕ)
    (b : SkewCell lam nu) (i : ℕ) : ℕ :=
  by
  classical
  exact (Finset.univ.filter fun a : SkewCell lam nu => ReadingLE a.val b.val ∧ f a = i).card

/-- Conventional LR tableaux, with positive letters shifted down by one.
The content equation is required for EVERY natural number, including the zero
rows beyond the support of mu. No degree condition is assumed. -/
structure LRTableau (lam mu nu : YoungDiagram) where
  entry : SkewCell lam nu → ℕ
  contained : lam ≤ nu
  rowWeak : ∀ a b, a.val.1 = b.val.1 → a.val.2 ≤ b.val.2 → entry a ≤ entry b
  colStrict : ∀ a b, a.val.2 = b.val.2 → a.val.1 < b.val.1 → entry a < entry b
  content : ∀ i, entryCount entry i = mu.rowLen i
  lattice : ∀ b i, prefixCount entry b (i + 1) ≤ prefixCount entry b i

/-- Every letter is below the number of nonempty content rows. -/
theorem LRTableau.entry_lt {lam mu nu : YoungDiagram} (T : LRTableau lam mu nu)
    (a : SkewCell lam nu) : T.entry a < mu.colLen 0 := by
  have hpos : 0 < entryCount T.entry (T.entry a) := by
    apply Finset.card_pos.mpr
    exact ⟨a, by simp [entryCount]⟩
  rw [T.content] at hpos
  have hcell : (T.entry a, 0) ∈ mu := YoungDiagram.mem_iff_lt_rowLen.mpr hpos
  exact YoungDiagram.mem_iff_lt_colLen.mp hcell

/-- The entry map determines a tableau; other fields are properties. -/
theorem LRTableau.entry_injective {lam mu nu : YoungDiagram} :
    Function.Injective (LRTableau.entry (lam := lam) (mu := mu) (nu := nu)) := by
  intro T U h
  cases T
  cases U
  cases h
  rfl

/-- All tableaux of fixed shape and content form a finite set. -/
instance lrTableauFinite (lam mu nu : YoungDiagram) : Finite (LRTableau lam mu nu) := by
  let encode : LRTableau lam mu nu → (SkewCell lam nu → Fin (mu.colLen 0)) :=
    fun T a => ⟨T.entry a, T.entry_lt a⟩
  apply Finite.of_injective encode
  intro T U h
  apply LRTableau.entry_injective
  funext a
  exact congrArg Fin.val (congrFun h a)

/-- Counting a diagram row by row recovers its number of boxes. -/
theorem diagram_card_eq_sum_rowLen (d : YoungDiagram) :
    d.card = ∑ i ∈ Finset.range (d.colLen 0), d.rowLen i := by
  have hm : d.cells.toSet.MapsTo Prod.fst (Finset.range (d.colLen 0)) := by
    intro a ha
    apply Finset.mem_range.mpr
    apply YoungDiagram.mem_iff_lt_colLen.mp
    exact d.up_left_mem le_rfl (Nat.zero_le a.2) ha
  calc
    d.card = ∑ i ∈ Finset.range (d.colLen 0), (d.cells.filter fun a => a.1 = i).card :=
      Finset.card_eq_sum_card_fiberwise hm
    _ = ∑ i ∈ Finset.range (d.colLen 0), d.rowLen i := by
      apply Finset.sum_congr rfl
      intro i _
      exact d.rowLen_eq_card.symm

/-- The degree restriction is PROVED by counting entries, not assumed in the definition. -/
theorem LRTableau.size_balance {lam mu nu : YoungDiagram} (T : LRTableau lam mu nu) :
    nu.card = lam.card + mu.card := by
  have hm : (Finset.univ : Finset (SkewCell lam nu)).toSet.MapsTo T.entry
      (Finset.range (mu.colLen 0)) := by
    intro a _
    exact Finset.mem_range.mpr (T.entry_lt a)
  have hsize : (nu.cells \ lam.cells).card = mu.card := by
    calc
      (nu.cells \ lam.cells).card = (Finset.univ : Finset (SkewCell lam nu)).card := by simp
      _ = ∑ i ∈ Finset.range (mu.colLen 0), entryCount T.entry i :=
        Finset.card_eq_sum_card_fiberwise hm
      _ = ∑ i ∈ Finset.range (mu.colLen 0), mu.rowLen i := by simp only [T.content]
      _ = mu.card := (diagram_card_eq_sum_rowLen mu).symm
  have hc := Finset.card_sdiff_add_card_eq_card T.contained
  change (nu.cells \ lam.cells).card + lam.card = nu.card at hc
  omega

/-- The standard combinatorial definition of the LR coefficient. -/
noncomputable def lrCoefficient (lam mu nu : YoungDiagram) : ℕ :=
  Nat.card (LRTableau lam mu nu)

/-- A nonexistent skew shape contributes no tableaux. -/
theorem lrCoefficient_eq_zero_of_not_contained (lam mu nu : YoungDiagram)
    (h : ¬ lam ≤ nu) : lrCoefficient lam mu nu = 0 := by
  have he : IsEmpty (LRTableau lam mu nu) := ⟨fun T => h T.contained⟩
  exact Nat.card_of_isEmpty

/-- The usual size-vanishing property follows from the actual tableaux. -/
theorem lrCoefficient_eq_zero_of_size_ne (lam mu nu : YoungDiagram)
    (h : nu.card ≠ lam.card + mu.card) : lrCoefficient lam mu nu = 0 := by
  have he : IsEmpty (LRTableau lam mu nu) := ⟨fun T => h T.size_balance⟩
  exact Nat.card_of_isEmpty

/-- An occupied row index is less than the total number of boxes. -/
theorem cell_row_lt_card {d : YoungDiagram} {i j : ℕ} (h : (i,j) ∈ d) : i < d.card := by
  have hs : (Finset.range (i + 1)).image (fun k => (k,j)) ⊆ d.cells := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    exact d.up_left_mem (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)) le_rfl h
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ (by intro a b h; exact Prod.mk.inj h |>.1),
    Finset.card_range] at hc
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hc

/-- An occupied column index is less than the total number of boxes. -/
theorem cell_col_lt_card {d : YoungDiagram} {i j : ℕ} (h : (i,j) ∈ d) : j < d.card := by
  have hs : (Finset.range (j + 1)).image (fun k => (i,k)) ⊆ d.cells := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    exact d.up_left_mem le_rfl (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)) h
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ (by intro a b h; exact Prod.mk.inj h |>.2),
    Finset.card_range] at hc
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hc

/-- There are finitely many partitions of each fixed size. -/
instance partitionFinite (n : ℕ) : Finite (Partition n) := by
  let box : Finset (ℕ × ℕ) := (Finset.range n).product (Finset.range n)
  let encode : Partition n → ↥(box.powerset) := fun d =>
    ⟨d.val.cells, Finset.mem_powerset.mpr (by
      intro a ha
      have hr := cell_row_lt_card (d := d.val) ha
      have hc := cell_col_lt_card (d := d.val) ha
      simp only [d.property] at hr hc
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hr, Finset.mem_range.mpr hc⟩)⟩
  apply Finite.of_injective encode
  intro d e h
  apply Subtype.ext
  apply YoungDiagram.ext
  exact congrArg Subtype.val h

/-- An index of a nonzero entry, with all three partitions of exactly n. -/
def NonzeroEntry (n : ℕ) :=
  {t : Partition n × Partition n × Partition n //
    lrCoefficient t.1.val t.2.1.val t.2.2.val ≠ 0}

/-- Hence the coefficient-table count is a cardinality of a finite type. -/
instance nonzeroEntryFinite (n : ℕ) : Finite (NonzeroEntry n) :=
  inferInstanceAs (Finite {t : Partition n × Partition n × Partition n //
    lrCoefficient t.1.val t.2.1.val t.2.2.val ≠ 0})

/-- The actual number of nonzero entries in the table with ALL three indices
partitions of n, as printed in both language versions of the conjecture. -/
noncomputable def nonzeroCount (n : ℕ) : ℕ := Nat.card (NonzeroEntry n)

/-- Equal-size inner and outer diagrams leave no cells for positive content. -/
theorem no_tableau_same_positive_size (n : ℕ) (hn : 0 < n)
    (lam mu nu : Partition n) : IsEmpty (LRTableau lam.val mu.val nu.val) := by
  constructor
  intro T
  have hb := T.size_balance
  rw [lam.property, mu.property, nu.property] at hb
  omega

/-- Every coefficient in the displayed table is zero for n > 0. -/
theorem lrCoefficient_eq_zero (n : ℕ) (hn : 0 < n) (lam mu nu : Partition n) :
    lrCoefficient lam.val mu.val nu.val = 0 := by
  letI := no_tableau_same_positive_size n hn lam mu nu
  exact Nat.card_of_isEmpty

/-- Exact count, valid for every positive index. -/
theorem nonzeroCount_eq_zero (n : ℕ) (hn : 0 < n) : nonzeroCount n = 0 := by
  have he : IsEmpty (NonzeroEntry n) := by
    constructor
    intro t
    exact t.property (lrCoefficient_eq_zero n hn t.val.1 t.val.2.1 t.val.2.2)
  exact Nat.card_of_isEmpty

/-- The exact positive comparison scale printed in the conjecture. -/
noncomputable def scale (n : ℕ) : ℝ := (4 : ℝ)^n / Real.rpow (n : ℝ) (5/4 : ℝ)

/-- The displayed comparison scale is strictly positive at every positive index. -/
theorem scale_pos (n : ℕ) (hn : 0 < n) : 0 < scale n := by
  exact div_pos (pow_pos (by norm_num) n)
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)

/-- Even the normalized sequence is eventually exactly zero. -/
theorem normalized_eventually_zero :
    ∀ᶠ n : ℕ in Filter.atTop, (nonzeroCount n : ℝ) / scale n = 0 := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  simp [nonzeroCount_eq_zero n hn]

/-- Standard filter formulation of its actual limit. -/
theorem normalized_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (nonzeroCount n : ℝ) / scale n)
      Filter.atTop (nhds 0) :=
  Filter.Tendsto.congr' (Filter.EventuallyEq.symm normalized_eventually_zero) tendsto_const_nhds

/-- The literal ratio-asymptotic assertion, fully quantified. -/
def RatioAsymptotic (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(nonzeroCount n : ℝ) / (c * scale n) - 1| < ε

/-- Negation for every real constant, stronger than only positive constants. -/
theorem not_ratioAsymptotic (c : ℝ) : ¬ RatioAsymptotic c := by
  intro h
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  have hbad := hN (N+1) (by omega)
  rw [nonzeroCount_eq_zero (N+1) (by omega)] at hbad
  norm_num at hbad

/-- No real c whatsoever satisfies the ratio claim. -/
theorem no_real_ratio_constant : ¬ ∃ c : ℝ, RatioAsymptotic c := by
  rintro ⟨c, h⟩
  exact not_ratioAsymptotic c h

/-- The conjectured positive leading constant does not exist. -/
theorem conjecture407_false : ¬ ∃ c : ℝ, 0 < c ∧ RatioAsymptotic c := by
  rintro ⟨c, _, h⟩
  exact not_ratioAsymptotic c h

end Conjecture407
