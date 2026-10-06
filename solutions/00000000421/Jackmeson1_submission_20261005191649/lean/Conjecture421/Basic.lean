import Mathlib

/-!
# Conjecture 00000000421 (disproof)

*Definition.* The growth-tree statistic `a(T)` is the number of outer-corner cells that can be
added to the tableau `T`.  *Conjecture.* The expectation of `a(T)` on a uniformly random tableau
converges to two, and the convergence rate is the inverse logarithm of the tableau size.

Young diagrams are Mathlib's `YoungDiagram` (finite lower sets of `ℕ × ℕ`, cell `(i, j)` in row `i`
and column `j`).  An addable (outer-corner) cell of `μ` is a cell `c ∉ μ` such that `μ ∪ {c}` is
again a Young diagram.  We show: for every prime `p ≥ 3` the expected number of addable cells is
at least `7/3`, for each of two measures on size-`p` objects:
* the uniform measure on standard Young tableaux with `p` cells (`E_SYT`, our main reading of the
  conjecture's "uniformly random tableau");
* the uniform measure on Young diagrams with `p` cells (`E_shape`).
Hence neither expectation tends to `2`, and neither is `2 + O(1 / log n)`.

Key facts: a nonempty diagram has the two addable cells `(0, rowLen 0)` and `(colLen 0, 0)`; a
non-rectangular diagram has a third one; a rectangle with a prime number of cells is a single row
or a single column; a single-row or single-column shape carries at most one standard tableau.
-/

open Finset Filter Topology

namespace C421

/-! ## Addable cells -/

/-- The addable (outer-corner) cells of `μ`: cells `c ∉ μ` such that `μ ∪ {c}` is a lower set,
i.e. again a Young diagram. -/
def addable (μ : YoungDiagram) : Set (ℕ × ℕ) :=
  {c | c ∉ μ ∧ IsLowerSet (insert c (μ : Set (ℕ × ℕ)))}

/-- The growth-tree statistic `a`: the number of addable outer-corner cells of a shape. -/
noncomputable def a (μ : YoungDiagram) : ℕ := (addable μ).ncard

lemma pred_mem {μ : YoungDiagram} {c d : ℕ × ℕ} (hc : c ∈ addable μ) (hdc : d ≤ c)
    (hne : d ≠ c) : d ∈ μ := by
  rcases hc.2 hdc (Set.mem_insert c _) with h | h
  · exact absurd h hne
  · exact h

lemma addable_subset (μ : YoungDiagram) :
    addable μ ⊆ ↑(range (μ.colLen 0 + 1) ×ˢ range (μ.rowLen 0 + 1)) := by
  rintro ⟨i, j⟩ hc
  simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
  constructor
  · rcases Nat.eq_zero_or_pos i with h | h
    · omega
    · have h1 : (i - 1, j) ∈ μ :=
        pred_mem hc (Prod.mk_le_mk.mpr ⟨by omega, le_rfl⟩) (by simp only [ne_eq, Prod.mk.injEq]; omega)
      have := YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le j) h1)
      omega
  · rcases Nat.eq_zero_or_pos j with h | h
    · omega
    · have h1 : (i, j - 1) ∈ μ :=
        pred_mem hc (Prod.mk_le_mk.mpr ⟨le_rfl, by omega⟩) (by simp only [ne_eq, Prod.mk.injEq]; omega)
      have := YoungDiagram.mem_iff_lt_rowLen.mp (μ.up_left_mem (Nat.zero_le i) le_rfl h1)
      omega

lemma addable_finite (μ : YoungDiagram) : (addable μ).Finite :=
  (Finset.finite_toSet _).subset (addable_subset μ)

lemma mem_addable_of {μ : YoungDiagram} {i j : ℕ} (hc : (i, j) ∉ μ)
    (h1 : 0 < i → (i - 1, j) ∈ μ) (h2 : 0 < j → (i, j - 1) ∈ μ) : (i, j) ∈ addable μ := by
  refine ⟨hc, ?_⟩
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩ hyx hx
  obtain ⟨ha, hb⟩ := Prod.mk_le_mk.mp hyx
  rw [Set.mem_insert_iff] at hx ⊢
  rcases hx with hx | hx
  · simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    by_cases hyc : y1 = x1 ∧ y2 = x2
    · left; rw [hyc.1, hyc.2]
    · right
      rcases Nat.lt_or_ge y1 x1 with h | h
      · exact μ.up_left_mem (by omega) hb (h1 (by omega))
      · exact μ.up_left_mem ha (by omega) (h2 (by omega))
  · exact Or.inr (μ.isLowerSet hyx hx)

lemma corner_row (μ : YoungDiagram) : (0, μ.rowLen 0) ∈ addable μ :=
  mem_addable_of (fun h => lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp h))
    (fun h => absurd h (lt_irrefl 0)) (fun h => YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))

lemma corner_col (μ : YoungDiagram) : (μ.colLen 0, 0) ∈ addable μ :=
  mem_addable_of (fun h => lt_irrefl _ (YoungDiagram.mem_iff_lt_colLen.mp h))
    (fun h => YoungDiagram.mem_iff_lt_colLen.mpr (by omega)) (fun h => absurd h (lt_irrefl 0))

/-- A nonempty Young diagram has at least two addable cells. -/
lemma two_le_a (μ : YoungDiagram) (h : (0, 0) ∈ μ) : 2 ≤ a μ := by
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp h
  have : 1 < a μ := (Set.one_lt_ncard_iff (addable_finite μ)).mpr
    ⟨_, _, corner_row μ, corner_col μ, by simp only [ne_eq, Prod.mk.injEq]; omega⟩
  omega

/-- A Young diagram that is not the full rectangle `colLen 0 × rowLen 0` has at least three
addable cells. -/
lemma three_le_a (μ : YoungDiagram)
    (h : ∃ i j, i < μ.colLen 0 ∧ j < μ.rowLen 0 ∧ (i, j) ∉ μ) : 3 ≤ a μ := by
  classical
  obtain ⟨i, j, hi, hj, hij⟩ := h
  have hP : ∃ k, μ.rowLen k < μ.rowLen 0 :=
    ⟨i, by have := mt YoungDiagram.mem_iff_lt_rowLen.mpr hij; omega⟩
  set k := Nat.find hP with hk
  have hk1 : μ.rowLen k < μ.rowLen 0 := Nat.find_spec hP
  have hk2 : ∀ m < k, μ.rowLen 0 ≤ μ.rowLen m := fun m hm => not_lt.mp (Nat.find_min hP hm)
  have hki : k ≤ i := Nat.find_min' hP (by have := mt YoungDiagram.mem_iff_lt_rowLen.mpr hij; omega)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hk1; exact absurd hk1 (lt_irrefl _)
    · exact h0
  have hkc : k < μ.colLen 0 := lt_of_le_of_lt hki hi
  have hrow : 0 < μ.rowLen k :=
    YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr hkc)
  have hthird : (k, μ.rowLen k) ∈ addable μ :=
    mem_addable_of (fun h => lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp h))
      (fun _ => YoungDiagram.mem_iff_lt_rowLen.mpr (by have := hk2 (k - 1) (by omega); omega))
      (fun _ => YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
  have : 2 < a μ := (Set.two_lt_ncard_iff (addable_finite μ)).mpr
    ⟨_, _, _, corner_row μ, corner_col μ, hthird, by simp only [ne_eq, Prod.mk.injEq]; omega,
      by simp only [ne_eq, Prod.mk.injEq]; omega, by simp only [ne_eq, Prod.mk.injEq]; omega⟩
  omega

/-- `μ` is a single row or a single column. -/
def IsRowOrCol (μ : YoungDiagram) : Prop := (∀ c ∈ μ, c.1 = 0) ∨ (∀ c ∈ μ, c.2 = 0)

lemma lt_card_of_mem {μ : YoungDiagram} {i j : ℕ} (h : (i, j) ∈ μ) :
    i < μ.cells.card ∧ j < μ.cells.card := by
  have h1 := YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le j) h)
  have h2 := YoungDiagram.mem_iff_lt_rowLen.mp (μ.up_left_mem (Nat.zero_le i) le_rfl h)
  rw [YoungDiagram.colLen_eq_card] at h1
  rw [YoungDiagram.rowLen_eq_card] at h2
  exact ⟨lt_of_lt_of_le h1 (card_filter_le _ _), lt_of_lt_of_le h2 (card_filter_le _ _)⟩

/-- A Young diagram with a prime number of cells is a single row or column, or has at least three
addable cells. -/
lemma rowOrCol_or_three_le (μ : YoungDiagram) (hp : μ.cells.card.Prime) :
    IsRowOrCol μ ∨ 3 ≤ a μ := by
  by_cases h : ∃ i j, i < μ.colLen 0 ∧ j < μ.rowLen 0 ∧ (i, j) ∉ μ
  · exact Or.inr (three_le_a μ h)
  · push Not at h
    have hcells : μ.cells = range (μ.colLen 0) ×ˢ range (μ.rowLen 0) := by
      ext ⟨i, j⟩
      simp only [YoungDiagram.mem_cells, mem_product, mem_range]
      refine ⟨fun hc => ⟨?_, ?_⟩, fun hc => h i j hc.1 hc.2⟩
      · exact YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le j) hc)
      · exact YoungDiagram.mem_iff_lt_rowLen.mp (μ.up_left_mem (Nat.zero_le i) le_rfl hc)
    rw [hcells, card_product, card_range, card_range] at hp
    left
    rcases Nat.prime_mul_iff.mp hp with ⟨_, h1⟩ | ⟨_, h1⟩
    · right
      rintro ⟨i, j⟩ hc
      have := YoungDiagram.mem_iff_lt_rowLen.mp (μ.up_left_mem (Nat.zero_le i) le_rfl hc)
      simp only; omega
    · left
      rintro ⟨i, j⟩ hc
      have := YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le j) hc)
      simp only; omega

/-- Averaging: if every object has a shape with a prime number of cells, at most one object has a
single-row shape, at most one has a single-column shape, and some object has another shape, then
the average number of addable cells is at least `7/3`. -/
lemma avg_bound {X : Type*} [Fintype X] (sh : X → YoungDiagram)
    (hp : ∀ x, (sh x).cells.card.Prime)
    (hrow : ∀ x y, (∀ c ∈ sh x, c.1 = 0) → (∀ c ∈ sh y, c.1 = 0) → x = y)
    (hcol : ∀ x y, (∀ c ∈ sh x, c.2 = 0) → (∀ c ∈ sh y, c.2 = 0) → x = y)
    (x0 : X) (hx0 : ¬ IsRowOrCol (sh x0)) :
    (7 : ℝ) / 3 ≤ (∑ x, (a (sh x) : ℝ)) / Fintype.card X := by
  classical
  set B := univ.filter fun x => IsRowOrCol (sh x)
  have hB : B.card ≤ 2 := by
    have hsub : B ⊆ univ.filter (fun x => ∀ c ∈ sh x, c.1 = 0) ∪
        univ.filter (fun x => ∀ c ∈ sh x, c.2 = 0) := by
      intro x hx
      rcases (mem_filter.mp hx).2 with h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩)
    have h1 : (univ.filter (fun x => ∀ c ∈ sh x, c.1 = 0)).card ≤ 1 :=
      card_le_one.mpr fun x hx y hy => hrow x y (mem_filter.mp hx).2 (mem_filter.mp hy).2
    have h2 : (univ.filter (fun x => ∀ c ∈ sh x, c.2 = 0)).card ≤ 1 :=
      card_le_one.mpr fun x hx y hy => hcol x y (mem_filter.mp hx).2 (mem_filter.mp hy).2
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))
  have hBt : B.card + 1 ≤ Fintype.card X :=
    card_lt_univ_of_notMem (x := x0) (by simp [B, hx0])
  have hpt : ∀ x, (3 : ℝ) - (if IsRowOrCol (sh x) then 1 else 0) ≤ a (sh x) := by
    intro x
    split_ifs with h
    · have hne : (sh x).cells.Nonempty := card_pos.mp (hp x).pos
      obtain ⟨⟨i, j⟩, hc⟩ := hne
      have := two_le_a (sh x) ((sh x).up_left_mem (Nat.zero_le i) (Nat.zero_le j) hc)
      have : (2 : ℝ) ≤ a (sh x) := by exact_mod_cast this
      linarith
    · rcases rowOrCol_or_three_le (sh x) (hp x) with h' | h'
      · exact absurd h' h
      · have : (3 : ℝ) ≤ a (sh x) := by exact_mod_cast h'
        linarith
  have hsum : (3 : ℝ) * Fintype.card X - B.card ≤ ∑ x, (a (sh x) : ℝ) := by
    have := sum_le_sum fun x (_ : x ∈ univ) => hpt x
    rw [sum_sub_distrib, sum_boole] at this
    simpa [mul_comm] using this
  have hX : (0 : ℝ) < Fintype.card X := by
    have : 0 < Fintype.card X := by omega
    exact_mod_cast this
  have hB' : (B.card : ℝ) ≤ 2 := by exact_mod_cast hB
  have hBt' : (B.card : ℝ) + 1 ≤ Fintype.card X := by exact_mod_cast hBt
  rw [le_div_iff₀ hX]
  linarith

/-! ## Standard Young tableaux -/

/-- A standard Young tableau with `n` cells, recorded by the cell `pos k ∈ ℕ × ℕ` that holds the
entry `k + 1` (`k = 0, …, n - 1`): the cells are distinct, they form a Young diagram, and entries
increase from left to right along each row and from top to bottom down each column. -/
@[ext] structure SYT (n : ℕ) where
  pos : Fin n → ℕ × ℕ
  inj : Function.Injective pos
  lower : IsLowerSet (Set.range pos)
  row_lt : ∀ k l, (pos k).1 = (pos l).1 → (pos k).2 < (pos l).2 → k < l
  col_lt : ∀ k l, (pos k).2 = (pos l).2 → (pos k).1 < (pos l).1 → k < l

/-- The shape of a standard Young tableau. -/
def SYT.shape {n : ℕ} (T : SYT n) : YoungDiagram where
  cells := univ.image T.pos
  isLowerSet := by rw [coe_image, coe_univ, Set.image_univ]; exact T.lower

lemma SYT.mem_shape {n : ℕ} (T : SYT n) (k : Fin n) : T.pos k ∈ T.shape := by
  rw [← YoungDiagram.mem_cells]; exact mem_image_of_mem _ (mem_univ k)

lemma SYT.card_shape {n : ℕ} (T : SYT n) : T.shape.cells.card = n := by
  simp [SYT.shape, card_image_of_injective _ T.inj]

lemma SYT.pos_lt {n : ℕ} (T : SYT n) (k : Fin n) : (T.pos k).1 < n ∧ (T.pos k).2 < n := by
  have := lt_card_of_mem (T.mem_shape k)
  rwa [T.card_shape] at this

instance (n : ℕ) : Finite (SYT n) :=
  Finite.of_injective (fun T : SYT n => fun k => ((⟨(T.pos k).1, (T.pos_lt k).1⟩ : Fin n),
      (⟨(T.pos k).2, (T.pos_lt k).2⟩ : Fin n)))
    (by
      intro T T' h
      apply SYT.ext; funext k
      have := congrFun h k
      simp only [Prod.mk.injEq, Fin.mk.injEq] at this
      exact Prod.ext this.1 this.2)

noncomputable instance (n : ℕ) : Fintype (SYT n) := Fintype.ofFinite _

/-- Expected number of addable cells of the shape of a uniformly random standard Young tableau
with `n` cells. -/
noncomputable def E_SYT (n : ℕ) : ℝ :=
  (∑ T : SYT n, (a T.shape : ℝ)) / Fintype.card (SYT n)

/-- A single-row standard tableau is unique. -/
lemma SYT.row_unique {n : ℕ} (T T' : SYT n) (h : ∀ c ∈ T.shape, c.1 = 0)
    (h' : ∀ c ∈ T'.shape, c.1 = 0) : T = T' := by
  have mono : ∀ U : SYT n, (∀ c ∈ U.shape, c.1 = 0) → StrictMono fun k => (U.pos k).2 := by
    intro U hU k l hkl
    have hk := hU _ (U.mem_shape k)
    have hl := hU _ (U.mem_shape l)
    rcases lt_trichotomy (U.pos k).2 (U.pos l).2 with h1 | h1 | h1
    · exact h1
    · exact absurd (U.inj (Prod.ext (hk.trans hl.symm) h1)) hkl.ne
    · exact absurd (U.row_lt l k (hl.trans hk.symm) h1) (not_lt.mpr hkl.le)
  have e := fun U : SYT n => fun hU => orderEmbOfFin_unique (s := range n) (card_range n)
    (f := fun k => (U.pos k).2) (fun k => mem_range.mpr (U.pos_lt k).2) (mono U hU)
  apply SYT.ext; funext k
  exact Prod.ext ((h _ (T.mem_shape k)).trans (h' _ (T'.mem_shape k)).symm)
    (congrFun ((e T h).trans (e T' h').symm) k)

/-- A single-column standard tableau is unique. -/
lemma SYT.col_unique {n : ℕ} (T T' : SYT n) (h : ∀ c ∈ T.shape, c.2 = 0)
    (h' : ∀ c ∈ T'.shape, c.2 = 0) : T = T' := by
  have mono : ∀ U : SYT n, (∀ c ∈ U.shape, c.2 = 0) → StrictMono fun k => (U.pos k).1 := by
    intro U hU k l hkl
    have hk := hU _ (U.mem_shape k)
    have hl := hU _ (U.mem_shape l)
    rcases lt_trichotomy (U.pos k).1 (U.pos l).1 with h1 | h1 | h1
    · exact h1
    · exact absurd (U.inj (Prod.ext h1 (hk.trans hl.symm))) hkl.ne
    · exact absurd (U.col_lt l k (hl.trans hk.symm) h1) (not_lt.mpr hkl.le)
  have e := fun U : SYT n => fun hU => orderEmbOfFin_unique (s := range n) (card_range n)
    (f := fun k => (U.pos k).1) (fun k => mem_range.mpr (U.pos_lt k).1) (mono U hU)
  apply SYT.ext; funext k
  exact Prod.ext (congrFun ((e T h).trans (e T' h').symm) k)
    ((h _ (T.mem_shape k)).trans (h' _ (T'.mem_shape k)).symm)

/-- Cells of the hook tableau: entry `1` at `(0,0)`, entry `2` at `(1,0)`, entries `3, …, n` at
`(0,1), …, (0,n-2)`. -/
def hookPos (n : ℕ) (k : Fin n) : ℕ × ℕ := if (k : ℕ) = 1 then (1, 0) else (0, (k : ℕ) - 1)

lemma hook_mem {n : ℕ} (hn : 3 ≤ n) (i j : ℕ) :
    (i, j) ∈ Set.range (hookPos n) ↔ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j + 2 ≤ n) := by
  constructor
  · rintro ⟨k, hk⟩
    have := k.isLt
    unfold hookPos at hk
    split_ifs at hk with h <;> simp only [Prod.mk.injEq] at hk <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, hj⟩)
    · exact ⟨⟨1, by omega⟩, by simp [hookPos]⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact ⟨⟨0, by omega⟩, by simp [hookPos]⟩
      · exact ⟨⟨j + 1, by omega⟩, by simp [hookPos, hj0.ne']⟩

/-- The hook tableau of shape `(n-1, 1)`. -/
def hook (n : ℕ) (hn : 3 ≤ n) : SYT n where
  pos := hookPos n
  inj := by
    intro k l h
    apply Fin.ext
    unfold hookPos at h
    split_ifs at h with h1 h2 h2 <;> simp only [Prod.mk.injEq] at h <;> omega
  lower := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ hba ha
    rw [hook_mem hn] at ha ⊢
    obtain ⟨h1, h2⟩ := Prod.mk_le_mk.mp hba
    omega
  row_lt := by
    intro k l h1 h2
    rw [Fin.lt_def]
    unfold hookPos at h1 h2
    split_ifs at h1 h2 <;> dsimp only at h1 h2 <;> omega
  col_lt := by
    intro k l h1 h2
    rw [Fin.lt_def]
    unfold hookPos at h1 h2
    split_ifs at h1 h2 <;> dsimp only at h1 h2 <;> omega

lemma hook_not_rowOrCol {n : ℕ} (hn : 3 ≤ n) : ¬ IsRowOrCol (hook n hn).shape := by
  have m : ∀ i j, (i, j) ∈ Set.range (hookPos n) → (i, j) ∈ (hook n hn).shape := by
    rintro i j ⟨k, hk⟩; rw [← hk]; exact (hook n hn).mem_shape k
  rintro (h | h)
  · exact absurd (h _ (m 1 0 ((hook_mem hn 1 0).mpr (Or.inl ⟨rfl, rfl⟩)))) (by norm_num)
  · exact absurd (h _ (m 0 1 ((hook_mem hn 0 1).mpr (Or.inr ⟨rfl, by omega⟩)))) (by norm_num)

/-- **Uniform standard tableaux.** For every prime `p ≥ 3`, `E_SYT p ≥ 7/3`. -/
theorem E_SYT_ge {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : (7 : ℝ) / 3 ≤ E_SYT p :=
  avg_bound (fun T : SYT p => T.shape) (fun T => by rw [T.card_shape]; exact hp) SYT.row_unique SYT.col_unique
    (hook p h3) (hook_not_rowOrCol h3)

/-! ## Uniform Young diagrams -/

/-- Young diagrams with `n` cells. -/
def Shape (n : ℕ) := {μ : YoungDiagram // μ.cells.card = n}

instance (n : ℕ) : Finite (Shape n) :=
  Finite.of_injective (β := ↥((range n ×ˢ range n).powerset))
    (fun μ => ⟨μ.1.cells, mem_powerset.mpr fun c hc => by
      obtain ⟨i, j⟩ := c
      have := lt_card_of_mem ((YoungDiagram.mem_cells _).mp hc)
      rw [μ.2] at this
      exact mem_product.mpr ⟨mem_range.mpr this.1, mem_range.mpr this.2⟩⟩)
    (fun μ ν h => Subtype.ext (YoungDiagram.ext (congrArg Subtype.val h)))

noncomputable instance (n : ℕ) : Fintype (Shape n) := Fintype.ofFinite _

/-- Expected number of addable cells of a uniformly random Young diagram with `n` cells. -/
noncomputable def E_shape (n : ℕ) : ℝ :=
  (∑ μ : Shape n, (a μ.1 : ℝ)) / Fintype.card (Shape n)

lemma shape_eq_of_row (μ ν : YoungDiagram) (hc : μ.cells.card = ν.cells.card)
    (h : ∀ c ∈ μ, c.1 = 0) (h' : ∀ c ∈ ν, c.1 = 0) : μ = ν := by
  have key : ∀ κ : YoungDiagram, (∀ c ∈ κ, c.1 = 0) → ∀ i j,
      (i, j) ∈ κ ↔ i = 0 ∧ j < κ.cells.card := by
    intro κ hκ i j
    have hr : κ.row 0 = κ.cells :=
      filter_true_of_mem fun c hc' => hκ c ((YoungDiagram.mem_cells c).mp hc')
    rw [← hr, ← YoungDiagram.rowLen_eq_card]
    refine ⟨fun hc' => ?_, fun ⟨hi, hj⟩ => ?_⟩
    · have hi : i = 0 := hκ _ hc'
      subst hi; exact ⟨rfl, YoungDiagram.mem_iff_lt_rowLen.mp hc'⟩
    · subst hi; exact YoungDiagram.mem_iff_lt_rowLen.mpr hj
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, key μ h, key ν h', hc]

lemma shape_eq_of_col (μ ν : YoungDiagram) (hc : μ.cells.card = ν.cells.card)
    (h : ∀ c ∈ μ, c.2 = 0) (h' : ∀ c ∈ ν, c.2 = 0) : μ = ν := by
  have key : ∀ κ : YoungDiagram, (∀ c ∈ κ, c.2 = 0) → ∀ i j,
      (i, j) ∈ κ ↔ j = 0 ∧ i < κ.cells.card := by
    intro κ hκ i j
    have hr : κ.col 0 = κ.cells :=
      filter_true_of_mem fun c hc' => hκ c ((YoungDiagram.mem_cells c).mp hc')
    rw [← hr, ← YoungDiagram.colLen_eq_card]
    refine ⟨fun hc' => ?_, fun ⟨hj, hi⟩ => ?_⟩
    · have hj : j = 0 := hκ _ hc'
      subst hj; exact ⟨rfl, YoungDiagram.mem_iff_lt_colLen.mp hc'⟩
    · subst hj; exact YoungDiagram.mem_iff_lt_colLen.mpr hi
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, key μ h, key ν h', hc]

/-- **Uniform Young diagrams.** For every prime `p ≥ 3`, `E_shape p ≥ 7/3`. -/
theorem E_shape_ge {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : (7 : ℝ) / 3 ≤ E_shape p :=
  avg_bound (fun μ : Shape p => μ.1) (fun μ => by rw [μ.2]; exact hp)
    (fun μ ν h h' => Subtype.ext (shape_eq_of_row _ _ (μ.2.trans ν.2.symm) h h'))
    (fun μ ν h h' => Subtype.ext (shape_eq_of_col _ _ (μ.2.trans ν.2.symm) h h'))
    ⟨(hook p h3).shape, (hook p h3).card_shape⟩ (hook_not_rowOrCol h3)

/-! ## Neither the limit nor the rate holds -/

/-- If `E p ≥ 7/3` for all primes `p ≥ 3`, then `E n` does not tend to `2`, and
`|E n - 2| ≤ C / log n` fails for every constant `C` (on every tail). -/
lemma not_limit_two (E : ℕ → ℝ) (h : ∀ p : ℕ, p.Prime → 3 ≤ p → (7 : ℝ) / 3 ≤ E p) :
    ¬ Tendsto E atTop (𝓝 2) ∧ ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, |E n - 2| ≤ C / Real.log n := by
  have key : ¬ ∀ᶠ n : ℕ in atTop, E n < 7 / 3 := by
    intro hev
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 3)
    exact absurd (h p hp (le_of_max_le_right hpN)) (not_le.mpr (hN p (le_of_max_le_left hpN)))
  refine ⟨fun ht => key ((tendsto_order.1 ht).2 _ (by norm_num)), ?_⟩
  rintro ⟨C, hC⟩
  have h0 : Tendsto (fun n : ℕ => C / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply key
  filter_upwards [hC, h0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))] with n h1 h2
  have := (abs_le.mp h1).2
  linarith

/-- **Main theorem (disproof of conjecture 00000000421).** Under the uniform measure on standard
Young tableaux with `n` cells, the expected number `E_SYT n` of addable outer-corner cells is at
least `7/3` for every prime `n ≥ 3`; hence `E_SYT n` does not converge to `2`, and
`|E_SYT n - 2| ≤ C / log n` fails on every tail for every constant `C`.  The same three statements
hold for the uniform measure on Young diagrams with `n` cells (`E_shape`). -/
theorem disproof :
    (∀ p : ℕ, p.Prime → 3 ≤ p → (7 : ℝ) / 3 ≤ E_SYT p ∧ (7 : ℝ) / 3 ≤ E_shape p) ∧
    (¬ Tendsto E_SYT atTop (𝓝 2) ∧
      ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, |E_SYT n - 2| ≤ C / Real.log n) ∧
    (¬ Tendsto E_shape atTop (𝓝 2) ∧
      ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, |E_shape n - 2| ≤ C / Real.log n) :=
  ⟨fun _ hp h3 => ⟨E_SYT_ge hp h3, E_shape_ge hp h3⟩,
    not_limit_two _ fun _ hp h3 => E_SYT_ge hp h3, not_limit_two _ fun _ hp h3 => E_shape_ge hp h3⟩

end C421
