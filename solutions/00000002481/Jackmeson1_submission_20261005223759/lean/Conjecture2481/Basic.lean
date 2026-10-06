import Mathlib

/-!
# Conjecture 00000002481: the Durfee square decomposition of a partition

Partitions are Mathlib `YoungDiagram`s (Ferrers diagrams; `|λ| = card`, conjugate = `transpose`).
(1) `durfeeEquiv`, `durfee_decomposition`: Durfee side `d` ↔ (right piece with `≤ d` parts,
lower piece with parts `≤ d`), `|λ| = d^2 + |α| + |β|`. (3) `durfeeEquiv_transpose`,
`glue_transpose`: conjugation fixes `d` and swaps the pieces. (2) `cnt_durfee`, `gf_durfee`,
`gf_rowsLt_mul_prod`, `gf_durfee_mul`, `hasSum_gf_durfee`: `Σ_λ q^|λ| = Σ_d q^(d^2)/(q;q)_d^2`.
-/

open Finset PowerSeries

namespace C2481

open YoungDiagram

/-! ## The Durfee side -/

theorem exists_diag_notMem (μ : YoungDiagram) : ∃ i, (i, i) ∉ μ := by
  obtain ⟨j, hj⟩ := μ.exists_notMem_row 0
  exact ⟨j, fun h => hj (μ.up_left_mem (Nat.zero_le _) le_rfl h)⟩

/-- The side of the Durfee square: the least `i` with `(i, i) ∉ μ`. -/
def durfee (μ : YoungDiagram) : ℕ := Nat.find (exists_diag_notMem μ)

theorem diag_mem_iff (μ : YoungDiagram) (i : ℕ) : (i, i) ∈ μ ↔ i < durfee μ :=
  ⟨fun h => not_le.1 fun hle => Nat.find_spec (exists_diag_notMem μ) (μ.up_left_mem hle hle h),
    fun h => not_not.1 (Nat.find_min (exists_diag_notMem μ) h)⟩

theorem square_mem {μ : YoungDiagram} {i j : ℕ} (hi : i < durfee μ) (hj : j < durfee μ) :
    (i, j) ∈ μ :=
  μ.up_left_mem (le_max_left i j) (le_max_right i j) ((diag_mem_iff μ _).2 (max_lt hi hj))

theorem notMem_of_le {μ : YoungDiagram} {i j : ℕ} (hi : durfee μ ≤ i) (hj : durfee μ ≤ j) :
    (i, j) ∉ μ := fun h =>
  lt_irrefl _ ((diag_mem_iff μ (durfee μ)).1 (μ.up_left_mem hi hj h))

/-- Textbook definition: `durfee μ` is the side of the largest square contained in `μ`. -/
theorem isGreatest_durfee (μ : YoungDiagram) :
    IsGreatest {d | ∀ i < d, ∀ j < d, (i, j) ∈ μ} (durfee μ) :=
  ⟨fun _ hi _ hj => square_mem hi hj,
    fun _ hd => not_lt.1 fun h => notMem_of_le le_rfl le_rfl (hd _ h _ h)⟩

/-- Equivalent textbook definition: the largest `s` such that at least `s` parts are `≥ s`
(row `s - 1` has length `≥ s`). -/
theorem isGreatest_durfee_rowLen (μ : YoungDiagram) :
    IsGreatest {s | s = 0 ∨ s ≤ μ.rowLen (s - 1)} (durfee μ) := by
  refine ⟨?_, fun s hs => ?_⟩
  · rcases Nat.eq_zero_or_pos (durfee μ) with h | h
    · exact Or.inl h
    · have := mem_iff_lt_rowLen.1 (square_mem (μ := μ) (i := durfee μ - 1)
        (j := durfee μ - 1) (by omega) (by omega))
      exact Or.inr (by omega)
  · rcases hs with rfl | hs
    · exact Nat.zero_le _
    · by_contra h
      push Not at h
      exact notMem_of_le (μ := μ) (i := s - 1) (j := s - 1) (by omega) (by omega)
        (mem_iff_lt_rowLen.2 (by omega))

theorem durfee_eq_of {μ : YoungDiagram} {d : ℕ} (h1 : ∀ i < d, ∀ j < d, (i, j) ∈ μ)
    (h2 : (d, d) ∉ μ) : durfee μ = d :=
  le_antisymm (not_lt.1 fun h => h2 ((diag_mem_iff μ d).2 h))
    (not_lt.1 fun h => lt_irrefl _ ((diag_mem_iff μ _).1 (h1 _ h _ h)))

/-! ## Cutting and splicing -/

theorem inj_col (k : ℕ) : Function.Injective fun c : ℕ × ℕ => (c.1, c.2 + k) := fun a b h => by
  simp only [Prod.mk.injEq, add_left_inj] at h; exact Prod.ext h.1 h.2

theorem inj_row (k : ℕ) : Function.Injective fun c : ℕ × ℕ => (c.1 + k, c.2) := fun a b h => by
  simp only [Prod.mk.injEq, add_left_inj] at h; exact Prod.ext h.1 h.2

/-- Remove the first `k` columns. -/
noncomputable def dropCols (k : ℕ) (μ : YoungDiagram) : YoungDiagram where
  cells := μ.cells.preimage (fun c => (c.1, c.2 + k)) (inj_col k).injOn
  isLowerSet := by
    intro a b hab ha
    rw [Finset.mem_coe, Finset.mem_preimage] at ha ⊢
    exact μ.up_left_mem hab.1 (Nat.add_le_add_right hab.2 k) ha

@[simp] theorem mem_dropCols {k : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ dropCols k μ ↔ (c.1, c.2 + k) ∈ μ := by
  show c ∈ (dropCols k μ).cells ↔ _
  exact Finset.mem_preimage (hf := (inj_col k).injOn)

/-- Remove the first `k` rows. -/
noncomputable def dropRows (k : ℕ) (μ : YoungDiagram) : YoungDiagram :=
  (dropCols k μ.transpose).transpose

@[simp] theorem mem_dropRows {k : ℕ} {μ : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ dropRows k μ ↔ (c.1 + k, c.2) ∈ μ := by
  simp [dropRows]

/-- Cells of the splice of an `r × s` rectangle, `α` to its right, `β` below it. -/
def glueCells (r s : ℕ) (α β : YoungDiagram) : Finset (ℕ × ℕ) :=
  (range r ×ˢ range s) ∪ ((α.cells.filter (·.1 < r)).image fun c => (c.1, c.2 + s)) ∪
    ((β.cells.filter (·.2 < s)).image fun c => (c.1 + r, c.2))

theorem mem_glueCells {r s : ℕ} {α β : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ glueCells r s α β ↔ (c.1 < r ∧ c.2 < s) ∨ (c.1 < r ∧ s ≤ c.2 ∧ (c.1, c.2 - s) ∈ α) ∨
      (r ≤ c.1 ∧ c.2 < s ∧ (c.1 - r, c.2) ∈ β) := by
  obtain ⟨i, j⟩ := c
  simp only [glueCells, mem_union, mem_product, mem_range, mem_image, mem_filter, mem_cells,
    Prod.mk.injEq]
  constructor
  · rintro ((⟨h1, h2⟩ | ⟨a, ⟨h, h'⟩, rfl, rfl⟩) | ⟨a, ⟨h, h'⟩, rfl, rfl⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h', by omega, by simpa using h⟩)
    · exact Or.inr (Or.inr ⟨by omega, h', by simpa using h⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · exact Or.inl (Or.inr ⟨(i, j - s), ⟨h3, h1⟩, rfl, by omega⟩)
    · exact Or.inr ⟨(i - r, j), ⟨h3, h2⟩, by omega, rfl⟩

/-- Splice an `r × s` rectangle, `α` (rows `< r`) to its right and `β` (columns `< s`) below. -/
def glue (r s : ℕ) (α β : YoungDiagram) : YoungDiagram where
  cells := glueCells r s α β
  isLowerSet := by
    intro a b hab ha
    have h1 : b.1 ≤ a.1 := hab.1
    have h2 : b.2 ≤ a.2 := hab.2
    simp only [Finset.mem_coe, mem_glueCells] at ha ⊢
    rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2, ha3⟩ | ⟨ha1, ha2, ha3⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · by_cases hb : b.2 < s
      · exact Or.inl ⟨by omega, hb⟩
      · exact Or.inr (Or.inl ⟨by omega, by omega, α.up_left_mem h1 (by omega) ha3⟩)
    · by_cases hb : b.1 < r
      · exact Or.inl ⟨hb, by omega⟩
      · exact Or.inr (Or.inr ⟨by omega, by omega, β.up_left_mem (by omega) h2 ha3⟩)

theorem mem_glue {r s : ℕ} {α β : YoungDiagram} {c : ℕ × ℕ} :
    c ∈ glue r s α β ↔ (c.1 < r ∧ c.2 < s) ∨ (c.1 < r ∧ s ≤ c.2 ∧ (c.1, c.2 - s) ∈ α) ∨
      (r ≤ c.1 ∧ c.2 < s ∧ (c.1 - r, c.2) ∈ β) :=
  mem_glueCells

/-- Diagrams with all cells in rows `< d`: partitions with at most `d` parts. -/
def RowsLt (d : ℕ) (μ : YoungDiagram) : Prop := ∀ c ∈ μ, c.1 < d

/-- Diagrams with all cells in columns `< d`: partitions with all parts `≤ d`. -/
def ColsLt (d : ℕ) (μ : YoungDiagram) : Prop := ∀ c ∈ μ, c.2 < d

/-- `RowsLt d μ` iff the number of parts `colLen 0 = rowLens.length` is `≤ d`. -/
theorem rowsLt_iff (d : ℕ) (μ : YoungDiagram) : RowsLt d μ ↔ μ.colLen 0 ≤ d :=
  ⟨fun h => not_lt.1 fun h' => lt_irrefl d (h _ (mem_iff_lt_colLen.2 h')), fun h c hc =>
    (mem_iff_lt_colLen.1 (μ.up_left_mem le_rfl (Nat.zero_le _) hc)).trans_le h⟩

/-- `ColsLt d μ` iff the largest part `rowLen 0` is `≤ d`. -/
theorem colsLt_iff (d : ℕ) (μ : YoungDiagram) : ColsLt d μ ↔ μ.rowLen 0 ≤ d :=
  ⟨fun h => not_lt.1 fun h' => lt_irrefl d (h _ (mem_iff_lt_rowLen.2 h')), fun h c hc =>
    (mem_iff_lt_rowLen.1 (μ.up_left_mem (Nat.zero_le _) le_rfl hc)).trans_le h⟩

theorem glue_drop {μ : YoungDiagram} {r s : ℕ} (hrect : ∀ i < r, ∀ j < s, (i, j) ∈ μ)
    (hrs : (r, s) ∉ μ) : glue r s (dropCols s μ) (dropRows r μ) = μ := by
  refine SetLike.ext fun c => ?_
  obtain ⟨i, j⟩ := c
  simp only [mem_glue, mem_dropCols, mem_dropRows]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact hrect i h1 j h2
    · rwa [Nat.sub_add_cancel h2] at h3
    · rwa [Nat.sub_add_cancel h1] at h3
  · intro h
    by_cases hi : i < r
    · by_cases hj : j < s
      · exact Or.inl ⟨hi, hj⟩
      · exact Or.inr (Or.inl ⟨hi, by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩)
    · have hj : j < s := by
        by_contra hj
        exact hrs (μ.up_left_mem (by omega) (by omega) h)
      exact Or.inr (Or.inr ⟨by omega, hj, by rwa [Nat.sub_add_cancel (by omega)]⟩)

theorem dropCols_glue {r s : ℕ} {α β : YoungDiagram} (hα : RowsLt r α) :
    dropCols s (glue r s α β) = α := SetLike.ext fun ⟨i, j⟩ => by
  simp only [mem_dropCols, mem_glue, Nat.add_sub_cancel]
  exact ⟨by rintro (⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, h, _⟩) <;> first | omega | exact h,
    fun h => Or.inr (Or.inl ⟨hα _ h, by omega, h⟩)⟩

theorem dropRows_glue {r s : ℕ} {α β : YoungDiagram} (hβ : ColsLt s β) :
    dropRows r (glue r s α β) = β := SetLike.ext fun ⟨i, j⟩ => by
  simp only [mem_dropRows, mem_glue, Nat.add_sub_cancel]
  exact ⟨by rintro (⟨h, _⟩ | ⟨h, _, _⟩ | ⟨_, _, h⟩) <;> first | omega | exact h,
    fun h => Or.inr (Or.inr ⟨by omega, hβ _ h, h⟩)⟩

theorem card_glue {r s : ℕ} {α β : YoungDiagram} (hα : RowsLt r α) (hβ : ColsLt s β) :
    (glue r s α β).card = r * s + α.card + β.card := by
  have hA : α.cells.filter (·.1 < r) = α.cells := filter_true_of_mem fun c hc => hα c hc
  have hB : β.cells.filter (·.2 < s) = β.cells := filter_true_of_mem fun c hc => hβ c hc
  show (glueCells r s α β).card = _
  unfold glueCells
  rw [card_union_of_disjoint, card_union_of_disjoint, card_product, card_range, card_range,
    card_image_of_injective _ (inj_col s), card_image_of_injective _ (inj_row r), hA, hB]
  · rw [disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [mem_product, mem_range, mem_image, mem_filter, mem_cells, Prod.mk.injEq] at h1 h2
    obtain ⟨a, _, rfl, rfl⟩ := h2
    omega
  · rw [disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [mem_union, mem_product, mem_range, mem_image, mem_filter, mem_cells,
      Prod.mk.injEq] at h1 h2
    obtain ⟨a, ⟨ha, _⟩, rfl, rfl⟩ := h2
    rcases h1 with ⟨h, _⟩ | ⟨a', ⟨_, h⟩, h', _⟩
    · omega
    · omega

/-! ## The Durfee decomposition -/

theorem rowsLt_dropCols {μ : YoungDiagram} {d : ℕ} (h : durfee μ = d) :
    RowsLt d (dropCols d μ) := by
  subst h
  exact fun c hc => not_le.1 fun h' => notMem_of_le h' (Nat.le_add_left _ _) (mem_dropCols.1 hc)

theorem colsLt_dropRows {μ : YoungDiagram} {d : ℕ} (h : durfee μ = d) :
    ColsLt d (dropRows d μ) := by
  subst h
  exact fun c hc => not_le.1 fun h' => notMem_of_le (Nat.le_add_left _ _) h' (mem_dropRows.1 hc)

theorem durfee_glue (d : ℕ) (α β : YoungDiagram) : durfee (glue d d α β) = d :=
  durfee_eq_of (fun _ hi _ hj => mem_glue.2 (Or.inl ⟨hi, hj⟩)) (by simp [mem_glue])

theorem glue_durfee (μ : YoungDiagram) :
    glue (durfee μ) (durfee μ) (dropCols (durfee μ) μ) (dropRows (durfee μ) μ) = μ :=
  glue_drop (fun _ hi _ hj => square_mem hi hj) (notMem_of_le le_rfl le_rfl)

theorem card_durfee (μ : YoungDiagram) :
    μ.card = durfee μ ^ 2 + (dropCols (durfee μ) μ).card + (dropRows (durfee μ) μ).card := by
  rw [sq, ← card_glue (rowsLt_dropCols rfl) (colsLt_dropRows rfl), glue_durfee]

/-- **Durfee decomposition (bijection).** A diagram with Durfee side `d` corresponds to the pair
(right piece, lower piece): the right piece lies in rows `< d` (at most `d` parts), the lower
piece in columns `< d` (parts `≤ d`); the inverse map splices the `d × d` square back in. -/
noncomputable def durfeeEquiv (d : ℕ) :
    {μ : YoungDiagram // durfee μ = d} ≃
      {α : YoungDiagram // RowsLt d α} × {β : YoungDiagram // ColsLt d β} where
  toFun μ := (⟨dropCols d μ.1, rowsLt_dropCols μ.2⟩, ⟨dropRows d μ.1, colsLt_dropRows μ.2⟩)
  invFun p := ⟨glue d d p.1.1 p.2.1, durfee_glue d _ _⟩
  left_inv μ := by
    obtain ⟨μ, rfl⟩ := μ
    exact Subtype.ext (glue_durfee μ)
  right_inv p := Prod.ext (Subtype.ext (dropCols_glue p.1.2)) (Subtype.ext (dropRows_glue p.2.2))

/-- **(1) Cell-level splitting.** The cells of `μ` (Durfee side `d`) are exactly the disjoint
union of the `d × d` square, the right piece shifted by `d` columns and the lower piece
shifted by `d` rows; and `|μ| = d^2 + |right| + |lower|`. -/
theorem durfee_decomposition (d : ℕ) (μ : {μ : YoungDiagram // durfee μ = d}) :
    (∀ c, c ∈ μ.1 ↔ (c.1 < d ∧ c.2 < d) ∨
        (c.1 < d ∧ d ≤ c.2 ∧ (c.1, c.2 - d) ∈ (durfeeEquiv d μ).1.1) ∨
        (d ≤ c.1 ∧ c.2 < d ∧ (c.1 - d, c.2) ∈ (durfeeEquiv d μ).2.1)) ∧
    μ.1.card = d ^ 2 + (durfeeEquiv d μ).1.1.card + (durfeeEquiv d μ).2.1.card := by
  obtain ⟨μ, rfl⟩ := μ
  exact ⟨fun c => (SetLike.ext_iff.1 (glue_durfee μ) c).symm.trans mem_glue, card_durfee μ⟩

/-! ## (3) Symmetry under conjugation -/

theorem durfee_transpose (μ : YoungDiagram) : durfee μ.transpose = durfee μ :=
  durfee_eq_of (fun _ hi _ hj => mem_transpose.2 (square_mem hj hi))
    (fun h => notMem_of_le le_rfl le_rfl (mem_transpose.1 h))

theorem dropCols_transpose (k : ℕ) (μ : YoungDiagram) :
    dropCols k μ.transpose = (dropRows k μ).transpose :=
  SetLike.ext fun c => by simp

theorem dropRows_transpose (k : ℕ) (μ : YoungDiagram) :
    dropRows k μ.transpose = (dropCols k μ).transpose :=
  SetLike.ext fun c => by simp

theorem rowsLt_transpose {d : ℕ} {μ : YoungDiagram} : RowsLt d μ.transpose ↔ ColsLt d μ :=
  ⟨fun h c hc => h c.swap (mem_transpose.2 (by simpa using hc)),
    fun h c hc => h c.swap (mem_transpose.1 hc)⟩

/-- **(3)** Conjugation preserves the Durfee side and exchanges the two pieces, each conjugated:
the right piece of `μᵀ` is the conjugate of the lower piece of `μ`, and vice versa. -/
theorem durfeeEquiv_transpose {d : ℕ} (μ : {μ : YoungDiagram // durfee μ = d}) :
    (durfeeEquiv d ⟨μ.1.transpose, (durfee_transpose μ.1).trans μ.2⟩).1.1 =
        ((durfeeEquiv d μ).2.1).transpose ∧
      (durfeeEquiv d ⟨μ.1.transpose, (durfee_transpose μ.1).trans μ.2⟩).2.1 =
        ((durfeeEquiv d μ).1.1).transpose :=
  ⟨dropCols_transpose d μ.1, dropRows_transpose d μ.1⟩

/-- **(3)** The splicing is symmetric: conjugating the splice of (square, `α`, `β`) gives the
splice of (square, `βᵀ`, `αᵀ`). -/
theorem glue_transpose (r s : ℕ) (α β : YoungDiagram) :
    (glue r s α β).transpose = glue s r β.transpose α.transpose := by
  refine SetLike.ext fun c => ?_
  obtain ⟨i, j⟩ := c
  simp only [mem_transpose, mem_glue, Prod.swap_prod_mk]
  tauto

/-! ## (2) Counting and generating functions -/

theorem lt_card_of_mem {μ : YoungDiagram} {c : ℕ × ℕ} (h : c ∈ μ) :
    c.1 < μ.card ∧ c.2 < μ.card :=
  ⟨(mem_iff_lt_colLen.1 h).trans_le (μ.colLen_eq_card.trans_le (card_le_card (filter_subset _ _))),
    (mem_iff_lt_rowLen.1 h).trans_le (μ.rowLen_eq_card.trans_le (card_le_card (filter_subset _ _)))⟩

theorem finite_card (n : ℕ) : {μ : YoungDiagram | μ.card = n}.Finite := by
  have hinj : Function.Injective YoungDiagram.cells := fun a b h => YoungDiagram.ext h
  refine ((range n ×ˢ range n).powerset.finite_toSet.preimage hinj.injOn).subset ?_
  intro μ hμ
  rw [Set.mem_ofPred_eq] at hμ
  simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_powerset]
  intro c hc
  have := lt_card_of_mem (μ := μ) hc
  rw [hμ] at this
  simpa [mem_product, mem_range] using this

/-- The finite set of Young diagrams with `n` cells (the partitions of `n`). -/
noncomputable def yd (n : ℕ) : Finset YoungDiagram := (finite_card n).toFinset

@[simp] theorem mem_yd {n : ℕ} {μ : YoungDiagram} : μ ∈ yd n ↔ μ.card = n := by
  simp [yd]

instance (d : ℕ) : DecidablePred (RowsLt d) := fun μ =>
  decidable_of_iff (∀ c ∈ μ.cells, c.1 < d) Iff.rfl

instance (d : ℕ) : DecidablePred (ColsLt d) := fun μ =>
  decidable_of_iff (∀ c ∈ μ.cells, c.2 < d) Iff.rfl

/-- The number of partitions of `n` (Young diagrams with `n` cells) satisfying `P`. -/
noncomputable def cnt (P : YoungDiagram → Prop) [DecidablePred P] (n : ℕ) : ℕ :=
  ((yd n).filter P).card

/-- The generating function `Σ_n #{λ ⊢ n | P λ} q^n`, a formal power series over `ℤ`. -/
noncomputable def gf (P : YoungDiagram → Prop) [DecidablePred P] : PowerSeries ℤ :=
  PowerSeries.mk fun n => (cnt P n : ℤ)

/-- **(2), counting form.** `#{λ ⊢ n : durfee λ = d} = Σ_{a+b=n-d^2} #{α ⊢ a : ≤ d parts} ·
#{β ⊢ b : parts ≤ d}` (and `0` if `d^2 > n`). -/
theorem cnt_durfee (d n : ℕ) : cnt (durfee · = d) n =
    if d ^ 2 ≤ n then ∑ p ∈ antidiagonal (n - d ^ 2), cnt (RowsLt d) p.1 * cnt (ColsLt d) p.2
    else 0 := by
  unfold cnt
  split_ifs with h
  · have hR : ∑ p ∈ antidiagonal (n - d ^ 2),
          ((yd p.1).filter (RowsLt d)).card * ((yd p.2).filter (ColsLt d)).card
        = ((antidiagonal (n - d ^ 2)).sigma fun p =>
            (yd p.1).filter (RowsLt d) ×ˢ (yd p.2).filter (ColsLt d)).card := by
      rw [card_sigma]; simp only [card_product]
    rw [hR]
    apply card_nbij'
      (fun μ => (⟨((dropCols d μ).card, (dropRows d μ).card), (dropCols d μ, dropRows d μ)⟩ :
        Σ _ : ℕ × ℕ, YoungDiagram × YoungDiagram))
      (fun x => glue d d x.2.1 x.2.2)
    · intro μ hμ
      simp only [mem_coe, mem_filter, mem_yd] at hμ
      obtain ⟨h1, rfl⟩ := hμ
      have := card_durfee μ
      simp only [mem_coe, mem_sigma, mem_product, mem_filter, mem_yd,
        HasAntidiagonal.mem_antidiagonal]
      exact ⟨by omega, ⟨trivial, rowsLt_dropCols rfl⟩, trivial, colsLt_dropRows rfl⟩
    · rintro ⟨⟨a, b⟩, α, β⟩ hx
      simp only [mem_coe, mem_sigma, mem_product, mem_filter, mem_yd,
        HasAntidiagonal.mem_antidiagonal] at hx
      obtain ⟨hab, ⟨hα1, hα2⟩, hβ1, hβ2⟩ := hx
      simp only [mem_coe, mem_filter, mem_yd]
      refine ⟨?_, durfee_glue d α β⟩
      rw [card_glue hα2 hβ2, ← sq]
      omega
    · intro μ hμ
      simp only [mem_coe, mem_filter, mem_yd] at hμ
      obtain ⟨_, rfl⟩ := hμ
      exact glue_durfee μ
    · rintro ⟨⟨a, b⟩, α, β⟩ hx
      simp only [mem_coe, mem_sigma, mem_product, mem_filter, mem_yd,
        HasAntidiagonal.mem_antidiagonal] at hx
      obtain ⟨hab, ⟨hα1, hα2⟩, hβ1, hβ2⟩ := hx
      simp only [dropCols_glue hα2, dropRows_glue hβ2, hα1, hβ1]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro μ hμ hd
    rw [mem_yd] at hμ
    have := card_durfee μ
    rw [hd] at this
    omega

/-- **(2), generating-function form.** The series of diagrams with Durfee side `d` is
`q^(d^2)` times the product of the two corner series. -/
theorem gf_durfee (d : ℕ) :
    gf (durfee · = d) = X ^ (d ^ 2) * (gf (RowsLt d) * gf (ColsLt d)) := by
  ext n
  rw [coeff_X_pow_mul']
  simp only [gf, coeff_mk]
  rw [cnt_durfee]
  split_ifs with h
  · rw [coeff_mul]; simp
  · simp

theorem card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  simp [YoungDiagram.card, transpose]

/-- Conjugation: partitions of `n` with parts `≤ d` are as many as those with `≤ d` parts. -/
theorem cnt_colsLt (d n : ℕ) : cnt (ColsLt d) n = cnt (RowsLt d) n := by
  unfold cnt
  apply card_nbij' transpose transpose <;> intro μ hμ <;>
    simp only [mem_coe, mem_filter, mem_yd, card_transpose, transpose_transpose] at hμ ⊢
  · exact ⟨hμ.1, rowsLt_transpose.2 hμ.2⟩
  · exact ⟨hμ.1, by rw [← rowsLt_transpose, transpose_transpose]; exact hμ.2⟩

theorem not_rowsLt_iff {d : ℕ} {μ : YoungDiagram} : ¬ RowsLt d μ ↔ (d, 0) ∈ μ := by
  refine ⟨fun h => ?_, fun h h' => lt_irrefl d (h' _ h)⟩
  simp only [RowsLt, not_forall, not_lt] at h
  obtain ⟨c, hc, hd⟩ := h
  exact μ.up_left_mem hd (Nat.zero_le _) hc

/-- Peeling the first column off a diagram with exactly `d + 1` rows. -/
theorem peel {μ : YoungDiagram} {d : ℕ} (h1 : RowsLt (d + 1) μ) (h2 : (d, 0) ∈ μ) :
    glue (d + 1) 1 (dropCols 1 μ) ⊥ = μ ∧ RowsLt (d + 1) (dropCols 1 μ) := by
  have hb : dropRows (d + 1) μ = ⊥ := SetLike.ext fun c => by
    simp only [mem_dropRows]
    exact ⟨fun h => absurd (h1 _ h) (by dsimp only; omega), fun h => absurd h (notMem_bot c)⟩
  have hr : RowsLt (d + 1) (dropCols 1 μ) := fun c hc => h1 (c.1, c.2 + 1) (mem_dropCols.1 hc)
  refine ⟨?_, hr⟩
  rw [← hb]
  exact glue_drop (fun i hi j hj => μ.up_left_mem (by omega) (by omega) h2)
    (fun h => absurd (h1 _ h) (lt_irrefl _))

theorem card_bot : (⊥ : YoungDiagram).card = 0 := by simp [YoungDiagram.card]

theorem cnt_rowsLt_succ (d n : ℕ) : cnt (RowsLt (d + 1)) n =
    cnt (RowsLt d) n + if d + 1 ≤ n then cnt (RowsLt (d + 1)) (n - (d + 1)) else 0 := by
  unfold cnt
  rw [← card_filter_add_card_filter_not (s := (yd n).filter (RowsLt (d + 1))) (RowsLt d),
    filter_filter, filter_filter]
  congr 1
  · exact congrArg card (filter_congr fun μ _ =>
      ⟨fun h => h.2, fun h => ⟨fun c hc => Nat.lt_succ_of_lt (h c hc), h⟩⟩)
  · have hbot : ColsLt 1 ⊥ := fun c hc => absurd hc (notMem_bot c)
    split_ifs with h
    · apply card_nbij' (dropCols 1) (fun ν => glue (d + 1) 1 ν ⊥)
      · intro μ hμ
        simp only [mem_coe, mem_filter, mem_yd, not_rowsLt_iff] at hμ ⊢
        obtain ⟨hc, h1, h2⟩ := hμ
        obtain ⟨hg, hr⟩ := peel h1 h2
        have := congrArg YoungDiagram.card hg
        rw [card_glue hr hbot, card_bot] at this
        exact ⟨by omega, hr⟩
      · intro ν hν
        simp only [mem_coe, mem_filter, mem_yd, not_rowsLt_iff] at hν ⊢
        refine ⟨by rw [card_glue hν.2 hbot, card_bot]; omega, fun c hc => ?_,
          mem_glue.2 (Or.inl ⟨by omega, by omega⟩)⟩
        rcases mem_glue.1 hc with h | h | h
        exacts [h.1, h.1, absurd h.2.2 (notMem_bot _)]
      · intro μ hμ
        simp only [mem_coe, mem_filter, mem_yd, not_rowsLt_iff] at hμ
        exact (peel hμ.2.1 hμ.2.2).1
      · intro ν hν
        simp only [mem_coe, mem_filter, mem_yd] at hν
        exact dropCols_glue hν.2
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro μ hμ hμ'
      rw [mem_yd] at hμ
      have := (lt_card_of_mem (not_rowsLt_iff.1 hμ'.2)).1
      simp only at this
      omega

theorem cnt_rowsLt_zero (n : ℕ) : cnt (RowsLt 0) n = if n = 0 then 1 else 0 := by
  have key : ∀ μ : YoungDiagram, RowsLt 0 μ ↔ μ = ⊥ := fun μ =>
    ⟨fun h => SetLike.ext fun c => ⟨fun hc => absurd (h c hc) (Nat.not_lt_zero _),
      fun hc => absurd hc (notMem_bot c)⟩, by rintro rfl c hc; exact absurd hc (notMem_bot c)⟩
  unfold cnt
  split_ifs with h
  · subst h
    refine card_eq_one.2 ⟨⊥, ext fun μ => ?_⟩
    simp only [mem_filter, mem_yd, mem_singleton, key]
    exact ⟨fun h => h.2, fun h => ⟨by rw [h, card_bot], h⟩⟩
  · refine card_eq_zero.2 (filter_eq_empty_iff.2 fun μ hμ h0 => ?_)
    rw [mem_yd] at hμ
    rw [key] at h0
    subst h0
    exact h (card_bot ▸ hμ).symm

theorem gf_rowsLt_zero : gf (RowsLt 0) = 1 := by
  ext n
  simp [gf, cnt_rowsLt_zero, coeff_one]

theorem gf_rowsLt_succ (d : ℕ) :
    gf (RowsLt (d + 1)) = gf (RowsLt d) + X ^ (d + 1) * gf (RowsLt (d + 1)) := by
  ext n
  rw [map_add, coeff_X_pow_mul']
  simp only [gf, coeff_mk]
  rw [cnt_rowsLt_succ d n]
  split_ifs <;> simp

/-- **Corner series.** The generating function of partitions with at most `d` parts is
`1/(q;q)_d`: it times `(q;q)_d = ∏_{i=1}^{d} (1 - q^i)` equals `1`. -/
theorem gf_rowsLt_mul_prod (d : ℕ) :
    gf (RowsLt d) * ∏ i ∈ range d, (1 - X ^ (i + 1)) = 1 := by
  induction d with
  | zero => simp [gf_rowsLt_zero]
  | succ d ih =>
    have h := gf_rowsLt_succ d
    rw [prod_range_succ]
    linear_combination ih + (∏ i ∈ range d, (1 - X ^ (i + 1) : PowerSeries ℤ)) * h

theorem gf_colsLt (d : ℕ) : gf (ColsLt d) = gf (RowsLt d) := by
  ext n
  simp [gf, cnt_colsLt]

/-- **(2), per `d`.** The generating function of partitions with Durfee side `d` is
`q^(d^2) / ((q;q)_d)^2`, i.e. multiplied by `((q;q)_d)^2` it equals `q^(d^2)`. -/
theorem gf_durfee_mul (d : ℕ) :
    gf (durfee · = d) * (∏ i ∈ range d, (1 - X ^ (i + 1))) ^ 2 = X ^ (d ^ 2) := by
  rw [gf_durfee, gf_colsLt]
  linear_combination (X ^ (d ^ 2) * (gf (RowsLt d) * ∏ i ∈ range d, (1 - X ^ (i + 1)) + 1)) *
    gf_rowsLt_mul_prod d

open PowerSeries.WithPiTopology in
/-- **(2), total.** `Σ_λ q^|λ| = Σ_d (series of Durfee side d) = Σ_d q^(d^2) · C_d^2`, where
`C_d = gf (RowsLt d) = 1/(q;q)_d`, as formal power series (coefficientwise topology). -/
theorem hasSum_gf_durfee :
    HasSum (fun d => gf (durfee · = d)) (gf fun _ => True) ∧
      HasSum (fun d => X ^ (d ^ 2) * gf (RowsLt d) ^ 2) (gf fun _ => True) := by
  have h1 : HasSum (fun d => gf (durfee · = d)) (gf fun _ => True) := by
    rw [hasSum_iff_hasSum_coeff]
    intro n
    simp only [gf, coeff_mk]
    have : cnt (fun _ => True) n = ∑ d ∈ range (n + 1), cnt (durfee · = d) n := by
      unfold cnt
      rw [filter_true_of_mem (fun _ _ => trivial)]
      apply card_eq_sum_card_fiberwise
      intro μ hμ
      rw [mem_coe, mem_yd] at hμ
      have := card_durfee μ
      have := Nat.le_self_pow two_ne_zero (durfee μ)
      rw [mem_coe, mem_range]
      omega
    rw [this, Nat.cast_sum]
    apply hasSum_sum_of_ne_finset_zero
    intro d hd
    rw [mem_range, not_lt] at hd
    have := Nat.le_self_pow two_ne_zero d
    rw [cnt_durfee, if_neg (by omega), Nat.cast_zero]
  refine ⟨h1, ?_⟩
  convert h1 using 2 with d
  rw [gf_durfee, gf_colsLt, sq]
  ring

end C2481
