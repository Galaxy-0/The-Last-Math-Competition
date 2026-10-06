import Mathlib

/-!
# Conjecture 00000003848 (affine cell-core dictionary) is false

Statement (official): "Two-sided cells of the affine 0-Hecke monoid are its two-sided
equivalence classes. Two-sided cells of type A_n^{(1)} correspond one-to-one with (n+1)-core
partitions, and the number of left cells in the corresponding cell equals the number of distinct
parts of the partition obtained by removing all (n+1)-hooks from that core."

* `not_cellCoreDictionary`: for every `n`, and every operation `strip` ("remove all
  (n+1)-hooks") that sends the empty partition to itself, no bijection between the two-sided
  cells of the affine 0-Hecke monoid of type `A_n^{(1)}` and the `(n+1)`-cores has the stated
  left-cell count (the empty core would need a cell with `0` left cells).
* `affineA1_jTrivial`, `numLeftCells_affineA1`, `affineA1_failures_infinite`: for `n = 1`
  the monoid is J-trivial, every two-sided cell contains exactly one left cell, and for every
  bijection the formula fails at infinitely many non-empty 2-cores (the staircases).

Green's-relation set-up (principal two-sided / left ideals, counting J- and L-classes) follows
the accepted solution of the finite analogue 00000003843 (orionsheep, GPL-3.0), here stated for an
arbitrary monoid.
-/

namespace C3848

open CoxeterSystem

/-! ## The affine 0-Hecke monoid of type `A_n^{(1)}` -/

/-- Coxeter matrix of type `A_n^{(1)}` on the nodes `Fin (n+1)` (cyclic Dynkin diagram).
For `n = 1` the two nodes are joined by an edge labelled `∞`, encoded by `0` as in Mathlib. -/
def affineAMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℕ := fun i j =>
  if i = j then 1
  else if n = 1 then 0
  else if (j : ℕ) = ((i : ℕ) + 1) % (n + 1) ∨ (i : ℕ) = ((j : ℕ) + 1) % (n + 1) then 3 else 2

/-- The Coxeter matrix of the affine Weyl group of type `A_n^{(1)}`. -/
def affineA (n : ℕ) : CoxeterMatrix (Fin (n + 1)) where
  M := affineAMatrix n
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, affineAMatrix]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h, or_comm]
  diagonal i := by simp [affineAMatrix]
  off_diagonal i j h := by
    simp only [affineAMatrix, h, if_false]
    split_ifs <;> omega

/-- Defining relations of the 0-Hecke monoid of a Coxeter matrix `M`: the absorption relation
`π_s π_s = π_s`, and for `s ≠ t` with `m_st < ∞` the braid relation `π_s π_t π_s ⋯ = π_t π_s π_t ⋯`
(`m_st` factors on each side). -/
inductive ZeroHeckeRel {B : Type*} (M : CoxeterMatrix B) : FreeMonoid B → FreeMonoid B → Prop
  | idem (s : B) : ZeroHeckeRel M (FreeMonoid.of s * FreeMonoid.of s) (FreeMonoid.of s)
  | braid (s t : B) (hst : s ≠ t) (hm : M s t ≠ 0) :
      ZeroHeckeRel M (FreeMonoid.ofList (alternatingWord s t (M s t)))
        (FreeMonoid.ofList (alternatingWord t s (M s t)))

/-- The 0-Hecke monoid of a Coxeter matrix, as a presented monoid. -/
abbrev ZeroHecke {B : Type*} (M : CoxeterMatrix B) := PresentedMonoid (ZeroHeckeRel M)

/-- The affine 0-Hecke monoid of type `A_n^{(1)}`. -/
abbrev AffineZeroHecke (n : ℕ) := ZeroHecke (affineA n)

/-! ## Green's relations, two-sided cells and left cells (any monoid) -/

section Green
variable {M : Type*} [Monoid M]

/-- Two-sided (Green `J`) equivalence: `MxM = MyM`. -/
def JRel (x y : M) : Prop := (∃ a b, x = a * y * b) ∧ ∃ a b, y = a * x * b

/-- Left (Green `L`) equivalence: `Mx = My`. -/
def LRel (x y : M) : Prop := (∃ a, x = a * y) ∧ ∃ a, y = a * x

theorem jRel_equivalence : Equivalence (JRel (M := M)) where
  refl x := ⟨⟨1, 1, by simp⟩, 1, 1, by simp⟩
  symm h := ⟨h.2, h.1⟩
  trans := by
    rintro x y z ⟨⟨a, b, hx⟩, c, d, hy⟩ ⟨⟨e, f, hy'⟩, g, h, hz⟩
    exact ⟨⟨a * e, f * b, by rw [hx, hy']; simp [mul_assoc]⟩, g * c, d * h,
      by rw [hz, hy]; simp [mul_assoc]⟩

theorem lRel_equivalence : Equivalence (LRel (M := M)) where
  refl x := ⟨⟨1, by simp⟩, 1, by simp⟩
  symm h := ⟨h.2, h.1⟩
  trans := by
    rintro x y z ⟨⟨a, hx⟩, c, hy⟩ ⟨⟨e, hy'⟩, g, hz⟩
    exact ⟨⟨a * e, by rw [hx, hy']; simp [mul_assoc]⟩, g * c, by rw [hz, hy]; simp [mul_assoc]⟩

/-- The two-sided cell (`J`-class) of `x`. -/
def jClass (x : M) : Set M := {y | JRel x y}

/-- The left cell (`L`-class) of `x`. -/
def lClass (x : M) : Set M := {y | LRel x y}

/-- The two-sided cells of `M`: its two-sided equivalence classes. -/
def TwoSidedCell (M : Type*) [Monoid M] := {C : Set M // ∃ x, C = jClass x}

/-- Number (in `ℕ∞`, so infinite counts are allowed) of left cells contained in `C`. -/
noncomputable def numLeftCells (C : Set M) : ℕ∞ :=
  {K : Set M | (∃ x, K = lClass x) ∧ K ⊆ C}.encard

theorem lClass_subset_jClass (x : M) : lClass x ⊆ jClass x := by
  rintro y ⟨⟨a, ha⟩, c, hc⟩
  exact ⟨⟨a, 1, by simpa using ha⟩, c, 1, by simpa using hc⟩

/-- Every two-sided cell contains at least one left cell. -/
theorem numLeftCells_ne_zero (C : TwoSidedCell M) : numLeftCells C.1 ≠ 0 := by
  obtain ⟨x, hx⟩ := C.2
  rw [numLeftCells, Ne, Set.encard_eq_zero, ← Ne, ← Set.nonempty_iff_ne_empty]
  exact ⟨lClass x, ⟨x, rfl⟩, hx ▸ lClass_subset_jClass x⟩

/-- In a J-trivial monoid every two-sided cell contains exactly one left cell. -/
theorem numLeftCells_of_jTrivial (htriv : ∀ x y : M, JRel x y → x = y) (C : TwoSidedCell M) :
    numLeftCells C.1 = 1 := by
  obtain ⟨x, hx⟩ := C.2
  have hJ : ∀ z, jClass z = {z} := fun z => by
    ext y
    refine ⟨fun h => (htriv z y h).symm, fun h => ?_⟩
    rw [Set.mem_singleton_iff] at h; subst h; exact jRel_equivalence.refl y
  have hL : ∀ z, lClass z = {z} := fun z => by
    ext y
    refine ⟨fun h => (htriv z y (lClass_subset_jClass z h)).symm, fun h => ?_⟩
    rw [Set.mem_singleton_iff] at h; subst h; exact lRel_equivalence.refl y
  rw [numLeftCells, hx, hJ, ← Set.encard_singleton ({x} : Set M)]
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨y, rfl⟩, hy⟩
    rw [hL] at hy ⊢
    rw [Set.singleton_subset_iff.mp hy]
  · rintro rfl
    exact ⟨⟨x, (hL x).symm⟩, le_rfl⟩

end Green

/-! ## Partitions, hooks and cores -/

/-- Hook length of the cell `c = (i, j)` of `μ`: arm + leg + 1. -/
def hookLength (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (μ.rowLen c.1 - c.2) + (μ.colLen c.2 - c.1) - 1

/-- `μ` is a `t`-core: none of its hook lengths is divisible by `t`. -/
def IsCore (t : ℕ) (μ : YoungDiagram) : Prop := ∀ c ∈ μ, ¬ t ∣ hookLength μ c

/-- The `t`-core partitions. -/
def Core (t : ℕ) := {μ : YoungDiagram // IsCore t μ}

/-- Number of distinct parts (distinct positive row lengths). -/
def distinctParts (μ : YoungDiagram) : ℕ := μ.rowLens.toFinset.card

theorem isCore_bot (t : ℕ) : IsCore t ⊥ := fun c hc => absurd hc (YoungDiagram.notMem_bot c)

theorem distinctParts_bot : distinctParts ⊥ = 0 := by
  have h : (⊥ : YoungDiagram).colLen 0 = 0 := by
    by_contra h
    exact YoungDiagram.notMem_bot (0, 0)
      (YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero h))
  simp [distinctParts, YoungDiagram.rowLens, h]

/-! ## The conjecture -/

/-- The conjecture for type `A_n^{(1)}`; `strip` is the operation "remove all `(n+1)`-hooks". -/
def CellCoreDictionary (n : ℕ) (strip : YoungDiagram → YoungDiagram) : Prop :=
  ∃ e : TwoSidedCell (AffineZeroHecke n) ≃ Core (n + 1),
    ∀ C, numLeftCells C.1 = (distinctParts (strip (e C).1) : ℕ∞)

/-- **Main theorem.** For every `n` the conjecture fails, for any hook-removal operation that
leaves the empty partition (which has no hooks) unchanged. -/
theorem not_cellCoreDictionary (n : ℕ) (strip : YoungDiagram → YoungDiagram)
    (hstrip : strip ⊥ = ⊥) : ¬ CellCoreDictionary n strip := by
  rintro ⟨e, he⟩
  obtain ⟨C, hC⟩ := e.surjective ⟨⊥, isCore_bot (n + 1)⟩
  have h := he C
  rw [hC] at h
  change numLeftCells C.1 = ((distinctParts (strip ⊥) : ℕ) : ℕ∞) at h
  rw [hstrip, distinctParts_bot, Nat.cast_zero] at h
  exact numLeftCells_ne_zero C h

/-! ## Type `A_1^{(1)}`: J-triviality and infinitely many non-empty failures -/

/-- Action of `π_i` on alternating words: prepend `i` unless the word already starts with `i`. -/
def act (i : Fin 2) (w : List (Fin 2)) : List (Fin 2) := if w.head? = some i then w else i :: w

/-- `act i` as an element of the monoid of self-maps (composition). -/
def actEnd (i : Fin 2) : Function.End (List (Fin 2)) := act i

/-- The action of the monoid on words (its relations hold for `act`). -/
def actHom : AffineZeroHecke 1 →* Function.End (List (Fin 2)) :=
  PresentedMonoid.lift actEnd (by
    intro a b h
    cases h with
    | idem s =>
      rw [map_mul, FreeMonoid.lift_eval_of, Function.End.mul_def]
      funext w
      simp only [Function.comp_apply, actEnd, act]
      split_ifs <;> simp_all
    | braid s t hst hm =>
      exfalso
      exact hm (by simp [affineA, affineAMatrix, hst]))

/-- The alternating normal form of an element. -/
def eval (m : AffineZeroHecke 1) : List (Fin 2) := actHom m []

theorem actHom_one_apply (w : List (Fin 2)) : actHom 1 w = w := by rw [map_one]; rfl

theorem hecke_induction {P : AffineZeroHecke 1 → Prop} (h1 : P 1)
    (hmul : ∀ i m, P m → P (PresentedMonoid.of _ i * m)) : ∀ m, P m := by
  intro m
  induction m using PresentedMonoid.inductionOn with
  | h a =>
    induction a using FreeMonoid.inductionOn' with
    | one => simpa using h1
    | of_mul x xs ih => rw [map_mul]; exact hmul x _ ih

theorem actHom_of_mul (i : Fin 2) (m : AffineZeroHecke 1) (w : List (Fin 2)) :
    actHom (PresentedMonoid.of _ i * m) w = act i (actHom m w) := by
  rw [map_mul, Function.End.mul_def]; rfl

theorem eval_mul (p q : AffineZeroHecke 1) : eval (p * q) = actHom p (eval q) := by
  rw [eval, map_mul, Function.End.mul_def]; rfl

/-- Product of generators along a word. -/
def sec (w : List (Fin 2)) : AffineZeroHecke 1 := (w.map (PresentedMonoid.of _)).prod

theorem of_mul_of (i : Fin 2) :
    PresentedMonoid.of (ZeroHeckeRel (affineA 1)) i * PresentedMonoid.of _ i =
      PresentedMonoid.of _ i := by
  have := PresentedMonoid.mk_eq_mk_of_rel (ZeroHeckeRel.idem (M := affineA 1) i)
  rw [map_mul] at this; exact this

theorem sec_act (i : Fin 2) (w : List (Fin 2)) : sec (act i w) = PresentedMonoid.of _ i * sec w := by
  unfold act
  split_ifs with h
  · obtain ⟨t, rfl⟩ : ∃ t, w = i :: t := by
      cases w with
      | nil => simp at h
      | cons a t => simp at h; exact ⟨t, by rw [h]⟩
    simp [sec, ← mul_assoc, of_mul_of]
  · simp [sec]

theorem sec_eval : ∀ m, sec (eval m) = m := by
  refine hecke_induction (by simp [eval, sec, actHom_one_apply]) ?_
  intro i m ih
  rw [eval, actHom_of_mul, sec_act, ← eval, ih]

theorem eval_injective : Function.Injective eval :=
  Function.LeftInverse.injective sec_eval

theorem act_length (i : Fin 2) (w : List (Fin 2)) :
    w.length ≤ (act i w).length ∧ ((act i w).length = w.length → act i w = w) := by
  unfold act; split_ifs <;> simp

theorem actHom_length : ∀ (a : AffineZeroHecke 1) (w : List (Fin 2)),
    w.length ≤ (actHom a w).length ∧ ((actHom a w).length = w.length → actHom a w = w) := by
  refine hecke_induction (by simp [actHom_one_apply]) ?_
  intro i m ih w
  rw [actHom_of_mul]
  obtain ⟨h1, h2⟩ := ih w
  obtain ⟨h3, h4⟩ := act_length i (actHom m w)
  refine ⟨h1.trans h3, fun h => ?_⟩
  have e1 : actHom m w = w := h2 (by omega)
  rw [h4 (by omega), e1]

theorem act_prefix (i : Fin 2) {u v : List (Fin 2)} (h : u <+: v) : act i u <+: act i v := by
  cases u with
  | nil =>
    unfold act
    cases v with
    | nil => simp
    | cons b t => split_ifs with hb <;> simp_all
  | cons a t =>
    obtain ⟨r, rfl⟩ := h
    unfold act
    by_cases ha : a = i <;> simp [ha]

theorem eval_prefix : ∀ (m : AffineZeroHecke 1) (w : List (Fin 2)), eval m <+: actHom m w := by
  refine hecke_induction (fun w => by simp [eval, actHom_one_apply]) ?_
  intro i m ih w
  rw [eval, actHom_of_mul, actHom_of_mul]
  exact act_prefix i (ih w)

/-- The affine 0-Hecke monoid of type `A_1^{(1)}` is J-trivial. -/
theorem affineA1_jTrivial (x y : AffineZeroHecke 1) (h : JRel x y) : x = y := by
  obtain ⟨⟨a, b, rfl⟩, c, d, hy⟩ := h
  have l1 : ∀ p q : AffineZeroHecke 1, (eval q).length ≤ (eval (p * q)).length := fun p q => by
    rw [eval_mul]; exact (actHom_length p (eval q)).1
  have l2 : ∀ p q : AffineZeroHecke 1, (eval p).length ≤ (eval (p * q)).length := fun p q => by
    rw [eval_mul]; exact (eval_prefix p (eval q)).length_le
  have h1 := l1 a y
  have h2 := l2 (a * y) b
  have h3 := l1 c (a * y * b)
  have h4 := l2 (c * (a * y * b)) d
  rw [← hy] at h4
  have hay : a * y = y := by
    apply eval_injective
    rw [eval_mul]
    exact (actHom_length a (eval y)).2 (by rw [← eval_mul]; omega)
  rw [hay] at h2 h3 h4 ⊢
  apply eval_injective
  have hp := eval_prefix y (eval b)
  rw [← eval_mul] at hp
  exact (hp.eq_of_length (by omega)).symm

/-- For `A_1^{(1)}` every two-sided cell contains exactly one left cell. -/
theorem numLeftCells_affineA1 (C : TwoSidedCell (AffineZeroHecke 1)) : numLeftCells C.1 = 1 :=
  numLeftCells_of_jTrivial affineA1_jTrivial C

/-- The staircase partition `(k, k-1, ..., 1)`. -/
def staircase (k : ℕ) : YoungDiagram where
  cells := (Finset.range k ×ˢ Finset.range k).filter (fun c => c.1 + c.2 < k)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at ha ⊢
    have := Prod.mk_le_mk.mp hba
    omega

theorem mem_staircase {k i j : ℕ} : (i, j) ∈ staircase k ↔ i + j < k := by
  simp only [← YoungDiagram.mem_cells, staircase, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  omega

theorem rowLen_staircase (k i : ℕ) : (staircase k).rowLen i = k - i :=
  eq_of_forall_lt_iff fun j => by rw [← YoungDiagram.mem_iff_lt_rowLen, mem_staircase]; omega

theorem colLen_staircase (k j : ℕ) : (staircase k).colLen j = k - j :=
  eq_of_forall_lt_iff fun i => by rw [← YoungDiagram.mem_iff_lt_colLen, mem_staircase]; omega

/-- All hook lengths of a staircase are odd, so it is a 2-core. -/
theorem staircase_isCore (k : ℕ) : IsCore 2 (staircase k) := by
  rintro ⟨i, j⟩ hc
  rw [mem_staircase] at hc
  simp only [hookLength, rowLen_staircase, colLen_staircase]
  omega

theorem distinctParts_staircase (k : ℕ) : distinctParts (staircase k) = k := by
  have hf : (staircase k).rowLen = fun i => k - i := funext (rowLen_staircase k)
  simp only [distinctParts, YoungDiagram.rowLens, colLen_staircase, hf, Nat.sub_zero]
  rw [List.toFinset_card_of_nodup, List.length_map, List.length_range]
  exact List.Nodup.map_on (fun x hx y hy h => by simp at hx hy; omega) List.nodup_range

/-- **Non-degenerate refutation for `A_1^{(1)}`.** For any hook-removal operation fixing
2-cores and for *every* bijection between two-sided cells and 2-cores, the left-cell formula
fails at infinitely many (non-empty) 2-cores: at every staircase with at least 2 parts. -/
theorem affineA1_failures_infinite (strip : YoungDiagram → YoungDiagram)
    (hstrip : ∀ μ, IsCore 2 μ → strip μ = μ)
    (e : TwoSidedCell (AffineZeroHecke 1) ≃ Core 2) :
    {κ : Core 2 | numLeftCells (e.symm κ).1 ≠ (distinctParts (strip κ.1) : ℕ∞)}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (⟨staircase (k + 2), staircase_isCore _⟩ : Core 2)) ?_ ?_
  · intro k l h
    have := congrArg (fun κ : Core 2 => distinctParts κ.1) h
    simp only [distinctParts_staircase] at this
    omega
  · intro k
    show numLeftCells (e.symm _).1 ≠ ((distinctParts (strip (staircase (k + 2))) : ℕ) : ℕ∞)
    rw [numLeftCells_affineA1, hstrip _ (staircase_isCore _), distinctParts_staircase]
    exact_mod_cast (show (1 : ℕ) ≠ k + 2 by omega)

theorem not_cellCoreDictionary_one (strip : YoungDiagram → YoungDiagram)
    (hstrip : ∀ μ, IsCore 2 μ → strip μ = μ) : ¬ CellCoreDictionary 1 strip := by
  rintro ⟨e, he⟩
  obtain ⟨κ, hκ⟩ := (affineA1_failures_infinite strip hstrip e).nonempty
  exact hκ (by simpa using he (e.symm κ))

end C3848
