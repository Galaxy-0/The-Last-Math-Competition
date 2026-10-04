import Conjecture7718.Substitution
import Mathlib.Data.List.OfFn
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Order.DenselyOrdered

/-!
Finite geometric realization by three colored unit intervals. The colors are
actual letters of the substituted word; tile interiors are disjoint and tile
supports cover exactly the inflated interval.
-/

noncomputable section
open Set

namespace Conjecture7718

/-- The three prototiles have the same geometric support and distinct letter colors. -/
def prototileSupport (_a : Letter) : Set ℝ := Icc 0 1

def expandedPrototileSupport (q : ℝ) (a : Letter) : Set ℝ :=
  (fun x : ℝ => q * x) '' prototileSupport a

def wordTileColor (w : List Letter) (i : Fin w.length) : Letter := w.get i

theorem wordTileColors_eq (w : List Letter) : List.ofFn (wordTileColor w) = w :=
  List.ofFn_get w

theorem wordTileColor_count (w : List Letter) (a : Letter) :
    (List.ofFn (wordTileColor w)).count a = w.count a := by
  rw [wordTileColors_eq]

/-- The geometric patch has exactly the incidence-matrix number of tiles of each color. -/
theorem substitution_tileColor_count (m : ℕ) (a b : Letter) :
    (List.ofFn (wordTileColor (substitution m b))).count a = familyCounts m a b := by
  rw [wordTileColor_count]
  exact congrFun (congrFun (incidenceCounts_substitution m) a) b

def wordTileSupport (w : List Letter) (i : Fin w.length) : Set ℝ :=
  Icc (i.val : ℝ) ((i.val : ℝ) + 1)

def wordTileInterior (w : List Letter) (i : Fin w.length) : Set ℝ :=
  interior (wordTileSupport w i)

theorem wordTileInterior_eq (w : List Letter) (i : Fin w.length) :
    wordTileInterior w i = Ioo (i.val : ℝ) ((i.val : ℝ) + 1) := by
  exact interior_Icc

/-- Each tile is a translate of the prototile with its actual word color. -/
theorem wordTileSupport_translate (w : List Letter) (i : Fin w.length) :
    wordTileSupport w i =
      (fun x : ℝ => (i.val : ℝ) + x) '' prototileSupport (wordTileColor w i) := by
  ext x
  constructor
  · intro hx
    change (i.val : ℝ) ≤ x ∧ x ≤ (i.val : ℝ) + 1 at hx
    refine ⟨x - (i.val : ℝ), ?_, by ring⟩
    change 0 ≤ x - (i.val : ℝ) ∧ x - (i.val : ℝ) ≤ 1
    constructor <;> linarith
  · rintro ⟨y, hy, rfl⟩
    change 0 ≤ y ∧ y ≤ 1 at hy
    change (i.val : ℝ) ≤ (i.val : ℝ) + y ∧
      (i.val : ℝ) + y ≤ (i.val : ℝ) + 1
    constructor <;> linarith

/-- Consecutive closed unit intervals cover the whole interval, including its right endpoint. -/
theorem union_unit_intervals (L : ℕ) (hL : 0 < L) :
    (⋃ i : Fin L, Icc (i.val : ℝ) ((i.val : ℝ) + 1)) = Icc (0 : ℝ) (L : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have hiL : (i.val : ℝ) + 1 ≤ (L : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    exact ⟨hi0.trans hi.1, hi.2.trans hiL⟩
  · intro hx
    by_cases hlast : x = (L : ℝ)
    · subst x
      have hindex : L - 1 < L := Nat.sub_lt hL (by norm_num)
      have hend : ((L - 1 : ℕ) : ℝ) + 1 = (L : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hL
      refine mem_iUnion.mpr ⟨⟨L - 1, hindex⟩, ?_⟩
      change ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) ∧
        (L : ℝ) ≤ ((L - 1 : ℕ) : ℝ) + 1
      constructor <;> linarith
    · have hxL : x < (L : ℝ) := lt_of_le_of_ne hx.2 hlast
      have hfloor : Nat.floor x < L := (Nat.floor_lt hx.1).mpr hxL
      exact mem_iUnion.mpr ⟨⟨Nat.floor x, hfloor⟩,
        Nat.floor_le hx.1, (Nat.lt_floor_add_one x).le⟩

theorem union_wordTileSupport (w : List Letter) (hw : 0 < w.length) :
    (⋃ i : Fin w.length, wordTileSupport w i) = Icc (0 : ℝ) (w.length : ℝ) :=
  union_unit_intervals w.length hw

theorem pairwise_disjoint_wordTileInterior (w : List Letter) :
    Pairwise (fun i j : Fin w.length => Disjoint (wordTileInterior w i) (wordTileInterior w j)) := by
  intro i j hij
  rw [wordTileInterior_eq, wordTileInterior_eq, Set.disjoint_left]
  intro x hxi hxj
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstep : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    linarith [hxi.2, hxj.1]
  · have hstep : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hgt
    linarith [hxj.2, hxi.1]

theorem expandedPrototileSupport_eq (q : ℝ) (hq : 0 < q) (a : Letter) :
    expandedPrototileSupport q a = Icc 0 q := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 ≤ y ∧ y ≤ 1 at hy
    exact ⟨mul_nonneg hq.le hy.1, by simpa using mul_le_mul_of_nonneg_left hy.2 hq.le⟩
  · intro hx
    refine ⟨x / q, ?_, ?_⟩
    · change 0 ≤ x / q ∧ x / q ≤ 1
      exact ⟨div_nonneg hx.1 hq.le, (div_le_one hq).mpr hx.2⟩
    · exact mul_div_cancel₀ x hq.ne'

/-- A geometric substitution by colored unit intervals, with actual coverage,
interior disjointness, and the correct translated color supports. -/
def UnitIntervalSubstitution (σ : Substitution) (q : ℝ) : Prop :=
  1 < q ∧ ∀ a : Letter,
    (⋃ i : Fin (σ a).length, wordTileSupport (σ a) i) = expandedPrototileSupport q a ∧
    Pairwise (fun i j : Fin (σ a).length =>
      Disjoint (wordTileInterior (σ a) i) (wordTileInterior (σ a) j)) ∧
    ∀ i : Fin (σ a).length, wordTileSupport (σ a) i =
      (fun x : ℝ => (i.val : ℝ) + x) '' prototileSupport (wordTileColor (σ a) i)

theorem substitution_unitInterval (m : ℕ) :
    UnitIntervalSubstitution (substitution m) (3 * (m : ℝ) + 3) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  refine ⟨by linarith, ?_⟩
  intro a
  refine ⟨?_, pairwise_disjoint_wordTileInterior _, wordTileSupport_translate _⟩
  rw [union_wordTileSupport _ (by rw [substitution_length]; omega),
    expandedPrototileSupport_eq _ (by linarith), substitution_length]
  norm_num

/-- Every member with m≥1 is both primitive as a word substitution and a genuine
expanding substitution of three colored unit intervals. -/
theorem substitution_primitive_unitInterval (m : ℕ) (hm : 1 ≤ m) :
    PrimitiveSubstitution (substitution m) ∧
      UnitIntervalSubstitution (substitution m) (3 * (m : ℝ) + 3) :=
  ⟨substitution_primitive m hm, substitution_unitInterval m⟩

end Conjecture7718
