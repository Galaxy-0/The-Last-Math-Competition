/-
Problem 00000007701. Conjecture (verbatim):
"Definition: For an irrational rotation T_alpha on the circle, a set B is a bounded remainder set (BRS) if the Birkhoff sums of its indicator minus n|B| are uniformly bounded; higher-dimensional BRS are built by the cut-and-project construction with a window W in R^m and lattice Gamma. Conjecture: W is a d-dimensional BRS if and only if W is a polytope defined by integer-coefficient half-spaces in R^m; and for d=1, m=2 the volume spectrum of W is a discrete set with all values in (1/2)Z. (polytopal characterization of bounded remainder sets)"

The primary reading has physical space R and internal space R^2.
The explicit rank-three parametrization, exact physical counting on all
real intervals, IsPhysicalBRS membership, literal volume-clause negation,
and density of areas in that class are formalized below. The only human
bridge needed for the literal disproof is lattice admissibility: the image
of Z^3 is a discrete full-rank lattice of covolume 6, its physical
projection is injective, and its internal projection is dense in R^2.
These facts for sqrt(2), sqrt(3) are proved in the report.
Circle and torus statements are retained as supporting/secondary results.
-/
import Mathlib

/-! # Irrational-volume BRS counterexamples to TLMC 00000007701
The conjecture and reading are recorded verbatim in the opening documentation. -/

set_option autoImplicit false

namespace BRSVolume
open scoped BigOperators
open MeasureTheory

/- The transfer-function definition and the next four lemmas are adapted from
trureturing (Apache-2.0), D5/S1/Phase/HeckeOstrowskiCoboundary.lean,
https://github.com/the-omega-institute/trureturing,
commit 1be30b25c4fe6cd46397090ca09b5696eb62ea78.
The upstream Apache-2.0 license is included as LICENSE.trureturing.
The namespace is changed and all internal headers/imports are removed. -/
noncomputable def transferFunction (α : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range q, Int.fract (x - (j + 1) * α)

/-- Fractional-part subtraction has exactly one carry, detected by the order
of the two fractional parts. -/
theorem fract_sub_eq_ite (x t : ℝ) :
    Int.fract (x - t) =
      if Int.fract x < Int.fract t then
        Int.fract x + 1 - Int.fract t
      else
        Int.fract x - Int.fract t := by
  split_ifs with h
  · apply Int.fract_eq_iff.mpr
    refine ⟨?_, ?_, ⌊x⌋ - ⌊t⌋ - 1, ?_⟩
    · linarith [Int.fract_nonneg x, Int.fract_lt_one t]
    · linarith
    · push_cast
      linarith [Int.fract_sub_self x, Int.fract_sub_self t]
  · apply Int.fract_eq_iff.mpr
    refine ⟨?_, ?_, ⌊x⌋ - ⌊t⌋, ?_⟩
    · linarith [le_of_not_gt h]
    · linarith [Int.fract_lt_one x, Int.fract_nonneg t]
    · push_cast
      linarith [Int.fract_sub_self x, Int.fract_sub_self t]

private theorem transferFunction_succ (α : ℝ) (q : ℕ) (x : ℝ) :
    transferFunction α (q + 1) x =
      transferFunction α q x + Int.fract (x - (q + 1) * α) := by
  simp [transferFunction, Finset.sum_range_succ]

private theorem transferFunction_difference (α : ℝ) (q : ℕ) (x : ℝ) :
    transferFunction α q x - transferFunction α q (x + α) =
      Int.fract (x - q * α) - Int.fract x := by
  induction q with
  | zero => simp [transferFunction]
  | succ q ih =>
      rw [transferFunction_succ, transferFunction_succ]
      push_cast
      rw [show x + α - ((q : ℝ) + 1) * α = x - q * α by ring]
      linarith [ih]

/-- The centered indicator of `[0, {qα})` is a coboundary for rotation by
`α`, with an explicit finite transfer function. -/
theorem hecke_ostrowski_coboundary (α : ℝ) (q : ℕ) (x : ℝ) :
    (if Int.fract x < Int.fract (q * α) then 1 else 0) -
        Int.fract (q * α) =
      transferFunction α q x - transferFunction α q (x + α) := by
  rw [transferFunction_difference, fract_sub_eq_ite]
  split_ifs <;> ring

/-- Uniform BRS definition on representatives of the circle R/Z. -/
def IsBRS (α : ℝ) (B : Set ℝ) : Prop :=
  MeasurableSet B ∧ B ⊆ Set.Ico 0 1 ∧
    ∃ C : ℝ, ∀ (x : ℝ) (N : ℕ),
      |(∑ n ∈ Finset.range N,
          B.indicator (fun _ => (1 : ℝ)) (Int.fract (x + n * α))) -
        N * (volume B).toReal| ≤ C

noncomputable def interval (α : ℝ) (q : ℕ) : Set ℝ :=
  Set.Ico 0 (Int.fract (q * α))

theorem interval_volume (α : ℝ) (q : ℕ) :
    (volume (interval α q)).toReal = Int.fract (q * α) := by
  simp [interval, Real.volume_Ico, Int.fract_nonneg]

theorem interval_indicator (α x : ℝ) (q : ℕ) :
    (interval α q).indicator (fun _ => (1 : ℝ)) (Int.fract x) =
      if Int.fract x < Int.fract (q * α) then 1 else 0 := by
  classical
  simp [interval, Set.indicator, Set.mem_Ico, Int.fract_nonneg]

theorem transfer_bounds (α x : ℝ) (q : ℕ) :
    0 ≤ transferFunction α q x ∧ transferFunction α q x ≤ q := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => Int.fract_nonneg _)
  · calc
      transferFunction α q x ≤ ∑ _j ∈ Finset.range q, (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => (Int.fract_lt_one _).le)
      _ = q := by simp

theorem interval_sum_telescope (α x : ℝ) (q N : ℕ) :
    (∑ n ∈ Finset.range N,
        (interval α q).indicator (fun _ => (1 : ℝ)) (Int.fract (x + n * α))) -
      N * Int.fract (q * α) =
        transferFunction α q x - transferFunction α q (x + N * α) := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, interval_indicator]
      have hc := hecke_ostrowski_coboundary α q (x + N * α)
      have hs : x + ((N + 1 : ℕ) : ℝ) * α = (x + N * α) + α := by
        push_cast
        ring
      rw [hs]
      push_cast
      linarith

theorem interval_isBRS (α : ℝ) (q : ℕ) : IsBRS α (interval α q) := by
  refine ⟨measurableSet_Ico, ?_, (q : ℝ), ?_⟩
  · intro x hx
    exact ⟨hx.1, hx.2.trans (Int.fract_lt_one _)⟩
  · intro x N
    rw [interval_volume, interval_sum_telescope, abs_le]
    have h₁ := transfer_bounds α x q
    have h₂ := transfer_bounds α (x + N * α) q
    constructor <;> linarith

theorem fract_irrational {t : ℝ} (ht : Irrational t) : Irrational (Int.fract t) := by
  simpa only [Int.fract] using ht.sub_intCast ⌊t⌋

theorem irrational_not_half_integer {t : ℝ} (ht : Irrational t) :
    ¬ ∃ k : ℤ, t = (k : ℝ) / 2 := by
  rintro ⟨k, hk⟩
  apply ht.ne_rat ((k : ℚ) / 2)
  simpa using hk

/-- The positive-integer family: every positive multiple gives irrational volume. -/
theorem interval_counterexamples (α : ℝ) (hα : Irrational α) (q : ℕ) (hq : 1 ≤ q) :
    IsBRS α (interval α q) ∧
    (volume (interval α q)).toReal = Int.fract (q * α) ∧
    ¬ ∃ k : ℤ, (volume (interval α q)).toReal = (k : ℝ) / 2 := by
  refine ⟨interval_isBRS α q, interval_volume α q, ?_⟩
  rw [interval_volume]
  exact irrational_not_half_integer (fract_irrational (hα.natCast_mul (by omega)))

/-- The volume clause is false for every irrational circle rotation. -/
theorem circle_volume_clause_false (α : ℝ) (hα : Irrational α) :
    ¬ (∀ B : Set ℝ, IsBRS α B → ∃ k : ℤ, (volume B).toReal = (k : ℝ) / 2) := by
  intro h
  exact (interval_counterexamples α hα 1 (by omega)).2.2
    (h (interval α 1) (interval_isBRS α 1))

/-- Supporting torus-action predicate, with product Lebesgue measure. -/
def IsBRS₂ (α β : ℝ) (W : Set (ℝ × ℝ)) : Prop :=
  MeasurableSet W ∧ W ⊆ (Set.Ico 0 1 ×ˢ Set.Ico 0 1) ∧
    ∃ C : ℝ, ∀ (x : ℝ × ℝ) (N : ℕ),
      |(∑ n ∈ Finset.range N, W.indicator (fun _ => (1 : ℝ))
          (Int.fract (x.1 + n * α), Int.fract (x.2 + n * β))) -
        N * (volume W).toReal| ≤ C

noncomputable def rectangle (α : ℝ) (q : ℕ) : Set (ℝ × ℝ) :=
  interval α q ×ˢ Set.Ico 0 1

theorem rectangle_volume (α : ℝ) (q : ℕ) :
    (volume (rectangle α q)).toReal = Int.fract (q * α) := by
  rw [rectangle, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    ENNReal.toReal_mul, interval_volume]
  simp [Real.volume_Ico]

theorem rectangle_indicator (α u v : ℝ) (q : ℕ) :
    (rectangle α q).indicator (fun _ => (1 : ℝ)) (Int.fract u, Int.fract v) =
      (interval α q).indicator (fun _ => (1 : ℝ)) (Int.fract u) := by
  classical
  simp [rectangle, Set.indicator, Set.mem_prod, Set.mem_Ico,
    Int.fract_nonneg, Int.fract_lt_one]

theorem rectangle_isBRS (α β : ℝ) (q : ℕ) : IsBRS₂ α β (rectangle α q) := by
  refine ⟨measurableSet_Ico.prod measurableSet_Ico, ?_, (q : ℝ), ?_⟩
  · intro x hx
    exact ⟨⟨hx.1.1, hx.1.2.trans (Int.fract_lt_one _)⟩, hx.2⟩
  · intro x N
    simp_rw [rectangle_indicator]
    rw [rectangle_volume, interval_sum_telescope, abs_le]
    have h₁ := transfer_bounds α x.1 q
    have h₂ := transfer_bounds α (x.1 + N * α) q
    constructor <;> linarith

theorem torus_volume_clause_false (α β : ℝ) (hα : Irrational α) :
    ¬ (∀ W : Set (ℝ × ℝ), IsBRS₂ α β W →
      ∃ k : ℤ, (volume W).toReal = (k : ℝ) / 2) := by
  intro h
  obtain ⟨k, hk⟩ := h (rectangle α 1) (rectangle_isBRS α β 1)
  rw [rectangle_volume] at hk
  exact irrational_not_half_integer (fract_irrational (by simpa using hα)) ⟨k, hk⟩

/-- A conjunction containing the volume clause fails, regardless of its other clause. -/
theorem circle_conjunction_false (α : ℝ) (hα : Irrational α) (P : Prop) :
    ¬ (P ∧ (∀ B : Set ℝ, IsBRS α B →
      ∃ k : ℤ, (volume B).toReal = (k : ℝ) / 2)) := by
  exact fun h => circle_volume_clause_false α hα h.2

/-- Every open subinterval of (0,1) contains the volume of one of the
explicit BRS intervals. This is an ordinary real-interval density statement. -/
theorem interval_volumes_dense (α : ℝ) (hα : Irrational α)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ q : ℕ, 1 ≤ q ∧ a < (volume (interval α q)).toReal ∧
      (volume (interval α q)).toReal < b := by
  have hz : DenseRange (fun z : ℤ => z • (α : AddCircle (1 : ℝ))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hα)
  have hn : DenseRange (fun n : ℕ => n • (α : AddCircle (1 : ℝ))) :=
    denseRange_zsmul_iff_nsmul.mp hz
  have hopen : IsOpen (((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ioo a b) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hne : (((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ioo a b).Nonempty :=
    (Set.nonempty_Ioo.mpr hab).image _
  obtain ⟨q, t, ht, heq⟩ := hn.exists_mem_open hopen hne
  have hfract : Int.fract (q * α) = t := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (a := (0 : ℝ)) (p := (1 : ℝ))
      (by simpa using And.intro (Int.fract_nonneg (q * α)) (Int.fract_lt_one (q * α)))
      (by constructor <;> linarith [ht.1, ht.2])).mp
    rw [AddCircle.coe_fract, ← nsmul_eq_mul, AddCircle.coe_nsmul]
    exact heq.symm
  refine ⟨q, ?_, ?_, ?_⟩
  · by_contra hq
    have : q = 0 := by omega
    subst q
    simp only [Nat.cast_zero, zero_mul, Int.fract_zero] at hfract
    linarith [ht.1]
  · rw [interval_volume, hfract]
    exact ht.1
  · rw [interval_volume, hfract]
    exact ht.2

/-! ## Physical R / internal R^2 counting reduction
The lattice image is parametrized by Z^3. The report verifies the lattice
and projection conditions for alpha = sqrt 2, beta = sqrt 3.
The following reduction uses actual physical and internal coordinates.
-/

abbrev Index₃ := ℤ × (ℤ × ℤ)
abbrev Ambient₃ := ℝ × (ℝ × ℝ)

noncomputable def gamma (α β : ℝ) (z : Index₃) : Ambient₃ :=
  (z.1 + α * z.2.1 + β * z.2.2,
    (z.2.1 - z.1 * α, z.2.2 - z.1 * β))

noncomputable def lattice (α β : ℝ) : Set Ambient₃ := Set.range (gamma α β)

def phys (p : Ambient₃) : ℝ := p.1

def internal (p : Ambient₃) : ℝ × ℝ := p.2

noncomputable def modelSet (α β : ℝ) (W : Set (ℝ × ℝ)) : Set ℝ :=
  phys '' {p ∈ lattice α β | internal p ∈ W}

noncomputable def covol (α β : ℝ) : ℝ := 1 + α ^ 2 + β ^ 2

/-- Standard physical counting definition, for all bounded half-open intervals.
`Set.ncard` is accompanied by an explicit finiteness requirement. -/
def IsPhysicalBRS (α β : ℝ) (W : Set (ℝ × ℝ)) : Prop :=
  MeasurableSet W ∧ ∃ C : ℝ, ∀ x y : ℝ, x ≤ y →
    (modelSet α β W ∩ Set.Ico x y).Finite ∧
    |((modelSet α β W ∩ Set.Ico x y).ncard : ℝ) -
      (volume W).toReal / covol α β * (y - x)| ≤ C

noncomputable def canonical (α β : ℝ) (k : ℤ) : Index₃ :=
  (k, -⌊-(k : ℝ) * α⌋, -⌊-(k : ℝ) * β⌋)

theorem canonical_internal (α β : ℝ) (k : ℤ) :
    internal (gamma α β (canonical α β k)) =
      (Int.fract (-(k : ℝ) * α), Int.fract (-(k : ℝ) * β)) := by
  simp only [internal, gamma, canonical, Int.fract, Int.cast_neg]
  congr 1 <;> ring

theorem canonical_phys (α β : ℝ) (k : ℤ) :
    phys (gamma α β (canonical α β k)) =
      covol α β * k + α * Int.fract (-(k : ℝ) * α) +
        β * Int.fract (-(k : ℝ) * β) := by
  simp only [phys, gamma, canonical, covol, Int.fract, Int.cast_neg]
  ring

private theorem internal_integer_unique (α : ℝ) (k m : ℤ)
    (h : (m : ℝ) - k * α ∈ Set.Ico (0 : ℝ) 1) :
    m = -⌊-(k : ℝ) * α⌋ := by
  have hf : ⌊-(k : ℝ) * α⌋ = -m := Int.floor_eq_iff.mpr (by
    simp only [Int.cast_neg]
    constructor <;> linarith [h.1, h.2])
  omega

theorem internal_unit_unique (α β : ℝ) (z : Index₃)
    (h : internal (gamma α β z) ∈ (Set.Ico 0 1 ×ˢ Set.Ico 0 1)) :
    z = canonical α β z.1 := by
  obtain ⟨k, m, n⟩ := z
  have hm := internal_integer_unique α k m h.1
  have hn := internal_integer_unique β k n h.2
  simp only [canonical, Prod.mk.injEq]
  exact ⟨trivial, hm, hn⟩

theorem covol_gt_displacement (α β : ℝ) : α + β < covol α β := by
  unfold covol
  nlinarith [sq_nonneg (α - 1 / 2), sq_nonneg (β - 1 / 2)]

theorem canonical_cell (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (k : ℤ) :
    phys (gamma α β (canonical α β k)) ∈
      Set.Ico (covol α β * k) (covol α β * ((k : ℝ) + 1)) := by
  rw [canonical_phys]
  have hu := Int.fract_nonneg (-(k : ℝ) * α)
  have hv := Int.fract_nonneg (-(k : ℝ) * β)
  have hu' := mul_le_mul_of_nonneg_left (Int.fract_lt_one (-(k : ℝ) * α)).le hα
  have hv' := mul_le_mul_of_nonneg_left (Int.fract_lt_one (-(k : ℝ) * β)).le hβ
  have hd := covol_gt_displacement α β
  constructor
  · nlinarith [mul_nonneg hα hu, mul_nonneg hβ hv]
  · nlinarith

/-- Exact physical-block reindexing: every accepted lattice parameter is
one canonical parameter, and its integer index lies in the indicated block. -/
theorem physical_block_reindex (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (W : Set (ℝ × ℝ)) (hW : W ⊆ (Set.Ico 0 1 ×ˢ Set.Ico 0 1))
    (K : ℤ) (N : ℕ) (z : Index₃) :
    (internal (gamma α β z) ∈ W ∧ phys (gamma α β z) ∈
      Set.Ico (covol α β * K) (covol α β * ((K : ℝ) + N))) ↔
    ∃ j ∈ Finset.range N, z = canonical α β (K + j) ∧
      internal (gamma α β (canonical α β (K + j))) ∈ W := by
  have hc : 0 < covol α β := by unfold covol; positivity
  constructor
  · rintro ⟨hzW, hzI⟩
    have hz := internal_unit_unique α β z (hW hzW)
    have hcell := canonical_cell α β hα hβ z.1
    rw [← hz] at hcell
    have hk : K ≤ z.1 := by
      by_contra hn
      have hi : (z.1 : ℝ) + 1 ≤ K := by exact_mod_cast (by omega : z.1 + 1 ≤ K)
      nlinarith [hzI.1, hcell.2]
    have hk' : z.1 < K + (N : ℤ) := by
      by_contra hn
      have hi : (K : ℝ) + N ≤ z.1 := by exact_mod_cast (by omega : K + (N : ℤ) ≤ z.1)
      nlinarith [hzI.2, hcell.1]
    let j : ℕ := (z.1 - K).toNat
    have hj : (j : ℤ) = z.1 - K := Int.toNat_of_nonneg (by omega)
    have hjN : j < N := by omega
    have heq : K + (j : ℤ) = z.1 := by omega
    refine ⟨j, Finset.mem_range.mpr hjN, ?_, ?_⟩
    · rw [heq]; exact hz
    · rw [heq, ← hz]; exact hzW
  · rintro ⟨j, hj, rfl, hmem⟩
    refine ⟨hmem, ?_⟩
    have hcell := canonical_cell α β hα hβ (K + j)
    have hjN := Finset.mem_range.mp hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hj1 : (j : ℝ) + 1 ≤ N := by exact_mod_cast (by omega : j + 1 ≤ N)
    push_cast at hcell
    constructor <;> nlinarith [hcell.1, hcell.2]

/-- Counts canonical parameters selected by the actual physical block.
The preceding equivalence supplies the bijection with all accepted parameters. -/
noncomputable def blockCount (α β : ℝ) (W : Set (ℝ × ℝ)) (K : ℤ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (fun (j : ℕ) =>
    internal (gamma α β (canonical α β (K + j))) ∈ W)).card

noncomputable def blockPoints (α β : ℝ) (W : Set (ℝ × ℝ)) (K : ℤ) (N : ℕ) : Finset ℝ := by
  classical
  exact ((Finset.range N).filter (fun (j : ℕ) =>
    internal (gamma α β (canonical α β (K + j))) ∈ W)).image
      (fun (j : ℕ) => phys (gamma α β (canonical α β (K + j))))

theorem canonical_phys_injective (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Function.Injective (fun k : ℤ => phys (gamma α β (canonical α β k))) := by
  intro k l heq
  have hk := canonical_cell α β hα hβ k
  have hl := canonical_cell α β hα hβ l
  have hc : 0 < covol α β := by unfold covol; positivity
  rcases lt_trichotomy k l with h | h | h
  · have hi : (k : ℝ) + 1 ≤ l := by exact_mod_cast (by omega : k + 1 ≤ l)
    exfalso
    nlinarith [hk.2, hl.1]
  · exact h
  · have hi : (l : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : l + 1 ≤ k)
    exfalso
    nlinarith [hl.2, hk.1]

theorem blockPoints_card (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (W : Set (ℝ × ℝ)) (K : ℤ) (N : ℕ) :
    (blockPoints α β W K N).card = blockCount α β W K N := by
  classical
  unfold blockPoints blockCount
  apply Finset.card_image_iff.mpr
  intro i hi j hj heq
  have hh := canonical_phys_injective α β hα hβ heq
  exact_mod_cast (by omega : (i : ℤ) = j)

theorem modelSet_block_eq (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (W : Set (ℝ × ℝ)) (hW : W ⊆ (Set.Ico 0 1 ×ˢ Set.Ico 0 1))
    (K : ℤ) (N : ℕ) :
    modelSet α β W ∩ Set.Ico (covol α β * K) (covol α β * ((K : ℝ) + N)) =
      (blockPoints α β W K N : Set ℝ) := by
  classical
  ext t
  constructor
  · rintro ⟨⟨p, ⟨⟨z, rfl⟩, hz⟩, rfl⟩, ht⟩
    obtain ⟨j, hj, heq, hmem⟩ := (physical_block_reindex α β hα hβ W hW K N z).mp ⟨hz, ht⟩
    subst z
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hmem⟩, rfl⟩
  · intro ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hj, hmem⟩ := Finset.mem_filter.mp hj
    have hb := (physical_block_reindex α β hα hβ W hW K N
      (canonical α β (K + j))).mpr ⟨j, hj, rfl, hmem⟩
    refine ⟨?_, hb.2⟩
    exact ⟨gamma α β (canonical α β (K + j)), ⟨⟨_, rfl⟩, hmem⟩, rfl⟩

noncomputable def physicalCount (α β : ℝ) (W : Set (ℝ × ℝ)) (x y : ℝ) : ℕ :=
  (modelSet α β W ∩ Set.Ico x y).ncard

theorem physicalCount_eq_blockCount (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (W : Set (ℝ × ℝ)) (hW : W ⊆ (Set.Ico 0 1 ×ˢ Set.Ico 0 1))
    (K : ℤ) (N : ℕ) :
    physicalCount α β W (covol α β * K) (covol α β * ((K : ℝ) + N)) =
      blockCount α β W K N := by
  unfold physicalCount
  rw [modelSet_block_eq α β hα hβ W hW, Set.ncard_coe_finset]
  exact blockPoints_card α β hα hβ W K N

theorem blockCount_reduction (α β : ℝ) (q : ℕ) (K : ℤ) (N : ℕ) :
    (blockCount α β (rectangle (-α) q) K N : ℝ) =
      ∑ j ∈ Finset.range N,
        (interval (-α) q).indicator (fun _ => (1 : ℝ))
          (Int.fract (-(K : ℝ) * α + j * (-α))) := by
  classical
  unfold blockCount
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [canonical_internal]
  have he : -((K + (j : ℤ) : ℤ) : ℝ) * α = -(K : ℝ) * α + j * (-α) := by
    push_cast; ring
  rw [he]
  simp [rectangle, interval, Set.indicator, Set.mem_prod, Set.mem_Ico,
    Int.fract_nonneg, Int.fract_lt_one]

theorem physical_block_discrepancy (α β : ℝ) (q : ℕ) (K : ℤ) (N : ℕ) :
    |(blockCount α β (rectangle (-α) q) K N : ℝ) -
      (volume (rectangle (-α) q)).toReal / covol α β *
        (covol α β * N)| ≤ q := by
  have hc : covol α β ≠ 0 := by unfold covol; positivity
  rw [blockCount_reduction, rectangle_volume]
  have he : Int.fract (q * (-α)) / covol α β * (covol α β * N) =
      N * Int.fract (q * (-α)) := by field_simp
  rw [he, interval_sum_telescope, abs_le]
  have h₁ := transfer_bounds (-α) (-(K : ℝ) * α) q
  have h₂ := transfer_bounds (-α) (-(K : ℝ) * α + N * (-α)) q
  constructor <;> linarith

/-- Discrepancy of the actual model-set cardinality on aligned physical blocks. -/
theorem modelSet_block_discrepancy (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (q : ℕ) (K : ℤ) (N : ℕ) :
    |(physicalCount α β (rectangle (-α) q)
      (covol α β * K) (covol α β * ((K : ℝ) + N)) : ℝ) -
      (volume (rectangle (-α) q)).toReal / covol α β * (covol α β * N)| ≤ q := by
  rw [physicalCount_eq_blockCount α β hα hβ]
  · exact physical_block_discrepancy α β q K N
  · intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (Int.fract_lt_one _)⟩, hp.2⟩

/-- Actual product area, independent of the physical normalization. -/
theorem literal_window_irrational_area (α : ℝ) (hα : Irrational α)
    (q : ℕ) (hq : 1 ≤ q) :
    Irrational ((volume (rectangle (-α) q)).toReal) ∧
    ¬ ∃ k : ℤ, (volume (rectangle (-α) q)).toReal = (k : ℝ) / 2 := by
  rw [rectangle_volume]
  have hi := fract_irrational (hα.neg.natCast_mul (by omega : q ≠ 0))
  exact ⟨hi, irrational_not_half_integer hi⟩

theorem literal_window_areas_dense (α : ℝ) (hα : Irrational α)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ q : ℕ, 1 ≤ q ∧ a < (volume (rectangle (-α) q)).toReal ∧
      (volume (rectangle (-α) q)).toReal < b := by
  simpa only [rectangle_volume, interval_volume] using
    interval_volumes_dense (-α) hα.neg a b ha hab hb

/-- The concrete physical-R/internal-R^2 lattice used in the report. -/
noncomputable def literalGamma : Set Ambient₃ := lattice (Real.sqrt 2) (Real.sqrt 3)

noncomputable def literalWindow (q : ℕ) : Set (ℝ × ℝ) := rectangle (-Real.sqrt 2) q

theorem literal_covol : covol (Real.sqrt 2) (Real.sqrt 3) = 6 := by
  norm_num [covol, Real.sq_sqrt]

/-- Concrete formal counterexamples on every aligned physical block. -/
theorem literal_block_counterexamples (q : ℕ) (hq : 1 ≤ q) :
    (∀ (K : ℤ) (N : ℕ),
      |(physicalCount (Real.sqrt 2) (Real.sqrt 3) (literalWindow q)
        (6 * K) (6 * ((K : ℝ) + N)) : ℝ) -
        (volume (literalWindow q)).toReal / 6 * (6 * N)| ≤ q) ∧
    Irrational ((volume (literalWindow q)).toReal) ∧
    ¬ ∃ k : ℤ, (volume (literalWindow q)).toReal = (k : ℝ) / 2 := by
  constructor
  · intro K N
    simpa only [literalWindow, literal_covol] using
      modelSet_block_discrepancy (Real.sqrt 2) (Real.sqrt 3)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) q K N
  · exact literal_window_irrational_area (Real.sqrt 2) irrational_sqrt_two q hq

theorem literal_areas_dense (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ q : ℕ, 1 ≤ q ∧ a < (volume (literalWindow q)).toReal ∧
      (volume (literalWindow q)).toReal < b := by
  exact literal_window_areas_dense (Real.sqrt 2) irrational_sqrt_two a b ha hab hb

/-- All real intervals are sandwiched between aligned blocks. The outer
block is finite; monotonicity of finite-set cardinality transfers the
aligned discrepancy bound, with at most two steps of length error. -/
theorem literal_window_discrepancy (q : ℕ) (x y : ℝ) (hxy : x ≤ y) :
    (modelSet (Real.sqrt 2) (Real.sqrt 3) (literalWindow q) ∩ Set.Ico x y).Finite ∧
    |(physicalCount (Real.sqrt 2) (Real.sqrt 3) (literalWindow q) x y : ℝ) -
      (volume (literalWindow q)).toReal / 6 * (y - x)| ≤ (q : ℝ) + 2 := by
  let S := modelSet (Real.sqrt 2) (Real.sqrt 3) (literalWindow q)
  let a := (volume (literalWindow q)).toReal
  have ha : 0 ≤ a := by
    dsimp [a, literalWindow]
    rw [rectangle_volume]
    exact Int.fract_nonneg _
  have ha1 : a ≤ 1 := by
    dsimp [a, literalWindow]
    rw [rectangle_volume]
    exact (Int.fract_lt_one _).le
  have hW : literalWindow q ⊆ (Set.Ico 0 1 ×ˢ Set.Ico 0 1) := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (Int.fract_lt_one _)⟩, hp.2⟩
  have hblock (K : ℤ) (N : ℕ) :
      (S ∩ Set.Ico (6 * K) (6 * ((K : ℝ) + N))).Finite ∧
      |((S ∩ Set.Ico (6 * K) (6 * ((K : ℝ) + N))).ncard : ℝ) - N * a| ≤ q := by
    constructor
    · have he := modelSet_block_eq (Real.sqrt 2) (Real.sqrt 3)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (literalWindow q) hW K N
      rw [literal_covol] at he
      dsimp [S]
      rw [he]
      exact Finset.finite_toSet _
    · have hd := modelSet_block_discrepancy (Real.sqrt 2) (Real.sqrt 3)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) q K N
      rw [literal_covol] at hd
      change |((S ∩ Set.Ico (6 * K) (6 * ((K : ℝ) + N))).ncard : ℝ) -
        a / 6 * (6 * N)| ≤ q at hd
      have he : a / 6 * (6 * (N : ℝ)) = N * a := by ring
      rw [he] at hd
      exact hd
  let K : ℤ := ⌊x / 6⌋
  let J : ℤ := ⌈y / 6⌉
  have hK := Int.floor_le (x / 6)
  have hK' := Int.lt_floor_add_one (x / 6)
  have hJ := Int.le_ceil (y / 6)
  have hJ' := Int.ceil_lt_add_one (y / 6)
  change (K : ℝ) ≤ x / 6 at hK
  change x / 6 < (K : ℝ) + 1 at hK'
  change y / 6 ≤ (J : ℝ) at hJ
  change (J : ℝ) < y / 6 + 1 at hJ'
  have hKJ : K ≤ J := by exact_mod_cast (show (K : ℝ) ≤ J by linarith)
  let N := (J - K).toNat
  have hN : (N : ℝ) = (J : ℝ) - K := by
    exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ J - K))
  have hout : S ∩ Set.Ico x y ⊆ S ∩ Set.Ico (6 * K) (6 * ((K : ℝ) + N)) := by
    intro t ht
    exact ⟨ht.1, ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩⟩
  have hb := hblock K N
  have hfin := hb.1.subset hout
  have hupper : ((S ∩ Set.Ico x y).ncard : ℝ) ≤
      ((S ∩ Set.Ico (6 * K) (6 * ((K : ℝ) + N))).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hout hb.1
  have hbupper := (abs_le.mp hb.2).2
  have hlength : (N : ℝ) - (y - x) / 6 ≤ 2 := by linarith
  have hu : ((S ∩ Set.Ico x y).ncard : ℝ) - a / 6 * (y - x) ≤ (q : ℝ) + 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlength ha]
  have hl : -((q : ℝ) + 2) ≤ ((S ∩ Set.Ico x y).ncard : ℝ) - a / 6 * (y - x) := by
    let L : ℤ := ⌈x / 6⌉
    let H : ℤ := ⌊y / 6⌋
    have hL := Int.le_ceil (x / 6)
    have hL' := Int.ceil_lt_add_one (x / 6)
    have hH := Int.floor_le (y / 6)
    have hH' := Int.lt_floor_add_one (y / 6)
    change x / 6 ≤ (L : ℝ) at hL
    change (L : ℝ) < x / 6 + 1 at hL'
    change (H : ℝ) ≤ y / 6 at hH
    change y / 6 < (H : ℝ) + 1 at hH'
    by_cases hLH : L ≤ H
    · let M := (H - L).toNat
      have hM : (M : ℝ) = (H : ℝ) - L := by
        exact_mod_cast (Int.toNat_of_nonneg (by omega : 0 ≤ H - L))
      have hin : S ∩ Set.Ico (6 * L) (6 * ((L : ℝ) + M)) ⊆ S ∩ Set.Ico x y := by
        intro t ht
        exact ⟨ht.1, ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩⟩
      have hlower : ((S ∩ Set.Ico (6 * L) (6 * ((L : ℝ) + M))).ncard : ℝ) ≤
          ((S ∩ Set.Ico x y).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hin hfin
      have hblower := (abs_le.mp (hblock L M).2).1
      have hlength : (y - x) / 6 - M ≤ 2 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hlength ha]
    · have hHL : (H : ℝ) + 1 ≤ L := by
        exact_mod_cast (by omega : H + 1 ≤ L)
      have hlength : (y - x) / 6 ≤ 2 := by linarith
      have hc : (0 : ℝ) ≤ (S ∩ Set.Ico x y).ncard := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hlength ha, (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  exact ⟨hfin, abs_le.mpr ⟨hl, hu⟩⟩

/-- Every positive member of the chosen family is a physical BRS, with
constant q + 2, for all real intervals and with explicit local finiteness. -/
theorem literal_window_isPhysicalBRS (q : ℕ) (_hq : 1 ≤ q) :
    IsPhysicalBRS (Real.sqrt 2) (Real.sqrt 3) (literalWindow q) := by
  refine ⟨measurableSet_Ico.prod measurableSet_Ico, (q : ℝ) + 2, ?_⟩
  intro x y hxy
  simpa only [literal_covol, physicalCount] using literal_window_discrepancy q x y hxy

/-- Headline negation in the literal physical-R/internal-R^2 class. -/
theorem literal_volume_clause_false :
    ¬ (∀ W : Set (ℝ × ℝ), IsPhysicalBRS (Real.sqrt 2) (Real.sqrt 3) W →
      ∃ k : ℤ, (volume W).toReal = (k : ℝ) / 2) := by
  intro h
  exact (literal_block_counterexamples 1 (by omega)).2.2
    (h (literalWindow 1) (literal_window_isPhysicalBRS 1 (by omega)))

/-- Areas in the literal physical BRS class meet every open subinterval
of (0,1); the witnesses are positive members of the same family. -/
theorem literal_physical_brs_areas_dense (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ q : ℕ, 1 ≤ q ∧
      IsPhysicalBRS (Real.sqrt 2) (Real.sqrt 3) (literalWindow q) ∧
      a < (volume (literalWindow q)).toReal ∧
      (volume (literalWindow q)).toReal < b := by
  obtain ⟨q, hq, hqa, hqb⟩ := literal_areas_dense a b ha hab hb
  exact ⟨q, hq, literal_window_isPhysicalBRS q hq, hqa, hqb⟩

/-- The full area spectrum of the literal physical BRS class. -/
noncomputable def literalAreaSpectrum : Set ℝ :=
  {a | ∃ W : Set (ℝ × ℝ), IsPhysicalBRS (Real.sqrt 2) (Real.sqrt 3) W ∧
    (volume W).toReal = a}

/-- The literal physical BRS area spectrum is not a discrete subset of R. -/
theorem literal_area_spectrum_not_discrete : ¬ IsDiscrete literalAreaSpectrum := by
  intro hd
  obtain ⟨q, hq, hB, ha, hb⟩ := literal_physical_brs_areas_dense
    0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  let v := (volume (literalWindow q)).toReal
  have hv : v ∈ literalAreaSpectrum := ⟨literalWindow q, hB, rfl⟩
  obtain ⟨U, hU, heq⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hd v hv
  have hvU : v ∈ U := by
    have hi : v ∈ U ∩ literalAreaSpectrum := by
      rw [heq]
      exact Set.mem_singleton v
    exact hi.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU v hvU
  have hmin : v < min 1 (v + ε) := lt_min (by dsimp [v]; linarith) (by linarith)
  obtain ⟨r, hr, hrB, hra, hrb⟩ := literal_physical_brs_areas_dense
    v (min 1 (v + ε)) ha.le hmin (min_le_left _ _)
  let w := (volume (literalWindow r)).toReal
  have hw : w ∈ literalAreaSpectrum := ⟨literalWindow r, hrB, rfl⟩
  have hwball : w ∈ Metric.ball v ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hra)]
    have := hrb.trans_le (min_le_right 1 (v + ε))
    linarith
  have hwv : w = v := Set.mem_singleton_iff.mp (heq ▸ ⟨hball hwball, hw⟩)
  exact (ne_of_gt hra) hwv

end BRSVolume

#print axioms BRSVolume.interval_counterexamples
#print axioms BRSVolume.circle_volume_clause_false
#print axioms BRSVolume.torus_volume_clause_false
#print axioms BRSVolume.circle_conjunction_false

#print axioms BRSVolume.interval_volumes_dense

#print axioms BRSVolume.physical_block_reindex
#print axioms BRSVolume.blockCount_reduction
#print axioms BRSVolume.physical_block_discrepancy
#print axioms BRSVolume.literal_window_irrational_area
#print axioms BRSVolume.literal_window_areas_dense

#print axioms BRSVolume.modelSet_block_eq
#print axioms BRSVolume.modelSet_block_discrepancy

#print axioms BRSVolume.literal_block_counterexamples
#print axioms BRSVolume.literal_areas_dense

#print axioms BRSVolume.literal_window_discrepancy
#print axioms BRSVolume.literal_window_isPhysicalBRS
#print axioms BRSVolume.literal_volume_clause_false
#print axioms BRSVolume.literal_physical_brs_areas_dense

#print axioms BRSVolume.literal_area_spectrum_not_discrete
