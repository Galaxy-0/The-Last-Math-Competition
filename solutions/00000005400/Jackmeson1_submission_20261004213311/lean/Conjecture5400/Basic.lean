import Mathlib

/-!
# Conjecture 00000005400 is false

Conjecture 00000005400 reads:

> Definition: Orbit distribution and period counting are two layers. Conjecture: There exist two
> maps with identical orbit distribution limits but different periodic point counts, and the
> separation is realized by an explicit conjugate pair with the same measure but different periods.

The final clause asks for a *conjugate pair* `f : X → X`, `g : Y → Y`, i.e. a bijection
`h : X ≃ Y` with `h ∘ f = g ∘ h` (Mathlib's `Function.Semiconj h f g`), whose periodic data differ.
This is impossible: a conjugacy maps `Fix(f^[n])` bijectively onto `Fix(g^[n])`, preserves the
minimal (least) period of every point, and maps the `n`-cycles of `f` bijectively onto those of `g`.
Topological conjugacies (`Homeomorph`) and measure-preserving measurable conjugacies
(`MeasurableEquiv` with `MeasurePreserving`) are special cases.

The side conditions "identical orbit distribution limits" and "the same measure" are left as
*arbitrary* predicates, so the disproof holds whatever they mean.

Periodic notions are Mathlib's: `Function.IsPeriodicPt`, `Function.ptsOfPeriod`,
`Function.minimalPeriod`, `Function.periodicOrbit`. Counts are cardinals (`Cardinal.mk`), so
infinite sets of periodic points are covered as well.

The transport argument is adapted from the accepted disproof of the sibling conjecture
00000005390 (solutions/00000005390/ziangni-sys_submission_20261004205500, The Last Math
Competition, GPL-3.0); this file is rewritten on top of Mathlib's periodic-point API.
-/

open Function Cardinal

namespace Conjecture5400

universe u

/-- Points of least period `n` (for `n > 0`, the points whose minimal period is exactly `n`). -/
def leastPeriodPts {X : Type u} (f : X → X) (n : ℕ) : Set X :=
  {x | x ∈ periodicPts f ∧ minimalPeriod f x = n}

/-- The `n`-cycles of `f`: periodic orbits (Mathlib `Cycle`s) of points of least period `n`. -/
def cycles {X : Type u} (f : X → X) (n : ℕ) : Set (Cycle X) :=
  {c | ∃ x ∈ leastPeriodPts f n, periodicOrbit f x = c}

/-- The set of periods (least periods) occurring for `f`. -/
def periodSet {X : Type u} (f : X → X) : Set ℕ :=
  {n | ∃ x ∈ periodicPts f, minimalPeriod f x = n}

/-- "Different periodic point counts / different periods": some periodic-point count, least-period
count or cycle count differs, or the sets of periods differ. -/
def PeriodDataDiffer {X Y : Type u} (f : X → X) (g : Y → Y) : Prop :=
  periodSet f ≠ periodSet g ∨
  ∃ n : ℕ, #(ptsOfPeriod f n) ≠ #(ptsOfPeriod g n) ∨
    #(leastPeriodPts f n) ≠ #(leastPeriodPts g n) ∨ #(cycles f n) ≠ #(cycles g n)

section Transport

variable {X Y : Type u} {f : X → X} {g : Y → Y} {h : X ≃ Y}

theorem isPeriodicPt_iff (hc : Semiconj h f g) (n : ℕ) (x : X) :
    IsPeriodicPt g n (h x) ↔ IsPeriodicPt f n x := by
  unfold IsPeriodicPt IsFixedPt
  rw [← (hc.iterate_right n).eq x]
  exact h.injective.eq_iff

theorem mem_periodicPts_iff (hc : Semiconj h f g) (x : X) :
    h x ∈ periodicPts g ↔ x ∈ periodicPts f := by
  simp only [mem_periodicPts, isPeriodicPt_iff hc]

/-- A conjugacy preserves the minimal period of every point. -/
theorem minimalPeriod_eq (hc : Semiconj h f g) (x : X) :
    minimalPeriod g (h x) = minimalPeriod f x :=
  minimalPeriod_eq_minimalPeriod_iff.2 fun n => isPeriodicPt_iff hc n x

theorem symm_semiconj (hc : Semiconj h f g) : Semiconj h.symm g f := fun y => by
  apply h.injective
  simp [hc.eq (h.symm y)]

theorem periodicOrbit_map (hc : Semiconj h f g) (x : X) :
    (periodicOrbit f x).map h = periodicOrbit g (h x) := by
  rw [periodicOrbit_def, periodicOrbit_def, Cycle.map_coe, List.map_map, minimalPeriod_eq hc]
  congr 2
  funext k
  exact (hc.iterate_right k).eq x

theorem mem_leastPeriodPts_iff (hc : Semiconj h f g) (n : ℕ) (x : X) :
    h x ∈ leastPeriodPts g n ↔ x ∈ leastPeriodPts f n := by
  simp only [leastPeriodPts, Set.mem_ofPred_eq, mem_periodicPts_iff hc, minimalPeriod_eq hc]

/-- `Fix(f^[n]) ≃ Fix(g^[n])`. -/
def ptsOfPeriodEquiv (hc : Semiconj h f g) (n : ℕ) : ptsOfPeriod f n ≃ ptsOfPeriod g n :=
  h.subtypeEquiv fun x => (isPeriodicPt_iff hc n x).symm

/-- Points of least period `n` correspond. -/
def leastPeriodPtsEquiv (hc : Semiconj h f g) (n : ℕ) :
    leastPeriodPts f n ≃ leastPeriodPts g n :=
  h.subtypeEquiv fun x => (mem_leastPeriodPts_iff hc n x).symm

theorem map_mem_cycles (hc : Semiconj h f g) (n : ℕ) {c : Cycle X} (hc' : c ∈ cycles f n) :
    c.map h ∈ cycles g n := by
  obtain ⟨x, hx, rfl⟩ := hc'
  exact ⟨h x, (mem_leastPeriodPts_iff hc n x).2 hx, (periodicOrbit_map hc x).symm⟩

/-- The `n`-cycles of `f` and of `g` correspond (via `c ↦ c.map h`). -/
def cyclesEquiv (hc : Semiconj h f g) (n : ℕ) : cycles f n ≃ cycles g n where
  toFun c := ⟨c.1.map h, map_mem_cycles hc n c.2⟩
  invFun c := ⟨c.1.map h.symm, map_mem_cycles (h := h.symm) (symm_semiconj hc) n c.2⟩
  left_inv := by
    rintro ⟨c, x, -, rfl⟩
    apply Subtype.ext
    simp only
    rw [periodicOrbit_map hc, periodicOrbit_map (h := h.symm) (symm_semiconj hc),
      Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨c, y, -, rfl⟩
    apply Subtype.ext
    simp only
    rw [periodicOrbit_map (h := h.symm) (symm_semiconj hc), periodicOrbit_map hc,
      Equiv.apply_symm_apply]

theorem periodSet_eq (hc : Semiconj h f g) : periodSet f = periodSet g := by
  ext n
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨h x, (mem_periodicPts_iff hc x).2 hx, minimalPeriod_eq hc x⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨h.symm y, (mem_periodicPts_iff hc _).1 (by simpa using hy), ?_⟩
    simpa using (minimalPeriod_eq hc (h.symm y)).symm

/-- **Conjugate maps cannot differ in any periodic data.** -/
theorem not_periodDataDiffer (hc : Semiconj h f g) :
    ¬ PeriodDataDiffer f g ∧ ∀ x, minimalPeriod g (h x) = minimalPeriod f x := by
  refine ⟨?_, minimalPeriod_eq hc⟩
  rintro (hne | ⟨n, hn | hn | hn⟩)
  · exact hne (periodSet_eq hc)
  · exact hn (mk_congr (ptsOfPeriodEquiv hc n))
  · exact hn (mk_congr (leastPeriodPtsEquiv hc n))
  · exact hn (mk_congr (cyclesEquiv hc n))

end Transport

/-- **Conjecture 00000005400**, with the unspecified side conditions as arbitrary predicates:
`SameOrbitLimits X Y f g` ("identical orbit distribution limits") and `SameMeasure X Y f g h`
("the same measure", which may depend on the conjugacy `h`). The separating conjugate pair
`(f', g')` may be `(f, g)` itself or any other pair; "different periods" means different periodic
data or a point whose least period differs from that of its conjugate image. -/
def Statement
    (SameOrbitLimits : ∀ X Y : Type u, (X → X) → (Y → Y) → Prop)
    (SameMeasure : ∀ X Y : Type u, (X → X) → (Y → Y) → (X ≃ Y) → Prop) : Prop :=
  ∃ (X Y : Type u) (f : X → X) (g : Y → Y),
    SameOrbitLimits X Y f g ∧ PeriodDataDiffer f g ∧
    ∃ (X' Y' : Type u) (f' : X' → X') (g' : Y' → Y') (h : X' ≃ Y'),
      Semiconj h f' g' ∧ SameMeasure X' Y' f' g' h ∧
      (PeriodDataDiffer f' g' ∨ ∃ x, minimalPeriod g' (h x) ≠ minimalPeriod f' x)

/-- **Main theorem.** Conjecture 00000005400 is false, whatever "identical orbit distribution
limits" and "the same measure" mean. -/
theorem conjecture5400_false
    (SameOrbitLimits : ∀ X Y : Type u, (X → X) → (Y → Y) → Prop)
    (SameMeasure : ∀ X Y : Type u, (X → X) → (Y → Y) → (X ≃ Y) → Prop) :
    ¬ Statement SameOrbitLimits SameMeasure := by
  rintro ⟨X, Y, f, g, -, -, X', Y', f', g', h, hc, -, hd⟩
  obtain ⟨hnd, hmin⟩ := not_periodDataDiffer hc
  rcases hd with hd | ⟨x, hx⟩
  · exact hnd hd
  · exact hx (hmin x)

/-- The reading in which `(f, g)` itself is the conjugate pair is a special case. -/
theorem conjecture5400_samePair_false
    (SameOrbitLimits : ∀ X Y : Type u, (X → X) → (Y → Y) → Prop)
    (SameMeasure : ∀ X Y : Type u, (X → X) → (Y → Y) → (X ≃ Y) → Prop) :
    ¬ ∃ (X Y : Type u) (f : X → X) (g : Y → Y) (h : X ≃ Y),
      SameOrbitLimits X Y f g ∧ PeriodDataDiffer f g ∧ Semiconj h f g ∧ SameMeasure X Y f g h :=
  fun ⟨_, _, _, _, _, _, hd, hc, _⟩ => (not_periodDataDiffer hc).1 hd

/-- Topological conjugacy (a homeomorphism `h` with `h ∘ f = g ∘ h`) is a special case. -/
theorem homeomorph_conjugate_same_periods {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → X} {g : Y → Y} (h : X ≃ₜ Y) (hc : Semiconj h f g) :
    ¬ PeriodDataDiffer f g ∧ ∀ x, minimalPeriod g (h x) = minimalPeriod f x :=
  not_periodDataDiffer (h := h.toEquiv) hc

/-- A measure-preserving measurable conjugacy ("conjugate pair with the same measure",
`h_* μ = ν`, conjugacy holding at every point) is a special case. -/
theorem measured_conjugate_same_periods {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : MeasureTheory.Measure X} {ν : MeasureTheory.Measure Y} {f : X → X} {g : Y → Y}
    (h : X ≃ᵐ Y) (_hμ : MeasureTheory.MeasurePreserving h μ ν) (hc : Semiconj h f g) :
    ¬ PeriodDataDiffer f g ∧ ∀ x, minimalPeriod g (h x) = minimalPeriod f x :=
  not_periodDataDiffer (h := h.toEquiv) hc

end Conjecture5400
