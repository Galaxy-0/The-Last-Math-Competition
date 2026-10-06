import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Geometric vocabulary for conjecture 00000001451.
Polytopes are convex hulls of finite point sets in genuine Euclidean space.
A facet is a nonempty proper exposed face of intrinsic codimension one.
Counts are witnessed by bijections, so no infinite-cardinality default is used.
-/
namespace TLMC1451
open Set MeasureTheory
open scoped symmDiff

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def IsPolytope {d : ℕ} (P : Set (Space d)) : Prop :=
  ∃ vertices : Finset (Space d), P = convexHull ℝ (vertices : Set (Space d))

def IsFacet {d : ℕ} (P F : Set (Space d)) : Prop :=
  F.Nonempty ∧ F ⊂ P ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
      Module.finrank ℝ (affineSpan ℝ P).direction

def Facets {d : ℕ} (P : Set (Space d)) : Set (Set (Space d)) :=
  {F | IsFacet P F}

def HasFacetCount {d : ℕ} (P : Set (Space d)) (n : ℕ) : Prop :=
  Nonempty (Fin n ≃ {F // F ∈ Facets P})

def UnitBall (d : ℕ) : Set (Space d) := Metric.closedBall 0 1

def Approximates {d : ℕ} (ε : ℝ) (K P : Set (Space d)) : Prop :=
  volume (K ∆ P) ≤ ENNReal.ofReal ε * volume K

def AdmissibleCount (d : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∃ P : Set (Space d), IsPolytope P ∧ Approximates ε (UnitBall d) P ∧ HasFacetCount P n

def IsMinimumFacetCount (d : ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  AdmissibleCount d ε n ∧ ∀ m, AdmissibleCount d ε m → n ≤ m

/-- Every exposed face is determined by a subset of the finite generating set. -/
theorem finite_exposed_faces {d : ℕ} {P : Set (Space d)} (hP : IsPolytope P) :
    {F : Set (Space d) | IsExposed ℝ P F}.Finite := by
  obtain ⟨S, rfl⟩ := hP
  have hc : IsCompact (convexHull ℝ (S : Set (Space d))) :=
    S.finite_toSet.isCompact_convexHull
  apply (S.finite_toSet.powerset.image
    (fun A : Set (Space d) => closure (convexHull ℝ A))).subset
  intro F hF
  refine ⟨F.extremePoints ℝ, ?_, ?_⟩
  · exact hF.isExtreme.extremePoints_subset_extremePoints.trans
      extremePoints_convexHull_subset
  · exact closure_convexHull_extremePoints (hF.isCompact hc)
      (hF.convex (convex_convexHull ℝ _))

theorem facets_finite {d : ℕ} {P : Set (Space d)} (hP : IsPolytope P) :
    (Facets P).Finite := by
  apply (finite_exposed_faces hP).subset
  intro F hF
  exact hF.2.2.1

theorem exists_facet_count {d : ℕ} {P : Set (Space d)} (hP : IsPolytope P) :
    ∃ n, HasFacetCount P n := by
  letI : Fintype {F // F ∈ Facets P} := (facets_finite hP).fintype
  exact ⟨Fintype.card {F // F ∈ Facets P}, ⟨(Fintype.equivFin _).symm⟩⟩

theorem facet_count_unique {d n m : ℕ} {P : Set (Space d)}
    (hn : HasFacetCount P n) (hm : HasFacetCount P m) : n = m := by
  obtain ⟨en⟩ := hn
  obtain ⟨em⟩ := hm
  exact Fin.equiv_iff_eq.mp ⟨en.trans em.symm⟩

/-- Existence of any approximant gives a minimum attained by an actual polytope. -/
theorem minimum_exists_iff {d : ℕ} {ε : ℝ} :
    (∃ n, IsMinimumFacetCount d ε n) ↔
      ∃ P : Set (Space d), IsPolytope P ∧ Approximates ε (UnitBall d) P := by
  classical
  constructor
  · rintro ⟨n, ⟨P, hp, ha, _⟩, _⟩
    exact ⟨P, hp, ha⟩
  · rintro ⟨P, hp, ha⟩
    obtain ⟨n, hn⟩ := exists_facet_count hp
    have h : ∃ n, AdmissibleCount d ε n := ⟨n, P, hp, ha, hn⟩
    exact ⟨Nat.find h, Nat.find_spec h, fun _ hm => Nat.find_min' h hm⟩

theorem minimum_unique {d n m : ℕ} {ε : ℝ}
    (hn : IsMinimumFacetCount d ε n) (hm : IsMinimumFacetCount d ε m) : n = m :=
  Nat.le_antisymm (hn.2 m hm.1) (hm.2 n hn.1)

end TLMC1451
