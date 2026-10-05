import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
universe u
open Set Metric EMetric Filter Topology
namespace HyperconvexTranslation

-- Full hyperconvexity: every arbitrary compatible family of closed balls intersects.
def Hyperconvex (X : Type*) [MetricSpace X] : Prop :=
  ∀ (ι : Type u) (x : ι → X) (r : ι → ℝ),
    (∀ i, 0 ≤ r i) → (∀ i j, dist (x i) (x j) ≤ r i + r j) →
    ∃ y : X, ∀ i, dist y (x i) ≤ r i

theorem real_hyperconvex : Hyperconvex ℝ := by
  intro ι x r hr hpair
  rcases isEmpty_or_nonempty ι with hi | hi
  · letI := hi
    exact ⟨0,fun i => isEmptyElim i⟩
  · letI := hi
    obtain ⟨j⟩ := hi
    have endpoints (i k : ι) : x i-r i ≤ x k+r k := by
      have hp := hpair i k
      rw [Real.dist_eq] at hp
      have hle := le_abs_self (x i-x k)
      linarith
    let L : Set ℝ := range (fun i => x i-r i)
    have hn : L.Nonempty := ⟨x j-r j,⟨j,rfl⟩⟩
    have hb : BddAbove L := ⟨x j+r j,by rintro z ⟨i,rfl⟩; exact endpoints i j⟩
    refine ⟨sSup L,?_⟩
    intro i
    have hlo : x i-r i ≤ sSup L := le_csSup hb ⟨i,rfl⟩
    have hhi : sSup L ≤ x i+r i := csSup_le hn (by rintro z ⟨k,rfl⟩; exact endpoints k i)
    rw [Real.dist_eq,abs_le]
    constructor <;> linarith

theorem real_complete : CompleteSpace ℝ := inferInstance

def T (x : ℝ) : Set ℝ := {x+1}

theorem actual_values (x : ℝ) : (T x).Nonempty ∧ IsClosed (T x) ∧
    Bornology.IsBounded (T x) ∧ Convex ℝ (T x) := by
  exact ⟨singleton_nonempty _,isClosed_singleton,Bornology.isBounded_singleton,
    convex_singleton _⟩

theorem actual_hausdorff (x y : ℝ) : hausdorffDist (T x) (T y) = dist x y := by
  have hs : hausdorffEdist (T x) (T y) = edist (x+1) (y+1) := by
    simp [T,hausdorffEdist_def,edist_comm]
  rw [hausdorffDist,hs,←dist_edist,dist_add_right]

def HausdorffNonexpansive (F : ℝ → Set ℝ) : Prop :=
  ∀ x y, hausdorffDist (F x) (F y) ≤ dist x y

theorem genuine_nonexpansive : HausdorffNonexpansive T := by
  intro x y
  simpa only [actual_hausdorff] using (le_refl (dist x y))

theorem no_fixed_point : ¬ ∃ x : ℝ, x ∈ T x := by
  rintro ⟨x,hx⟩
  have heq : x=x+1 := hx
  linarith

def f (x : ℝ) : ℝ := x+1

theorem unique_selection (x y : ℝ) : y ∈ T x ↔ y=f x := Iff.rfl

def orbit (n : ℕ) : ℝ := (f^[n]) 0

theorem actual_orbit (n : ℕ) : orbit n = n := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    rw [orbit,Function.iterate_succ_apply']
    change f (orbit n) = (n+1:ℕ)
    rw [ih]
    simp [f]

theorem orbit_diverges : Tendsto orbit atTop atTop := by
  change Tendsto (fun n => orbit n) atTop atTop
  simpa only [actual_orbit] using (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)

theorem actual_counterexample : Hyperconvex ℝ ∧
    (∀ x, (T x).Nonempty ∧ IsClosed (T x) ∧ Bornology.IsBounded (T x) ∧ Convex ℝ (T x)) ∧
    HausdorffNonexpansive T ∧ ¬ ∃ x : ℝ, x ∈ T x :=
  ⟨real_hyperconvex,actual_values,genuine_nonexpansive,no_fixed_point⟩

end HyperconvexTranslation
#print axioms HyperconvexTranslation.real_hyperconvex
#print axioms HyperconvexTranslation.actual_values
#print axioms HyperconvexTranslation.actual_hausdorff
#print axioms HyperconvexTranslation.no_fixed_point
#print axioms HyperconvexTranslation.actual_orbit
#print axioms HyperconvexTranslation.orbit_diverges
#print axioms HyperconvexTranslation.actual_counterexample
