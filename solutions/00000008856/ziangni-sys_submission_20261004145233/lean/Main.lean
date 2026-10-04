import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

noncomputable section
namespace CesaroSemigroup
open Filter
open scoped Topology
def T (n : ℕ) (x : ℝ) : ℝ := if n = 0 then x else |x|
def fixedSet : Set ℝ := {x | ∀ n, T n x = x}
def initial : ℝ := -1
def average (n : ℕ) : ℝ := (∑ k ∈ Finset.range (n+1), T k initial) / (n+1 : ℝ)
def Nearest (K : Set ℝ) (x p : ℝ) : Prop := p ∈ K ∧ ∀ z ∈ K, dist x p ≤ dist x z
def WeaklyConverges (u : ℕ → ℝ) (p : ℝ) : Prop :=
  ∀ f : ℝ →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f p))

theorem semigroup_identity (x : ℝ) : T 0 x = x := by simp [T]
theorem semigroup_law (m n : ℕ) (x : ℝ) : T (m+n) x = T m (T n x) := by
  by_cases hm : m = 0
  · subst m; simp [T]
  · by_cases hn : n = 0
    · subst n; simp [T]
    · have hs : m+n ≠ 0 := by omega
      simp [T, hm, hn, hs]

theorem nonexpansive (n : ℕ) (x y : ℝ) : dist (T n x) (T n y) ≤ dist x y := by
  by_cases h : n = 0
  · simp [T, h]
  · simpa [T, h, Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y

theorem actual_iterates (n : ℕ) (x : ℝ) : (fun y : ℝ => |y|)^[n] x = T n x := by
  induction n with
  | zero => simp [T]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      by_cases h : n = 0 <;> simp [T, h]

theorem fixedSet_eq : fixedSet = Set.Ici 0 := by
  ext x
  constructor
  · intro h
    have hx := h 1
    simp [T] at hx
    exact hx
  · intro hx n
    change 0 ≤ x at hx
    simp [T, abs_of_nonneg hx]

theorem fixed_geometry : IsClosed fixedSet ∧ Convex ℝ fixedSet ∧ fixedSet.Nonempty := by
  rw [fixedSet_eq]
  exact ⟨isClosed_Ici, convex_Ici 0, ⟨0, by simp⟩⟩

theorem orbit_values : T 0 initial = -1 ∧ ∀ n, T (n+1) initial = 1 := by
  norm_num [T, initial]

theorem orbit_bounded (n : ℕ) : |T n initial| ≤ 1 := by
  by_cases h : n = 0 <;> norm_num [T, initial, h]

theorem actual_sum (n : ℕ) : (∑ k ∈ Finset.range (n+1), T k initial) = (n : ℝ) - 1 := by
  induction n with
  | zero => norm_num [T, initial]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, orbit_values.2]
      push_cast
      ring

theorem average_formula (n : ℕ) : average n = 1 - 2 / (n+1 : ℝ) := by
  rw [average, actual_sum]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem average_strong_limit : Tendsto average atTop (𝓝 1) := by
  change Tendsto (fun n => average n) atTop (𝓝 1)
  simp_rw [average_formula, div_eq_mul_inv]
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
      tendsto_one_div_add_atTop_nhds_zero_nat)
  simpa only [one_div, mul_zero, sub_zero] using h

theorem average_weak_limit : WeaklyConverges average 1 := by
  intro f
  exact f.continuous.continuousAt.tendsto.comp average_strong_limit

theorem weak_limit_unique (p : ℝ) (hp : WeaklyConverges average p) : p = 1 := by
  exact tendsto_nhds_unique (hp (ContinuousLinearMap.id ℝ ℝ)) average_strong_limit

theorem actual_metric_projection : Nearest fixedSet initial 0 := by
  rw [Nearest, fixedSet_eq]
  constructor
  · simp
  · intro z hz
    change 0 ≤ z at hz
    simp only [initial, Real.dist_eq, sub_zero, abs_neg, abs_one]
    rw [abs_of_nonpos (by linarith : (-1 : ℝ)-z ≤ 0)]
    linarith

theorem metric_projection_unique (p : ℝ) (hp : Nearest fixedSet initial p) : p = 0 := by
  have hnonneg : 0 ≤ p := by simpa [fixedSet_eq] using hp.1
  have hb := hp.2 0 actual_metric_projection.1
  simp only [initial, Real.dist_eq, sub_zero, abs_neg, abs_one] at hb
  rw [abs_of_nonpos (by linarith : (-1 : ℝ)-p ≤ 0)] at hb
  linarith

theorem no_nearest_weak_limit : ¬ ∃ p, WeaklyConverges average p ∧ Nearest fixedSet initial p := by
  rintro ⟨p, hw, hn⟩
  have h1 := weak_limit_unique p hw
  have h0 := metric_projection_unique p hn
  linarith

theorem counterexample : (∀ m n x, T (m+n) x = T m (T n x)) ∧
    (∀ n x y, dist (T n x) (T n y) ≤ dist x y) ∧
    fixedSet.Nonempty ∧ (∀ n, |T n initial| ≤ 1) ∧
    Nearest fixedSet initial 0 ∧ WeaklyConverges average 1 ∧
    ¬ ∃ p, WeaklyConverges average p ∧ Nearest fixedSet initial p :=
  ⟨semigroup_law, nonexpansive, fixed_geometry.2.2, orbit_bounded,
    actual_metric_projection, average_weak_limit, no_nearest_weak_limit⟩
end CesaroSemigroup
#print axioms CesaroSemigroup.semigroup_law
#print axioms CesaroSemigroup.nonexpansive
#print axioms CesaroSemigroup.actual_sum
#print axioms CesaroSemigroup.average_strong_limit
#print axioms CesaroSemigroup.actual_metric_projection
#print axioms CesaroSemigroup.no_nearest_weak_limit
#print axioms CesaroSemigroup.counterexample
