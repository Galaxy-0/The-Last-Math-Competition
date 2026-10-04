import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
namespace Counterexample

def zeros : Set ℝ := {x | Real.sin x = 0}
def sineGraph : Set (ℝ × ℝ) := {p | p.2 = Real.sin p.1}

theorem sine_smooth : ContDiff ℝ ⊤ Real.sin := Real.contDiff_sin
theorem sine_solves_polynomial_ode (t : ℝ) : deriv (deriv Real.sin) t + Real.sin t = 0 := by
  simp [Real.deriv_sin, Real.deriv_cos]
theorem sine_initial_data : Real.sin 0 = 0 ∧ deriv Real.sin 0 = 1 := by
  simp [Real.deriv_sin]

theorem zeros_characterization (x : ℝ) : x ∈ zeros ↔ ∃ n : ℤ, (n : ℝ) * Real.pi = x :=
  Real.sin_eq_zero_iff

theorem zeros_infinite : zeros.Infinite := by
  have hi : Function.Injective (fun n : ℕ => (n : ℝ) * Real.pi) := by
    intro a b h
    have hc : (a : ℝ) = b := (mul_right_cancel₀ (ne_of_gt Real.pi_pos)) h
    exact_mod_cast hc
  apply (Set.infinite_range_of_injective hi).mono
  rintro x ⟨n, rfl⟩
  apply (zeros_characterization _).mpr
  exact ⟨n, by simp⟩

/-- Between any two distinct sine zeros lies a point where sine is nonzero. -/
theorem nonzero_between {x y : ℝ} (hx : x ∈ zeros) (hy : y ∈ zeros) (hxy : x < y) :
    ∃ z ∈ Set.Icc x y, z ∉ zeros := by
  obtain ⟨n, hn⟩ := (zeros_characterization x).mp hx
  obtain ⟨m, hm⟩ := (zeros_characterization y).mp hy
  have hnmR : (n : ℝ) < m := by
    apply (mul_lt_mul_iff_of_pos_right Real.pi_pos).mp
    simpa [hn, hm] using hxy
  have hnm : n < m := by exact_mod_cast hnmR
  have hstep : (n : ℝ) + 1 ≤ m := by exact_mod_cast (Int.add_one_le_iff.mpr hnm)
  have hgap : x + Real.pi ≤ y := by
    have hmul := mul_le_mul_of_nonneg_right hstep Real.pi_pos.le
    nlinarith
  refine ⟨x + Real.pi / 2, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, ?_⟩
  intro hz
  change Real.sin (x + Real.pi / 2) = 0 at hz
  rw [← hn, add_comm, Real.sin_add_int_mul_pi, Real.sin_pi_div_two, mul_one] at hz
  exact (zpow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) hz

theorem connected_subset_subsingleton {s : Set ℝ} (hc : Set.OrdConnected s)
    (hs : s ⊆ zeros) : s.Subsingleton := by
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | heq | hyx
  · obtain ⟨z, hz, hnz⟩ := nonzero_between (hs hx) (hs hy) hxy
    exact False.elim (hnz (hs (hc.out hx hy hz)))
  · exact heq
  · obtain ⟨z, hz, hnz⟩ := nonzero_between (hs hy) (hs hx) hyx
    exact False.elim (hnz (hs (hc.out hy hx hz)))

/-- A necessary unary o-minimal condition: a finite union of points and intervals.
Using order-connected pieces even permits all endpoint conventions and unbounded intervals. -/
def UnaryTame (s : Set ℝ) : Prop :=
  ∃ n : ℕ, ∃ F : Fin n → Set ℝ, (∀ i, Set.OrdConnected (F i)) ∧ s = ⋃ i, F i

theorem zeros_not_tame : ¬ UnaryTame zeros := by
  rintro ⟨n, F, hconn, heq⟩
  have hfin : ∀ i, (F i).Finite := by
    intro i
    apply (connected_subset_subsingleton (hconn i) ?_).finite
    intro x hx
    rw [heq]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hzfin : zeros.Finite := by
    rw [heq]
    exact Set.finite_iUnion hfin
  exact zeros_infinite hzfin

/-- Intersection with the horizontal zero line, followed by coordinate projection. -/
def zeroFiber (G : Set (ℝ × ℝ)) : Set ℝ :=
  Prod.fst '' (G ∩ {p | p.2 = 0})

theorem graph_zero_fiber : zeroFiber sineGraph = zeros := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hg, hb⟩, ha⟩
    change b = Real.sin a at hg
    change b = 0 at hb
    change a = x at ha
    change Real.sin x = 0
    simpa [ha, hb] using hg.symm
  · intro hx
    exact ⟨(x, 0), ⟨hx.symm, rfl⟩, rfl⟩

/-- Unbundled necessary definable-set axioms, not a claimed Mathlib model-theory structure. -/
structure DefinableFamilies where
  unary : Set (Set ℝ)
  binary : Set (Set (ℝ × ℝ))
  zeroFiber_mem : ∀ G ∈ binary, zeroFiber G ∈ unary

def HasOMinimalUnaryProperty (D : DefinableFamilies) : Prop :=
  ∀ s ∈ D.unary, UnaryTame s

theorem no_o_minimal_sine (D : DefinableFamilies) (hs : sineGraph ∈ D.binary) :
    ¬ HasOMinimalUnaryProperty D := by
  intro ht
  apply zeros_not_tame
  have hm := D.zeroFiber_mem sineGraph hs
  rw [graph_zero_fiber] at hm
  exact ht zeros hm

theorem counterexample :
    (∀ t : ℝ, deriv (deriv Real.sin) t + Real.sin t = 0) ∧
    ∀ D : DefinableFamilies, sineGraph ∈ D.binary → ¬ HasOMinimalUnaryProperty D :=
  ⟨sine_solves_polynomial_ode, no_o_minimal_sine⟩

#print axioms sine_smooth
#print axioms sine_solves_polynomial_ode
#print axioms sine_initial_data
#print axioms zeros_infinite
#print axioms connected_subset_subsingleton
#print axioms zeros_not_tame
#print axioms graph_zero_fiber
#print axioms counterexample
end Counterexample
