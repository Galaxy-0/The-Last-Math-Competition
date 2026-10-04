import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Counterexample
abbrev Ω := Fin 2
instance : MeasurableSpace Ω := borel Ω
instance : BorelSpace Ω := ⟨rfl⟩
def T : Ω → Ω := id
def f : Ω → ℝ := fun _ => 0

theorem compact_system : CompactSpace Ω := inferInstance
theorem T_continuous : Continuous T := continuous_id
theorem f_continuous : Continuous f := continuous_const

/-- Every finite measurable partition of the finite discrete space is represented
by its equivalence relation; its atoms are the quotient classes. -/
def atom (P : Setoid Ω) (q : Quotient P) : Set Ω := {x | Quotient.mk P x = q}


theorem atoms_partition (P : Setoid Ω) :
    (∀ q : Quotient P, (atom P q).Nonempty ∧ MeasurableSet (atom P q)) ∧
    (∀ q r : Quotient P, q ≠ r → Disjoint (atom P q) (atom P r)) ∧
    (⋃ q : Quotient P, atom P q) = Set.univ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    constructor
    · obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      exact ⟨x, rfl⟩
    · exact (Set.toFinite _).measurableSet
  · intro q r hqr
    exact Set.disjoint_left.mpr (fun x hx hr => hqr (hx.symm.trans hr))
  · ext x
    simp [atom]

def partitionEntropy (μ : Measure Ω) (P : Setoid Ω) : ℝ := by
  classical
  exact ∑ q : Quotient P, -(μ (atom P q)).toReal * Real.log (μ (atom P q)).toReal

/-- Join of the partitions T^{-j}P for 0 ≤ j < n; infimum of equivalence
relations is the common refinement of their quotient-class partitions. -/
def refinement (P : Setoid Ω) (n : ℕ) : Setoid Ω :=
  ⨅ j : Fin n, Setoid.comap (T^[j.val]) P

theorem refinement_identity (P : Setoid Ω) {n : ℕ} (hn : 0 < n) : refinement P n = P := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h (j : Fin n) : Setoid.comap (T^[j.val]) P = P := by
    ext x y
    simp [T, Setoid.comap, Function.onFun]
  simp only [refinement, h, iInf_const]

def entropyRate (μ : Measure Ω) (P : Setoid Ω) : ℝ :=
  limsup (fun n : ℕ => partitionEntropy μ (refinement P n) / (n : ℝ)) atTop

theorem entropy_rate_limit (μ : Measure Ω) (P : Setoid Ω) :
    Tendsto (fun n : ℕ => partitionEntropy μ (refinement P n) / (n : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => partitionEntropy μ P / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hi
  apply hc.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [refinement_identity P hn]

theorem entropyRate_zero (μ : Measure Ω) (P : Setoid Ω) : entropyRate μ P = 0 :=
  (entropy_rate_limit μ P).limsup_eq

/-- Kolmogorov--Sinai entropy: supremum of the rates over ALL finite measurable
partitions. On this finite discrete space, all partitions are finite and measurable. -/
def entropy (μ : Measure Ω) : ℝ := sSup (Set.range (entropyRate μ))

theorem entropy_zero (μ : Measure Ω) : entropy μ = 0 := by
  have he : entropyRate μ = fun _ : Setoid Ω => 0 := funext (entropyRate_zero μ)
  simp [entropy, he]

theorem dirac_ergodic (a : Ω) : Ergodic T (Measure.dirac a) where
  toMeasurePreserving := MeasurePreserving.id _
  aeconst_set s _hs _hpre :=
    eventuallyConst_iff_exists_eventuallyEq.mpr ⟨s a, ae_eq_dirac s⟩

def value (t : ℝ) (μ : Measure Ω) : ℝ := (∫ x, f x ∂μ) + t * entropy μ

def pressureValues (t : ℝ) : Set ℝ := {r | ∃ μ : Measure Ω,
  IsProbabilityMeasure μ ∧ Ergodic T μ ∧ r = value t μ}

def pressure (t : ℝ) : ℝ := sSup (pressureValues t)

theorem value_zero (t : ℝ) (μ : Measure Ω) : value t μ = 0 := by
  simp [value, f, entropy_zero]

theorem pressureValues_exact (t : ℝ) : pressureValues t = {0} := by
  ext r
  constructor
  · rintro ⟨μ, hp, he, hr⟩
    simpa [value_zero] using hr
  · intro hr
    have hr0 : r = 0 := hr
    exact ⟨Measure.dirac 0, inferInstance, dirac_ergodic 0, by simp [hr0, value_zero]⟩

theorem pressure_zero (t : ℝ) : pressure t = 0 := by
  simp [pressure, pressureValues_exact]

theorem pressure_analytic (t : ℝ) : AnalyticAt ℝ pressure t := by
  have hp : pressure = fun _ => 0 := funext pressure_zero
  rw [hp]
  exact analyticAt_const

def Equilibrium (t : ℝ) (μ : Measure Ω) : Prop :=
  IsProbabilityMeasure μ ∧ Ergodic T μ ∧ value t μ = pressure t

theorem dirac_equilibrium (t : ℝ) (a : Ω) : Equilibrium t (Measure.dirac a) :=
  ⟨inferInstance, dirac_ergodic a, by simp [value_zero, pressure_zero]⟩

theorem diracs_distinct : (Measure.dirac (0 : Ω)) ≠ Measure.dirac 1 := by
  intro h
  have he := congrArg (fun μ : Measure Ω => μ {0}) h
  norm_num at he

theorem equilibrium_nonunique (t : ℝ) : ∃ μ ν : Measure Ω,
    Equilibrium t μ ∧ Equilibrium t ν ∧ μ ≠ ν :=
  ⟨Measure.dirac 0, Measure.dirac 1, dirac_equilibrium t 0, dirac_equilibrium t 1, diracs_distinct⟩

def PhaseTransition (t : ℝ) : Prop := ¬ AnalyticAt ℝ pressure t

theorem counterexample : (¬ ∃ t, PhaseTransition t) ∧
    ∀ t : ℝ, ∃ μ ν : Measure Ω, Equilibrium t μ ∧ Equilibrium t ν ∧ μ ≠ ν :=
  ⟨by rintro ⟨t, h⟩; exact h (pressure_analytic t), equilibrium_nonunique⟩

#print axioms atoms_partition
#print axioms refinement_identity
#print axioms entropy_rate_limit
#print axioms entropy_zero
#print axioms dirac_ergodic
#print axioms pressureValues_exact
#print axioms pressure_analytic
#print axioms equilibrium_nonunique
#print axioms counterexample
end Counterexample
