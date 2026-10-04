import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter
open scoped Topology
noncomputable section
namespace StochasticSplitting

def A (_ : ℝ) : Set ℝ := {1}
def graph : Set (ℝ × ℝ) := {p | p.2 ∈ A p.1}
def MonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, 0 ≤ inner (𝕜 := ℝ) (p.1-q.1) (p.2-q.2)
def MaximalMonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  MonotoneGraph G ∧ ∀ H, MonotoneGraph H → G ⊆ H → H ⊆ G

theorem maximal : MaximalMonotoneGraph graph := by
  have hm : MonotoneGraph graph := by
    intro p hp q hq
    have hp' : p.2 = 1 := hp
    have hq' : q.2 = 1 := hq
    simp [hp', hq']
  refine ⟨hm, ?_⟩
  intro H hH hsub p hp
  have hl := hH p hp (p.1-1, 1) (hsub (by simp [graph, A]))
  have hr := hH p hp (p.1+1, 1) (hsub (by simp [graph, A]))
  simp only [RCLike.inner_apply, conj_trivial] at hl hr
  change p.2 = 1
  nlinarith

theorem lipschitz : LipschitzWith 1 (fun _ : ℝ => (1 : ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_self, NNReal.coe_one, one_mul]
  exact dist_nonneg

def ResolventEquation (x y : ℝ) : Prop := ∃ a ∈ A y, x = y+a
def resolvent (x : ℝ) : ℝ := x-1
theorem actual_resolvent (x y : ℝ) :
    ResolventEquation x y ↔ y = resolvent x := by
  constructor
  · rintro ⟨a, ha, hx⟩
    have ha' : a = 1 := ha
    dsimp [resolvent]
    linarith
  · intro hy
    refine ⟨1, rfl, ?_⟩
    dsimp [resolvent] at hy
    linarith

def orbit (x : ℝ) (n : ℕ) : ℝ := resolvent^[n] x
def error (_ : ℕ) : ℝ := 0
def tolerance (_ : ℕ) : ℝ := 0

-- Standard additive-error inexact proximal inclusion, with unit proximal parameter.
def InexactPPA (u : ℕ → ℝ) (e eps : ℕ → ℝ) : Prop :=
  ∀ n, (∃ a ∈ A (u (n+1)), u n-u (n+1)-e n = a) ∧
    ‖e n‖ ≤ eps n

theorem actual_iterates (x : ℝ) (n : ℕ) : orbit x n = x-(n : ℝ) := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    have hs : orbit x (n+1) = resolvent (orbit x n) :=
      Function.iterate_succ_apply' resolvent n x
    rw [hs, resolvent, ih]
    push_cast
    ring

theorem genuine_inexact_inclusion (x : ℝ) :
    InexactPPA (orbit x) error tolerance := by
  intro n
  constructor
  · refine ⟨1, rfl, ?_⟩
    rw [actual_iterates, actual_iterates]
    dsimp [error]
    push_cast
    ring
  · simp [error, tolerance]

theorem genuine_resolvent_steps (x : ℝ) (n : ℕ) :
    ResolventEquation (orbit x n) (orbit x (n+1)) := by
  rw [actual_resolvent]
  exact Function.iterate_succ_apply' resolvent n x

theorem summable_tolerances :
    (∀ n, 0 ≤ tolerance n) ∧ Summable tolerance ∧
    (∑' n, tolerance n) = 0 := by
  refine ⟨fun _ => le_rfl, ?_, ?_⟩
  · exact summable_zero
  · exact tsum_zero

theorem no_zero : ¬ ∃ x, (0 : ℝ) ∈ A x := by simp [A]

theorem no_strong_limit (x a : ℝ) : ¬ Tendsto (orbit x) atTop (𝓝 a) := by
  intro h
  have hs := h.comp (tendsto_add_atTop_nat 1)
  have hd : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have he : (fun n => orbit x (n+1)-orbit x n) = fun _ => (-1 : ℝ) := by
      funext n
      rw [actual_iterates, actual_iterates]
      push_cast
      ring
    simpa [Function.comp_def, he] using hs.sub h
  have hz : (-1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hd
  norm_num at hz

theorem counterexample :
    MaximalMonotoneGraph graph ∧
    LipschitzWith 1 (fun _ : ℝ => (1 : ℝ)) ∧
    (∀ x y, ResolventEquation x y ↔ y = resolvent x) ∧
    ((∀ n, 0 ≤ tolerance n) ∧ Summable tolerance ∧ (∑' n, tolerance n) = 0) ∧
    (∀ x, InexactPPA (orbit x) error tolerance) ∧
    (∀ x n, ResolventEquation (orbit x n) (orbit x (n+1))) ∧
    (∀ x a, ¬ Tendsto (orbit x) atTop (𝓝 a)) ∧
    (¬ ∃ x, (0 : ℝ) ∈ A x) :=
  ⟨maximal, lipschitz, actual_resolvent, summable_tolerances,
    genuine_inexact_inclusion, genuine_resolvent_steps, no_strong_limit, no_zero⟩

open MeasureTheory ProbabilityTheory
def μ : Measure Unit := Measure.dirac ()
instance : IsProbabilityMeasure μ := by unfold μ; infer_instance
def filtration : Filtration ℕ (inferInstance : MeasurableSpace Unit) := ⊥
def noise (_ : ℕ) (_ : Unit) : ℝ := 0
def trajectory (x : ℝ) (n : ℕ) (_ : Unit) : ℝ := orbit x n

-- Full martingale-difference hypotheses: adapted, integrable and conditionally centered.
def MartingaleDifference : Prop :=
  (∀ n, StronglyMeasurable[filtration n] (noise n)) ∧
  (∀ n, Integrable (noise n) μ) ∧
  (∀ n, μ[noise (n+1)|filtration n] = (0 : Unit → ℝ))

theorem actual_martingale_difference : MartingaleDifference := by
  refine ⟨fun _ => stronglyMeasurable_const, ?_, ?_⟩
  · intro n
    exact integrable_zero Unit ℝ μ
  · intro n
    exact condExp_zero

theorem trajectories_adapted (x : ℝ) (n : ℕ) :
    StronglyMeasurable[filtration n] (trajectory x n) := stronglyMeasurable_const

theorem actual_stochastic_step (x : ℝ) (n : ℕ) (ω : Unit) :
    trajectory x (n+1) ω = resolvent (trajectory x n ω)+noise n ω := by
  simpa [trajectory, noise] using Function.iterate_succ_apply' resolvent n x

theorem square_summability :
    (∀ ω : Unit, Summable (fun n => ‖noise n ω‖^2)) ∧
    (∀ ω : Unit, (∑' n, ‖noise n ω‖^2) = 0) ∧
    Summable (fun n => ∫ ω, ‖noise n ω‖^2 ∂μ) ∧
    (∑' n, ∫ ω, ‖noise n ω‖^2 ∂μ) = 0 := by
  simp only [noise, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero]
  exact ⟨fun _ => summable_zero, fun _ => tsum_zero, summable_zero, tsum_zero⟩

theorem actual_expected_trajectory (x : ℝ) (n : ℕ) :
    (∫ ω, trajectory x n ω ∂μ) = x-(n : ℝ) := by
  simp [μ, trajectory, integral_dirac, actual_iterates]

def convergenceEvent (x : ℝ) : Set Unit :=
  {ω | ∃ a : ℝ, Tendsto (fun n => trajectory x n ω) atTop (𝓝 a)}

theorem empty_convergence_event (x : ℝ) : convergenceEvent x = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro ω ⟨a,ha⟩
  exact no_strong_limit x a ha

theorem event_measure_zero (x : ℝ) : μ (convergenceEvent x) = 0 := by
  rw [empty_convergence_event, measure_empty]

theorem not_almost_sure_convergence (x : ℝ) :
    ¬ ∀ᵐ ω ∂μ, ∃ a : ℝ, Tendsto (fun n => trajectory x n ω) atTop (𝓝 a) := by
  intro h
  have hf : ∀ᵐ ω ∂μ, False := h.mono (fun ω ha => by
    rcases ha with ⟨a,ha⟩
    exact no_strong_limit x a ha)
  have hz : μ = 0 := by simpa using hf
  have hu : μ Set.univ = 1 := measure_univ
  rw [hz] at hu
  norm_num at hu

theorem stochastic_counterexample :
    MaximalMonotoneGraph graph ∧
    MartingaleDifference ∧
    ((∀ ω : Unit, Summable (fun n => ‖noise n ω‖^2)) ∧
      (∀ ω : Unit, (∑' n, ‖noise n ω‖^2) = 0) ∧
      Summable (fun n => ∫ ω, ‖noise n ω‖^2 ∂μ) ∧
      (∑' n, ∫ ω, ‖noise n ω‖^2 ∂μ) = 0) ∧
    (∀ x n ω, trajectory x (n+1) ω = resolvent (trajectory x n ω)+noise n ω) ∧
    (∀ x, μ (convergenceEvent x) = 0) ∧
    (∀ x, ¬ ∀ᵐ ω ∂μ, ∃ a : ℝ,
      Tendsto (fun n => trajectory x n ω) atTop (𝓝 a)) ∧
    (¬ ∃ x, (0 : ℝ) ∈ A x) :=
  ⟨maximal, actual_martingale_difference, square_summability, actual_stochastic_step,
    event_measure_zero, not_almost_sure_convergence, no_zero⟩

#print axioms maximal
#print axioms actual_resolvent
#print axioms actual_iterates
#print axioms actual_martingale_difference
#print axioms trajectories_adapted
#print axioms actual_stochastic_step
#print axioms square_summability
#print axioms actual_expected_trajectory
#print axioms empty_convergence_event
#print axioms not_almost_sure_convergence
#print axioms stochastic_counterexample
end StochasticSplitting
