import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology
namespace ThreeOperatorDomain

/-- On the real Hilbert space, its inner product is multiplication. -/
def MonotoneOperator (R : ℝ → Set ℝ) : Prop :=
  ∀ x y u v, u ∈ R x → v ∈ R y → 0 ≤ (u-v)*(x-y)
def MaximalMonotone (R : ℝ → Set ℝ) : Prop :=
  MonotoneOperator R ∧ ∀ Q, MonotoneOperator Q →
    (∀ x, R x ⊆ Q x) → ∀ x, Q x ⊆ R x

def A (_ : ℝ) : Set ℝ := {0}
def B (_ : ℝ) : Set ℝ := {0}
def C (_ : ℝ) : ℝ := 1

theorem A_monotone : MonotoneOperator A := by
  intro x y u v hu hv
  have hu0 : u = 0 := hu
  have hv0 : v = 0 := hv
  simp [hu0,hv0]

theorem A_maximal : MaximalMonotone A := by
  refine ⟨A_monotone, ?_⟩
  intro Q hQ hAQ x u hu
  have h0 : 0 ∈ Q (x+u) := hAQ (x+u) rfl
  have h := hQ x (x+u) u 0 hu h0
  have he : u = 0 := by nlinarith [sq_nonneg u]
  exact he

theorem B_maximal : MaximalMonotone B := A_maximal

def Cocoercive (β : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x y, β * ‖F x - F y‖^2 ≤ (F x - F y)*(x-y)

theorem C_cocoercive (β : ℝ) : Cocoercive β C := by
  intro x y
  simp [C]

theorem C_continuous : Continuous C := continuous_const

def zeros : Set ℝ := {x | ∃ u ∈ A x, ∃ v ∈ B x, u+v+C x=0}
theorem no_solution : zeros = ∅ := by
  ext x
  simp [zeros,A,B,C]

/-- The defining equation of the actual resolvent of a set-valued operator. -/
def ResolventRelation (R : ℝ → Set ℝ) (γ p x : ℝ) : Prop :=
  ∃ u ∈ R x, p = x + γ*u

def JA (_γ : ℝ) : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
def JB (_γ : ℝ) : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

theorem JA_resolvent (γ p x : ℝ) : ResolventRelation A γ p x ↔ x = JA γ p := by
  simp [ResolventRelation,A,JA,eq_comm]
theorem JB_resolvent (γ p x : ℝ) : ResolventRelation B γ p x ↔ x = JB γ p := by
  simp [ResolventRelation,B,JB,eq_comm]

/-- The two resolvent stages and the relaxed Davis--Yin update. -/
def stageB (γ z : ℝ) : ℝ := JB γ z
def stageA (γ z : ℝ) : ℝ := JA γ (2*stageB γ z-z-γ*C (stageB γ z))
def step (γ ρ z : ℝ) : ℝ := z+ρ*(stageA γ z-stageB γ z)
def orbit (γ ρ z : ℝ) (n : ℕ) : ℝ := (step γ ρ)^[n] z

theorem stages_exact (γ z : ℝ) : stageB γ z = z ∧ stageA γ z = z-γ := by
  constructor
  · rfl
  · simp [stageA,stageB,JA,JB,C]
    ring

theorem step_exact (γ ρ z : ℝ) : step γ ρ z = z-ρ*γ := by
  simp only [step,(stages_exact γ z).1,(stages_exact γ z).2]
  ring

theorem orbit_succ (γ ρ z : ℝ) (n : ℕ) :
    orbit γ ρ z (n+1) = step γ ρ (orbit γ ρ z n) :=
  Function.iterate_succ_apply' _ _ _

theorem orbit_exact (γ ρ z : ℝ) (n : ℕ) : orbit γ ρ z n = z-(n:ℝ)*(ρ*γ) := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    rw [orbit_succ,step_exact,ih]
    push_cast
    ring

/-- Weak convergence, tested against every continuous real linear functional. -/
def WeaklyConverges (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ f : ℝ →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f a))

theorem decrement_not_weak (u : ℕ → ℝ) (d : ℝ) (hd : d ≠ 0)
    (hstep : ∀ n, u (n+1)-u n = -d) (a : ℝ) : ¬ WeaklyConverges u a := by
  intro h
  have hi : Tendsto u atTop (𝓝 a) := by
    simpa using h (ContinuousLinearMap.id ℝ ℝ)
  have hs := hi.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun _ : ℕ => -d) atTop (𝓝 (0:ℝ)) := by
    simpa [Function.comp_def,hstep] using hs.sub hi
  have he : -d = 0 := tendsto_nhds_unique tendsto_const_nhds hdiff
  exact hd (neg_eq_zero.mp he)

theorem no_weak_limit (γ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (z a : ℝ) :
    ¬ WeaklyConverges (orbit γ ρ z) a := by
  apply decrement_not_weak _ (ρ*γ) (ne_of_gt (mul_pos hρ hγ))
  intro n
  rw [orbit_succ,step_exact]
  ring

theorem neither_shadow_converges (γ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ)
    (z a : ℝ) :
    ¬ WeaklyConverges (fun n => stageB γ (orbit γ ρ z n)) a ∧
    ¬ WeaklyConverges (fun n => stageA γ (orbit γ ρ z n)) a := by
  constructor
  · simpa only [(stages_exact _ _).1] using no_weak_limit γ ρ hγ hρ z a
  · apply decrement_not_weak _ (ρ*γ) (ne_of_gt (mul_pos hρ hγ))
    intro n
    simp only [(stages_exact _ _).2,orbit_succ,step_exact]
    ring

/-- Even existence of one converging initial orbit defines an empty positive-parameter domain. -/
def convergenceDomain : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ ∃ z a, WeaklyConverges (orbit p.1 p.2 z) a}

theorem convergence_domain_empty : convergenceDomain = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  obtain ⟨hγ,hρ,z,a,h⟩ := hp
  exact no_weak_limit p.1 p.2 hγ hρ z a h

theorem claimed_nonempty_false : ¬ convergenceDomain.Nonempty := by
  rw [convergence_domain_empty]
  exact Set.not_nonempty_empty

#print axioms A_maximal
#print axioms B_maximal
#print axioms C_cocoercive
#print axioms no_solution
#print axioms JA_resolvent
#print axioms JB_resolvent
#print axioms stages_exact
#print axioms orbit_exact
#print axioms no_weak_limit
#print axioms neither_shadow_converges
#print axioms convergence_domain_empty
#print axioms claimed_nonempty_false
end ThreeOperatorDomain
