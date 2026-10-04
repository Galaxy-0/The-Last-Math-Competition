import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology
namespace InertialThreshold

def scalarMap (a : ℝ) : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ
@[simp] theorem scalarMap_apply (a x : ℝ) : scalarMap a x = a*x := rfl

def A : ℝ →L[ℝ] ℝ := scalarMap 9
def T : ℝ →L[ℝ] ℝ := scalarMap (1/10)
def inverseT : ℝ →L[ℝ] ℝ := scalarMap 10

def MonotoneOperator (R : ℝ → Set ℝ) : Prop :=
  ∀ x y u v, u ∈ R x → v ∈ R y → 0 ≤ (u-v)*(x-y)
def MaximalMonotone (R : ℝ → Set ℝ) : Prop :=
  MonotoneOperator R ∧ ∀ B, MonotoneOperator B →
    (∀ x, R x ⊆ B x) → ∀ x, B x ⊆ R x
def graphOperator (L : ℝ →L[ℝ] ℝ) (x : ℝ) : Set ℝ := {L x}

theorem A_monotone : MonotoneOperator (graphOperator A) := by
  intro x y u v hu hv
  have hu0 : u = 9*x := hu
  have hv0 : v = 9*y := hv
  rw [hu0,hv0]
  nlinarith [sq_nonneg (x-y)]

theorem A_maximal : MaximalMonotone (graphOperator A) := by
  refine ⟨A_monotone, ?_⟩
  intro B hB hAB x u hu
  let y : ℝ := x + (u-9*x)/18
  have hv : 9*y ∈ B y := hAB y rfl
  have he := hB x y u (9*y) hu hv
  dsimp [y] at he
  have heq : u = 9*x := by nlinarith [sq_nonneg (u-9*x)]
  exact heq

theorem zero_unique (x : ℝ) : A x = 0 ↔ x = 0 := by simp [A]

theorem resolvent_equation (p x : ℝ) : x + A x = p ↔ x = T p := by
  simp [A,T]
  constructor <;> intro h <;> linarith

theorem genuine_inverse :
    T.comp inverseT = ContinuousLinearMap.id ℝ ℝ ∧
    inverseT.comp T = ContinuousLinearMap.id ℝ ℝ := by
  constructor <;> apply ContinuousLinearMap.ext <;> intro x <;>
    norm_num [T,inverseT,scalarMap,smul_eq_mul] <;> ring

theorem shifted_is_inverse : ContinuousLinearMap.id ℝ ℝ + A = inverseT := by
  apply ContinuousLinearMap.ext
  intro x
  simp [A,inverseT,scalarMap,smul_eq_mul]
  ring

theorem scalarMap_norm (a : ℝ) : ‖scalarMap a‖ = |a| := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a)
    intro x
    simp [Real.norm_eq_abs, abs_mul]
  · have h := ContinuousLinearMap.le_opNorm (scalarMap a) 1
    simpa [Real.norm_eq_abs] using h

def proposedBound : ℝ := ‖inverseT‖⁻¹

theorem bound_value : proposedBound = 1/10 := by
  norm_num [proposedBound,inverseT,scalarMap_norm]

/-- Weighted state: first coordinate x_k, second coordinate x_{k-1}/2. -/
def step (β : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (T ((1+β)*z.1 - 2*β*z.2), z.1/2)
def state (β a b : ℝ) (n : ℕ) : ℝ × ℝ := (step β)^[n] (a,b/2)
def orbit (β a b : ℝ) (n : ℕ) : ℝ := (state β a b n).1

theorem state_succ (β a b : ℝ) (n : ℕ) :
    state β a b (n+1) = step β (state β a b n) := by
  exact Function.iterate_succ_apply' _ _ _

theorem initial_value (β a b : ℝ) : orbit β a b 0 = a := rfl

theorem first_update (β a b : ℝ) : orbit β a b 1 = T (a+β*(a-b)) := by
  rw [orbit,state_succ]
  dsimp [step,state]
  congr 1
  ring

theorem actual_inertial_recurrence (β a b : ℝ) (n : ℕ) :
    orbit β a b (n+2) = T (orbit β a b (n+1) + β*(orbit β a b (n+1)-orbit β a b n)) := by
  change (state β a b ((n+1)+1)).1 = _
  rw [state_succ]
  change T ((1+β)*(state β a b (n+1)).1 - 2*β*(state β a b (n+1)).2) = _
  have hs : (state β a b (n+1)).2 = orbit β a b n / 2 := by rw [state_succ]; rfl
  rw [hs]
  change T ((1+β)*orbit β a b (n+1) - 2*β*(orbit β a b n/2)) = _
  congr 1
  ring

theorem half_step_formula (z : ℝ × ℝ) :
    step (1/2) z = ((3/20)*z.1 - (1/10)*z.2, z.1/2) := by
  apply Prod.ext
  · dsimp [step,T,scalarMap]; ring
  · rfl

theorem half_step_bound (z : ℝ × ℝ) : ‖step (1/2) z‖ ≤ (1/2)*‖z‖ := by
  rw [half_step_formula, Prod.norm_def]
  apply max_le
  · have ht := norm_sub_le ((3/20 : ℝ)*z.1) ((1/10 : ℝ)*z.2)
    rw [norm_mul,norm_mul] at ht
    norm_num at ht
    have h1 : |z.1| ≤ ‖z‖ := by exact le_max_left _ _
    have h2 : |z.2| ≤ ‖z‖ := by exact le_max_right _ _
    change |(3/20)*z.1 - (1/10)*z.2| ≤ (1/2)*‖z‖
    nlinarith [norm_nonneg z]
  · rw [norm_div]
    norm_num
    have h1 : |z.1| ≤ ‖z‖ := by exact le_max_left _ _
    linarith

theorem state_geometric (a b : ℝ) (n : ℕ) :
    ‖state (1/2) a b n‖ ≤ (1/2 : ℝ)^n * ‖(a,b/2)‖ := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    rw [state_succ]
    calc
      _ ≤ (1/2)*‖state (1/2) a b n‖ := half_step_bound _
      _ ≤ (1/2)*((1/2 : ℝ)^n * ‖(a,b/2)‖) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1/2 : ℝ)^(n+1) * ‖(a,b/2)‖ := by rw [pow_succ]; ring

theorem state_converges (a b : ℝ) : Tendsto (state (1/2) a b) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (state_geometric a b)
  have hp : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using hp.mul_const ‖(a,b/2)‖

theorem all_initials_converge (a b : ℝ) : Tendsto (orbit (1/2) a b) atTop (𝓝 0) := by
  exact (continuous_fst.tendsto (0 : ℝ × ℝ)).comp (state_converges a b)

/-- Admissibility requires convergence for every pair of initial values. -/
def admissible : Set ℝ := {β | ∀ a b : ℝ, Tendsto (orbit β a b) atTop (𝓝 0)}

theorem half_admissible : (1/2 : ℝ) ∈ admissible := all_initials_converge

theorem bound_not_upper : proposedBound ∉ upperBounds admissible := by
  intro h
  have hh := h half_admissible
  rw [bound_value] at hh
  norm_num at hh

theorem claimed_supremum_false : ¬ IsLUB admissible proposedBound := by
  intro h
  exact bound_not_upper h.1

#print axioms A_maximal
#print axioms zero_unique
#print axioms resolvent_equation
#print axioms genuine_inverse
#print axioms bound_value
#print axioms first_update
#print axioms actual_inertial_recurrence
#print axioms state_geometric
#print axioms all_initials_converge
#print axioms claimed_supremum_false
end InertialThreshold
