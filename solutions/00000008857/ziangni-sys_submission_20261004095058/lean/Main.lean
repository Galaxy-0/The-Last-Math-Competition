import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace MonotoneGameCounterexample

abbrev Player := Fin 2
abbrev Profile := EuclideanSpace ℝ Player

def cost (i : Player) (x : Profile) : ℝ := Real.exp (x i)
def changeAction (x : Profile) (i : Player) (a : ℝ) : Profile :=
  (WithLp.equiv 2 (Player → ℝ)).symm (Function.update x i a)
def pseudoGradient (x : Profile) : Profile :=
  (WithLp.equiv 2 (Player → ℝ)).symm (fun i => Real.exp (x i))
def IsNash (x : Profile) : Prop :=
  ∀ i : Player, ∀ a : ℝ, cost i x ≤ cost i (changeAction x i a)
def IsMonotoneGame : Prop :=
  ∀ x y : Profile, 0 ≤ @inner ℝ Profile _ (pseudoGradient x - pseudoGradient y) (x - y)

theorem strategy_geometry :
    (univ : Set ℝ).Nonempty ∧ IsClosed (univ : Set ℝ) ∧ Convex ℝ (univ : Set ℝ) ∧
    ∀ M : ℝ, ∃ a ∈ (univ : Set ℝ), M < a := by
  refine ⟨⟨0, mem_univ 0⟩, isClosed_univ, convex_univ, ?_⟩
  intro M
  exact ⟨M + 1, mem_univ _, by linarith⟩

@[simp] theorem cost_changeAction (x : Profile) (i : Player) (a : ℝ) :
    cost i (changeAction x i a) = Real.exp a := by
  simp [cost, changeAction]

theorem unilateral_derivative (x : Profile) (i : Player) (a : ℝ) :
    HasDerivAt (fun b => cost i (changeAction x i b)) (Real.exp a) a := by
  simpa using Real.hasDerivAt_exp a

theorem pseudoGradient_is_actual_derivative (x : Profile) (i : Player) :
    pseudoGradient x i = deriv (fun a => cost i (changeAction x i a)) (x i) := by
  exact (unilateral_derivative x i (x i)).deriv.symm

theorem cost_smooth (i : Player) : ContDiff ℝ ⊤ (cost i) := by
  exact Real.contDiff_exp.comp (EuclideanSpace.proj i : Profile →L[ℝ] ℝ).contDiff

theorem unilateral_strictConvex (x : Profile) (i : Player) :
    StrictConvexOn ℝ univ (fun a => cost i (changeAction x i a)) := by
  simpa using strictConvexOn_exp

theorem cost_positive (i : Player) (x : Profile) : 0 < cost i x := Real.exp_pos _

theorem component_monotone (a b : ℝ) :
    0 ≤ (Real.exp a - Real.exp b) * (a - b) := by
  rcases le_total b a with h | h
  · exact mul_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)) (sub_nonneg.mpr h)
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (Real.exp_le_exp.mpr h)) (sub_nonpos.mpr h)

theorem actual_game_monotone : IsMonotoneGame := by
  intro x y
  simp only [PiLp.inner_apply, PiLp.sub_apply, pseudoGradient, WithLp.equiv_symm_pi_apply,
    RCLike.inner_apply, conj_trivial]
  exact Finset.sum_nonneg (fun i _ => by simpa [mul_comm] using component_monotone (x i) (y i))

theorem profitable_deviation (x : Profile) (i : Player) :
    cost i (changeAction x i (x i - 1)) < cost i x := by
  rw [cost_changeAction]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem no_nash (x : Profile) : ¬ IsNash x := by
  intro h
  exact (not_lt_of_ge (h 0 (x 0 - 1))) (profitable_deviation x 0)

theorem nash_set_empty : {x : Profile | IsNash x} = ∅ := by
  ext x
  simp [no_nash]

theorem counterexample : IsMonotoneGame ∧ ¬ ∃ x : Profile, IsNash x := by
  exact ⟨actual_game_monotone, fun ⟨x, hx⟩ => no_nash x hx⟩

#print axioms unilateral_derivative
#print axioms pseudoGradient_is_actual_derivative
#print axioms cost_smooth
#print axioms unilateral_strictConvex
#print axioms actual_game_monotone
#print axioms profitable_deviation
#print axioms nash_set_empty
#print axioms counterexample
end MonotoneGameCounterexample
