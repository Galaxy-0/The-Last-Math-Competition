import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Conjecture1277

/-- Shannon entropy, in natural-logarithm units, of an actual finite probability mass function. -/
def entropy {α : Type*} [Fintype α] (p : PMF α) : ℝ :=
  ∑ a, Real.negMulLog ((p a).toReal)

/-- The joint distribution formed by drawing the first coordinate and then its conditional row. -/
def joint {α β : Type*} (p : PMF α) (K : α → PMF β) : PMF (α × β) :=
  p.bind (fun a => (K a).map (fun b => (a,b)))

theorem sum_prob {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), ← tsum_fintype, PMF.tsum_coe]
  simp

theorem joint_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (K : α → PMF β) (a : α) (b : β) :
    joint p K (a,b) = p a * K a b := by
  classical
  simp [joint, PMF.bind_apply, PMF.map_apply, tsum_fintype, Prod.mk_inj, ite_and]

theorem joint_map_fst {α β : Type*} (p : PMF α) (K : α → PMF β) :
    (joint p K).map Prod.fst = p := by
  simp only [joint, PMF.map_bind, PMF.map_comp]
  change (p.bind fun a => (K a).map (Function.const β a)) = p
  simp [PMF.map_const]

theorem joint_map_snd {α β : Type*} (p : PMF α) (K : α → PMF β) :
    (joint p K).map Prod.snd = p.bind K := by
  simp only [joint, PMF.map_bind, PMF.map_comp]
  change (p.bind fun a => (K a).map id) = p.bind K
  simp only [PMF.map_id]

/-- The Shannon chain rule, derived from the actual joint probabilities. -/
theorem entropy_joint {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (K : α → PMF β) :
    entropy (joint p K) = entropy p + ∑ a, (p a).toReal * entropy (K a) := by
  classical
  simp only [entropy, Fintype.sum_prod_type, joint_apply, ENNReal.toReal_mul,
    Real.negMulLog_mul, Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, sum_prob, one_mul]

/-- Expectations under a pushforward are expectations of the composed observable. -/
theorem expectation_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (g : β → ℝ) :
    ∑ b, ((p.map f) b).toReal * g b = ∑ a, (p a).toReal * g (f a) := by
  classical
  have hmap (b : β) : ((p.map f) b).toReal =
      ∑ a, if b = f a then (p a).toReal else 0 := by
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> rfl
    · intro a _
      split_ifs <;> simp [p.apply_ne_top]
  simp_rw [hmap, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

/-- Relabeling the finite outcome space by an equivalence leaves Shannon entropy unchanged. -/
theorem entropy_map_equiv {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (e : α ≃ β) : entropy (p.map e) = entropy p := by
  classical
  unfold entropy
  rw [← e.sum_comp (fun b => Real.negMulLog (((p.map e) b).toReal))]
  simp [PMF.map_apply, e.injective.eq_iff, tsum_fintype]

end Conjecture1277
