import Conjecture2802.Law
import Conjecture2802.Formula
import Mathlib.Data.EReal.Basic

noncomputable section
open MeasureTheory Set

namespace Conjecture2802

/-- The actual extended-real convex dual, with parameters restricted to the domain
where the exponential integral is finite. This avoids totalized nonintegrable CGFs. -/
def cramerRate (μ : Measure ℝ) (x : ℝ) : EReal :=
  ⨆ t : {t : ℝ // Integrable (fun y : ℝ => Real.exp (t*y)) μ},
    ((t.val*x - ProbabilityTheory.cgf id μ t.val : ℝ) : EReal)

theorem dualTerm_le_cramerRate (μ : Measure ℝ) (x t : ℝ)
    (ht : Integrable (fun y : ℝ => Real.exp (t*y)) μ) :
    ((t*x - ProbabilityTheory.cgf id μ t : ℝ) : EReal) ≤ cramerRate μ x :=
  le_iSup (fun u : {u : ℝ // Integrable (fun y : ℝ => Real.exp (u*y)) μ} =>
    ((u.val*x - ProbabilityTheory.cgf id μ u.val : ℝ) : EReal)) ⟨t, ht⟩

/-- The zero tilt gives zero, so the rate of every probability law is nonnegative. -/
theorem cramerRate_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    0 ≤ cramerRate μ x := by
  have ht : Integrable (fun y : ℝ => Real.exp (0*y)) μ := by simp
  simpa using dualTerm_le_cramerRate μ x 0 ht

/-- All tilts are integrable for this law; its dual is the unrestricted real-parameter supremum. -/
theorem cramerRate_fairBernoulli_eq_iSup (x : ℝ) :
    cramerRate fairBernoulli x =
      ⨆ t : ℝ, ((t*x - Real.log ((1 + Real.exp t)/2) : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    rw [cgf_fairBernoulli]
    exact le_iSup (fun u : ℝ => ((u*x - Real.log ((1 + Real.exp u)/2) : ℝ) : EReal)) t.val
  · apply iSup_le
    intro t
    simpa only [cgf_fairBernoulli] using
      dualTerm_le_cramerRate fairBernoulli x t (integrable_exp_fairBernoulli t)

/-- The actual supremum is finite and equals the derived formula at every interior point. -/
theorem cramerRate_fairBernoulli (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    cramerRate fairBernoulli x = (binaryRate x : EReal) := by
  rw [cramerRate_fairBernoulli_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro t
    exact EReal.coe_le_coe_iff.mpr (dual_objective_le_binaryRate x t hx hx1)
  · have h := le_iSup (fun t : ℝ => ((t*x - Real.log ((1 + Real.exp t)/2) : ℝ) : EReal))
      (optimalTilt x)
    rwa [dual_objective_optimalTilt x hx hx1] at h

/-- A negative tilt has moment generating function at most one. -/
theorem cgf_fairBernoulli_nonpos (t : ℝ) (ht : t ≤ 0) :
    ProbabilityTheory.cgf id fairBernoulli t ≤ 0 := by
  rw [cgf_fairBernoulli]
  apply Real.log_nonpos (by positivity)
  have he : Real.exp t ≤ 1 := by simpa using Real.exp_le_exp.mpr ht
  linarith

/-- At a nonnegative tilt, the cumulant generating function is at most the tilt. -/
theorem cgf_fairBernoulli_le_self (t : ℝ) (ht : 0 ≤ t) :
    ProbabilityTheory.cgf id fairBernoulli t ≤ t := by
  rw [cgf_fairBernoulli]
  have he : 1 ≤ Real.exp t := by simpa using Real.exp_le_exp.mpr ht
  calc
    Real.log ((1 + Real.exp t)/2) ≤ Real.log (Real.exp t) :=
      (Real.log_le_log_iff (by positivity) (Real.exp_pos t)).2 (by linarith)
    _ = t := Real.log_exp t

/-- To the left of zero, negative tilts make the actual dual unbounded above. -/
theorem cramerRate_fairBernoulli_eq_top_of_neg (x : ℝ) (hx : x < 0) :
    cramerRate fairBernoulli x = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).2
  intro M
  let t : ℝ := (|M| + 1) / x
  have ht : t ≤ 0 := (div_neg_of_pos_of_neg (by positivity) hx).le
  have htx : t*x = |M|+1 := by dsimp [t]; field_simp [hx.ne]
  have hc := cgf_fairBernoulli_nonpos t ht
  have hM : M < t*x - ProbabilityTheory.cgf id fairBernoulli t := by
    have habs := le_abs_self M
    linarith
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hM)
    (dualTerm_le_cramerRate fairBernoulli x t (integrable_exp_fairBernoulli t))

/-- To the right of one, positive tilts make the actual dual unbounded above. -/
theorem cramerRate_fairBernoulli_eq_top_of_one_lt (x : ℝ) (hx : 1 < x) :
    cramerRate fairBernoulli x = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).2
  intro M
  let t : ℝ := (|M| + 1) / (x-1)
  have ht : 0 ≤ t := (div_pos (by positivity) (sub_pos.mpr hx)).le
  have htx : t*(x-1) = |M|+1 := by dsimp [t]; field_simp [(sub_pos.mpr hx).ne']
  have hc := cgf_fairBernoulli_le_self t ht
  have hM : M < t*x - ProbabilityTheory.cgf id fairBernoulli t := by
    have habs := le_abs_self M
    nlinarith
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hM)
    (dualTerm_le_cramerRate fairBernoulli x t (integrable_exp_fairBernoulli t))

/-- For a probability law the rate is nonnegative; this is its finite effective domain. -/
def effectiveDomain (μ : Measure ℝ) : Set ℝ := {x | cramerRate μ x < ⊤}

theorem Ioo_subset_effectiveDomain_fairBernoulli :
    Set.Ioo 0 1 ⊆ effectiveDomain fairBernoulli := by
  intro x hx
  change cramerRate fairBernoulli x < ⊤
  rw [cramerRate_fairBernoulli x hx.1 hx.2]
  exact EReal.coe_lt_top _

theorem effectiveDomain_fairBernoulli_subset_Icc :
    effectiveDomain fairBernoulli ⊆ Set.Icc 0 1 := by
  intro x hx
  change cramerRate fairBernoulli x < ⊤ at hx
  constructor
  · by_contra h
    rw [cramerRate_fairBernoulli_eq_top_of_neg x (lt_of_not_ge h)] at hx
    exact (lt_irrefl _ hx)
  · by_contra h
    rw [cramerRate_fairBernoulli_eq_top_of_one_lt x (lt_of_not_ge h)] at hx
    exact (lt_irrefl _ hx)

/-- The interior is exact without assigning any unproved endpoint values. -/
theorem interior_effectiveDomain_fairBernoulli :
    interior (effectiveDomain fairBernoulli) = Set.Ioo 0 1 := by
  apply le_antisymm
  · simpa only [interior_Icc] using interior_mono effectiveDomain_fairBernoulli_subset_Icc
  · simpa only [isOpen_Ioo.interior_eq] using
      interior_mono Ioo_subset_effectiveDomain_fairBernoulli

end Conjecture2802
