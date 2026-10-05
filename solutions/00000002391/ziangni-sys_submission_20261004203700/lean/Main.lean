import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

noncomputable section
open Set Metric MeasureTheory Filter Topology
namespace AtomicDoubling

def mu : Measure ℝ := Measure.dirac (-1) + Measure.dirac 1
def S : Set ℝ := {-1,1}
def mass (x r : ℝ) : ℝ := (mu (ball x r)).toReal

theorem mass_formula (x r : ℝ) : mass x r =
    (if dist (-1) x < r then 1 else 0) + (if dist 1 x < r then 1 else 0) := by
  simp only [mass,mu,Measure.add_apply,Measure.dirac_apply' _ measurableSet_ball,
    Set.indicator_apply,mem_ball]
  by_cases h1 : dist (-1) x < r
  <;> by_cases h2 : dist 1 x < r
  <;> simp [Set.indicator,mem_ball,h1,h2] <;> norm_num

theorem mass_bounds (x r : ℝ) : 0 ≤ mass x r ∧ mass x r ≤ 2 := by
  rw [mass_formula]; split_ifs <;> norm_num

def support : Set ℝ := {x | ∀ r : ℝ, 0 < r → 0 < mass x r}

theorem support_eq : support = S := by
  ext x
  constructor
  · intro h
    by_contra hn
    have h1 : x ≠ -1 := by intro hx; exact hn (by simp [S,hx])
    have h2 : x ≠ 1 := by intro hx; exact hn (by simp [S,hx])
    let r := min (dist (-1) x) (dist 1 x) / 2
    have hd1 : 0 < dist (-1) x := dist_pos.mpr (Ne.symm h1)
    have hd2 : 0 < dist 1 x := dist_pos.mpr (Ne.symm h2)
    have hr : 0 < r := by dsimp [r]; positivity
    have hh := h r hr
    rw [mass_formula] at hh
    have a := min_le_left (dist (-1) x) (dist 1 x)
    have b := min_le_right (dist (-1) x) (dist 1 x)
    have nr1 : ¬ dist (-1) x < r := by dsimp [r]; linarith
    have nr2 : ¬ dist 1 x < r := by dsimp [r]; linarith
    simp [nr1,nr2] at hh
  · intro h r hr
    simp only [S,mem_insert_iff,mem_singleton_iff] at h
    rcases h with rfl | rfl <;> rw [mass_formula] <;> simp [hr] <;> split_ifs <;> norm_num

def Doubling (C : ℝ) : Prop := ∀ x ∈ support, ∀ r : ℝ, 0 < r →
  mass x (2*r) ≤ C * mass x r

theorem doubling_two : Doubling 2 := by
  intro x hx r hr
  have hlo : 1 ≤ mass x r := by
    rw [support_eq] at hx
    simp only [S,mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> rw [mass_formula] <;> simp [hr] <;> split_ifs <;> norm_num
  have hi := (mass_bounds x (2*r)).2
  linarith

theorem minimal_constant (C : ℝ) (h : Doubling C) : 2 ≤ C := by
  have hh := h (-1) (by rw [support_eq]; simp [S]) (3/2) (by norm_num)
  norm_num [mass_formula,Real.dist_eq] at hh
  exact hh

def Covers (s : Finset ℝ) (r : ℝ) : Prop := ∀ x ∈ S, ∃ c ∈ s, dist x c < r

theorem two_cover (r : ℝ) (hr : 0 < r) : Covers {-1,1} r := by
  intro x hx
  exact ⟨x,by simpa [S] using hx,by simpa using hr⟩

def coverNumber (r : ℝ) : ℕ := sInf {n | ∃ s : Finset ℝ, s.card=n ∧ Covers s r}

theorem actual_cover_number (r : ℝ) (hr : 0 < r) (hsmall : r ≤ 1) : coverNumber r = 2 := by
  have upper : (2:ℕ) ∈ {n | ∃ s : Finset ℝ, s.card=n ∧ Covers s r} :=
    ⟨{-1,1},by norm_num,two_cover r hr⟩
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) upper
  · apply le_csInf ⟨2,upper⟩
    rintro n ⟨s,hs,hcover⟩
    obtain ⟨a,ha,hda⟩ := hcover (-1) (by simp [S])
    obtain ⟨b,hb,hdb⟩ := hcover 1 (by simp [S])
    have hab : a ≠ b := by
      intro heq
      subst b
      have htri := dist_triangle (-1:ℝ) a 1
      rw [dist_comm a 1] at htri
      rw [show dist (-1:ℝ) 1 = 2 by norm_num [Real.dist_eq]] at htri
      linarith
    have hc : 1 < s.card := Finset.one_lt_card.mpr ⟨a,ha,b,hb,hab⟩
    omega

-- The standard logarithmic covering exponent, with epsilon=exp(-t).
def exponent (t : ℝ) : ℝ := Real.log (coverNumber (Real.exp (-t)) : ℝ) / t
def upperBoxDimension : ℝ := limsup exponent atTop
def lowerBoxDimension : ℝ := liminf exponent atTop

theorem exponent_limit : Tendsto exponent atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => Real.log 2 / t) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  have hs : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  simp [exponent,actual_cover_number _ (Real.exp_pos _) hs]

theorem upper_dimension_zero : upperBoxDimension = 0 := exponent_limit.limsup_eq
theorem lower_dimension_zero : lowerBoxDimension = 0 := exponent_limit.liminf_eq

def localSet (x : ℝ) : Set ℝ := S ∩ ball x 1

theorem local_singleton (x : ℝ) (hx : x ∈ S) : localSet x = {x} := by
  simp only [S,mem_insert_iff,mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> ext y
  all_goals
    simp only [localSet,S,mem_inter_iff,mem_insert_iff,mem_singleton_iff,mem_ball]
    constructor
    · rintro ⟨h,hball⟩
      rcases h with rfl | rfl <;> norm_num [Real.dist_eq] at *
    · intro h
      subst y
      norm_num [Real.dist_eq]

def localCoverNumber (x r : ℝ) : ℕ := sInf {n | ∃ s : Finset ℝ,
  s.card=n ∧ ∀ y ∈ localSet x, ∃ c ∈ s, dist y c < r}

theorem local_cover_one (x r : ℝ) (hx : x ∈ S) (hr : 0 < r) :
    localCoverNumber x r = 1 := by
  have upper : (1:ℕ) ∈ {n | ∃ s : Finset ℝ,
      s.card=n ∧ ∀ y ∈ localSet x, ∃ c ∈ s, dist y c < r} := by
    refine ⟨{x},by simp,?_⟩
    intro y hy
    rw [local_singleton x hx] at hy
    have hyx : y=x := hy
    subst y
    exact ⟨x,by simp,by simpa using hr⟩
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) upper
  · apply le_csInf ⟨1,upper⟩
    rintro n ⟨s,hs,hcover⟩
    obtain ⟨c,hc,_⟩ := hcover x (by rw [local_singleton x hx]; simp)
    have hcard : 0 < s.card := Finset.card_pos.mpr ⟨c,hc⟩
    omega

def localBoxDimension (x : ℝ) : ℝ :=
  limsup (fun t : ℝ => Real.log (localCoverNumber x (Real.exp (-t)) : ℝ) / t) atTop

theorem local_dimension_zero (x : ℝ) (hx : x ∈ S) : localBoxDimension x = 0 := by
  simp [localBoxDimension,local_cover_one x _ hx (Real.exp_pos _)]

theorem claimed_bound_fails : ¬ Real.log 2 / Real.log 2 ≤ upperBoxDimension := by
  rw [upper_dimension_zero,div_self (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))]
  norm_num

end AtomicDoubling
#print axioms AtomicDoubling.support_eq
#print axioms AtomicDoubling.doubling_two
#print axioms AtomicDoubling.minimal_constant
#print axioms AtomicDoubling.actual_cover_number
#print axioms AtomicDoubling.upper_dimension_zero
#print axioms AtomicDoubling.local_dimension_zero
#print axioms AtomicDoubling.claimed_bound_fails
