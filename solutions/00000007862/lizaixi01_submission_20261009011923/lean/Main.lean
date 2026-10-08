import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter Topology

namespace LLLSingleton

noncomputable section

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  sum_mass : ∑ x, mass x = 1

def prob {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (A : Finset Ω) : ℝ :=
  ∑ x ∈ A, μ.mass x

def bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteLaw (Fin 2) where
  mass x := if x = 0 then p else 1-p
  mass_nonneg x := by split_ifs <;> linarith
  sum_mass := by simp [Fin.sum_univ_two]

def badEvent : Finset (Fin 2) := {0}

theorem bad_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    prob (bernoulli p hp0 hp1) badEvent = p := by
  simp [prob, bernoulli, badEvent]

def singletonBound (E p : ℝ) : ℝ :=
  (∑ _i : Fin 1, p) / ((1-E*p) * ∏ _i : Fin 1, (1-p))

theorem singleton_bound_reduce (E p : ℝ) :
    singletonBound E p = p / ((1-E*p)*(1-p)) := by
  simp [singletonBound]

theorem bound_from_actual_event (E p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ _i : Fin 1, prob (bernoulli p hp0 hp1) badEvent) /
      ((1-E*prob (bernoulli p hp0 hp1) badEvent) *
        ∏ _i : Fin 1, (1-prob (bernoulli p hp0 hp1) badEvent)) =
      singletonBound E p := by
  simp [bad_probability, singletonBound]

theorem critical_less_one {E : ℝ} (hE : 1 < E) : 1/E < 1 := by
  apply (div_lt_one (by linarith : 0 < E)).2
  exact hE

theorem denominator_ne_zero {E p : ℝ} (hE : 1 < E) (hp : p < 1/E) :
    1-E*p ≠ 0 := by
  have hEp : E*p < 1 := by
    have := (lt_div_iff₀ (by linarith : 0 < E)).1 hp
    nlinarith
  linarith

theorem scaled_square_reduce {E p : ℝ} (hE : 1 < E) (hp : p < 1/E) :
    (1-E*p)^2 * singletonBound E p = (1-E*p)*p/(1-p) := by
  rw [singleton_bound_reduce]
  have h1 : 1-E*p ≠ 0 := denominator_ne_zero hE hp
  have h2 : 1-p ≠ 0 := by
    have := critical_less_one hE
    linarith
  field_simp

theorem scaled_square_tendsto_zero {E : ℝ} (hE : 1 < E) :
    Tendsto (fun p : ℝ => (1-E*p)^2 * singletonBound E p)
      (𝓝[<] (1/E)) (𝓝 0) := by
  have hE0 : E ≠ 0 := by linarith
  have hden : (1 : ℝ)-1/E ≠ 0 := by
    have := critical_less_one hE
    linarith
  have hcont : Tendsto (fun p : ℝ => (1-E*p)*p/(1-p)) (𝓝 (1/E)) (𝓝 0) := by
    have h : Tendsto (fun p : ℝ => (1-E*p)*p/(1-p)) (𝓝 (1/E))
        (𝓝 (((1-E*(1/E))*(1/E))/(1-1/E))) :=
      ((tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_id)).mul
        tendsto_id).div (tendsto_const_nhds.sub tendsto_id) hden
    simpa [hE0] using h
  apply (hcont.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (scaled_square_reduce hE hp).symm

def pn (E : ℝ) (n : ℕ) : ℝ := (1-1/((n : ℝ)+2))/E

theorem pn_admissible {E : ℝ} (hE : 1 < E) (n : ℕ) :
    0 < pn E n ∧ pn E n < 1 ∧ E*pn E n < 1 := by
  have hEpos : 0 < E := by linarith
  have hn : (1 : ℝ) < (n : ℝ)+2 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ)+2 := by positivity
  have hinvpos : 0 < 1/((n : ℝ)+2) := by positivity
  have hinvlt : 1/((n : ℝ)+2) < 1 := (div_lt_one hnpos).2 hn
  have hp0 : 0 < pn E n := by unfold pn; exact div_pos (by linarith) hEpos
  have hpcrit : pn E n < 1/E := by
    unfold pn
    exact (div_lt_div_iff_of_pos_right hEpos).2 (by linarith)
  have hp1 : pn E n < 1 := hpcrit.trans (critical_less_one hE)
  have hEp : E*pn E n < 1 := by
    have := (lt_div_iff₀ hEpos).1 hpcrit
    nlinarith
  exact ⟨hp0, hp1, hEp⟩

theorem pn_actual_bad_probability {E : ℝ} (hE : 1 < E) (n : ℕ) :
    prob (bernoulli (pn E n) (pn_admissible hE n).1.le
      (pn_admissible hE n).2.1.le) badEvent = pn E n :=
  bad_probability _ _ _

theorem pn_lt_critical {E : ℝ} (hE : 1 < E) (n : ℕ) : pn E n < 1/E := by
  have hp := (pn_admissible hE n).2.2
  apply (lt_div_iff₀ (by linarith : 0 < E)).2
  nlinarith

theorem pn_tendsto_critical (E : ℝ) : Tendsto (pn E) atTop (𝓝 (1/E)) := by
  have hi0 : Tendsto (fun n : ℕ => 1 / (((n+2 : ℕ) : ℝ))) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).2 tendsto_one_div_atTop_nhds_zero_nat
  have hi : Tendsto (fun n : ℕ => 1/((n : ℝ)+2)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hi0
  have h : Tendsto (pn E) atTop (𝓝 ((1-0)/E)) :=
    (tendsto_const_nhds.sub hi).div_const E
  simpa using h

theorem pn_tendsto_critical_below {E : ℝ} (hE : 1 < E) :
    Tendsto (pn E) atTop (𝓝[<] (1/E)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨pn_tendsto_critical E, Eventually.of_forall (pn_lt_critical hE)⟩

theorem pn_scaled_square_tendsto_zero {E : ℝ} (hE : 1 < E) :
    Tendsto (fun n : ℕ => (1-E*pn E n)^2 * singletonBound E (pn E n))
      atTop (𝓝 0) :=
  (scaled_square_tendsto_zero hE).comp (pn_tendsto_critical_below hE)

theorem quadratic_coefficient_zero {E c : ℝ} (hE : 1 < E)
    (hc : Tendsto (fun n : ℕ => (1-E*pn E n)^2 * singletonBound E (pn E n))
      atTop (𝓝 c)) : c = 0 :=
  tendsto_nhds_unique hc (pn_scaled_square_tendsto_zero hE)

theorem no_positive_quadratic_normalized_lower_bound {E c : ℝ}
    (hE : 1 < E) (hc : 0 < c) :
    ¬ ∀ᶠ n : ℕ in atTop,
      c ≤ (1-E*pn E n)^2 * singletonBound E (pn E n) := by
  intro hlarge
  have hsmall := (pn_scaled_square_tendsto_zero hE).eventually (gt_mem_nhds hc)
  obtain ⟨n, hn, hsn⟩ := (hlarge.and hsmall).exists
  exact (not_lt_of_ge hn) hsn

theorem scaled_linear_reduce {E p : ℝ} (hE : 1 < E) (hp : p < 1/E) :
    (1-E*p) * singletonBound E p = p/(1-p) := by
  rw [singleton_bound_reduce]
  have h1 : 1-E*p ≠ 0 := denominator_ne_zero hE hp
  have h2 : 1-p ≠ 0 := by
    have := critical_less_one hE
    linarith
  field_simp

theorem scaled_linear_tendsto {E : ℝ} (hE : 1 < E) :
    Tendsto (fun p : ℝ => (1-E*p) * singletonBound E p)
      (𝓝[<] (1/E)) (𝓝 (1/(E-1))) := by
  have hE0 : E ≠ 0 := by linarith
  have hden : (1 : ℝ)-1/E ≠ 0 := by
    have := critical_less_one hE
    linarith
  have hEm1 : E-1 ≠ 0 := by linarith
  have hval : (1/E)/(1-1/E) = 1/(E-1) := by
    field_simp
  have hcont : Tendsto (fun p : ℝ => p/(1-p)) (𝓝 (1/E)) (𝓝 (1/(E-1))) := by
    have h : Tendsto (fun p : ℝ => p/(1-p)) (𝓝 (1/E)) (𝓝 ((1/E)/(1-1/E))) :=
      tendsto_id.div (tendsto_const_nhds.sub tendsto_id) hden
    rwa [hval] at h
  apply (hcont.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (scaled_linear_reduce hE hp).symm

theorem linear_coefficient_positive {E : ℝ} (hE : 1 < E) : 0 < 1/(E-1) := by
  exact div_pos zero_lt_one (by linarith)

theorem e_gt_one : 1 < Real.exp 1 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem original_scaled_square_tendsto_zero :
    Tendsto (fun p : ℝ => (1-Real.exp 1*p)^2 * singletonBound (Real.exp 1) p)
      (𝓝[<] (1/Real.exp 1)) (𝓝 0) :=
  scaled_square_tendsto_zero e_gt_one

/-! Concrete variable-event model. Its sole variable has two outcomes. -/

abbrev Outcome := Fin 2
abbrev Variable := Fin 1
abbrev Event := Fin 1

def variableValue (ω : Outcome) (_v : Variable) : Fin 2 := ω
def eventFamily (_i : Event) : Finset Outcome := badEvent
def eventVariables (_i : Event) : Finset Variable := {0}

theorem event_depends_on_its_variables (i : Event) (ω ω' : Outcome)
    (h : ∀ v ∈ eventVariables i, variableValue ω v = variableValue ω' v) :
    ω ∈ eventFamily i ↔ ω' ∈ eventFamily i := by
  have hω : ω = ω' := h 0 (by simp [eventVariables])
  rw [hω]

/-- Distinct events are adjacent exactly when their variable supports overlap. -/
def dependencyAdj (i j : Event) : Prop :=
  i ≠ j ∧ ¬ Disjoint (eventVariables i) (eventVariables j)

theorem dependencyAdj_false (i j : Event) : ¬ dependencyAdj i j := by
  have hij : i = j := Subsingleton.elim _ _
  simp [dependencyAdj, hij]

theorem dependencyAdj_symmetric : ∀ i j, dependencyAdj i j → dependencyAdj j i := by
  intro i j hij
  exact False.elim (dependencyAdj_false i j hij)

theorem dependencyAdj_irreflexive : ∀ i, ¬ dependencyAdj i i := by
  intro i
  exact dependencyAdj_false i i

def dependencyDegree (i : Event) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => dependencyAdj i j)).card

theorem dependencyDegree_zero (i : Event) : dependencyDegree i = 0 := by
  classical
  simp [dependencyDegree, dependencyAdj_false]

def instanceLaw (n : ℕ) : FiniteLaw Outcome :=
  bernoulli (pn (Real.exp 1) n) (pn_admissible e_gt_one n).1.le
    (pn_admissible e_gt_one n).2.1.le

def eventProbability (n : ℕ) (i : Event) : ℝ :=
  prob (instanceLaw n) (eventFamily i)

def pStar (n : ℕ) : ℝ := eventProbability n 0

theorem eventProbability_eq (n : ℕ) (i : Event) :
    eventProbability n i = pn (Real.exp 1) n := by
  exact bad_probability _ _ _

theorem pStar_eq (n : ℕ) : pStar n = pn (Real.exp 1) n :=
  eventProbability_eq n 0

theorem pStar_largest (n : ℕ) :
    IsGreatest (Set.range (eventProbability n)) (pStar n) := by
  constructor
  · exact ⟨0, rfl⟩
  · rintro _ ⟨i, rfl⟩
    rw [eventProbability_eq, pStar_eq]

theorem distinct_event_independence (n : ℕ) (i j : Event) (hij : i ≠ j) :
    prob (instanceLaw n) (eventFamily i ∩ eventFamily j) =
      eventProbability n i * eventProbability n j := by
  exact False.elim (hij (Subsingleton.elim _ _))

theorem instance_admissible (n : ℕ) :
    0 < pStar n ∧ pStar n < 1 ∧
      Real.exp 1 * pStar n * ((dependencyDegree 0 : ℝ)+1) < 1 := by
  simpa only [pStar_eq, dependencyDegree_zero, Nat.cast_zero, zero_add, mul_one]
    using pn_admissible e_gt_one n

/-- The exact displayed source bound, using the actual event probabilities and their maximum. -/
def actualBound (n : ℕ) : ℝ :=
  (∑ i : Event, eventProbability n i) /
    ((1-Real.exp 1*pStar n) * ∏ i : Event, (1-eventProbability n i))

theorem actualBound_eq_bridge (n : ℕ) :
    actualBound n = singletonBound (Real.exp 1) (pn (Real.exp 1) n) := by
  simp [actualBound, eventProbability_eq, pStar_eq, singletonBound]

theorem actualBound_eq_formula (n : ℕ) :
    actualBound n = pStar n / ((1-Real.exp 1*pStar n)*(1-pStar n)) := by
  rw [actualBound_eq_bridge, singleton_bound_reduce, pStar_eq]

def gap (n : ℕ) : ℝ := 1-Real.exp 1*pStar n

theorem gap_pos (n : ℕ) : 0 < gap n := by
  have h := (pn_admissible e_gt_one n).2.2
  simp only [gap, pStar_eq]
  linarith

theorem actualBound_pos (n : ℕ) : 0 < actualBound n := by
  rw [actualBound_eq_formula]
  have hp0 := (instance_admissible n).1
  have hp1 := (instance_admissible n).2.1
  exact div_pos hp0 (mul_pos (gap_pos n) (by linarith))

theorem criticalProduct_tendsto_one :
    Tendsto (fun n : ℕ => Real.exp 1*pStar n) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => Real.exp 1*pn (Real.exp 1) n)
      atTop (𝓝 (Real.exp 1*(1/Real.exp 1))) :=
    tendsto_const_nhds.mul (pn_tendsto_critical (Real.exp 1))
  simpa [pStar_eq, (Real.exp_pos 1).ne'] using h

theorem actual_scaled_square_tendsto_zero :
    Tendsto (fun n : ℕ => (gap n)^2 * actualBound n) atTop (𝓝 0) := by
  simpa only [gap, pStar_eq, actualBound_eq_bridge]
    using pn_scaled_square_tendsto_zero e_gt_one

theorem actual_scaled_linear_tendsto :
    Tendsto (fun n : ℕ => gap n * actualBound n) atTop
      (𝓝 (1/(Real.exp 1-1))) := by
  simpa only [gap, pStar_eq, actualBound_eq_bridge, Function.comp_def] using
    (scaled_linear_tendsto e_gt_one).comp (pn_tendsto_critical_below e_gt_one)

theorem actual_no_positive_quadratic_lower_bound (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ n : ℕ in atTop, c/(gap n)^2 ≤ actualBound n := by
  intro hlarge
  apply no_positive_quadratic_normalized_lower_bound e_gt_one hc
  filter_upwards [hlarge] with n hn
  have hn' : c ≤ actualBound n * (gap n)^2 :=
    (div_le_iff₀ (pow_pos (gap_pos n) 2)).1 hn
  simpa only [gap, pStar_eq, actualBound_eq_bridge, mul_comm] using hn'

/-- Premise-free certificate for a genuine admissible singleton family and the literal bound. -/
theorem literal_bound_counterexample :
    (∀ n : ℕ, (∑ ω : Outcome, (instanceLaw n).mass ω) = 1) ∧
    (∀ n : ℕ, ∀ ω : Outcome, 0 ≤ (instanceLaw n).mass ω) ∧
    (∀ n : ℕ, ∀ i : Event, eventProbability n i = pn (Real.exp 1) n) ∧
    (∀ n : ℕ, IsGreatest (Set.range (eventProbability n)) (pStar n)) ∧
    (∀ n : ℕ, actualBound n =
      pStar n / ((1-Real.exp 1*pStar n)*(1-pStar n))) ∧
    (∀ i : Event, dependencyDegree i = 0) ∧
    (∀ n : ℕ, 0 < pStar n ∧ pStar n < 1 ∧
      Real.exp 1*pStar n*((dependencyDegree 0 : ℝ)+1) < 1) ∧
    (∀ n : ℕ, 0 < actualBound n) ∧
    Tendsto (fun n : ℕ => Real.exp 1*pStar n) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (gap n)^2*actualBound n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => gap n*actualBound n) atTop (𝓝 (1/(Real.exp 1-1))) ∧
    0 < 1/(Real.exp 1-1) ∧
    (∀ c : ℝ, 0 < c → ¬ ∀ᶠ n : ℕ in atTop, c/(gap n)^2 ≤ actualBound n) := by
  exact ⟨fun n => (instanceLaw n).sum_mass, fun n => (instanceLaw n).mass_nonneg,
    eventProbability_eq, pStar_largest, actualBound_eq_formula,
    dependencyDegree_zero, instance_admissible,
    actualBound_pos, criticalProduct_tendsto_one, actual_scaled_square_tendsto_zero,
    actual_scaled_linear_tendsto, linear_coefficient_positive e_gt_one,
    actual_no_positive_quadratic_lower_bound⟩

#print axioms literal_bound_counterexample

end

end LLLSingleton
