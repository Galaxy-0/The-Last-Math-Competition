import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter Topology MeasureTheory
open scoped ENNReal
noncomputable section
namespace Route2

def primesLE (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

def primeCDF (N : ℕ) (α t : ℝ) : ℝ :=
  (((primesLE N).filter fun (p : ℕ) => Int.fract (α * (p : ℝ)) < t).card : ℝ) / (N : ℝ)

def primeKS (N : ℕ) (α : ℝ) : ℝ :=
  sSup (Set.range fun t : Set.Icc (0 : ℝ) 1 => |primeCDF N α t - t|)

def scaledKS (N : ℕ) (α : ℝ) : ℝ := (N : ℝ) * primeKS N α

theorem primeCDF_one (N : ℕ) (α : ℝ) :
    primeCDF N α 1 = ((primesLE N).card : ℝ) / (N : ℝ) := by
  unfold primeCDF
  rw [Finset.filter_eq_self.mpr (fun _ _ => Int.fract_lt_one _)]

theorem primeCDF_nonneg (N : ℕ) (α t : ℝ) : 0 ≤ primeCDF N α t := by
  unfold primeCDF
  positivity

theorem primeCDF_le (N : ℕ) (α t : ℝ) :
    primeCDF N α t ≤ ((primesLE N).card : ℝ) / (N : ℝ) := by
  unfold primeCDF
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_filter_le (primesLE N) _

theorem ks_range_nonempty (N : ℕ) (α : ℝ) :
    (Set.range fun t : Set.Icc (0 : ℝ) 1 => |primeCDF N α t - t|).Nonempty := by
  exact ⟨_, ⟨⟨0, by norm_num⟩, rfl⟩⟩

theorem ks_range_bdd (N : ℕ) (α : ℝ) :
    BddAbove (Set.range fun t : Set.Icc (0 : ℝ) 1 => |primeCDF N α t - t|) := by
  refine ⟨((primesLE N).card : ℝ) / (N : ℝ) + 1, ?_⟩
  rintro y ⟨t, rfl⟩
  have h0 := primeCDF_nonneg N α t
  have h1 := primeCDF_le N α t
  have hc : 0 ≤ ((primesLE N).card : ℝ) / (N : ℝ) := by positivity
  rcases t.property with ⟨ht0, ht1⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem endpoint_lower (N : ℕ) (α : ℝ) :
    1 - ((primesLE N).card : ℝ) / (N : ℝ) ≤ primeKS N α := by
  have h := le_csSup (ks_range_bdd N α)
    (show |primeCDF N α 1 - 1| ∈
      Set.range (fun t : Set.Icc (0 : ℝ) 1 => |primeCDF N α t - t|) from
      ⟨⟨1, by norm_num⟩, rfl⟩)
  rw [primeCDF_one] at h
  unfold primeKS
  have h' := (neg_le_abs _).trans h
  simpa only [neg_sub] using h'

theorem scaled_endpoint_lower (N : ℕ) (hN : 0 < N) (α : ℝ) :
    (N : ℝ) - (primesLE N).card ≤ scaledKS N α := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := mul_le_mul_of_nonneg_left (endpoint_lower N α) hn.le
  have he : (N : ℝ) * (1 - ((primesLE N).card : ℝ) / N) = N - (primesLE N).card := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ (ne_of_gt hn)]
  rwa [he] at h

#print axioms scaled_endpoint_lower

theorem prime_card_bound (N : ℕ) (hN : 2 ≤ N) :
    (primesLE N).card ≤ N / 2 + 2 := by
  have h2 : Nat.primeCounting 2 = 1 := by
    decide
  have h := Nat.primeCounting_add_le (a := 2) (k := 2) (by decide) (by decide) (N - 2)
  have he : 2 + (N - 2) = N := by omega
  rw [he, h2] at h
  norm_num at h
  change (Nat.primesLE N).card ≤ _
  rw [Nat.primesLE_card_eq_primeCounting]
  omega

theorem uniform_escape_bound (N : ℕ) (hN : 2 ≤ N) (α : ℝ) :
    (N : ℝ) / 2 - 2 ≤ scaledKS N α := by
  have hs := scaled_endpoint_lower N (by omega) α
  have hc : ((primesLE N).card : ℝ) ≤ (N / 2 : ℕ) + 2 := by
    exact_mod_cast prime_card_bound N hN
  have hd : ((N / 2 : ℕ) : ℝ) * 2 ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N 2
  linarith

theorem measurable_fract_real : Measurable (Int.fract : ℝ → ℝ) := by
  intro s hs
  rw [Int.preimage_fract]
  exact MeasurableSet.iUnion fun z => measurable_id.sub_const _ (hs.inter measurableSet_Ico)

theorem finite_gap (s : Finset ℕ) (x : ℕ → ℝ) (t : ℝ) (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧ a < t ∧ ∀ p ∈ s, x p < t → x p < a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨t / 2, by linarith, by linarith, by simp⟩
  | @insert p s hp ih =>
    obtain ⟨a, ha0, hat, hax⟩ := ih
    by_cases hpt : x p < t
    · obtain ⟨b, hab, hbt⟩ := exists_between (max_lt hat hpt)
      refine ⟨b, ha0.trans (lt_of_le_of_lt (le_max_left _ _) hab), hbt, ?_⟩
      intro q hq hqt
      rcases Finset.mem_insert.mp hq with rfl | hqs
      · exact lt_of_le_of_lt (le_max_right _ _) hab
      · exact (hax q hqs hqt).trans (lt_of_le_of_lt (le_max_left _ _) hab)
    · refine ⟨a, ha0, hat, ?_⟩
      intro q hq hqt
      rcases Finset.mem_insert.mp hq with rfl | hqs
      · exact (hpt hqt).elim
      · exact hax q hqs hqt

abbrev RatUnit := {q : ℚ // 0 ≤ q ∧ q ≤ 1}

def rationalKS (N : ℕ) (α : ℝ) : ℝ :=
  sSup (Set.range fun q : RatUnit => |primeCDF N α (q : ℚ) - (q : ℚ)|)

theorem ratUnit_real_mem (q : RatUnit) : ((q : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact_mod_cast q.property.1
  · exact_mod_cast q.property.2

theorem rational_range_bdd (N : ℕ) (α : ℝ) :
    BddAbove (Set.range fun q : RatUnit => |primeCDF N α (q : ℚ) - (q : ℚ)|) := by
  apply (ks_range_bdd N α).mono
  rintro y ⟨q, rfl⟩
  exact ⟨⟨q, ratUnit_real_mem q⟩, rfl⟩

theorem rational_range_nonempty (N : ℕ) (α : ℝ) :
    (Set.range fun q : RatUnit => |primeCDF N α (q : ℚ) - (q : ℚ)|).Nonempty := by
  exact ⟨_, ⟨⟨0, by norm_num⟩, rfl⟩⟩

theorem primeCDF_zero (N : ℕ) (α : ℝ) : primeCDF N α 0 = 0 := by
  have he : ((primesLE N).filter fun (p : ℕ) => Int.fract (α * (p : ℝ)) < 0) = ∅ := by
    exact Finset.filter_eq_empty_iff.mpr (fun p _ => not_lt_of_ge (Int.fract_nonneg _))
  simp [primeCDF, he]

theorem rationalKS_nonneg (N : ℕ) (α : ℝ) : 0 ≤ rationalKS N α := by
  have h := le_csSup (rational_range_bdd N α)
    (show |primeCDF N α 0 - 0| ∈
      Set.range (fun q : RatUnit => |primeCDF N α (q : ℚ) - (q : ℚ)|) from
      ⟨⟨0, by norm_num⟩, by simp⟩)
  simpa [primeCDF_zero, rationalKS] using h

theorem primeKS_eq_rationalKS (N : ℕ) (α : ℝ) : primeKS N α = rationalKS N α := by
  classical
  apply le_antisymm
  · apply csSup_le (ks_range_nonempty N α)
    rintro y ⟨t, rfl⟩
    by_cases ht : (t : ℝ) = 0
    · simpa [ht, primeCDF_zero] using rationalKS_nonneg N α
    · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨a, ha0, hat, hax⟩ := finite_gap (primesLE N)
        (fun p => Int.fract (α * (p : ℝ))) t ht0
      obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn (max_lt hat (by linarith : (t : ℝ) - ε < t))
      have haq : a < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hqlo
      have heq : primeCDF N α (q : ℝ) = primeCDF N α t := by
        unfold primeCDF
        have hfilter : ((primesLE N).filter fun (p : ℕ) => Int.fract (α * (p : ℝ)) < q) =
            ((primesLE N).filter fun (p : ℕ) => Int.fract (α * (p : ℝ)) < t) := by
          apply Finset.filter_congr
          intro p hp
          constructor
          · intro h; exact h.trans hqhi
          · intro h; exact (hax p hp h).trans haq
        rw [hfilter]
      let qu : RatUnit := ⟨q, by
        constructor
        · exact_mod_cast (ha0.trans haq).le
        · exact_mod_cast (hqhi.trans_le t.property.2).le⟩
      have hsup : |primeCDF N α (q : ℝ) - q| ≤ rationalKS N α :=
        le_csSup (rational_range_bdd N α) ⟨qu, rfl⟩
      have htri := abs_sub_le (primeCDF N α t) (q : ℝ) (t : ℝ)
      rw [← heq] at htri
      have hab : |(q : ℝ) - t| = t - q := by
        rw [abs_of_neg (sub_neg.mpr hqhi)]; ring
      rw [hab] at htri
      have hclose : (t : ℝ) - q < ε := by
        have h := lt_of_le_of_lt (le_max_right a ((t : ℝ) - ε)) hqlo
        linarith
      rw [heq] at htri hsup
      linarith
  · apply csSup_le (rational_range_nonempty N α)
    rintro y ⟨q, rfl⟩
    exact le_csSup (ks_range_bdd N α) ⟨⟨q, ratUnit_real_mem q⟩, rfl⟩

theorem measurable_primeCDF (N : ℕ) (t : ℝ) : Measurable (fun α => primeCDF N α t) := by
  classical
  have hm : Measurable (fun α : ℝ =>
      ∑ p ∈ primesLE N, if Int.fract (α * (p : ℝ)) < t then (1 : ℝ) else 0) := by
    apply Finset.measurable_sum
    intro p hp
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_lt (measurable_fract_real.comp (measurable_id.mul_const _)) measurable_const
  simpa only [primeCDF, Finset.card_filter, Nat.cast_sum, apply_ite, Nat.cast_one, Nat.cast_zero]
    using hm.div_const (N : ℝ)

theorem measurable_primeKS (N : ℕ) : Measurable (primeKS N) := by
  have he : primeKS N = rationalKS N := funext (primeKS_eq_rationalKS N)
  rw [he]
  change Measurable (fun α => ⨆ q : RatUnit, |primeCDF N α (q : ℚ) - (q : ℚ)|)
  apply Measurable.iSup
  intro q
  have hf := (measurable_primeCDF N ((q : ℚ) : ℝ)).sub_const ((q : ℚ) : ℝ)
  simpa only [abs_eq_max_neg, Pi.neg_apply] using hf.max hf.neg

theorem measurable_scaledKS (N : ℕ) : Measurable (scaledKS N) :=
  (measurable_primeKS N).const_mul _

#print axioms uniform_escape_bound
#print axioms primeKS_eq_rationalKS
#print axioms measurable_scaledKS
#check measurable_primeKS
#check measurable_scaledKS


/-- The standard bounded continuous test definition, normalized to real tests in [0,1].
For probabilities, affine normalization recovers every bounded real continuous test.
The lower integral here is the nonnegative test integral, not a new convergence proxy. -/
def WeaklyConverges (laws : ℕ → Measure ℝ) (ν : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    Tendsto (fun N => ∫⁻ x, ENNReal.ofReal (f x) ∂laws N) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂ν))

def test (x : ℝ) : ℝ := 1 / (1 + |x|)
def testBound (N : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / ((N : ℝ) / 2 - 1))
def laws (μ : ℕ → Measure ℝ) (N : ℕ) : Measure ℝ := Measure.map (scaledKS N) (μ N)

theorem test_continuous : Continuous test := by
  unfold test
  apply continuous_const.div (continuous_const.add continuous_abs)
  intro x
  change 1 + |x| ≠ 0
  positivity

theorem test_normalized (x : ℝ) : 0 ≤ test x ∧ test x ≤ 1 := by
  unfold test
  have hp : 0 < 1 + |x| := by positivity
  constructor
  · positivity
  · apply (div_le_one hp).mpr
    linarith [abs_nonneg x]

theorem test_positive (x : ℝ) : 0 < ENNReal.ofReal (test x) := by
  apply ENNReal.ofReal_pos.mpr
  unfold test
  positivity

theorem test_integral_positive (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    0 < ∫⁻ x, ENNReal.ofReal (test x) ∂ν := by
  have hm : Measurable (fun x => ENNReal.ofReal (test x)) :=
    (ENNReal.continuous_ofReal.comp test_continuous).measurable
  rw [lintegral_pos_iff_support hm]
  have hs : Function.support (fun x => ENNReal.ofReal (test x)) = Set.univ := by
    ext x
    simp [Function.mem_support, ne_of_gt (test_positive x)]
  simp [hs]

theorem laws_probability (μ : ℕ → Measure ℝ) (hμ : ∀ N, IsProbabilityMeasure (μ N))
    (N : ℕ) : IsProbabilityMeasure (laws μ N) := by
  haveI : IsProbabilityMeasure (μ N) := hμ N
  exact Measure.isProbabilityMeasure_map (measurable_scaledKS N).aemeasurable

theorem test_transport (μ : ℕ → Measure ℝ) (N : ℕ) :
    (∫⁻ x, ENNReal.ofReal (test x) ∂laws μ N) =
      ∫⁻ α, ENNReal.ofReal (test (scaledKS N α)) ∂μ N := by
  exact lintegral_map (ENNReal.continuous_ofReal.comp test_continuous).measurable
    (measurable_scaledKS N)

theorem test_uniform_bound (N : ℕ) (α : ℝ) (hN : 4 ≤ N) :
    ENNReal.ofReal (test (scaledKS N α)) ≤ testBound N := by
  unfold test testBound
  apply ENNReal.ofReal_le_ofReal
  apply one_div_le_one_div_of_le
  · have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  · have hs := uniform_escape_bound N (by omega) α
    linarith [le_abs_self (scaledKS N α)]

theorem test_integral_bound (μ : ℕ → Measure ℝ) (hμ : ∀ N, IsProbabilityMeasure (μ N))
    (N : ℕ) (hN : 4 ≤ N) :
    (∫⁻ x, ENNReal.ofReal (test x) ∂laws μ N) ≤ testBound N := by
  haveI : IsProbabilityMeasure (μ N) := hμ N
  rw [test_transport]
  calc
    (∫⁻ α, ENNReal.ofReal (test (scaledKS N α)) ∂μ N) ≤ ∫⁻ _, testBound N ∂μ N :=
      lintegral_mono fun α => test_uniform_bound N α hN
    _ = testBound N := by simp [lintegral_const]

theorem testBound_tendsto_zero : Tendsto testBound atTop (𝓝 0) := by
  have hd : Tendsto (fun N : ℕ => (N : ℝ) / 2 - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
          (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop))
  have hi : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) / 2 - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hd
  change Tendsto (fun N : ℕ => ENNReal.ofReal (1 / ((N : ℝ) / 2 - 1))) atTop (𝓝 0)
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hi

theorem test_integrals_tendsto_zero (μ : ℕ → Measure ℝ)
    (hμ : ∀ N, IsProbabilityMeasure (μ N)) :
    Tendsto (fun N => ∫⁻ x, ENNReal.ofReal (test x) ∂laws μ N) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds testBound_tendsto_zero
  · exact Eventually.of_forall fun _ => bot_le
  · exact eventually_atTop.2 ⟨4, fun N hN => test_integral_bound μ hμ N hN⟩

/-- The actual statistic has no real probability weak limit under arbitrary N-dependent laws
of alpha. In particular, no real-valued Brownian bridge functional can be its weak limit. -/
theorem no_probability_weak_limit (μ : ℕ → Measure ℝ)
    (hμ : ∀ N, IsProbabilityMeasure (μ N)) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ¬ WeaklyConverges (laws μ) ν := by
  intro hw
  have ht := hw test test_continuous test_normalized
  have heq := tendsto_nhds_unique (test_integrals_tendsto_zero μ hμ) ht
  have hp := test_integral_positive ν
  rw [← heq] at hp
  exact (lt_irrefl _ hp)

#print no_probability_weak_limit
#print axioms no_probability_weak_limit
#print axioms measurable_scaledKS
#check laws_probability
#check test_transport
#check test_integrals_tendsto_zero
#check test_integral_positive
end Route2

