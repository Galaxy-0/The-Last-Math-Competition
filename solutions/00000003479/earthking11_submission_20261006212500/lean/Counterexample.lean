import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace HarmoniousCounterexample

/-- The problem's definition, using sums of natural-number color labels,
not the different, standard unordered-color-pair definition. -/
structure HarmoniousColoring {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) where
  proper : G.Coloring (Fin k)
  sums_unique : ∀ a b c d, G.Adj a b → G.Adj c d →
    (proper a).val + (proper b).val = (proper c).val + (proper d).val →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A base larger than the sum of two squared vertex indices. -/
def sidonBase (n : ℕ) : ℕ := 2 * n ^ 2 + 1

/-- Sidon labels: the base records the sum of indices, while the low-order
square sum distinguishes the unordered pair. -/
def sidonLabel {n : ℕ} (v : Fin n) : ℕ :=
  sidonBase n * v.val + v.val ^ 2

/-- Equal sums of two distinct Sidon labels determine the unordered pair. -/
theorem sidonPair_unique {n : ℕ} (a b c d : Fin n)
    (hs : sidonLabel a + sidonLabel b = sidonLabel c + sidonLabel d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hnBase : 0 < sidonBase n := by
    dsimp [sidonBase]
    positivity
  have ha2 : a.val ^ 2 < n ^ 2 := Nat.pow_lt_pow_left a.isLt (by decide)
  have hb2 : b.val ^ 2 < n ^ 2 := Nat.pow_lt_pow_left b.isLt (by decide)
  have hc2 : c.val ^ 2 < n ^ 2 := Nat.pow_lt_pow_left c.isLt (by decide)
  have hd2 : d.val ^ 2 < n ^ 2 := Nat.pow_lt_pow_left d.isLt (by decide)
  have hr : a.val ^ 2 + b.val ^ 2 < sidonBase n := by
    dsimp [sidonBase]
    omega
  have hq : c.val ^ 2 + d.val ^ 2 < sidonBase n := by
    dsimp [sidonBase]
    omega
  have hs' : sidonBase n * (a.val + b.val) + (a.val ^ 2 + b.val ^ 2) =
      sidonBase n * (c.val + d.val) + (c.val ^ 2 + d.val ^ 2) := by
    dsimp [sidonLabel] at hs
    nlinarith [hs]
  have hrem : a.val ^ 2 + b.val ^ 2 = c.val ^ 2 + d.val ^ 2 := by
    have hmod := congrArg (fun x : ℕ => x % sidonBase n) hs'
    have hleft :
        (sidonBase n * (a.val + b.val) + (a.val ^ 2 + b.val ^ 2)) % sidonBase n =
          a.val ^ 2 + b.val ^ 2 := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
    have hright :
        (sidonBase n * (c.val + d.val) + (c.val ^ 2 + d.val ^ 2)) % sidonBase n =
          c.val ^ 2 + d.val ^ 2 := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hq]
    rw [hleft, hright] at hmod
    exact hmod
  have hsumMul : sidonBase n * (a.val + b.val) = sidonBase n * (c.val + d.val) := by
    have h := hs'
    rw [hrem] at h
    exact Nat.add_right_cancel h
  have hsum : a.val + b.val = c.val + d.val :=
    Nat.mul_left_cancel hnBase hsumMul
  have hsumZ : (a.val : ℤ) + b.val = c.val + d.val := by exact_mod_cast hsum
  have hremZ : (a.val : ℤ) ^ 2 + b.val ^ 2 = c.val ^ 2 + d.val ^ 2 := by
    exact_mod_cast hrem
  have hprodZ : (a.val : ℤ) * b.val = c.val * d.val := by
    nlinarith [congrArg (fun x : ℤ => x ^ 2) hsumZ]
  have hfactor :
      ((a.val : ℤ) - c.val) * ((a.val : ℤ) - d.val) = 0 := by
    nlinarith [hsumZ, hremZ, hprodZ]
  rcases mul_eq_zero.mp hfactor with hac | had
  · have hacZ : (a.val : ℤ) = c.val := sub_eq_zero.mp hac
    have hacNat : a.val = c.val := by exact_mod_cast hacZ
    left
    constructor
    · exact Fin.ext hacNat
    · have hbd : b.val = d.val := by omega
      exact Fin.ext hbd
  · have hadZ : (a.val : ℤ) = d.val := sub_eq_zero.mp had
    have hadNat : a.val = d.val := by exact_mod_cast hadZ
    right
    constructor
    · exact Fin.ext hadNat
    · have hbc : b.val = c.val := by omega
      exact Fin.ext hbc

/-- Every finite simple graph has a harmonious coloring. The Sidon labels are
strictly increasing, and all endpoint sums are unique even for the complete
graph; a larger finite color range contains all labels. -/
theorem harmoniousColoring_exists {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ k, Nonempty (HarmoniousColoring G k) := by
  let k := sidonBase n * n + n ^ 2 + 1
  have hbase : 0 < sidonBase n := by
    dsimp [sidonBase]
    positivity
  have hlabel (v : Fin n) : sidonLabel v < k := by
    have hm := Nat.mul_lt_mul_of_pos_left v.isLt hbase
    have hp := Nat.pow_lt_pow_left v.isLt (by decide : 2 ≠ 0)
    dsimp [k, sidonLabel]
    omega
  refine ⟨k, ⟨⟨SimpleGraph.Coloring.mk
      (fun v => (⟨sidonLabel v, hlabel v⟩ : Fin k)) ?_, ?_⟩⟩⟩
  · intro a b hab
    have hne : a ≠ b := hab.ne
    have hval : sidonLabel a ≠ sidonLabel b := by
      intro heq
      by_cases hlt : a.val < b.val
      · have hmul := Nat.mul_lt_mul_of_pos_left hlt hbase
        have hp := Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0)
        have : sidonLabel a < sidonLabel b := by
          dsimp [sidonLabel]
          omega
        omega
      · have hlt' : b.val < a.val := by omega
        have hmul := Nat.mul_lt_mul_of_pos_left hlt' hbase
        have hp := Nat.pow_lt_pow_left hlt' (by decide : 2 ≠ 0)
        have : sidonLabel b < sidonLabel a := by
          dsimp [sidonLabel]
          omega
        omega
    intro heq
    apply hval
    exact congrArg Fin.val heq
  · intro a b c d hab hcd hsum
    have hlabels : sidonLabel a + sidonLabel b = sidonLabel c + sidonLabel d := by
      exact_mod_cast hsum
    exact sidonPair_unique a b c d hlabels

/-- A probability law with every distinct edge present with probability one.
This characterizes the p=1 boundary of the usual independent-edge G(n,p).
No independence hypothesis is necessary at this deterministic boundary. -/
def GnpOneLaw {n : ℕ} (μ : PMF (SimpleGraph (Fin n))) : Prop :=
  ∀ a b, a ≠ b → μ.toOuterMeasure {G | G.Adj a b} = 1

noncomputable def gnpOne (n : ℕ) : PMF (SimpleGraph (Fin n)) :=
  PMF.pure (SimpleGraph.completeGraph (Fin n))

theorem gnpOne_has_edge_law (n : ℕ) : GnpOneLaw (gnpOne n) := by
  intro a b hab
  change (PMF.pure (SimpleGraph.completeGraph (Fin n))).toOuterMeasure
    {G | G.Adj a b} = 1
  rw [PMF.toOuterMeasure_pure_apply]
  simp [hab]

theorem support_is_complete {n : ℕ} {μ : PMF (SimpleGraph (Fin n))}
    (hμ : GnpOneLaw μ) {G : SimpleGraph (Fin n)} (hG : G ∈ μ.support) :
    G = SimpleGraph.completeGraph (Fin n) := by
  ext a b
  constructor
  · intro hab
    exact hab.ne
  · intro hab
    exact (μ.toOuterMeasure_apply_eq_one_iff {G | G.Adj a b}).mp
      (hμ a b hab) hG

theorem complete_coloring_lower_bound {n k : ℕ}
    (C : HarmoniousColoring (SimpleGraph.completeGraph (Fin n)) k) : n ≤ k := by
  have hi : Function.Injective C.proper := by
    intro a b hab
    by_contra hne
    exact C.proper.valid hne hab
  simpa using Fintype.card_le_of_injective C.proper hi

def upperEvent (n : ℕ) : Set (SimpleGraph (Fin n)) :=
  {G | ∃ k, Nonempty (HarmoniousColoring G k) ∧ (k : ℝ) ≤ 2 * Real.sqrt n}

theorem complete_not_upperEvent {n : ℕ} (hn : 4 < n) :
    SimpleGraph.completeGraph (Fin n) ∉ upperEvent n := by
  rintro ⟨k, ⟨C⟩, hk⟩
  have hnk : (n : ℝ) ≤ k := by exact_mod_cast complete_coloring_lower_bound C
  have hn4 : (4 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  nlinarith

theorem upper_probability_zero {n : ℕ} (hn : 4 < n)
    {μ : PMF (SimpleGraph (Fin n))} (hμ : GnpOneLaw μ) :
    μ.toOuterMeasure (upperEvent n) = 0 := by
  apply (μ.toOuterMeasure_apply_eq_zero_iff _).mpr
  rw [Set.disjoint_left]
  intro G hG hEvent
  rw [support_is_complete hμ hG] at hEvent
  exact complete_not_upperEvent hn hEvent

noncomputable def upperProbability (n : ℕ) : ℝ :=
  ((gnpOne n).toOuterMeasure (upperEvent n)).toReal

theorem upperProbability_eventually_zero :
    ∀ᶠ n in atTop, upperProbability n = 0 := by
  filter_upwards [eventually_gt_atTop 4] with n hn
  simp [upperProbability, upper_probability_zero hn (gnpOne_has_edge_law n)]

theorem upperProbability_tends_zero : Tendsto upperProbability atTop (nhds 0) := by
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)).congr'
    (Filter.EventuallyEq.symm upperProbability_eventually_zero)

/-- Asymptotic disproof: the required upper concentration event has
probability eventually exactly zero, rather than tending to one. -/
theorem concentration_at_one_is_false :
    ¬ Tendsto upperProbability atTop (nhds 1) := by
  intro h
  have : (0 : ℝ) = 1 := tendsto_nhds_unique upperProbability_tends_zero h
  norm_num at this

/-- p=1 lies in the stipulated range log(n)/n ≤ p for all positive n. -/
theorem one_is_admissible {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) / n ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hnpos).mpr
  have h := Real.log_le_sub_one_of_pos hnpos
  linarith

/-- Attainment and minimality, rather than an assumed arithmetic surrogate. -/
def IsHarmoniousNumber {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  Nonempty (HarmoniousColoring G k) ∧
    ∀ j, Nonempty (HarmoniousColoring G j) → k ≤ j

/-- The minimum harmonious color count, defined by well-ordering of `ℕ`. -/
noncomputable def harmoniousNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  by
    classical
    exact Nat.find (harmoniousColoring_exists G)

theorem harmoniousNumber_is_minimum {n : ℕ} (G : SimpleGraph (Fin n)) :
    IsHarmoniousNumber G (harmoniousNumber G) := by
  classical
  constructor
  · exact Nat.find_spec (harmoniousColoring_exists G)
  · intro j hj
    exact Nat.find_min' (harmoniousColoring_exists G) hj

def concentrationEvent (n : ℕ) (ε : ℝ) : Set (SimpleGraph (Fin n)) :=
  {G | ∃ k, IsHarmoniousNumber G k ∧ |(k : ℝ) / Real.sqrt n - 1| < ε}

/-- The existential minimum witness in the event is exactly the explicitly
defined minimum harmonious number. -/
theorem concentrationEvent_iff_harmoniousNumber {n : ℕ}
    (G : SimpleGraph (Fin n)) (ε : ℝ) :
    G ∈ concentrationEvent n ε ↔
      |(harmoniousNumber G : ℝ) / Real.sqrt n - 1| < ε := by
  constructor
  · rintro ⟨k, hk, hε⟩
    have hmin := harmoniousNumber_is_minimum G
    have hkn : k ≤ harmoniousNumber G := hk.2 _ hmin.1
    have hnk : harmoniousNumber G ≤ k := hmin.2 _ hk.1
    have heq : k = harmoniousNumber G := Nat.le_antisymm hkn hnk
    simpa [heq] using hε
  · intro hε
    exact ⟨harmoniousNumber G, harmoniousNumber_is_minimum G, hε⟩

theorem concentrationEvent_one_subset {n : ℕ} (hn : 0 < n) :
    concentrationEvent n 1 ⊆ upperEvent n := by
  rintro G ⟨k, hk, hband⟩
  refine ⟨k, hk.1, ?_⟩
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hfrac : (k : ℝ) / Real.sqrt n < 2 := by
    have := (abs_lt.mp hband).2
    linarith
  exact le_of_lt ((div_lt_iff₀ hs).mp hfrac)

theorem concentration_probability_zero {n : ℕ} (hn : 4 < n)
    {μ : PMF (SimpleGraph (Fin n))} (hμ : GnpOneLaw μ) :
    μ.toOuterMeasure (concentrationEvent n 1) = 0 := by
  apply le_antisymm _ zero_le
  calc
    μ.toOuterMeasure (concentrationEvent n 1) ≤ μ.toOuterMeasure (upperEvent n) :=
      μ.toOuterMeasure.mono (concentrationEvent_one_subset (by omega))
    _ = 0 := upper_probability_zero hn hμ

noncomputable def concentrationProbability (n : ℕ) (ε : ℝ) : ℝ :=
  ((gnpOne n).toOuterMeasure (concentrationEvent n ε)).toReal

/-- Constant-one relative concentration at the deterministic p=1 boundary.
The asserted uniform law necessarily includes this boundary statement. -/
def ConcentrationLawAtOne : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => concentrationProbability n ε) atTop (nhds 1)

theorem conjecture_boundary_is_false : ¬ ConcentrationLawAtOne := by
  intro h
  have hz : Tendsto (fun n => concentrationProbability n 1) atTop (nhds (0 : ℝ)) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)).congr'
    filter_upwards [eventually_gt_atTop 4] with n hn
    simp [concentrationProbability,
      concentration_probability_zero hn (gnpOne_has_edge_law n)]
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hz (h 1 (by norm_num))
  norm_num at this

#print axioms concentration_at_one_is_false
#print axioms upper_probability_zero
#print axioms one_is_admissible
#print axioms harmoniousColoring_exists
#print axioms harmoniousNumber_is_minimum
#print axioms concentrationEvent_iff_harmoniousNumber
#print axioms conjecture_boundary_is_false

end HarmoniousCounterexample
