import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum

open Set
open scoped BigOperators
set_option linter.unusedSectionVars false
noncomputable section
namespace CongestionCounterexample
section General
variable {P R : Type*} [Fintype P] [Fintype R] [DecidableEq P] [DecidableEq R]
abbrev Profile (P R : Type*) := P → R
abbrev Latency (R : Type*) := R → ℕ → ℝ

def load (s : Profile P R) (r : R) : ℕ := (Finset.univ.filter fun i => s i = r).card
def cost (l : Latency R) (s : Profile P R) (i : P) : ℝ := l (s i) (load s (s i))
def socialCost (l : Latency R) (s : Profile P R) : ℝ := ∑ i, cost l s i
def Nash (l : Latency R) (s : Profile P R) : Prop :=
  ∀ i r, cost l s i ≤ cost l (Function.update s i r) i
def optimum (l : Latency R) : ℝ := sInf (Set.range (socialCost (P := P) l))
def equilibriumRatios (l : Latency R) : Set ℝ :=
  {v | ∃ s : Profile P R, Nash l s ∧ v = socialCost l s / optimum (P := P) l}
def poa (l : Latency R) : ℝ := sSup (equilibriumRatios (P := P) l)
def constantLatency (c : R → ℝ) : Latency R := fun r _ => c r
def Admissible (l : Latency R) : Prop := ∀ r, (∀ n, 0 < l r n) ∧ Monotone (l r)

theorem constant_admissible (c : R → ℝ) (hc : ∀ r, 0 < c r) :
    Admissible (constantLatency c) := by
  intro r
  exact ⟨fun _ => hc r, fun _ _ _ => le_rfl⟩

theorem nash_iff_minimal (c : R → ℝ) (s : Profile P R) :
    Nash (constantLatency c) s ↔ ∀ i r, c (s i) ≤ c r := by
  simp [Nash, cost, constantLatency]

theorem nash_social_minimum (c : R → ℝ) (s : Profile P R)
    (hs : Nash (constantLatency c) s) (t : Profile P R) :
    socialCost (constantLatency c) s ≤ socialCost (constantLatency c) t := by
  exact Finset.sum_le_sum fun i _ => (nash_iff_minimal c s).1 hs i (t i)

theorem optimum_at_nash (c : R → ℝ) (s : Profile P R)
    (hs : Nash (constantLatency c) s) :
    optimum (P := P) (constantLatency c) = socialCost (constantLatency c) s := by
  apply IsLeast.csInf_eq
  refine ⟨⟨s, rfl⟩, ?_⟩
  rintro v ⟨t, rfl⟩
  exact nash_social_minimum c s hs t

variable [Nonempty R]
theorem nash_exists (c : R → ℝ) : ∃ s : Profile P R, Nash (constantLatency c) s := by
  obtain ⟨r, hr⟩ := Finite.exists_min c
  refine ⟨fun _ => r, (nash_iff_minimal c _).2 ?_⟩
  exact fun _ t => hr t

variable [Nonempty P]
theorem social_positive (c : R → ℝ) (hc : ∀ r, 0 < c r) (s : Profile P R) :
    0 < socialCost (constantLatency c) s :=
  Finset.sum_pos (fun i _ => hc (s i)) Finset.univ_nonempty

theorem ratios_singleton (c : R → ℝ) (hc : ∀ r, 0 < c r) :
    equilibriumRatios (P := P) (constantLatency c) = {1} := by
  ext v
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [optimum_at_nash c s hs, div_self (ne_of_gt (social_positive c hc s))]
    exact mem_singleton 1
  · intro hv
    have hv1 : v = 1 := mem_singleton_iff.mp hv
    obtain ⟨s, hs⟩ := nash_exists (P := P) c
    refine ⟨s, hs, ?_⟩
    rw [optimum_at_nash c s hs, div_self (ne_of_gt (social_positive c hc s)), hv1]

theorem constant_poa (c : R → ℝ) (hc : ∀ r, 0 < c r) :
    poa (P := P) (constantLatency c) = 1 := by
  rw [poa, ratios_singleton c hc, csSup_singleton]

def constantClassValues : Set ℝ :=
  {v | ∃ c : R → ℝ, (∀ r, 0 < c r) ∧ poa (P := P) (constantLatency c) = v}

theorem class_values : constantClassValues (P := P) (R := R) = {1} := by
  ext v
  constructor
  · rintro ⟨c, hc, he⟩
    rw [constant_poa c hc] at he
    exact mem_singleton_iff.mpr he.symm
  · intro hv
    refine ⟨fun _ => 1, fun _ => by norm_num, ?_⟩
    rw [constant_poa _ (fun _ => by norm_num)]
    exact (mem_singleton_iff.mp hv).symm

theorem tight_class_bound : sSup (constantClassValues (P := P) (R := R)) = 1 := by
  rw [class_values, csSup_singleton]
end General

abbrev Player := Fin 2
abbrev Resource := Fin 2
def unitLatency : Latency Resource := constantLatency (fun _ => 1)

theorem unit_social (s : Profile Player Resource) : socialCost unitLatency s = 2 := by
  simp [socialCost, cost, unitLatency, constantLatency]

theorem unit_all_nash (s : Profile Player Resource) : Nash unitLatency s := by
  intro i r
  simp [cost, unitLatency, constantLatency]

theorem unit_optimum : optimum (P := Player) unitLatency = 2 := by
  exact (optimum_at_nash (fun _ : Resource => 1) (fun _ : Player => 0)
    (unit_all_nash _)).trans (unit_social _)

theorem unit_poa : poa (P := Player) unitLatency = 1 :=
  constant_poa _ (fun _ => by norm_num)

-- Every finite probability law on all four profiles also has expected cost 2.
def ProbabilityWeights (w : Profile Player Resource → ℝ) : Prop :=
  (∀ s, 0 ≤ w s) ∧ ∑ s, w s = 1
def expectedSocial (w : Profile Player Resource → ℝ) : ℝ :=
  ∑ s, w s * socialCost unitLatency s

theorem all_randomized_costs (w : Profile Player Resource → ℝ) (hw : ProbabilityWeights w) :
    expectedSocial w = 2 := by
  simp only [expectedSocial, unit_social, ← Finset.sum_mul, hw.2, one_mul]

def spectrumValues : Set ℝ := {v | ∃ l : Latency Resource,
  Admissible l ∧ (∃ s : Profile Player Resource, Nash l s) ∧ poa (P := Player) l = v}

theorem one_in_spectrum : (1 : ℝ) ∈ spectrumValues :=
  ⟨unitLatency, constant_admissible _ (fun _ => by norm_num),
    ⟨fun _ => 0, unit_all_nash _⟩, unit_poa⟩

theorem not_first_four_thirds : ¬ IsLeast spectrumValues (4 / 3 : ℝ) := by
  intro h
  have hb := h.2 one_in_spectrum
  norm_num at hb

#print axioms constant_admissible
#print axioms nash_iff_minimal
#print axioms optimum_at_nash
#print axioms nash_exists
#print axioms ratios_singleton
#print axioms constant_poa
#print axioms tight_class_bound
#print axioms unit_optimum
#print axioms all_randomized_costs
#print axioms one_in_spectrum
#print axioms not_first_four_thirds
end CongestionCounterexample
