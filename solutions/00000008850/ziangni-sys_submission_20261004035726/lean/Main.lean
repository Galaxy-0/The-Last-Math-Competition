import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace InclusionCounterexample

def zeroOperator (_ : ℝ) : Set ℝ := {0}
def positiveDomain : Set (ℝ × ℝ) := {z | 0 < z.2}
def Solution (A : ℝ → Set ℝ) (z : ℝ × ℝ) (x : ℝ) : Prop :=
  ∃ u ∈ A x, u + z.2 * x - z.1 = 0

def MonotoneOperator (A : ℝ → Set ℝ) : Prop :=
  ∀ x y u v, u ∈ A x → v ∈ A y → 0 ≤ (u-v)*(x-y)
def StronglyMonotone (A : ℝ → Set ℝ) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ x y u v, u ∈ A x → v ∈ A y →
    m * (x-y)^2 ≤ (u-v)*(x-y)
def MaximalMonotone (A : ℝ → Set ℝ) : Prop :=
  MonotoneOperator A ∧ ∀ B, MonotoneOperator B →
    (∀ x, A x ⊆ B x) → ∀ x, B x ⊆ A x

noncomputable def solutionFunction (z : ℝ × ℝ) : ℝ := z.1 / z.2

theorem zero_inclusion_iff (z : ℝ × ℝ) (hz : z ∈ positiveDomain) (x : ℝ) :
    Solution zeroOperator z x ↔ x = solutionFunction z := by
  have hn : z.2 ≠ 0 := ne_of_gt hz
  constructor
  · rintro ⟨u, hu, he⟩
    have hu0 : u = 0 := hu
    subst u
    apply (eq_div_iff hn).2
    nlinarith
  · intro hx
    refine ⟨0, rfl, ?_⟩
    rw [hx, solutionFunction]
    field_simp

theorem unique_solution (z : ℝ × ℝ) (hz : z ∈ positiveDomain) :
    ∃! x, Solution zeroOperator z x := by
  refine ⟨solutionFunction z, (zero_inclusion_iff z hz _).2 rfl, ?_⟩
  intro x hx
  exact (zero_inclusion_iff z hz x).1 hx

theorem solution_continuous : ContinuousOn solutionFunction positiveDomain := by
  exact continuousOn_fst.div continuousOn_snd (fun z hz => ne_of_gt hz)

theorem domain_connected : IsConnected positiveDomain := by
  have heq : positiveDomain = ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    ext z
    simp [positiveDomain]
  rw [heq]
  exact ((convex_univ : Convex ℝ (Set.univ : Set ℝ)).prod (convex_Ioi (0 : ℝ))).isConnected ⟨(0,1), by simp⟩

theorem zero_monotone : MonotoneOperator zeroOperator := by
  intro x y u v hu hv
  have hu0 : u = 0 := hu
  have hv0 : v = 0 := hv
  simp [hu0, hv0]

theorem zero_maximal_monotone : MaximalMonotone zeroOperator := by
  refine ⟨zero_monotone, ?_⟩
  intro B hB hAB x u hu
  have hplus := hB x (x+1) u 0 hu (hAB (x+1) rfl)
  have hminus := hB x (x-1) u 0 hu (hAB (x-1) rfl)
  have : u = 0 := by nlinarith
  exact this

theorem zero_not_strongly_monotone : ¬ StronglyMonotone zeroOperator := by
  rintro ⟨m, hm, h⟩
  have he := h 0 1 0 0 rfl rfl
  norm_num at he
  linarith

-- Single-valued continuity uses the actual supporting solution predicate.
def SingleValuedContinuous (A : ℝ → Set ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ∃ f : (ℝ × ℝ) → ℝ, ContinuousOn f D ∧
    ∀ z ∈ D, ∀ x, Solution A z x ↔ x = f z

theorem zero_single_valued_continuous : SingleValuedContinuous zeroOperator positiveDomain :=
  ⟨solutionFunction, solution_continuous, zero_inclusion_iff⟩

theorem counterexample : MaximalMonotone zeroOperator ∧ IsConnected positiveDomain ∧
    SingleValuedContinuous zeroOperator positiveDomain ∧ ¬ StronglyMonotone zeroOperator :=
  ⟨zero_maximal_monotone, domain_connected, zero_single_valued_continuous,
    zero_not_strongly_monotone⟩

-- Even restricting the conjecture to maximal monotone operators and positive lambda fails.
def ClaimedEquivalence : Prop := ∀ A : ℝ → Set ℝ, MaximalMonotone A →
  ∀ D : Set (ℝ × ℝ), D ⊆ positiveDomain →
    (SingleValuedContinuous A D ↔ StronglyMonotone A ∧ IsConnected D)

theorem conjecture_00000008850_equivalence_false : ¬ ClaimedEquivalence := by
  intro h
  exact zero_not_strongly_monotone
    ((h zeroOperator zero_maximal_monotone positiveDomain (fun _ hz => hz)).1
      zero_single_valued_continuous).1

#print axioms zero_inclusion_iff
#print axioms solution_continuous
#print axioms domain_connected
#print axioms zero_maximal_monotone
#print axioms counterexample
#print axioms conjecture_00000008850_equivalence_false
end InclusionCounterexample
