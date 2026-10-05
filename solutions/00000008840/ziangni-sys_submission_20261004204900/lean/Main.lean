import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
namespace OpenZeros

def A (x : ℝ) : ℝ := if x ≤ 0 then -1 else if 1 ≤ x then 1 else 0
def graph : Set (ℝ × ℝ) := {p | p.2 = A p.1}
def zeros : Set ℝ := {x | A x = 0}
def MonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, 0 ≤ inner (𝕜 := ℝ) (p.1-q.1) (p.2-q.2)

theorem inner_real (x y : ℝ) : inner (𝕜 := ℝ) x y = x*y := by
  simp [RCLike.inner_apply,mul_comm]

theorem actual_full_domain : ∀ x : ℝ, ∃ y : ℝ, (x,y) ∈ graph :=
  fun x => ⟨A x,rfl⟩
theorem increasing : Monotone A := by
  intro x y hxy
  unfold A
  split_ifs <;> linarith

theorem actual_monotonicity (x y : ℝ) :
    0 ≤ inner (𝕜 := ℝ) (x-y) (A x-A y) := by
  rw [inner_real]
  rcases le_total x y with h|h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr (increasing h))
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (increasing h))
theorem graph_monotone : MonotoneGraph graph := by
  rintro ⟨x,a⟩ ha ⟨y,b⟩ hb
  change a=A x at ha
  change b=A y at hb
  subst a; subst b
  exact actual_monotonicity x y

theorem actual_zero_set : zeros = Set.Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    change A x = 0 at hx
    have h0 : ¬ x ≤ 0 := by
      intro h; simp [A,h] at hx
    have h1 : ¬ 1 ≤ x := by
      intro h; simp [A,h0,h] at hx
    exact ⟨lt_of_not_ge h0,lt_of_not_ge h1⟩
  · rintro ⟨hx0,hx1⟩
    change A x = 0
    simp [A,not_le.mpr hx0,not_le.mpr hx1]

theorem actual_closure : closure zeros = Set.Icc (0 : ℝ) 1 := by
  rw [actual_zero_set]
  exact closure_Ioo (by norm_num)
theorem zero_not_in_zeros : (0 : ℝ) ∉ zeros := by rw [actual_zero_set]; simp
theorem zeros_not_closed : ¬ IsClosed zeros := by
  intro hc
  have hz : (0 : ℝ) ∈ closure zeros := by rw [actual_closure]; norm_num
  rw [hc.closure_eq] at hz
  exact zero_not_in_zeros hz

theorem minty_range_misses_zero : (0 : ℝ) ∉ Set.range (fun x : ℝ => x+A x) := by
  rintro ⟨x,hx⟩
  change x+A x=0 at hx
  unfold A at hx
  split_ifs at hx <;> linarith

def extension : Set (ℝ × ℝ) := graph ∪ {(0,0)}
theorem compatible_origin (x : ℝ) : 0 ≤ inner (𝕜 := ℝ) x (A x) := by
  rw [inner_real]
  unfold A
  split_ifs <;> simp_all <;> linarith
theorem extension_monotone : MonotoneGraph extension := by
  intro p hp q hq
  rcases hp with hp|hp <;> rcases hq with hq|hq
  · exact graph_monotone p hp q hq
  · have hq0 : q=(0,0) := Set.mem_singleton_iff.mp hq
    subst q
    have hpA : p.2=A p.1 := hp
    simpa [inner_real,hpA] using compatible_origin p.1
  · have hp0 : p=(0,0) := Set.mem_singleton_iff.mp hp
    subst p
    have hqA : q.2=A q.1 := hq
    rw [inner_real]
    change 0 ≤ (0-q.1)*(0-q.2)
    simpa [inner_real,hqA,mul_comm] using compatible_origin q.1
  · have hp0 : p=(0,0) := Set.mem_singleton_iff.mp hp
    have hq0 : q=(0,0) := Set.mem_singleton_iff.mp hq
    subst p; subst q; simp

theorem strict_extension : graph ⊂ extension := by
  refine ⟨Set.subset_union_left,?_⟩
  intro h
  have hm : (0,0) ∈ graph := h (by simp [extension])
  change (0 : ℝ)=A 0 at hm
  norm_num [A] at hm

theorem counterexample : MonotoneGraph graph ∧ (∀ x : ℝ, ∃ y : ℝ, (x,y) ∈ graph) ∧
    ¬ IsClosed zeros ∧ (0 : ℝ) ∉ Set.range (fun x : ℝ => x+A x) :=
  ⟨graph_monotone,actual_full_domain,zeros_not_closed,minty_range_misses_zero⟩

#print axioms actual_full_domain
#print axioms increasing
#print axioms actual_monotonicity
#print axioms graph_monotone
#print axioms actual_zero_set
#print axioms actual_closure
#print axioms zeros_not_closed
#print axioms minty_range_misses_zero
#print axioms extension_monotone
#print axioms strict_extension
#print axioms counterexample
end OpenZeros
