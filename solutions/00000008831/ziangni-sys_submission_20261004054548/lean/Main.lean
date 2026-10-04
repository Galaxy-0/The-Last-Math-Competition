import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace DouglasRachfordCounterexample

noncomputable section

-- Actual graphs in the real Hilbert line.
def MonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, 0 ≤ inner (𝕜 := ℝ) (p.1 - q.1) (p.2 - q.2)

def MaximalMonotoneGraph (G : Set (ℝ × ℝ)) : Prop :=
  MonotoneGraph G ∧ ∀ H, MonotoneGraph H → G ⊆ H → H ⊆ G

def constantOperator (c : ℝ) (_ : ℝ) : Set ℝ := {c}

def graph (c : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ constantOperator c p.1}

theorem inner_real (x y : ℝ) : inner (𝕜 := ℝ) x y = x * y := by
  simp [RCLike.inner_apply, mul_comm]

theorem graph_membership (c : ℝ) (p : ℝ × ℝ) : p ∈ graph c ↔ p.2 = c := by
  rfl

theorem constant_monotone (c : ℝ) : MonotoneGraph (graph c) := by
  intro p hp q hq
  have hp' := (graph_membership c p).mp hp
  have hq' := (graph_membership c q).mp hq
  simp [hp', hq']

-- Maximality is proved against every monotone graph extension.
theorem constant_maximal (c : ℝ) : MaximalMonotoneGraph (graph c) := by
  refine ⟨constant_monotone c, ?_⟩
  intro H hH hsub p hp
  have hleft : (p.1 - 1, c) ∈ H := hsub (by simp [graph, constantOperator])
  have hright : (p.1 + 1, c) ∈ H := hsub (by simp [graph, constantOperator])
  have hl := hH p hp (p.1 - 1, c) hleft
  have hr := hH p hp (p.1 + 1, c) hright
  rw [inner_real] at hl hr
  apply (graph_membership c p).mpr
  dsimp at hl hr
  nlinarith

-- Membership in the genuine resolvent equation x ∈ y + C_c(y).
def ResolventEquation (c x y : ℝ) : Prop :=
  ∃ a ∈ constantOperator c y, x = y + a

def resolvent (c x : ℝ) : ℝ := x - c

theorem resolvent_equation (c x y : ℝ) :
    ResolventEquation c x y ↔ y = resolvent c x := by
  constructor
  · rintro ⟨a, ha, hx⟩
    have ha' : a = c := ha
    dsimp [resolvent]
    linarith
  · intro hy
    refine ⟨c, rfl, ?_⟩
    dsimp [resolvent] at hy
    linarith

theorem unique_resolvent (c x : ℝ) : ∃! y, ResolventEquation c x y := by
  exact ⟨resolvent c x, (resolvent_equation c x _).mpr rfl,
    fun y hy => (resolvent_equation c x y).mp hy⟩

def reflectedResolvent (c x : ℝ) : ℝ := 2 * resolvent c x - x

def dr (x : ℝ) : ℝ := reflectedResolvent 1 (reflectedResolvent 0 x)
def reverseDR (x : ℝ) : ℝ := reflectedResolvent 0 (reflectedResolvent 1 x)
def averagedDR (x : ℝ) : ℝ := (x + dr x) / 2

theorem reflection_formula (c x : ℝ) : reflectedResolvent c x = x - 2*c := by
  dsimp [reflectedResolvent, resolvent]
  ring

theorem dr_formula (x : ℝ) : dr x = x - 2 := by
  simp [dr, reflection_formula]

theorem reverse_dr_formula (x : ℝ) : reverseDR x = dr x := by
  simp [reverseDR, dr, reflection_formula]

theorem averaged_formula (x : ℝ) : averagedDR x = x - 1 := by
  dsimp [averagedDR]
  rw [dr_formula]
  ring

theorem dr_iterate (n : ℕ) (x : ℝ) : dr^[n] x = x - 2*(n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', dr_formula, ih]
    push_cast
    ring

theorem averaged_iterate (n : ℕ) (x : ℝ) : averagedDR^[n] x = x - (n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', averaged_formula, ih]
    push_cast
    ring

def WeaklyConverges (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ f : ℝ →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f a))

theorem constant_decrement_not_weak (u : ℕ → ℝ) (d : ℝ) (hd : d ≠ 0)
    (hstep : ∀ n, u (n+1) - u n = -d) (a : ℝ) : ¬ WeaklyConverges u a := by
  intro h
  have hi : Tendsto u atTop (𝓝 a) := by
    simpa using h (ContinuousLinearMap.id ℝ ℝ)
  have hs := hi.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun _ : ℕ => -d) atTop (𝓝 (0:ℝ)) := by
    simpa [Function.comp_def, hstep] using hs.sub hi
  have he : -d = 0 := tendsto_nhds_unique tendsto_const_nhds hdiff
  exact hd (neg_eq_zero.mp he)

theorem dr_not_weak (x a : ℝ) : ¬ WeaklyConverges (fun n => dr^[n] x) a := by
  apply constant_decrement_not_weak _ 2 (by norm_num)
  intro n
  rw [Function.iterate_succ_apply', dr_formula]
  ring

theorem averaged_not_weak (x a : ℝ) :
    ¬ WeaklyConverges (fun n => averagedDR^[n] x) a := by
  apply constant_decrement_not_weak _ 1 (by norm_num)
  intro n
  rw [Function.iterate_succ_apply', averaged_formula]
  ring

theorem no_zero (x : ℝ) :
    ¬ ∃ a ∈ constantOperator 0 x, ∃ b ∈ constantOperator 1 x, a+b = 0 := by
  rintro ⟨a, ha, b, hb, h⟩
  have ha' : a = 0 := ha
  have hb' : b = 1 := hb
  norm_num [ha', hb'] at h

theorem counterexample :
    MaximalMonotoneGraph (graph 0) ∧ MaximalMonotoneGraph (graph 1) ∧
    (∀ c x, ∃! y, ResolventEquation c x y) ∧
    (∀ x, ¬ ∃ a, WeaklyConverges (fun n => dr^[n] x) a) ∧
    (∀ x, ¬ ∃ a, WeaklyConverges (fun n => averagedDR^[n] x) a) := by
  exact ⟨constant_maximal 0, constant_maximal 1, unique_resolvent,
    fun x ⟨a, h⟩ => dr_not_weak x a h,
    fun x ⟨a, h⟩ => averaged_not_weak x a h⟩

#print axioms constant_maximal
#print axioms unique_resolvent
#print axioms dr_iterate
#print axioms averaged_iterate
#print axioms dr_not_weak
#print axioms averaged_not_weak
#print axioms counterexample
end
end DouglasRachfordCounterexample
