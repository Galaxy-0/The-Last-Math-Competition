import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Probability.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ConstantFPP

abbrev Vertex := ℤ × ℤ

/-- The usual undirected nearest-neighbor square lattice. -/
def lattice : SimpleGraph Vertex where
  Adj u v := ((u.1 = v.1 + 1 ∨ v.1 = u.1 + 1) ∧ u.2 = v.2) ∨
    ((u.2 = v.2 + 1 ∨ v.2 = u.2 + 1) ∧ u.1 = v.1)
  symm := by intro u v h; omega
  loopless := by intro u h; omega

abbrev Edge := {e : Sym2 Vertex // e ∈ lattice.edgeSet}
def probability : Measure Unit := Measure.dirac ()
instance : IsProbabilityMeasure probability := by unfold probability; infer_instance

/-- The iid edge law is the point mass at the positive number one. -/
def weight (_e : Edge) (_ω : Unit) : ℝ := 1

theorem weights_independent : iIndepFun weight probability := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  classical
  by_cases h : ∀ i ∈ S, (1 : ℝ) ∈ sets i
  · have hleft : (⋂ i ∈ S, weight i ⁻¹' sets i) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro ω
      exact Set.mem_iInter.mpr (fun i => Set.mem_iInter.mpr (fun hi => h i hi))
    rw [hleft]
    simp only [measure_univ]
    symm
    apply Finset.prod_eq_one
    intro i hi
    have : weight i ⁻¹' sets i = Set.univ := by ext ω; simp [weight, h i hi]
    simp [this]
  · push_neg at h
    obtain ⟨i, hi, hnot⟩ := h
    have hz : weight i ⁻¹' sets i = ∅ := by ext ω; simp [weight, hnot]
    have hleft : (⋂ j ∈ S, weight j ⁻¹' sets j) = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro ω hω
      have := Set.mem_iInter.mp (Set.mem_iInter.mp hω i) hi
      simpa [hz] using this
    rw [hleft, measure_empty]
    symm
    exact Finset.prod_eq_zero hi (by simp [hz])

theorem weight_law (e : Edge) : Measure.map (weight e) probability = Measure.dirac (1 : ℝ) := by
  change Measure.map (fun _ : Unit => (1 : ℝ)) (Measure.dirac ()) = _
  exact Measure.map_dirac measurable_const ()

theorem weights_positive (e : Edge) (ω : Unit) : 0 < weight e ω := by norm_num [weight]
theorem weights_finite_variance (e : Edge) : Integrable (fun ω => weight e ω ^ 2) probability := by
  simpa [weight] using (integrable_const (1 : ℝ) : Integrable (fun _ : Unit => (1 : ℝ)) probability)
theorem weights_exponential_moments (e : Edge) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * weight e ω)) probability := by
  simpa [weight] using (integrable_const (Real.exp t) : Integrable (fun _ : Unit => Real.exp t) probability)

/-- Sum of edge weights along a genuine finite lattice walk. -/
def cost {u v : Vertex} : lattice.Walk u v → Unit → ℝ
  | .nil, _ => 0
  | .cons h p, ω => weight ⟨s(_, _), h⟩ ω + cost p ω

theorem cost_eq_length {u v : Vertex} (p : lattice.Walk u v) (ω : Unit) :
    cost p ω = p.length := by
  induction p with
  | nil => simp [cost]
  | cons h p ih => simpa [cost, weight, add_comm] using congrArg (fun x : ℝ => 1 + x) ih

theorem coordinate_bound {u v : Vertex} (p : lattice.Walk u v) :
    u.1 ≤ v.1 + (p.length : ℤ) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have hedge : u.1 ≤ v.1 + 1 := by change lattice.Adj u v at h; dsimp [lattice] at h; omega
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    omega

def horizontal : (n : ℕ) → lattice.Walk ((n : ℤ), 0) (0, 0)
  | 0 => .nil
  | n + 1 => .cons (by left; constructor; left; push_cast; rfl; rfl) (horizontal n)

theorem horizontal_length (n : ℕ) : (horizontal n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [horizontal, ih]

/-- First-passage time: the infimum over ALL finite nearest-neighbor walks. -/
def passage (n : ℕ) (ω : Unit) : ℝ :=
  sInf {r | ∃ p : lattice.Walk ((n : ℤ), 0) (0, 0), cost p ω = r}

theorem passage_eq_distance (n : ℕ) (ω : Unit) : passage n ω = n := by
  let A : Set ℝ := {r | ∃ p : lattice.Walk ((n : ℤ), 0) (0, 0), cost p ω = r}
  have hmem : (n : ℝ) ∈ A := ⟨horizontal n, by rw [cost_eq_length, horizontal_length]⟩
  have hlower : ∀ r ∈ A, (n : ℝ) ≤ r := by
    rintro r ⟨p, rfl⟩
    rw [cost_eq_length]
    have h := coordinate_bound p
    simp only [zero_add] at h
    exact_mod_cast h
  apply le_antisymm
  · exact csInf_le ⟨n, hlower⟩ hmem
  · exact le_csInf ⟨n, hmem⟩ hlower

theorem passage_variance_zero (n : ℕ) : variance (passage n) probability = 0 := by
  simp [variance, evariance, passage_eq_distance]

/-- Even the weakest eventual positive square-root lower bound is false. -/
theorem no_positive_sqrt_lower_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      c * Real.sqrt n ≤ variance (passage n) probability := by
  rintro ⟨c, hc, N, h⟩
  have hbad := h (N + 1) (by omega)
  rw [passage_variance_zero] at hbad
  have hpos : 0 < c * Real.sqrt (N + 1 : ℕ) :=
    mul_pos hc (Real.sqrt_pos.2 (by positivity))
  linarith

#print axioms weights_independent
#print axioms weight_law
#print axioms weights_positive
#print axioms weights_finite_variance
#print axioms weights_exponential_moments
#print axioms passage_eq_distance
#print axioms passage_variance_zero
#print axioms no_positive_sqrt_lower_bound
end ConstantFPP
