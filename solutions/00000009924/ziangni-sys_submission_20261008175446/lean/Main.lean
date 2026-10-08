import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic
open scoped NNReal
namespace HodgeJump

/-- A genuine abstract simplicial complex, including the empty simplex. -/
structure Complex (V : Type*) where
  faces : Set (Finset V)
  downward : ∀ s ∈ faces, ∀ u : Finset V, u ⊆ s → u ∈ faces

def filtration (t : ℝ) : Complex (Fin 2) where
  faces := {s | s.card ≤ 1 ∨ 0 ≤ t}
  downward := by
    intro s hs u hu
    rcases hs with hs | ht
    · exact Or.inl ((Finset.card_le_card hu).trans hs)
    · exact Or.inr ht

theorem filtration_monotone {s t : ℝ} (hst : s ≤ t) :
    (filtration s).faces ⊆ (filtration t).faces := by
  intro f hf
  rcases hf with hf | hs
  · exact Or.inl hf
  · exact Or.inr (hs.trans hst)

theorem vertices_present (t : ℝ) (i : Fin 2) : {i} ∈ (filtration t).faces := by
  exact Or.inl (by simp)

theorem edge_present (t : ℝ) : (Finset.univ : Finset (Fin 2)) ∈ (filtration t).faces ↔ 0 ≤ t := by
  simp [filtration]

/-- The actual edge chain space has dimension zero before insertion and one afterward. -/
abbrev EdgeIndex (t : ℝ) := Fin (if 0 ≤ t then 1 else 0)
noncomputable def boundary (t : ℝ) : Matrix (Fin 2) (EdgeIndex t) ℝ :=
  fun i _ => if i = 0 then -1 else 1
/-- Unweighted degree-zero Hodge Laplacian, with the transpose as the real adjoint. -/
noncomputable def laplacian (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  boundary t * (boundary t).transpose

theorem laplacian_entries (t : ℝ) (i j : Fin 2) :
    laplacian t i j = if 0 ≤ t then (if i = j then 1 else -1) else 0 := by
  by_cases ht : 0 ≤ t
  · fin_cases i <;> fin_cases j <;>
      simp [laplacian, boundary, EdgeIndex, ht, Matrix.mul_apply, Fin.sum_univ_one]
  · simp [laplacian, boundary, EdgeIndex, ht, Matrix.mul_apply]

noncomputable def topValue (t : ℝ) : ℝ := if 0 ≤ t then 2 else 0
def Eigenvalue (t mu : ℝ) : Prop :=
  ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ (laplacian t).mulVec v = mu • v

theorem spectral_values {t mu : ℝ} (he : Eigenvalue t mu) :
    mu = 0 ∨ (0 ≤ t ∧ mu = 2) := by
  obtain ⟨v, hv, he⟩ := he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, laplacian_entries,
    Pi.smul_apply, smul_eq_mul] at h0 h1
  by_cases ht : 0 ≤ t
  · simp [ht] at h0 h1
    by_cases hm : mu = 0
    · exact Or.inl hm
    · right
      refine ⟨ht, ?_⟩
      by_contra hm2
      have hp : mu * (mu-2) ≠ 0 := mul_ne_zero hm (sub_ne_zero.mpr hm2)
      have hz0 : mu * (mu-2) * v 0 = 0 := by linear_combination (1-mu)*h0 + h1
      have hz1 : mu * (mu-2) * v 1 = 0 := by linear_combination h0 - (mu-1)*h1
      have hv0 := (mul_eq_zero.mp hz0).resolve_left hp
      have hv1 := (mul_eq_zero.mp hz1).resolve_left hp
      apply hv
      funext i
      fin_cases i <;> assumption
  · simp [ht] at h0 h1
    left
    by_contra hm
    have hv0 := h0.resolve_left hm
    have hv1 := h1.resolve_left hm
    apply hv
    funext i
    fin_cases i <;> assumption

theorem top_is_eigenvalue (t : ℝ) : Eigenvalue t (topValue t) := by
  let v : Fin 2 → ℝ := fun i => if i = 0 then 1 else -1
  refine ⟨v, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    norm_num [v] at h0
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      laplacian_entries, topValue, v] <;> split_ifs <;> norm_num

theorem zero_is_eigenvalue (t : ℝ) : Eigenvalue t 0 := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    norm_num at h0
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      laplacian_entries] <;> split_ifs <;> norm_num

theorem complete_spectrum (t mu : ℝ) :
    Eigenvalue t mu ↔ mu = 0 ∨ (0 ≤ t ∧ mu = 2) := by
  constructor
  · exact spectral_values
  · rintro (rfl | ⟨ht, rfl⟩)
    · exact zero_is_eigenvalue t
    · simpa [topValue, ht] using top_is_eigenvalue t

theorem top_is_largest (t mu : ℝ) (he : Eigenvalue t mu) : mu ≤ topValue t := by
  rcases spectral_values he with rfl | ⟨ht, rfl⟩
  · unfold topValue
    split_ifs <;> norm_num
  · simp [topValue, ht]

/-- The actual top eigenvalue fails every proposed Lipschitz bound. -/
theorem conjecture_false : ¬ ∃ K : ℝ≥0, LipschitzWith K topValue := by
  rintro ⟨K, hK⟩
  let t : ℝ := -1 / ((K : ℝ)+1)
  have hden : 0 < (K : ℝ)+1 := by positivity
  have ht : t < 0 := by dsimp [t]; exact div_neg_of_neg_of_pos (by norm_num) hden
  have h := hK.dist_le_mul t 0
  have hval : topValue t = 0 := if_neg (not_le.mpr ht)
  have hval0 : topValue 0 = 2 := if_pos le_rfl
  rw [hval, hval0, Real.dist_eq, Real.dist_eq, sub_zero, abs_of_neg ht] at h
  norm_num at h
  have hneg : -t = 1 / ((K : ℝ)+1) := by dsimp [t]; ring
  rw [← mul_neg, hneg] at h
  have hsmall : (K : ℝ) * (1 / ((K : ℝ)+1)) < 1 := by
    rw [mul_one_div]
    exact (div_lt_one hden).mpr (by linarith)
  linarith

end HodgeJump
#print axioms HodgeJump.filtration_monotone
#print axioms HodgeJump.edge_present
#print axioms HodgeJump.laplacian_entries
#print axioms HodgeJump.spectral_values
#print axioms HodgeJump.top_is_eigenvalue
#print axioms HodgeJump.top_is_largest
#print axioms HodgeJump.conjecture_false

#print axioms HodgeJump.complete_spectrum
