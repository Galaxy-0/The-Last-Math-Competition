import Conjecture6891.Core

set_option synthInstance.maxHeartbeats 80000
noncomputable section
open scoped TensorProduct
open Finset
namespace Conjecture6891

/-- A decomposition with at most `r` actual simple tensors; zero terms are allowed. -/
def RankLE (r : ℕ) (t : Tensor) : Prop :=
  ∃ a b c : Fin r → Vector, t = ∑ i, pure (a i) (b i) (c i)

theorem exists_rankLE (t : Tensor) : ∃ r, RankLE r t := by
  classical
  let E := Fintype.equivFin Coordinate
  let a : Fin (Fintype.card Coordinate) → Vector :=
    fun i => coords t (E.symm i) • (Pi.basisFun ℂ (Fin 2)) (E.symm i).1
  let b : Fin (Fintype.card Coordinate) → Vector :=
    fun i => (Pi.basisFun ℂ (Fin 2)) (E.symm i).2.1
  let c : Fin (Fintype.card Coordinate) → Vector :=
    fun i => (Pi.basisFun ℂ (Fin 2)) (E.symm i).2.2
  refine ⟨Fintype.card Coordinate, a, b, c, ?_⟩
  calc
    t = ∑ i : Coordinate, coords t i • tensorBasis i :=
      (tensorBasis.sum_equivFun t).symm
    _ = ∑ i, pure (a i) (b i) (c i) := by
      apply Fintype.sum_equiv E
      intro i
      simp [a, b, c, tensorBasis, Basis.tensorProduct_apply', pure]
      exact TensorProduct.smul_tmul' _ _ _

def tensorRank (t : Tensor) : ℕ := by
  classical
  exact Nat.find (exists_rankLE t)

theorem tensorRank_has_decomposition (t : Tensor) : RankLE (tensorRank t) t := by
  classical
  exact Nat.find_spec (exists_rankLE t)

theorem tensorRank_le_of_rankLE {r : ℕ} {t : Tensor} (h : RankLE r t) :
    tensorRank t ≤ r := by
  classical
  exact Nat.find_min' (exists_rankLE t) h

theorem rankLE_succ {r : ℕ} {t : Tensor} (h : RankLE r t) : RankLE (r + 1) t := by
  classical
  rcases h with ⟨a, b, c, ht⟩
  refine ⟨Fin.cons 0 a, Fin.cons 0 b, Fin.cons 0 c, ?_⟩
  simpa [Fin.sum_univ_succ] using ht

theorem rankLE_mono {r s : ℕ} {t : Tensor} (hrs : r ≤ s) (h : RankLE r t) :
    RankLE s t := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact rankLE_succ ih

theorem tensorRank_le_iff (t : Tensor) (r : ℕ) : tensorRank t ≤ r ↔ RankLE r t := by
  constructor
  · intro h
    exact rankLE_mono h (tensorRank_has_decomposition t)
  · exact tensorRank_le_of_rankLE

theorem rankLE_smul {r : ℕ} {t : Tensor} (h : RankLE r t) (s : ℂ) :
    RankLE r (s • t) := by
  rcases h with ⟨a, b, c, ht⟩
  refine ⟨fun i => s • a i, b, c, ?_⟩
  rw [ht, Finset.smul_sum]
  simp only [pure_smul_left]

theorem tensorRank_smul (s : ℂ) (hs : s ≠ 0) (t : Tensor) :
    tensorRank (s • t) = tensorRank t := by
  apply Nat.le_antisymm
  · exact tensorRank_le_of_rankLE (rankLE_smul (tensorRank_has_decomposition t) s)
  · have h := rankLE_smul (tensorRank_has_decomposition (s • t)) s⁻¹
    rw [smul_smul, inv_mul_cancel₀ hs, one_smul] at h
    exact tensorRank_le_of_rankLE h

theorem rankLE_three_W : RankLE 3 W := by
  refine ⟨![e1, e0, e0], ![e0, e1, e0], ![e0, e0, e1], ?_⟩
  simp [Fin.sum_univ_succ, W, add_assoc]

/-- A two-simple-term expression for W would force the second leading factor's
second coordinate to vanish. The proof eliminates slices without dividing. -/
theorem second_factor_coordinate_zero (a b c d e f : Vector)
    (h : W = pure a b c + pure d e f) : d 1 = 0 := by
  have hc (i j k : Fin 2) := congrArg (fun t => coords t (i, (j, k))) h
  simp only [map_add, Pi.add_apply, coords_W, coords_pure] at hc
  have h001 := hc 0 0 1
  have h010 := hc 0 1 0
  have h011 := hc 0 1 1
  have h101 := hc 1 0 1
  have h110 := hc 1 1 0
  have h111 := hc 1 1 1
  simp [e0, e1] at h001 h010 h011 h101 h110 h111
  let δ := a 0 * d 1 - a 1 * d 0
  have h01 : δ * b 0 * c 1 = d 1 := by
    dsimp [δ]
    linear_combination -d 1 * h001 + d 0 * h101
  have h10 : δ * b 1 * c 0 = d 1 := by
    dsimp [δ]
    linear_combination -d 1 * h010 + d 0 * h110
  have h11 : δ * b 1 * c 1 = 0 := by
    dsimp [δ]
    linear_combination -d 1 * h011 + d 0 * h111
  have hs : d 1 * d 1 = 0 := calc
    d 1 * d 1 = (δ * b 0 * c 1) * (δ * b 1 * c 0) := by rw [h01, h10]
    _ = (δ * b 0 * c 0) * (δ * b 1 * c 1) := by ring
    _ = 0 := by rw [h11, mul_zero]
  exact (mul_self_eq_zero.mp hs)

theorem W_ne_sum_two_pure (a b c d e f : Vector) : W ≠ pure a b c + pure d e f := by
  intro h
  have hd := second_factor_coordinate_zero a b c d e f h
  have ha := second_factor_coordinate_zero d e f a b c (h.trans (add_comm _ _))
  have he := congrArg (fun t => coords t (1, (0, 0))) h
  simp only [map_add, Pi.add_apply, coords_W, coords_pure] at he
  norm_num [e0, e1, ha, hd] at he

theorem not_rankLE_two_W : ¬ RankLE 2 W := by
  rintro ⟨a, b, c, h⟩
  apply W_ne_sum_two_pure (a 0) (b 0) (c 0) (a 1) (b 1) (c 1)
  simpa [Fin.sum_univ_two] using h

theorem tensorRank_W : tensorRank W = 3 := by
  have hu := tensorRank_le_of_rankLE rankLE_three_W
  have hl : ¬ tensorRank W ≤ 2 := by
    rw [tensorRank_le_iff]
    exact not_rankLE_two_W
  omega

end Conjecture6891
