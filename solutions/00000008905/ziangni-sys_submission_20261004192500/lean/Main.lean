import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum


set_option maxRecDepth 4000
set_option maxHeartbeats 500000
namespace SpectralHom
open Matrix Polynomial

def G : SimpleGraph (Fin 6) where
  Adj i j := (i = 0 ∧ j ≠ 0 ∧ j ≠ 5) ∨ (j = 0 ∧ i ≠ 0 ∧ i ≠ 5)
  symm := by intro i j h; exact h.elim Or.inr Or.inl
  loopless := by intro i; simp only; omega

def H : SimpleGraph (Fin 6) where
  Adj i j := ((i = 0 ∨ i = 2) ∧ (j = 1 ∨ j = 3)) ∨
    ((j = 0 ∨ j = 2) ∧ (i = 1 ∨ i = 3))
  symm := by intro i j h; exact h.elim Or.inr Or.inl
  loopless := by intro i; simp only; omega

def P : SimpleGraph (Fin 3) where
  Adj i j := (i = 1 ∧ j ≠ 1) ∨ (j = 1 ∧ i ≠ 1)
  symm := by intro i j h; exact h.elim Or.inr Or.inl
  loopless := by intro i; simp only; omega

instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable ((i = 0 ∧ j ≠ 0 ∧ j ≠ 5) ∨ (j = 0 ∧ i ≠ 0 ∧ i ≠ 5)))
instance : DecidableRel H.Adj := fun i j => inferInstanceAs (Decidable (((i = 0 ∨ i = 2) ∧ (j = 1 ∨ j = 3)) ∨ ((j = 0 ∨ j = 2) ∧ (i = 1 ∨ i = 3))))
instance : DecidableRel P.Adj := fun i j => inferInstanceAs (Decidable ((i = 1 ∧ j ≠ 1) ∨ (j = 1 ∧ i ≠ 1)))

def T : Matrix (Fin 6) (Fin 6) ℚ := !![0, 1, 0, 1, 0, 0;
1, 1/2, 0, -1/2, 1, 0;
0, 0, 1, 0, 0, 0;
1/2, -1/2, 1/2, 1/2, 0, 0;
1/2, 0, 1/2, 0, -1, 0;
0, 0, 0, 0, 0, 1]
def U : Matrix (Fin 6) (Fin 6) ℚ := !![0, 1/2, -1/2, 1/2, 1/2, 0;
1/2, 1/4, 1/4, -3/4, 1/4, 0;
0, 0, 1, 0, 0, 0;
1/2, -1/4, -1/4, 3/4, -1/4, 0;
0, 1/4, 1/4, 1/4, -3/4, 0;
0, 0, 0, 0, 0, 1]

theorem inverse_certificate : T * U = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [T, U, Matrix.mul_apply, Fin.sum_univ_succ]

theorem G_matrix : G.adjMatrix ℚ =
    !![0,1,1,1,1,0; 1,0,0,0,0,0; 1,0,0,0,0,0;
       1,0,0,0,0,0; 1,0,0,0,0,0; 0,0,0,0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem H_matrix : H.adjMatrix ℚ =
    !![0,1,0,1,0,0; 1,0,1,0,0,0; 0,1,0,1,0,0;
       1,0,1,0,0,0; 0,0,0,0,0,0; 0,0,0,0,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem intertwining : G.adjMatrix ℚ * T = T * H.adjMatrix ℚ := by
  rw [G_matrix, H_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [T, Matrix.mul_apply, Fin.sum_univ_succ]

theorem charpoly_of_intertwiner {n : Type*} [Fintype n] [DecidableEq n] (A B T U : Matrix n n ℚ)
    (hTU : T * U = 1) (hAT : A * T = T * B) : A.charpoly = B.charpoly := by
  have ht : T.det ≠ 0 := by
    have hd := congrArg Matrix.det hTU
    rw [Matrix.det_mul, Matrix.det_one] at hd
    intro h
    rw [h, zero_mul] at hd
    exact zero_ne_one hd
  have hm : A.charmatrix * T.map C = T.map C * B.charmatrix := by
    simp only [Matrix.charmatrix, RingHom.mapMatrix_apply, Matrix.scalar_apply]
    rw [sub_mul, mul_sub]
    congr 1
    · apply Matrix.ext
      intro i j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
      exact mul_comm _ _
    · rw [← Matrix.map_mul, ← Matrix.map_mul, hAT]
  have hd := congrArg Matrix.det hm
  have hdT : (T.map C).det = C T.det := (C.map_det T).symm
  rw [Matrix.det_mul, Matrix.det_mul, hdT] at hd
  change A.charpoly * C T.det = C T.det * B.charpoly at hd
  exact mul_left_cancel₀ (by simpa using ht : C T.det ≠ (0 : ℚ[X]))
    ((mul_comm _ _).trans hd)

theorem cospectral : (G.adjMatrix ℚ).charpoly = (H.adjMatrix ℚ).charpoly :=
  charpoly_of_intertwiner _ _ T U inverse_certificate intertwining

def HomCode (J : SimpleGraph (Fin 6)) :=
  {f : Fin 3 → Fin 6 // ∀ i j, P.Adj i j → J.Adj (f i) (f j)}

def homEquiv (J : SimpleGraph (Fin 6)) : HomCode J ≃ (P →g J) where
  toFun f := ⟨f.val, fun h => f.property _ _ h⟩
  invFun f := ⟨f, fun _ _ h => f.map_rel h⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

instance (J : SimpleGraph (Fin 6)) [DecidableRel J.Adj] : Fintype (HomCode J) :=
  inferInstanceAs (Fintype {f : Fin 3 → Fin 6 // ∀ i j, P.Adj i j → J.Adj (f i) (f j)})

instance (J : SimpleGraph (Fin 6)) [DecidableRel J.Adj] : Fintype (P →g J) :=
  Fintype.ofEquiv (HomCode J) (homEquiv J)

theorem hom_G : Fintype.card (P →g G) = 20 := by
  rw [← Fintype.card_congr (homEquiv G)]
  decide

theorem hom_H : Fintype.card (P →g H) = 16 := by
  rw [← Fintype.card_congr (homEquiv H)]
  decide

theorem no_reconstruction : ¬ ∃ F : ℚ[X] → ℕ,
    F (G.adjMatrix ℚ).charpoly = Fintype.card (P →g G) ∧
    F (H.adjMatrix ℚ).charpoly = Fintype.card (P →g H) := by
  rintro ⟨F, hG, hH⟩
  rw [cospectral, hom_G] at hG
  rw [hom_H] at hH
  omega


theorem complex_charpoly (J : SimpleGraph (Fin 6)) [DecidableRel J.Adj] :
    (J.adjMatrix ℂ).charpoly = (J.adjMatrix ℚ).charpoly.map (Rat.castHom ℂ) := by
  have hm : (J.adjMatrix ℚ).map (Rat.castHom ℂ) = J.adjMatrix ℂ := by
    ext i j
    simp only [SimpleGraph.adjMatrix, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [← hm, Matrix.charpoly_map]

theorem eigenvalue_multisets_equal :
    (G.adjMatrix ℂ).charpoly.roots = (H.adjMatrix ℂ).charpoly.roots := by
  rw [complex_charpoly, complex_charpoly, cospectral]

theorem no_eigenvalue_reconstruction : ¬ ∃ F : Multiset ℂ → ℕ,
    F (G.adjMatrix ℂ).charpoly.roots = Fintype.card (P →g G) ∧
    F (H.adjMatrix ℂ).charpoly.roots = Fintype.card (P →g H) := by
  rintro ⟨F, hG, hH⟩
  rw [eigenvalue_multisets_equal, hom_G] at hG
  rw [hom_H] at hH
  omega

#print axioms complex_charpoly
#print axioms eigenvalue_multisets_equal
#print axioms no_eigenvalue_reconstruction
#print axioms inverse_certificate
#print axioms intertwining
#print axioms charpoly_of_intertwiner
#print axioms hom_G
#print axioms hom_H
#print axioms cospectral
#print axioms no_reconstruction
end SpectralHom
