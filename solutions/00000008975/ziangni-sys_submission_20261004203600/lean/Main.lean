import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.Notation
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
namespace BoundaryCubic
open Matrix Polynomial
open scoped Kronecker
abbrev V := Fin 2
abbrev Pair := V × V
abbrev Triple := V × V × V
abbrev Mat := Matrix V V ℝ

def flip : Pair ≃ Pair where
  toFun p := (p.2,p.1)
  invFun p := (p.2,p.1)
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
def R : Matrix Pair Pair ℝ := flip.toPEquiv.toMatrix
def K (u : ℝ) : Mat := diagonal ![1,1+u^3]
def K1 (u : ℝ) : Matrix Pair Pair ℝ := K u ⊗ₖ (1 : Mat)
def K2 (u : ℝ) : Matrix Pair Pair ℝ := (1 : Mat) ⊗ₖ K u

theorem flip_symm : flip.symm = flip := rfl
theorem involutive_R : R*R = 1 := by
  unfold R
  rw [PEquiv.toMatrix_toPEquiv_mul]
  ext p q
  simp [Matrix.submatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,flip,Matrix.one_apply,eq_comm]

theorem first_leg (u : ℝ) :
    K1 u = diagonal (fun p : Pair => (![1,1+u^3] : V → ℝ) p.1) := by
  unfold K1 K
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  simp
theorem second_leg (u : ℝ) :
    K2 u = diagonal (fun p : Pair => (![1,1+u^3] : V → ℝ) p.2) := by
  unfold K2 K
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  simp

theorem flip_conjugation (u : ℝ) : R*K1 u*R = K2 u := by
  rw [first_leg,second_leg]
  unfold R
  rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
  ext p q
  simp [Matrix.submatrix,Matrix.diagonal,flip,eq_comm,Prod.ext_iff,and_comm]

theorem second_legs_commute (u v : ℝ) : K2 u*K2 v = K2 v*K2 u := by
  rw [second_leg u,second_leg v]
  rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  ext p q
  simp [Matrix.diagonal,mul_comm]

-- R(u-v)=R and R_21(u+v)=R for this constant flip solution.
def ReflectionEquation (u v : ℝ) : Prop :=
  R*K1 u*R*K2 v = K2 v*R*K1 u*R
theorem reflection_all_parameters (u v : ℝ) : ReflectionEquation u v := by
  unfold ReflectionEquation
  calc
    R*K1 u*R*K2 v = K2 u*K2 v := by rw [flip_conjugation]
    _ = K2 v*K2 u := second_legs_commute u v
    _ = K2 v*(R*K1 u*R) := congrArg (fun M => K2 v*M) (flip_conjugation u).symm
    _ = K2 v*R*K1 u*R := by simp only [mul_assoc]

-- The genuine eight-dimensional tensor-leg Yang--Baxter identity.
def s12 : Triple ≃ Triple where
  toFun p := (p.2.1,p.1,p.2.2)
  invFun p := (p.2.1,p.1,p.2.2)
  left_inv p := by rcases p with ⟨a,b,c⟩; rfl
  right_inv p := by rcases p with ⟨a,b,c⟩; rfl
def s13 : Triple ≃ Triple where
  toFun p := (p.2.2,p.2.1,p.1)
  invFun p := (p.2.2,p.2.1,p.1)
  left_inv p := by rcases p with ⟨a,b,c⟩; rfl
  right_inv p := by rcases p with ⟨a,b,c⟩; rfl
def s23 : Triple ≃ Triple where
  toFun p := (p.1,p.2.2,p.2.1)
  invFun p := (p.1,p.2.2,p.2.1)
  left_inv p := by rcases p with ⟨a,b,c⟩; rfl
  right_inv p := by rcases p with ⟨a,b,c⟩; rfl
def R12 : Matrix Triple Triple ℝ := s12.toPEquiv.toMatrix
def R13 : Matrix Triple Triple ℝ := s13.toPEquiv.toMatrix
def R23 : Matrix Triple Triple ℝ := s23.toPEquiv.toMatrix

theorem perm_product (e f : Triple ≃ Triple) :
    (e.toPEquiv.toMatrix : Matrix Triple Triple ℝ)*f.toPEquiv.toMatrix =
    (e.trans f).toPEquiv.toMatrix := by
  rw [Equiv.toPEquiv_trans,PEquiv.toMatrix_trans]

theorem tensor_leg_bridge :
    R23 = (1 : Mat) ⊗ₖ R ∧
    R12 = (R ⊗ₖ (1 : Mat)).submatrix
      (fun p : Triple => ((p.1,p.2.1),p.2.2))
      (fun p : Triple => ((p.1,p.2.1),p.2.2)) := by
  constructor
  all_goals
    ext p q
    rcases p with ⟨a,b,c⟩
    rcases q with ⟨d,e,f⟩
    simp [R12,R23,R,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
      s12,s23,flip,Matrix.kroneckerMap_apply,Matrix.submatrix,Matrix.one_apply,
      Prod.mk.injEq]
    split_ifs <;> simp_all

theorem yang_baxter : R12*R13*R23 = R23*R13*R12 := by
  unfold R12 R13 R23
  rw [perm_product,perm_product,perm_product,perm_product]
  have he : (s12.trans s13).trans s23 = (s23.trans s13).trans s12 := by
    apply Equiv.ext
    intro p
    rcases p with ⟨a,b,c⟩
    rfl
  rw [he]

def polynomialK : Matrix V V ℝ[X] := diagonal ![1,X^3+1]
theorem actual_evaluation (u : ℝ) : polynomialK.map (Polynomial.eval u) = K u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [polynomialK,K,Matrix.diagonal,add_comm]

theorem normalized : K 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [K,Matrix.diagonal]

theorem determinant (u : ℝ) : (K u).det = 1+u^3 := by
  simp [K,Matrix.det_fin_two,Matrix.diagonal]
theorem invertible_except_minus_one (u : ℝ) (hu : u ≠ -1) : IsUnit (K u).det := by
  rw [determinant,isUnit_iff_ne_zero]
  have hp : 0 < u^2-u+1 := by nlinarith [sq_nonneg (u-1/2)]
  have hlin : u+1 ≠ 0 := by intro h; apply hu; linarith
  have hprod := mul_ne_zero hlin (ne_of_gt hp)
  convert hprod using 1 <;> ring

theorem actual_degree : (polynomialK 1 1).natDegree = 3 ∧
    (∀ i j, (polynomialK i j).natDegree ≤ 3) := by
  constructor
  · simpa [polynomialK,Matrix.diagonal] using
      (Polynomial.natDegree_X_pow_add_C (R := ℝ) (n := 3) (r := 1))
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [polynomialK,Matrix.diagonal]
    simpa using (le_of_eq (Polynomial.natDegree_X_pow_add_C (R := ℝ) (n := 3) (r := 1)))

theorem primitive_polynomial (d : ℝ[X]) (hd : ∀ i j, d ∣ polynomialK i j) : IsUnit d := by
  have hh := hd 0 0
  simpa [polynomialK,Matrix.diagonal] using (isUnit_of_dvd_one hh)

theorem not_scalar_at_one : ¬ ∃ c : ℝ, K 1 = c • (1 : Mat) := by
  rintro ⟨c,h⟩
  have h0 := congrArg (fun M : Mat => M 0 0) h
  have h1 := congrArg (fun M : Mat => M 1 1) h
  norm_num [K,Matrix.diagonal] at h0 h1
  linarith

theorem counterexample :
    (∀ u v, ReflectionEquation u v) ∧ K 0 = 1 ∧
    (polynomialK 1 1).natDegree > 2 :=
  ⟨reflection_all_parameters,normalized,by rw [actual_degree.1]; norm_num⟩

#print axioms involutive_R
#print axioms flip_conjugation
#print axioms reflection_all_parameters
#print axioms tensor_leg_bridge
#print axioms yang_baxter
#print axioms actual_evaluation
#print axioms normalized
#print axioms invertible_except_minus_one
#print axioms actual_degree
#print axioms primitive_polynomial
#print axioms not_scalar_at_one
#print axioms counterexample
end BoundaryCubic
