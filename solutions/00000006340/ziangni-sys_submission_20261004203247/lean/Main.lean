import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega

noncomputable section
namespace RigidityPair
open Matrix
abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ
def A : Mat := 1
def J : Mat := !![0,-1;1,0]
def K : Mat := !![0,1;-1,0]

-- Actual number of unequal entries; each entry contributes zero or one.
def changes (M N : Mat) : ℕ := by
  classical
  exact ∑ i, ∑ j, if M i j = N i j then 0 else 1
def costs (M : Mat) (r : ℕ) : Set ℕ := {k | ∃ N : Mat, N.rank ≤ r ∧ changes M N = k}
def rigidity (M : Mat) (r : ℕ) : ℕ := sInf (costs M r)

theorem rotation_inverse : K * J = 1 ∧ J * K = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [K,J,Matrix.mul_apply,Fin.sum_univ_two]
theorem actual_orthogonality :
    A.transpose * A = 1 ∧ J.transpose * J = 1 ∧
    A * A.transpose = 1 ∧ J * J.transpose = 1 := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [A,J,Matrix.transpose,Matrix.mul_apply,Fin.sum_univ_two]
theorem frobenius_orthogonal : (∑ i, ∑ j, A i j * J i j) = 0 := by
  norm_num [A,J,Fin.sum_univ_two]

theorem det_J : J.det = 1 := by norm_num [J,Matrix.det_fin_two]
theorem det_K : K.det = 1 := by norm_num [K,Matrix.det_fin_two]
theorem rotation_rank (N : Mat) : (J*N).rank = N.rank :=
  Matrix.rank_mul_eq_right_of_isUnit_det J N (by rw [det_J]; exact isUnit_one)
theorem inverse_rotation_rank (N : Mat) : (K*N).rank = N.rank :=
  Matrix.rank_mul_eq_right_of_isUnit_det K N (by rw [det_K]; exact isUnit_one)

theorem rotation_changes (M N : Mat) : changes (J*M) (J*N) = changes M N := by
  classical
  simp [changes,J,Matrix.mul_apply,Fin.sum_univ_two]
  omega
theorem inverse_rotation_changes (M N : Mat) : changes (K*M) (K*N) = changes M N := by
  classical
  simp [changes,K,Matrix.mul_apply,Fin.sum_univ_two]
  omega

theorem identical_attainable_costs (r : ℕ) : costs A r = costs J r := by
  ext k
  constructor
  · rintro ⟨N,hN,hc⟩
    refine ⟨J*N,by simpa [rotation_rank] using hN,?_⟩
    have hh := rotation_changes A N
    simpa [A] using hh.trans hc
  · rintro ⟨N,hN,hc⟩
    refine ⟨K*N,by simpa [inverse_rotation_rank] using hN,?_⟩
    have hh := inverse_rotation_changes J N
    rw [rotation_inverse.1] at hh
    simpa [A] using hh.trans hc

theorem genuine_minimum (M : Mat) (r : ℕ) :
    (∃ N : Mat, N.rank ≤ r ∧ changes M N = rigidity M r) ∧
    (∀ N : Mat, N.rank ≤ r → rigidity M r ≤ changes M N) := by
  have hn : (costs M r).Nonempty := ⟨changes M 0,0,by simp, rfl⟩
  exact ⟨Nat.sInf_mem hn,fun N hN => Nat.sInf_le ⟨N,hN,rfl⟩⟩
theorem full_rigidity_equality : rigidity A = rigidity J := by
  funext r
  unfold rigidity
  rw [identical_attainable_costs]

-- Complex eigenvalues are defined by their actual nonzero eigenvectors.
def eigen (M : Mat) (z : ℂ) : Prop :=
  ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (M.map Complex.ofReal) *ᵥ v = z • v
def spectrum (M : Mat) : Set ℂ := {z | eigen M z}

theorem eigen_A_iff (z : ℂ) : eigen A z ↔ z = 1 := by
  constructor
  · rintro ⟨v,hv,he⟩
    have he0 := congrArg (fun w : Fin 2 → ℂ => w 0) he
    have he1 := congrArg (fun w : Fin 2 → ℂ => w 1) he
    simp [A,Matrix.mulVec, dotProduct,Fin.sum_univ_two] at he0 he1
    by_contra hz
    have h0 : v 0 = 0 := by
      have hp : (z-1)*v 0 = 0 := by linear_combination -he0
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hz)
    have h1 : v 1 = 0 := by
      have hp : (z-1)*v 1 = 0 := by linear_combination -he1
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hz)
    apply hv
    ext i; fin_cases i
    · simpa using h0
    · simpa using h1
  · intro hz; subst z
    refine ⟨![1,0],?_,?_⟩
    · intro h; have hh := congrArg (fun v : Fin 2 → ℂ => v 0) h; norm_num at hh
    · ext i; fin_cases i <;> simp [A,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem eigen_J_iff (z : ℂ) : eigen J z ↔ z = Complex.I ∨ z = -Complex.I := by
  constructor
  · rintro ⟨v,hv,he⟩
    have hx := congrArg (fun w : Fin 2 → ℂ => w 0) he
    have hy := congrArg (fun w : Fin 2 → ℂ => w 1) he
    simp [J,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hx hy
    have hv0 : v 0 ≠ 0 := by
      intro h0
      have h1 : v 1 = 0 := by simpa [h0] using hx
      apply hv
      ext i; fin_cases i
      · simpa using h0
      · simpa using h1
    have hp : (z^2+1)*v 0 = 0 := by linear_combination hy-z*hx
    have hz : z^2+1 = 0 := (mul_eq_zero.mp hp).resolve_right hv0
    have hf : (z-Complex.I)*(z+Complex.I)=0 := by
      calc
        (z-Complex.I)*(z+Complex.I) = z^2-Complex.I^2 := by ring
        _ = 0 := by rw [Complex.I_sq]; simpa using hz
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · rintro (hz|hz) <;> subst z
    · refine ⟨![1,-Complex.I],?_,?_⟩
      · intro h; have hh := congrArg (fun v : Fin 2 → ℂ => v 0) h; norm_num at hh
      · ext i; fin_cases i <;> norm_num [J,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Complex.I_mul_I]
    · refine ⟨![1,Complex.I],?_,?_⟩
      · intro h; have hh := congrArg (fun v : Fin 2 → ℂ => v 0) h; norm_num at hh
      · ext i; fin_cases i <;> norm_num [J,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Complex.I_mul_I]

theorem actual_spectra : spectrum A = {1} ∧ spectrum J = {Complex.I,-Complex.I} := by
  constructor
  · ext z; simp [spectrum,eigen_A_iff]
  · ext z; simp [spectrum,eigen_J_iff]
theorem different_spectra : spectrum A ≠ spectrum J := by
  intro h
  have hm : (1 : ℂ) ∈ spectrum J := by rw [← h]; simp [spectrum,eigen_A_iff]
  rcases (eigen_J_iff 1).mp hm with hi | hi
  all_goals have hh := congrArg Complex.re hi; norm_num at hh

theorem separation : rigidity A = rigidity J ∧ spectrum A ≠ spectrum J ∧
    A.transpose*A=1 ∧ J.transpose*J=1 ∧ (∑ i,∑ j,A i j*J i j)=0 :=
  ⟨full_rigidity_equality,different_spectra,actual_orthogonality.1,
    actual_orthogonality.2.1,frobenius_orthogonal⟩

#print axioms actual_orthogonality
#print axioms frobenius_orthogonal
#print axioms rotation_rank
#print axioms rotation_changes
#print axioms identical_attainable_costs
#print axioms genuine_minimum
#print axioms full_rigidity_equality
#print axioms eigen_A_iff
#print axioms eigen_J_iff
#print axioms actual_spectra
#print axioms different_spectra
#print axioms separation
end RigidityPair
