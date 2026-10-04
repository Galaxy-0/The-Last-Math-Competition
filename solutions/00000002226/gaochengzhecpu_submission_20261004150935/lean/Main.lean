import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.BigOperators.Fin

/-! For a nonzero commutative ring `R` and `n ≥ 1`, the matrix ring `M_n(R)` has the McCoy
property if and only if `n = 1`. For `n ≥ 2` it is neither right nor left McCoy. -/
namespace Conjecture2226

open Polynomial Matrix

section Definitions

variable (A : Type*) [Ring A]

/-- Right McCoy: if `f g = 0` with `f, g ≠ 0`, a nonzero constant annihilates `f` on the right. -/
def RightMcCoy : Prop :=
  ∀ f g : A[X], f ≠ 0 → g ≠ 0 → f * g = 0 → ∃ r : A, r ≠ 0 ∧ f * C r = 0

/-- Left McCoy: if `f g = 0` with `f, g ≠ 0`, a nonzero constant annihilates `g` on the left. -/
def LeftMcCoy : Prop :=
  ∀ f g : A[X], f ≠ 0 → g ≠ 0 → f * g = 0 → ∃ s : A, s ≠ 0 ∧ C s * g = 0

/-- The McCoy property: both one-sided conditions. -/
def McCoy : Prop := RightMcCoy A ∧ LeftMcCoy A

end Definitions

/-! ### Commutative rings are McCoy (McCoy's theorem) -/

theorem leftMcCoy_of_comm (R : Type*) [CommRing R] : LeftMcCoy R := by
  intro f g hf _ hfg
  have hg : g ∉ nonZeroDivisors R[X] := fun h => hf (mem_nonZeroDivisors_iff.mp h f hfg)
  obtain ⟨a, ha, h⟩ := Polynomial.nmem_nonZeroDivisors_iff.mp hg
  exact ⟨a, ha, by rw [← smul_eq_C_mul]; exact h⟩

theorem rightMcCoy_of_comm (R : Type*) [CommRing R] : RightMcCoy R := by
  intro f g _ hg hfg
  have hf : f ∉ nonZeroDivisors R[X] := fun h =>
    hg (mem_nonZeroDivisors_iff.mp h g (by rw [mul_comm]; exact hfg))
  obtain ⟨a, ha, h⟩ := Polynomial.nmem_nonZeroDivisors_iff.mp hf
  exact ⟨a, ha, by rw [mul_comm, ← smul_eq_C_mul]; exact h⟩

/-! ### The property is invariant under ring isomorphism -/

section Transfer

variable {A B : Type*} [Ring A] [Ring B]

theorem RightMcCoy.of_ringEquiv (e : A ≃+* B) (hB : RightMcCoy B) : RightMcCoy A := by
  intro f g hf hg hfg
  have hinj : Function.Injective (Polynomial.map (e : A →+* B)) :=
    Polynomial.map_injective _ e.injective
  have hf' : f.map (e : A →+* B) ≠ 0 := fun h => hf (hinj (by rw [h, Polynomial.map_zero]))
  have hg' : g.map (e : A →+* B) ≠ 0 := fun h => hg (hinj (by rw [h, Polynomial.map_zero]))
  have hfg' : f.map (e : A →+* B) * g.map (e : A →+* B) = 0 := by
    rw [← Polynomial.map_mul, hfg, Polynomial.map_zero]
  obtain ⟨r, hr, h⟩ := hB _ _ hf' hg' hfg'
  refine ⟨e.symm r, fun h0 => hr ?_, hinj ?_⟩
  · have h1 := congrArg e h0
    rwa [e.apply_symm_apply, map_zero] at h1
  · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_zero, RingEquiv.coe_toRingHom,
      e.apply_symm_apply]
    exact h

theorem LeftMcCoy.of_ringEquiv (e : A ≃+* B) (hB : LeftMcCoy B) : LeftMcCoy A := by
  intro f g hf hg hfg
  have hinj : Function.Injective (Polynomial.map (e : A →+* B)) :=
    Polynomial.map_injective _ e.injective
  have hf' : f.map (e : A →+* B) ≠ 0 := fun h => hf (hinj (by rw [h, Polynomial.map_zero]))
  have hg' : g.map (e : A →+* B) ≠ 0 := fun h => hg (hinj (by rw [h, Polynomial.map_zero]))
  have hfg' : f.map (e : A →+* B) * g.map (e : A →+* B) = 0 := by
    rw [← Polynomial.map_mul, hfg, Polynomial.map_zero]
  obtain ⟨s, hs, h⟩ := hB _ _ hf' hg' hfg'
  refine ⟨e.symm s, fun h0 => hs ?_, hinj ?_⟩
  · have h1 := congrArg e h0
    rwa [e.apply_symm_apply, map_zero] at h1
  · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_zero, RingEquiv.coe_toRingHom,
      e.apply_symm_apply]
    exact h

end Transfer

/-! ### Two-term polynomial identities over an arbitrary ring -/

section TwoTerm

variable {A : Type*} [Ring A]

theorem two_term_mul (a b c d : A) (h1 : a * c = 0) (h2 : b * c = a * d) (h3 : b * d = 0) :
    (monomial 0 a + monomial 1 b) * (monomial 0 c - monomial 1 d) = 0 := by
  simp only [add_mul, mul_sub, monomial_mul_monomial, h1, h2, h3]
  simp

theorem two_term_mul' (a b c d : A) (h1 : a * c = 0) (h2 : a * d = b * c) (h3 : b * d = 0) :
    (monomial 0 a - monomial 1 b) * (monomial 0 c + monomial 1 d) = 0 := by
  simp only [sub_mul, mul_add, monomial_mul_monomial, h1, h2, h3]
  simp

theorem coeffs_of_mul_C (a b r : A) (h : (monomial 0 a + monomial 1 b) * C r = 0) :
    a * r = 0 ∧ b * r = 0 := by
  rw [← monomial_zero_left r, add_mul, monomial_mul_monomial, monomial_mul_monomial] at h
  constructor
  · have h0 := congrArg (fun p => p.coeff 0) h
    simpa [coeff_monomial] using h0
  · have h1 := congrArg (fun p => p.coeff 1) h
    simpa [coeff_monomial] using h1

theorem coeffs_of_C_mul (s c d : A) (h : C s * (monomial 0 c + monomial 1 d) = 0) :
    s * c = 0 ∧ s * d = 0 := by
  rw [← monomial_zero_left s, mul_add, monomial_mul_monomial, monomial_mul_monomial] at h
  constructor
  · have h0 := congrArg (fun p => p.coeff 0) h
    simpa [coeff_monomial] using h0
  · have h1 := congrArg (fun p => p.coeff 1) h
    simpa [coeff_monomial] using h1

end TwoTerm

/-! ### Matrix rings of size at least two are neither right nor left McCoy -/

section MatrixCounterexample

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Type*} [Ring S] [Nontrivial S]

omit [Fintype ι] in
theorem unit_ne_zero (a b : ι) : (stdBasisMatrix a b (1 : S) : Matrix ι ι S) ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun h a) b
  rw [StdBasisMatrix.apply_same] at h1
  exact one_ne_zero h1

/-- With `f = (1 - E_jj) + E_ij X` and `g = E_ji - E_ii X` one has `f g = 0`, while no nonzero
constant matrix annihilates `f` on the right. -/
theorem not_rightMcCoy_matrix {i j : ι} (hij : i ≠ j) : ¬ RightMcCoy (Matrix ι ι S) := by
  intro hM
  have h1 : (1 - stdBasisMatrix j j (1 : S)) * stdBasisMatrix j i (1 : S) = 0 := by
    rw [sub_mul, one_mul, StdBasisMatrix.mul_same, mul_one, sub_self]
  have h2 : stdBasisMatrix i j (1 : S) * stdBasisMatrix j i (1 : S)
      = (1 - stdBasisMatrix j j (1 : S)) * stdBasisMatrix i i (1 : S) := by
    rw [sub_mul, one_mul, StdBasisMatrix.mul_same, mul_one,
      StdBasisMatrix.mul_of_ne _ _ _ _ hij.symm, sub_zero]
  have h3 : stdBasisMatrix i j (1 : S) * stdBasisMatrix i i (1 : S) = 0 :=
    StdBasisMatrix.mul_of_ne _ _ _ _ hij.symm _
  have hf : monomial 0 (1 - stdBasisMatrix j j (1 : S)) + monomial 1 (stdBasisMatrix i j (1 : S))
      ≠ 0 := by
    intro h
    have hc := congrArg (fun p => p.coeff 1) h
    simp only [coeff_add, coeff_monomial, coeff_zero] at hc
    simp only [zero_ne_one, if_false, if_true, zero_add] at hc
    exact unit_ne_zero i j hc
  have hg : monomial 0 (stdBasisMatrix j i (1 : S)) - monomial 1 (stdBasisMatrix i i (1 : S))
      ≠ 0 := by
    intro h
    have hc := congrArg (fun p => p.coeff 0) h
    simp only [coeff_sub, coeff_monomial, coeff_zero] at hc
    simp only [one_ne_zero, if_false, if_true, sub_zero] at hc
    exact unit_ne_zero j i hc
  obtain ⟨r, hr, h⟩ := hM _ _ hf hg (two_term_mul _ _ _ _ h1 h2 h3)
  obtain ⟨har, hbr⟩ := coeffs_of_mul_C _ _ r h
  apply hr
  have hjj : stdBasisMatrix j j (1 : S) * r = r := by
    rw [sub_mul, one_mul, sub_eq_zero] at har
    exact har.symm
  calc r = stdBasisMatrix j j (1 : S) * r := hjj.symm
    _ = stdBasisMatrix j i (1 : S) * stdBasisMatrix i j (1 : S) * r := by
        rw [StdBasisMatrix.mul_same, mul_one]
    _ = stdBasisMatrix j i (1 : S) * (stdBasisMatrix i j (1 : S) * r) := mul_assoc _ _ _
    _ = 0 := by rw [hbr, mul_zero]

/-- With `f = E_ij - E_ii X` and `g = (1 - E_jj) + E_ji X` one has `f g = 0`, while no nonzero
constant matrix annihilates `g` on the left. -/
theorem not_leftMcCoy_matrix {i j : ι} (hij : i ≠ j) : ¬ LeftMcCoy (Matrix ι ι S) := by
  intro hM
  have h1 : stdBasisMatrix i j (1 : S) * (1 - stdBasisMatrix j j (1 : S)) = 0 := by
    rw [mul_sub, mul_one, StdBasisMatrix.mul_same, mul_one, sub_self]
  have h2 : stdBasisMatrix i j (1 : S) * stdBasisMatrix j i (1 : S)
      = stdBasisMatrix i i (1 : S) * (1 - stdBasisMatrix j j (1 : S)) := by
    rw [mul_sub, mul_one, StdBasisMatrix.mul_same, mul_one,
      StdBasisMatrix.mul_of_ne _ _ _ _ hij, sub_zero]
  have h3 : stdBasisMatrix i i (1 : S) * stdBasisMatrix j i (1 : S) = 0 :=
    StdBasisMatrix.mul_of_ne _ _ _ _ hij _
  have hf : monomial 0 (stdBasisMatrix i j (1 : S)) - monomial 1 (stdBasisMatrix i i (1 : S))
      ≠ 0 := by
    intro h
    have hc := congrArg (fun p => p.coeff 0) h
    simp only [coeff_sub, coeff_monomial, coeff_zero] at hc
    simp only [one_ne_zero, if_false, if_true, sub_zero] at hc
    exact unit_ne_zero i j hc
  have hg : monomial 0 (1 - stdBasisMatrix j j (1 : S)) + monomial 1 (stdBasisMatrix j i (1 : S))
      ≠ 0 := by
    intro h
    have hc := congrArg (fun p => p.coeff 1) h
    simp only [coeff_add, coeff_monomial, coeff_zero] at hc
    simp only [zero_ne_one, if_false, if_true, zero_add] at hc
    exact unit_ne_zero j i hc
  obtain ⟨s, hs, h⟩ := hM _ _ hf hg (two_term_mul' _ _ _ _ h1 h2 h3)
  obtain ⟨hsc, hsd⟩ := coeffs_of_C_mul s _ _ h
  apply hs
  have hjj : s * stdBasisMatrix j j (1 : S) = s := by
    rw [mul_sub, mul_one, sub_eq_zero] at hsc
    exact hsc.symm
  calc s = s * stdBasisMatrix j j (1 : S) := hjj.symm
    _ = s * (stdBasisMatrix j i (1 : S) * stdBasisMatrix i j (1 : S)) := by
        rw [StdBasisMatrix.mul_same, mul_one]
    _ = s * stdBasisMatrix j i (1 : S) * stdBasisMatrix i j (1 : S) := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hsd, zero_mul]

end MatrixCounterexample

/-! ### The matrix rings `M_n(R)` -/

theorem two_indices {n : ℕ} (hn : 2 ≤ n) :
    (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
  intro h
  have h1 := congrArg Fin.val h
  simp at h1

theorem not_rightMcCoy_fin (S : Type*) [Ring S] [Nontrivial S] {n : ℕ} (hn : 2 ≤ n) :
    ¬ RightMcCoy (Matrix (Fin n) (Fin n) S) :=
  not_rightMcCoy_matrix (two_indices hn)

theorem not_leftMcCoy_fin (S : Type*) [Ring S] [Nontrivial S] {n : ℕ} (hn : 2 ≤ n) :
    ¬ LeftMcCoy (Matrix (Fin n) (Fin n) S) :=
  not_leftMcCoy_matrix (two_indices hn)

/-- `M_1(R)` is isomorphic to `R` by reading off its single entry. -/
def oneByOne (R : Type*) [Ring R] : Matrix (Fin 1) (Fin 1) R ≃+* R where
  toFun M := M 0 0
  invFun r := Matrix.of fun _ _ => r
  left_inv M := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    rfl
  right_inv _ := rfl
  map_mul' M N := by
    rw [Matrix.mul_apply, Fin.sum_univ_one]
  map_add' _ _ := rfl

theorem mcCoy_one (R : Type*) [CommRing R] : McCoy (Matrix (Fin 1) (Fin 1) R) :=
  ⟨(rightMcCoy_of_comm R).of_ringEquiv (oneByOne R),
   (leftMcCoy_of_comm R).of_ringEquiv (oneByOne R)⟩

/-- The conjecture, for a nonzero commutative ring `R` and `n ≥ 1`. -/
theorem matrix_mcCoy_iff (R : Type*) [CommRing R] [Nontrivial R] {n : ℕ} (hn : 1 ≤ n) :
    McCoy (Matrix (Fin n) (Fin n) R) ↔ n = 1 := by
  constructor
  · intro h
    by_contra hne
    exact not_rightMcCoy_fin R (by omega) h.1
  · rintro rfl
    exact mcCoy_one R

/-- The same equivalence for the right-handed property alone. -/
theorem matrix_rightMcCoy_iff (R : Type*) [CommRing R] [Nontrivial R] {n : ℕ} (hn : 1 ≤ n) :
    RightMcCoy (Matrix (Fin n) (Fin n) R) ↔ n = 1 := by
  constructor
  · intro h
    by_contra hne
    exact not_rightMcCoy_fin R (by omega) h
  · rintro rfl
    exact (mcCoy_one R).1

/-- The same equivalence for the left-handed property alone. -/
theorem matrix_leftMcCoy_iff (R : Type*) [CommRing R] [Nontrivial R] {n : ℕ} (hn : 1 ≤ n) :
    LeftMcCoy (Matrix (Fin n) (Fin n) R) ↔ n = 1 := by
  constructor
  · intro h
    by_contra hne
    exact not_leftMcCoy_fin R (by omega) h
  · rintro rfl
    exact (mcCoy_one R).2

/-- Degenerate case: the zero ring is McCoy vacuously. This is why `R ≠ 0` and `n ≥ 1` are
assumed above: `M_n(0)` and `M_0(R)` are zero rings. -/
theorem mcCoy_of_subsingleton (A : Type*) [Ring A] [Subsingleton A] : McCoy A :=
  ⟨fun f _ hf _ _ => absurd (Subsingleton.elim f 0) hf,
   fun f _ hf _ _ => absurd (Subsingleton.elim f 0) hf⟩

#print axioms leftMcCoy_of_comm
#print axioms rightMcCoy_of_comm
#print axioms not_rightMcCoy_matrix
#print axioms not_leftMcCoy_matrix
#print axioms mcCoy_one
#print axioms matrix_mcCoy_iff
#print axioms matrix_rightMcCoy_iff
#print axioms matrix_leftMcCoy_iff
#print axioms mcCoy_of_subsingleton

end Conjecture2226
