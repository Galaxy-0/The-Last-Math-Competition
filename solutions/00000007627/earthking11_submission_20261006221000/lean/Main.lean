import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Central.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

/-!
Counterexample to conjecture 00000007627 using the actual matrix ring
`M₂(F₂)` and its left regular module.
-/

namespace TLMC7627

abbrev K := ZMod 2
abbrev R := Matrix (Fin 2) (Fin 2) K

/-- The identity one-factor decomposition of this matrix ring as a finite
direct product of matrix factors (with the sole factor indexed by `Fin 1`). -/
def matrixOneFactorDecomposition : R ≃+* (Fin 1 → Matrix (Fin 2) (Fin 2) K) :=
  (RingEquiv.piUnique (fun _ : Fin 1 => R)).symm

instance : IsSimpleRing K := inferInstance
instance : IsSimpleRing R := inferInstance

/-- The first coordinate-column left ideal in the left regular module. -/
def leftColumn0 : Submodule R R where
  carrier := {A | ∀ i : Fin 2, A i 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i
    simp [hA i, hB i]
  smul_mem' := by
    intro C A hA i
    change (C * A) i 1 = 0
    change ∀ i : Fin 2, A i 1 = 0 at hA
    simp [Matrix.mul_apply, hA]

/-- The second coordinate-column left ideal in the left regular module. -/
def leftColumn1 : Submodule R R where
  carrier := {A | ∀ i : Fin 2, A i 0 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i
    simp [hA i, hB i]
  smul_mem' := by
    intro C A hA i
    change (C * A) i 0 = 0
    change ∀ i : Fin 2, A i 0 = 0 at hA
    simp [Matrix.mul_apply, hA]

/-- Minimality for left ideals of the left regular module. -/
def IsMinimalLeftIdeal (I : Submodule R R) : Prop :=
  I ≠ ⊥ ∧ ∀ J : Submodule R R, J ≤ I → J ≠ ⊥ → I ≤ J

/-- The genuine set of minimal left ideals of the left regular module. -/
def MinimalLeftIdeal := {I : Submodule R R // IsMinimalLeftIdeal I}

instance : Finite (Submodule R R) :=
  Finite.of_injective (fun I : Submodule R R => (I : Set R))
    (fun _ _ h => SetLike.coe_injective h)

instance : Finite MinimalLeftIdeal :=
  Finite.of_injective (fun I : MinimalLeftIdeal => I.1) Subtype.val_injective

/-- Any nonzero matrix supported in column 0 left-generates that column ideal. -/
theorem leftMul_surjective_column0 (A B : R) (hA : A ∈ leftColumn0)
    (hAnz : A ≠ 0) (hB : B ∈ leftColumn0) : ∃ C : R, C * A = B := by
  change ∀ i, A i 1 = 0 at hA
  change ∀ i, B i 1 = 0 at hB
  have hpivot : A 0 0 = 1 ∨ A 1 0 = 1 := by
    by_contra hn
    have h00or : A 0 0 = 0 ∨ A 0 0 = 1 := by
      have hv := (A 0 0).val_lt
      have hv' : (A 0 0).val = 0 ∨ (A 0 0).val = 1 := by omega
      rcases hv' with hv' | hv'
      · exact Or.inl ((ZMod.val_eq_zero _).mp hv')
      · exact Or.inr ((ZMod.val_eq_one (by norm_num) _).mp hv')
    have h10or : A 1 0 = 0 ∨ A 1 0 = 1 := by
      have hv := (A 1 0).val_lt
      have hv' : (A 1 0).val = 0 ∨ (A 1 0).val = 1 := by omega
      rcases hv' with hv' | hv'
      · exact Or.inl ((ZMod.val_eq_zero _).mp hv')
      · exact Or.inr ((ZMod.val_eq_one (by norm_num) _).mp hv')
    have h00 : A 0 0 = 0 := by
      rcases h00or with h | h
      · exact h
      · exact False.elim (hn (Or.inl h))
    have h10 : A 1 0 = 0 := by
      rcases h10or with h | h
      · exact h
      · exact False.elim (hn (Or.inr h))
    apply hAnz
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  rcases hpivot with hpivot | hpivot
  · let C : R := fun i j => if j = 0 then B i 0 else 0
    refine ⟨C, ?_⟩
    ext i j
    change (∑ k : Fin 2, C i k * A k j) = B i j
    fin_cases j <;> simp [C, hpivot, hA, hB]
  · let C : R := fun i j => if j = 1 then B i 0 else 0
    refine ⟨C, ?_⟩
    ext i j
    change (∑ k : Fin 2, C i k * A k j) = B i j
    fin_cases j <;> simp [C, hpivot, hA, hB]

/-- Any nonzero matrix supported in column 1 left-generates that column ideal. -/
theorem leftMul_surjective_column1 (A B : R) (hA : A ∈ leftColumn1)
    (hAnz : A ≠ 0) (hB : B ∈ leftColumn1) : ∃ C : R, C * A = B := by
  change ∀ i, A i 0 = 0 at hA
  change ∀ i, B i 0 = 0 at hB
  have hpivot : A 0 1 = 1 ∨ A 1 1 = 1 := by
    by_contra hn
    have h01or : A 0 1 = 0 ∨ A 0 1 = 1 := by
      have hv := (A 0 1).val_lt
      have hv' : (A 0 1).val = 0 ∨ (A 0 1).val = 1 := by omega
      rcases hv' with hv' | hv'
      · exact Or.inl ((ZMod.val_eq_zero _).mp hv')
      · exact Or.inr ((ZMod.val_eq_one (by norm_num) _).mp hv')
    have h11or : A 1 1 = 0 ∨ A 1 1 = 1 := by
      have hv := (A 1 1).val_lt
      have hv' : (A 1 1).val = 0 ∨ (A 1 1).val = 1 := by omega
      rcases hv' with hv' | hv'
      · exact Or.inl ((ZMod.val_eq_zero _).mp hv')
      · exact Or.inr ((ZMod.val_eq_one (by norm_num) _).mp hv')
    have h01 : A 0 1 = 0 := by
      rcases h01or with h | h
      · exact h
      · exact False.elim (hn (Or.inl h))
    have h11 : A 1 1 = 0 := by
      rcases h11or with h | h
      · exact h
      · exact False.elim (hn (Or.inr h))
    apply hAnz
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  rcases hpivot with hpivot | hpivot
  · let C : R := fun i j => if j = 0 then B i 1 else 0
    refine ⟨C, ?_⟩
    ext i j
    change (∑ k : Fin 2, C i k * A k j) = B i j
    fin_cases j <;> simp [C, hpivot, hA, hB]
  · let C : R := fun i j => if j = 1 then B i 1 else 0
    refine ⟨C, ?_⟩
    ext i j
    change (∑ k : Fin 2, C i k * A k j) = B i j
    fin_cases j <;> simp [C, hpivot, hA, hB]

theorem leftColumn0_minimal : IsMinimalLeftIdeal leftColumn0 := by
  constructor
  · intro h
    have hE : (Matrix.single 0 0 (1 : K) : R) ∈ leftColumn0 := by simp [leftColumn0]
    have hzero : (Matrix.single 0 0 (1 : K) : R) ∈ (⊥ : Submodule R R) := by
      rw [← h]
      exact hE
    have : (Matrix.single 0 0 (1 : K) : R) = 0 := by simpa using hzero
    have h00 := congrFun (congrFun this 0) 0
    simp at h00
  · intro J hJI hJ
    obtain ⟨A, hAJ, hAnz⟩ := (Submodule.ne_bot_iff J).mp hJ
    intro B hB
    obtain ⟨C, hC⟩ := leftMul_surjective_column0 A B (hJI hAJ) hAnz hB
    rw [← hC]
    exact J.smul_mem C hAJ

theorem leftColumn1_minimal : IsMinimalLeftIdeal leftColumn1 := by
  constructor
  · intro h
    have hE : (Matrix.single 0 1 (1 : K) : R) ∈ leftColumn1 := by simp [leftColumn1]
    have hzero : (Matrix.single 0 1 (1 : K) : R) ∈ (⊥ : Submodule R R) := by
      rw [← h]
      exact hE
    have : (Matrix.single 0 1 (1 : K) : R) = 0 := by simpa using hzero
    have h01 := congrFun (congrFun this 0) 1
    simp at h01
  · intro J hJI hJ
    obtain ⟨A, hAJ, hAnz⟩ := (Submodule.ne_bot_iff J).mp hJ
    intro B hB
    obtain ⟨C, hC⟩ := leftMul_surjective_column1 A B (hJI hAJ) hAnz hB
    rw [← hC]
    exact J.smul_mem C hAJ

theorem leftColumn0_ne_leftColumn1 : leftColumn0 ≠ leftColumn1 := by
  intro h
  have hE : (Matrix.single 0 0 (1 : K) : R) ∈ leftColumn0 := by simp [leftColumn0]
  have hbad : (Matrix.single 0 0 (1 : K) : R) ∈ leftColumn1 := by
    rw [← h]
    exact hE
  simp [leftColumn1] at hbad

theorem matrix_ring_center_finrank :
    Module.finrank K (Subalgebra.center K R) = 1 := by
  rw [Algebra.IsCentral.center_eq_bot]
  exact Subalgebra.finrank_bot

theorem minimal_left_ideal_count_at_least_two :
    2 ≤ Nat.card MinimalLeftIdeal := by
  classical
  let : Fintype MinimalLeftIdeal := Fintype.ofFinite MinimalLeftIdeal
  let f : Fin 2 → MinimalLeftIdeal := fun i =>
    if i = 0 then ⟨leftColumn0, leftColumn0_minimal⟩
    else ⟨leftColumn1, leftColumn1_minimal⟩
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (leftColumn0_ne_leftColumn1 (congrArg Subtype.val hij))
    · exact False.elim (leftColumn0_ne_leftColumn1 (congrArg Subtype.val hij).symm)
    · rfl
  rw [Nat.card_eq_fintype_card]
  simpa using Fintype.card_le_of_injective f hf

theorem minimal_left_ideal_count_ne_center_dimension :
    Nat.card MinimalLeftIdeal ≠ Module.finrank K (Subalgebra.center K R) := by
  rw [matrix_ring_center_finrank]
  exact Nat.ne_of_gt (lt_of_lt_of_le (by omega) minimal_left_ideal_count_at_least_two)

theorem matrix_factor_index_card : Nat.card (Fin 1) = 1 := by
  simp

theorem minimal_left_ideal_count_ne_matrix_factor_count :
    Nat.card MinimalLeftIdeal ≠ Nat.card (Fin 1) := by
  rw [matrix_factor_index_card]
  exact Nat.ne_of_gt (lt_of_lt_of_le (by omega) minimal_left_ideal_count_at_least_two)

/-- Actual ring decomposition and both actual counting mismatches together. -/
theorem actual_matrix_counterexample :
    Nonempty (R ≃+* (Fin 1 → Matrix (Fin 2) (Fin 2) K)) ∧
      IsSimpleRing R ∧
      2 ≤ Nat.card MinimalLeftIdeal ∧
      Module.finrank K (Subalgebra.center K R) = 1 ∧
      Nat.card MinimalLeftIdeal ≠ Nat.card (Fin 1) ∧
      Nat.card MinimalLeftIdeal ≠ Module.finrank K (Subalgebra.center K R) := by
  exact ⟨⟨matrixOneFactorDecomposition⟩, inferInstance,
    minimal_left_ideal_count_at_least_two, matrix_ring_center_finrank,
    minimal_left_ideal_count_ne_matrix_factor_count,
    minimal_left_ideal_count_ne_center_dimension⟩

#print axioms leftColumn0_minimal
#print axioms leftColumn1_minimal
#print axioms matrixOneFactorDecomposition
#print axioms matrix_ring_center_finrank
#print axioms minimal_left_ideal_count_ne_center_dimension
#print axioms minimal_left_ideal_count_ne_matrix_factor_count
#print axioms actual_matrix_counterexample

end TLMC7627
