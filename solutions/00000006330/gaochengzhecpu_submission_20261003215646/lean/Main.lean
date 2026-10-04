import Std

namespace Conjecture6330

abbrev Matrix := Fin 2 → Fin 2 → Int

/-- The actual row-column product; the index set has exactly two entries. -/
def mul (M N : Matrix) : Matrix := fun i j => M i 0 * N 0 j + M i 1 * N 1 j
def det (M : Matrix) : Int := M 0 0 * M 1 1 - M 0 1 * M 1 0
def permanent (M : Matrix) : Int := M 0 0 * M 1 1 + M 0 1 * M 1 0
def Unimodular (M : Matrix) : Prop := det M = 1 ∨ det M = -1

def RowEquivalent (M N : Matrix) : Prop :=
  ∃ U : Matrix, Unimodular U ∧ mul U M = N

def IntegerEquivalent (M N : Matrix) : Prop :=
  ∃ U V : Matrix, Unimodular U ∧ Unimodular V ∧ mul (mul U M) V = N

def A : Matrix := fun i j => if i = j then if i = 0 then 1 else 4 else 0
def B : Matrix := fun i j => if i = j then 2 else 0

theorem equal_determinants : det A = 4 ∧ det B = 4 := by decide
theorem equal_permanents : permanent A = 4 ∧ permanent B = 4 := by decide

/-- Positive diagonal entries in divisibility order are already Smith form. -/
def SmithDiagonal (M : Matrix) : Prop :=
  M 0 1 = 0 ∧ M 1 0 = 0 ∧ 0 < M 0 0 ∧ 0 < M 1 1 ∧ M 0 0 ∣ M 1 1
instance (M : Matrix) : Decidable (SmithDiagonal M) := by
  unfold SmithDiagonal; infer_instance

theorem actual_smith_forms : SmithDiagonal A ∧ SmithDiagonal B ∧
    A 0 0 = 1 ∧ A 1 1 = 4 ∧ B 0 0 = 2 ∧ B 1 1 = 2 := by decide

def EvenMatrix (M : Matrix) : Prop := ∀ i j, ∃ k : Int, M i j = 2*k

theorem B_even : EvenMatrix B := by
  intro i j
  by_cases h : i = j
  · refine ⟨1, ?_⟩; simp [B, h]
  · refine ⟨0, ?_⟩; simp [B, h]

theorem A_not_even : ¬ EvenMatrix A := by
  intro h
  obtain ⟨k, hk⟩ := h 0 0
  change (1 : Int) = 2*k at hk
  omega

/-- This is universal over ALL integer matrices, with no bounded search. -/
theorem even_left_product (M U : Matrix) (hM : EvenMatrix M) : EvenMatrix (mul U M) := by
  intro i j
  obtain ⟨a, ha⟩ := hM 0 j
  obtain ⟨b, hb⟩ := hM 1 j
  refine ⟨U i 0*a + U i 1*b, ?_⟩
  unfold mul
  rw [ha, hb]
  simp [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem even_right_product (M V : Matrix) (hM : EvenMatrix M) : EvenMatrix (mul M V) := by
  intro i j
  obtain ⟨a, ha⟩ := hM i 0
  obtain ⟨b, hb⟩ := hM i 1
  refine ⟨a*V 0 j + b*V 1 j, ?_⟩
  unfold mul
  rw [ha, hb]
  simp [Int.mul_add, Int.mul_assoc]

theorem no_integer_double_transform (U V : Matrix) : mul (mul U B) V ≠ A := by
  intro h
  have he := even_right_product (mul U B) V (even_left_product B U B_even)
  rw [h] at he
  exact A_not_even he

theorem no_row_transform_B_A (U : Matrix) : mul U B ≠ A := by
  intro h
  have he := even_left_product B U B_even
  rw [h] at he
  exact A_not_even he

theorem no_row_transform_A_B (U : Matrix) : mul U A ≠ B := by
  intro h
  have h11 := congrFun (congrFun h 1) 1
  change U 1 0 * 0 + U 1 1 * 4 = 2 at h11
  omega

theorem not_integer_equivalent : ¬ IntegerEquivalent B A := by
  rintro ⟨U,V,_,_,h⟩
  exact no_integer_double_transform U V h

theorem not_row_equivalent_both_directions :
    ¬ RowEquivalent B A ∧ ¬ RowEquivalent A B := by
  constructor
  · rintro ⟨U,_,h⟩; exact no_row_transform_B_A U h
  · rintro ⟨U,_,h⟩; exact no_row_transform_A_B U h

/-- A complete existence witness for the separation in the source. It even
    separates the coarser equivalence allowing unimodular column operations. -/
theorem conjecture_6330 : ∃ M N : Matrix,
    det M = det N ∧ permanent M = permanent N ∧
    SmithDiagonal M ∧ SmithDiagonal N ∧
    ¬ RowEquivalent M N ∧ ¬ RowEquivalent N M ∧ ¬ IntegerEquivalent M N := by
  refine ⟨B,A,?_,?_,actual_smith_forms.2.1,actual_smith_forms.1,
    not_row_equivalent_both_directions.1,not_row_equivalent_both_directions.2,
    not_integer_equivalent⟩
  · exact equal_determinants.2.trans equal_determinants.1.symm
  · exact equal_permanents.2.trans equal_permanents.1.symm

#print axioms no_integer_double_transform
#print axioms not_row_equivalent_both_directions
#print axioms conjecture_6330
end Conjecture6330
