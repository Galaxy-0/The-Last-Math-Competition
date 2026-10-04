import Conjecture4107.Geometry
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-! The actual intersection poset and characteristic polynomial of a finite real subspace arrangement. -/

noncomputable section
open Finset Polynomial

namespace Conjecture4107

/-- All finite intersections of the given subspaces, ordered by reverse inclusion.
The empty intersection is the ambient space. -/
abbrev IntersectionPoset {n m : ℕ} (A : Fin m → Submodule ℝ (Fin n → ℝ)) :=
  OrderDual {S : Submodule ℝ (Fin n → ℝ) // ∃ s : Finset (Fin m), s.inf A = S}

def intersectionPoint {n m : ℕ} (A : Fin m → Submodule ℝ (Fin n → ℝ))
    (s : Finset (Fin m)) : IntersectionPoset A :=
  ⟨s.inf A, ⟨s, rfl⟩⟩

theorem intersectionPoint_surjective {n m : ℕ}
    (A : Fin m → Submodule ℝ (Fin n → ℝ)) : Function.Surjective (intersectionPoint A) := by
  rintro ⟨S, ⟨s, hs⟩⟩
  exact ⟨s, Subtype.ext hs⟩

instance intersectionFintype {n m : ℕ} (A : Fin m → Submodule ℝ (Fin n → ℝ)) :
    Fintype (IntersectionPoset A) := by
  classical
  exact Fintype.ofSurjective (intersectionPoint A) (intersectionPoint_surjective A)

instance intersectionLocallyFiniteOrder {n m : ℕ}
    (A : Fin m → Submodule ℝ (Fin n → ℝ)) : LocallyFiniteOrder (IntersectionPoset A) := by
  classical
  exact Fintype.toLocallyFiniteOrder

def ambient {n m : ℕ} (A : Fin m → Submodule ℝ (Fin n → ℝ)) : IntersectionPoset A :=
  intersectionPoint A ∅

@[simp] theorem ambient_val {n m : ℕ} (A : Fin m → Submodule ℝ (Fin n → ℝ)) :
    (ambient A).val = ⊤ := by simp [ambient, intersectionPoint]

/-- The poset order is the inclusion order of the actual subspaces, reversed. -/
theorem intersection_le_iff {n m : ℕ} {A : Fin m → Submodule ℝ (Fin n → ℝ)}
    (S T : IntersectionPoset A) : S ≤ T ↔ T.val ≤ S.val := Iff.rfl

theorem ambient_le {n m : ℕ} (A : Fin m → Submodule ℝ (Fin n → ℝ))
    (S : IntersectionPoset A) : ambient A ≤ S := by
  rw [intersection_le_iff, ambient_val]
  exact le_top

/-- The standard Möbius-weighted characteristic polynomial, with actual submodule dimensions. -/
def characteristicPolynomial {n m : ℕ} (A : Fin m → Submodule ℝ (Fin n → ℝ)) : ℤ[X] := by
  classical
  exact ∑ S : IntersectionPoset A,
    C (IncidenceAlgebra.mu ℤ (ambient A) S) * X ^ Module.finrank ℝ S.val

def arrangement : Fin 2 → Submodule ℝ V := ![U, W]

abbrev ConcretePoset := IntersectionPoset arrangement

instance concreteDecidableEq : DecidableEq ConcretePoset := Classical.decEq _

def planePoint : ConcretePoset := intersectionPoint arrangement {0}

def axisPoint : ConcretePoset := intersectionPoint arrangement {1}

def originPoint : ConcretePoset := intersectionPoint arrangement {0, 1}

@[simp] theorem planePoint_val : planePoint.val = U := by
  simp [planePoint, intersectionPoint, arrangement]

@[simp] theorem axisPoint_val : axisPoint.val = W := by
  simp [axisPoint, intersectionPoint, arrangement]

@[simp] theorem originPoint_val : originPoint.val = ⊥ := by
  simp [originPoint, intersectionPoint, arrangement, U_inf_W]

@[simp] theorem finrank_ambientPoint :
    Module.finrank ℝ (ambient arrangement).val = 3 := by
  rw [ambient_val]
  exact finrank_top

@[simp] theorem finrank_planePoint : Module.finrank ℝ planePoint.val = 2 := by
  rw [planePoint_val]
  exact finrank_U

@[simp] theorem finrank_axisPoint : Module.finrank ℝ axisPoint.val = 1 := by
  rw [axisPoint_val]
  exact finrank_W

@[simp] theorem finrank_originPoint : Module.finrank ℝ originPoint.val = 0 := by
  rw [originPoint_val]
  exact finrank_bot

theorem finTwo_subsets (s : Finset (Fin 2)) :
    s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {0, 1} := by
  fin_cases s <;> decide

/-- Every member of the actual finite-intersection poset is one of the four displayed subspaces. -/
theorem concretePoset_cases (S : ConcretePoset) :
    S = ambient arrangement ∨ S = planePoint ∨ S = axisPoint ∨ S = originPoint := by
  obtain ⟨s, hs⟩ := intersectionPoint_surjective arrangement S
  rcases finTwo_subsets s with rfl | rfl | rfl | rfl
  · exact Or.inl hs.symm
  · exact Or.inr (Or.inl hs.symm)
  · exact Or.inr (Or.inr (Or.inl hs.symm))
  · exact Or.inr (Or.inr (Or.inr hs.symm))

theorem concretePoset_univ :
    (Finset.univ : Finset ConcretePoset) = {ambient arrangement, planePoint, axisPoint, originPoint} := by
  classical
  ext S
  simpa only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff] using
    concretePoset_cases S

theorem U_ne_W : U ≠ W := fun h => U_not_le_W h.le

@[simp] theorem concrete_eq_iff (S T : ConcretePoset) : S = T ↔ S.val = T.val :=
  Subtype.ext_iff

theorem Ico_ambient_plane :
    Finset.Ico (ambient arrangement) planePoint = {ambient arrangement} := by
  ext S
  rcases concretePoset_cases S with rfl | rfl | rfl | rfl <;>
    simp [Finset.mem_Ico, lt_iff_le_not_le, intersection_le_iff, Subtype.ext_iff,
      U_not_le_W, W_not_le_U, U_ne_W, eq_comm]

theorem Ico_ambient_axis :
    Finset.Ico (ambient arrangement) axisPoint = {ambient arrangement} := by
  ext S
  rcases concretePoset_cases S with rfl | rfl | rfl | rfl <;>
    simp [Finset.mem_Ico, lt_iff_le_not_le, intersection_le_iff, Subtype.ext_iff,
      U_not_le_W, W_not_le_U, U_ne_W, eq_comm]

theorem Ico_ambient_origin :
    Finset.Ico (ambient arrangement) originPoint =
      {ambient arrangement, planePoint, axisPoint} := by
  ext S
  rcases concretePoset_cases S with rfl | rfl | rfl | rfl <;>
    simp [Finset.mem_Ico, lt_iff_le_not_le, intersection_le_iff, Subtype.ext_iff,
      U_not_le_W, W_not_le_U, U_ne_W, eq_comm]

@[simp] theorem mu_ambient_plane :
    IncidenceAlgebra.mu ℤ (ambient arrangement) planePoint = -1 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne]
  · simp [Ico_ambient_plane]
  · simp [Subtype.ext_iff, eq_comm]

@[simp] theorem mu_ambient_axis :
    IncidenceAlgebra.mu ℤ (ambient arrangement) axisPoint = -1 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne]
  · simp [Ico_ambient_axis]
  · simp [Subtype.ext_iff, eq_comm]

@[simp] theorem mu_ambient_origin :
    IncidenceAlgebra.mu ℤ (ambient arrangement) originPoint = 1 := by
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne]
  · simp [Ico_ambient_origin, Subtype.ext_iff, U_ne_W, eq_comm]
  · simp [Subtype.ext_iff]

/-- The polynomial is computed from the actual intersection poset, its Möbius function,
and the finranks of its real subspaces. -/
theorem characteristicPolynomial_arrangement :
    characteristicPolynomial arrangement = X ^ 3 - X ^ 2 - X + 1 := by
  unfold characteristicPolynomial
  rw [concretePoset_univ]
  simp [Subtype.ext_iff, U_ne_W, eq_comm]
  ring

end Conjecture4107
