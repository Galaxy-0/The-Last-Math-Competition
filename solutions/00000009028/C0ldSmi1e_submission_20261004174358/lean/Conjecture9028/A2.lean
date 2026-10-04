import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators InnerProductSpace

namespace Conjecture9028.A2

abbrev Ambient := EuclideanSpace ℝ (Fin 3)

/-- The real plane containing the standard root lattice A₂. -/
def space : Submodule ℝ Ambient where
  carrier := {x | x 0 + x 1 + x 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (x 0 + y 0) + (x 1 + y 1) + (x 2 + y 2) = 0
    change x 0 + x 1 + x 2 = 0 at hx
    change y 0 + y 1 + y 2 = 0 at hy
    linarith
  smul_mem' := by
    intro a x hx
    change a * x 0 + a * x 1 + a * x 2 = 0
    change x 0 + x 1 + x 2 = 0 at hx
    linear_combination a * hx

def coordinatesEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] space where
  toFun := fun x => ⟨(WithLp.equiv 2 (Fin 3 → ℝ)).symm ![x 0, -x 0 + x 1, -x 1],
    by change x 0 + (-x 0 + x 1) + -x 1 = 0; ring⟩
  invFun := fun x => ![(x : Ambient) 0, -(x : Ambient) 2]
  left_inv := by
    intro x
    ext i
    fin_cases i <;> simp
  right_inv := by
    intro x
    apply Subtype.ext
    ext i
    have hx := x.property
    change (x : Ambient) 0 + (x : Ambient) 1 + (x : Ambient) 2 = 0 at hx
    fin_cases i
    · simp
    · simp; linarith
    · simp
  map_add' := by
    intro x y
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [add_comm, add_left_comm, add_assoc]
  map_smul' := by
    intro a x
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [mul_add]

def realBasis : Basis (Fin 2) ℝ space := (Pi.basisFun ℝ (Fin 2)).map coordinatesEquiv

def lattice : Submodule ℤ space := Submodule.span ℤ (Set.range realBasis)

def intBasis : Basis (Fin 2) ℤ lattice := realBasis.restrictScalars ℤ

theorem intBasis_coe (i : Fin 2) : (intBasis i : space) = realBasis i :=
  realBasis.restrictScalars_apply ℤ i

instance lattice_discrete : DiscreteTopology lattice := by
  unfold lattice
  infer_instance

instance lattice_isZLattice : IsZLattice ℝ lattice := by
  unfold lattice
  infer_instance

theorem space_finrank : Module.finrank ℝ space = 2 := by
  simpa using Module.finrank_eq_card_basis realBasis

theorem lattice_finrank : Module.finrank ℤ lattice = 2 := by
  simpa using Module.finrank_eq_card_basis intBasis

theorem realBasis_apply (i : Fin 2) :
    ((realBasis i : space) : Ambient) =
      (WithLp.equiv 2 (Fin 3 → ℝ)).symm
        ![if i = 0 then 1 else 0, if i = 0 then -1 else 1, if i = 0 then 0 else -1] := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [realBasis, coordinatesEquiv, Pi.basisFun_apply]

def coord (x : lattice) : Fin 2 → ℤ := intBasis.repr x

theorem lattice_coordinates (x : lattice) :
    ((x : space) : Ambient) =
      (WithLp.equiv 2 (Fin 3 → ℝ)).symm
        ![(coord x 0 : ℝ), -(coord x 0 : ℝ) + (coord x 1 : ℝ), -(coord x 1 : ℝ)] := by
  have hx := congrArg (fun y : lattice => ((y : space) : Ambient)) (intBasis.sum_repr x)
  calc
    ((x : space) : Ambient) =
        coord x 0 • ((realBasis 0 : space) : Ambient) +
        coord x 1 • ((realBasis 1 : space) : Ambient) := by
      simpa only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower,
        intBasis_coe, coord] using hx.symm
    _ = _ := by
      ext i
      fin_cases i <;> simp [realBasis_apply]

/-- This integer pairing is proved below to be the inherited Euclidean pairing. -/
def integerPairing (x y : lattice) : ℤ :=
  2 * coord x 0 * coord y 0 - coord x 0 * coord y 1 -
    coord x 1 * coord y 0 + 2 * coord x 1 * coord y 1

theorem integerPairing_eq_inner (x y : lattice) :
    (integerPairing x y : ℝ) = ⟪(x : space), (y : space)⟫_ℝ := by
  change (integerPairing x y : ℝ) = ⟪((x : space) : Ambient), ((y : space) : Ambient)⟫_ℝ
  rw [lattice_coordinates, lattice_coordinates]
  simp [integerPairing, EuclideanSpace.inner_piLp_equiv_symm, dotProduct,
    Fin.sum_univ_succ]
  ring

theorem integral_pairing (x y : lattice) :
    ∃ z : ℤ, ⟪(x : space), (y : space)⟫_ℝ = (z : ℝ) :=
  ⟨integerPairing x y, (integerPairing_eq_inner x y).symm⟩

theorem even_norm (x : lattice) : ∃ z : ℤ, ‖(x : space)‖ ^ 2 = (2 * z : ℤ) := by
  refine ⟨coord x 0 ^ 2 - coord x 0 * coord x 1 + coord x 1 ^ 2, ?_⟩
  rw [← real_inner_self_eq_norm_sq, ← integerPairing_eq_inner]
  push_cast
  simp only [integerPairing]
  push_cast
  ring

theorem even_inner (x : lattice) :
    ∃ z : ℤ, ⟪(x : space), (x : space)⟫_ℝ = 2 * (z : ℝ) := by
  obtain ⟨z, hz⟩ := even_norm x
  refine ⟨z, ?_⟩
  rw [real_inner_self_eq_norm_sq]
  exact_mod_cast hz

theorem positive_definite (x : space) (hx : x ≠ 0) : 0 < ⟪x, x⟫_ℝ :=
  real_inner_self_pos.mpr hx

theorem lattice_positive_definite (x : lattice) (hx : x ≠ 0) :
    0 < ⟪(x : space), (x : space)⟫_ℝ := by
  apply real_inner_self_pos.mpr
  exact_mod_cast hx

/-- The actual Gram matrix in the integral basis. -/
def gram : Matrix (Fin 2) (Fin 2) ℤ := fun i j => integerPairing (intBasis i) (intBasis j)

theorem gram_eq : gram = !![2, -1; -1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, integerPairing, coord, Basis.repr_self]

theorem gram_real (i j : Fin 2) :
    (gram i j : ℝ) = ⟪(realBasis i : space), (realBasis j : space)⟫_ℝ := by
  change (integerPairing (intBasis i) (intBasis j) : ℝ) = _
  rw [integerPairing_eq_inner, intBasis_coe, intBasis_coe]

theorem gram_det : gram.det = 3 := by
  rw [gram_eq]
  norm_num [Matrix.det_fin_two]

theorem gram_det_odd : Odd gram.det := by rw [gram_det]; exact ⟨1, by norm_num⟩

/-- Gram matrix of the actual real basis for the inherited Euclidean inner product. -/
def realGram : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ⟪(realBasis i : space), (realBasis j : space)⟫_ℝ

theorem realGram_eq : realGram = !![2, -1; -1, 2] := by
  ext i j
  change ⟪(realBasis i : space), (realBasis j : space)⟫_ℝ = _
  rw [← gram_real, gram_eq]
  fin_cases i <;> fin_cases j <;> norm_num

theorem realGram_det : realGram.det = 3 := by
  rw [realGram_eq]
  norm_num [Matrix.det_fin_two]

theorem realGram_det_not_even : ¬ ∃ z : ℤ, realGram.det = 2 * (z : ℝ) := by
  rintro ⟨z, hz⟩
  rw [realGram_det] at hz
  have hz' : (3 : ℤ) = 2 * z := by exact_mod_cast hz
  omega

end Conjecture9028.A2
