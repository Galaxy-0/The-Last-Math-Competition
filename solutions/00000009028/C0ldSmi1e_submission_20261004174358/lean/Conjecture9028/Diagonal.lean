import Conjecture9028.Definitions
import Mathlib.Tactic

noncomputable section

namespace Conjecture9028.Diagonal

abbrev Ambient := EuclideanSpace ℝ (Fin 3)

/-- The concrete plane of vectors `(a,b,b)` in Euclidean three-space. -/
def plane : Submodule ℝ Ambient where
  carrier := {x | x 1 = x 2}
  zero_mem' := rfl
  add_mem' := by intro x y hx hy; simp_all
  smul_mem' := by intro c x hx; simp_all

@[simp] theorem mem_plane (x : Ambient) : x ∈ plane ↔ x 1 = x 2 := Iff.rfl

/-- The actual linear parametrization of the plane. -/
def parametrization : (Fin 2 → ℝ) ≃ₗ[ℝ] plane where
  toFun := fun v => ⟨(WithLp.equiv 2 (Fin 3 → ℝ)).symm ![v 0, v 1, v 1], rfl⟩
  invFun := fun x => ![(x : Ambient) 0, (x : Ambient) 1]
  left_inv := by intro v; funext i; fin_cases i <;> rfl
  right_inv := by
    intro x
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact x.property
  map_add' := by
    intro x y
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  map_smul' := by
    intro c x
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl

/-- A real basis of the concrete plane, not an assigned Gram matrix. -/
def realBasis : Basis (Fin 2) ℝ plane := (Pi.basisFun ℝ (Fin 2)).map parametrization

/-- The lattice is the integer span of that real basis. -/
def lattice : Submodule ℤ plane := Submodule.span ℤ (Set.range realBasis)

/-- The actual integral basis of the integer span. -/
def intBasis : Basis (Fin 2) ℤ lattice := realBasis.restrictScalars ℤ

theorem intBasis_coe (i : Fin 2) : (intBasis i : plane) = realBasis i :=
  realBasis.restrictScalars_apply ℤ i

instance lattice_discrete : DiscreteTopology lattice := by
  unfold lattice
  infer_instance

instance lattice_isZLattice : IsZLattice ℝ lattice := by
  unfold lattice
  infer_instance

theorem plane_finrank : Module.finrank ℝ plane = 2 := by
  simpa using Module.finrank_eq_card_basis realBasis

theorem lattice_finrank : Module.finrank ℤ lattice = 2 := by
  simpa using Module.finrank_eq_card_basis intBasis

theorem plane_inner (x y : plane) :
    inner (𝕜 := ℝ) x y = (x : Ambient) 0 * (y : Ambient) 0 +
      2 * (x : Ambient) 1 * (y : Ambient) 1 := by
  change inner (𝕜 := ℝ) (x : Ambient) (y : Ambient) = _
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.coe_castSucc, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.sum_univ_zero,
    RCLike.inner_apply, starRingEnd_apply, star_trivial, add_zero]
  change (y : Ambient) 0 * (x : Ambient) 0 +
    ((y : Ambient) 1 * (x : Ambient) 1 + (y : Ambient) 2 * (x : Ambient) 2) = _
  rw [← x.property, ← y.property]
  ring

@[simp] theorem realBasis_zero : (realBasis 0 : Ambient) = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![1, 0, 0] := by
  ext i
  fin_cases i <;> norm_num [realBasis, parametrization, Pi.basisFun_apply]

@[simp] theorem realBasis_one : (realBasis 1 : Ambient) = (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![0, 1, 1] := by
  ext i
  fin_cases i <;> norm_num [realBasis, parametrization, Pi.basisFun_apply]

theorem gram_eq : gramMatrix realBasis = !![(1 : ℝ), 0; 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramMatrix, plane_inner, realBasis_zero, realBasis_one, Fin.sum_univ_succ]

theorem gram_det : (gramMatrix realBasis).det = 2 := by
  rw [gram_eq, Matrix.det_fin_two]
  norm_num

theorem basis_repr (x : plane) (i : Fin 2) :
    realBasis.repr x i = ![(x : Ambient) 0, (x : Ambient) 1] i := by
  simp [realBasis, Basis.map_repr, parametrization]

theorem integral_pairings : IntegralLattice lattice := by
  intro x y
  obtain ⟨a, ha⟩ := (realBasis.mem_span_iff_repr_mem ℤ _).mp x.property 0
  obtain ⟨b, hb⟩ := (realBasis.mem_span_iff_repr_mem ℤ _).mp x.property 1
  obtain ⟨c, hc⟩ := (realBasis.mem_span_iff_repr_mem ℤ _).mp y.property 0
  obtain ⟨d, hd⟩ := (realBasis.mem_span_iff_repr_mem ℤ _).mp y.property 1
  refine ⟨a * c + 2 * b * d, ?_⟩
  rw [plane_inner]
  simp only [basis_repr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at ha hb hc hd
  norm_num at ha hb hc hd
  rw [← ha, ← hb, ← hc, ← hd]
  push_cast
  rfl

theorem first_basis_inner : inner (𝕜 := ℝ) (realBasis 0) (realBasis 0) = 1 := by
  norm_num [plane_inner, realBasis_zero, Fin.sum_univ_succ]

theorem first_basis_norm_sq : ‖realBasis 0‖ ^ 2 = (1 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  exact first_basis_inner

theorem lattice_vector_norm_sq : ‖((intBasis 0 : lattice) : plane)‖ ^ 2 = (1 : ℝ) := by
  rw [intBasis_coe]
  exact first_basis_norm_sq

theorem even_determinant : EvenDeterminant realBasis := by
  refine ⟨1, ?_⟩
  norm_num [gram_det]

theorem not_even : ¬EvenLattice lattice := by
  intro h
  obtain ⟨k, hk⟩ := h (intBasis 0)
  have hone : inner (𝕜 := ℝ) ((intBasis 0 : lattice) : plane) ((intBasis 0 : lattice) : plane) = 1 := by
    rw [intBasis_coe]
    exact first_basis_inner
  rw [hone] at hk
  have hint : (1 : ℤ) = 2 * k := by exact_mod_cast hk
  omega

theorem plane_positive {x : plane} (hx : x ≠ 0) : 0 < inner (𝕜 := ℝ) x x :=
  real_inner_self_pos.mpr hx

theorem counterexample : IntegralLattice lattice ∧ EvenDeterminant realBasis ∧
    ¬EvenLattice lattice :=
  ⟨integral_pairings, even_determinant, not_even⟩

end Conjecture9028.Diagonal
