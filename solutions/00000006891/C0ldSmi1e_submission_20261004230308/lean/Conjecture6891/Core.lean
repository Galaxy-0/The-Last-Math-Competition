import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option synthInstance.maxHeartbeats 80000

noncomputable section
open scoped TensorProduct
namespace Conjecture6891

abbrev Vector := Fin 2 → ℂ
abbrev Tensor := Vector ⊗[ℂ] (Vector ⊗[ℂ] Vector)
abbrev Coordinate := Fin 2 × (Fin 2 × Fin 2)

def pure (a b c : Vector) : Tensor := a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c)

def tensorBasis : Basis Coordinate ℂ Tensor :=
  (Pi.basisFun ℂ (Fin 2)).tensorProduct
    ((Pi.basisFun ℂ (Fin 2)).tensorProduct (Pi.basisFun ℂ (Fin 2)))

def coords : Tensor ≃ₗ[ℂ] (Coordinate → ℂ) := tensorBasis.equivFun

@[simp] theorem coords_pure (a b c : Vector) (i j k : Fin 2) :
    coords (pure a b c) (i, (j, k)) = a i * b j * c k := by
  simp [coords, tensorBasis, pure, Basis.equivFun_apply, mul_comm, mul_left_comm]

theorem tensor_ext {u v : Tensor} (h : ∀ i j k, coords u (i, (j, k)) =
    coords v (i, (j, k))) : u = v := by
  apply coords.injective
  funext x
  exact h x.1 x.2.1 x.2.2

def e0 : Vector := ![1, 0]
def e1 : Vector := ![0, 1]

def W : Tensor := pure e1 e0 e0 + pure e0 e1 e0 + pure e0 e0 e1

@[simp] theorem coords_W (i j k : Fin 2) :
    coords W (i, (j, k)) =
      e1 i * e0 j * e0 k + e0 i * e1 j * e0 k + e0 i * e0 j * e1 k := by
  simp [W]

theorem W_ne_zero : W ≠ 0 := by
  intro h
  have he := congrArg (fun x => coords x (0, (1, 0))) h
  norm_num [e0, e1] at he

@[simp] theorem pure_zero_left (b c : Vector) : pure 0 b c = 0 := by
  simp [pure]

@[simp] theorem pure_smul_left (s : ℂ) (a b c : Vector) :
    pure (s • a) b c = s • pure a b c := by
  exact (TensorProduct.smul_tmul' s a (b ⊗ₜ[ℂ] c)).symm

end Conjecture6891
