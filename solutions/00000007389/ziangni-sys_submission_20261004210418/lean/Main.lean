import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic.Abel

namespace AffineNewton
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def coord (T : E ≃L[𝕜] E) (b x : E) : E := T x + b
def invCoord (T : E ≃L[𝕜] E) (b y : E) : E := T.symm (y - b)
def residual (T : E ≃L[𝕜] E) (b : E) (f : E → E) (y : E) : E :=
  T (f (invCoord T b y))
def tangent (T D : E ≃L[𝕜] E) : E ≃L[𝕜] E := T.symm.trans (D.trans T)
def newton (f : E → E) (D : E ≃L[𝕜] E) (x : E) : E := x - D.symm (f x)

@[simp] theorem inv_coord (T : E ≃L[𝕜] E) (b x : E) :
    invCoord T b (coord T b x) = x := by simp [invCoord, coord]
@[simp] theorem coord_inv (T : E ≃L[𝕜] E) (b y : E) :
    coord T b (invCoord T b y) = y := by simp [invCoord, coord]
@[simp] theorem tangent_apply (T D : E ≃L[𝕜] E) (v : E) :
    tangent T D v = T (D (T.symm v)) := rfl
@[simp] theorem tangent_inverse_apply (T D : E ≃L[𝕜] E) (v : E) :
    (tangent T D).symm v = T (D.symm (T.symm v)) := rfl

theorem coordinate_derivative (T : E ≃L[𝕜] E) (b x : E) :
    HasFDerivAt (coord T b) (T : E →L[𝕜] E) x := by
  exact T.toContinuousLinearMap.hasFDerivAt.add_const b

theorem inverse_coordinate_derivative (T : E ≃L[𝕜] E) (b y : E) :
    HasFDerivAt (invCoord T b) (T.symm : E →L[𝕜] E) y := by
  change HasFDerivAt (fun z : E => T.symm (z - b)) (T.symm : E →L[𝕜] E) y
  have h := (hasFDerivAt_id (𝕜 := 𝕜) y).sub_const b
  simpa [invCoord, Function.comp_def] using
    T.symm.toContinuousLinearMap.hasFDerivAt.comp y h

theorem transformed_derivative (T D : E ≃L[𝕜] E) (b x : E) (f : E → E)
    (hf : HasFDerivAt f (D : E →L[𝕜] E) x) :
    HasFDerivAt (residual T b f) (tangent T D : E →L[𝕜] E) (coord T b x) := by
  have hi := inverse_coordinate_derivative T b (coord T b x)
  have hf' : HasFDerivAt f (D : E →L[𝕜] E) (invCoord T b (coord T b x)) := by simpa using hf
  have hm := hf'.comp (coord T b x) hi
  have ht : HasFDerivAt (fun z : E => T z) (T : E →L[𝕜] E) (f (invCoord T b (coord T b x))) := T.toContinuousLinearMap.hasFDerivAt
  have ho := ht.comp (coord T b x) hm
  simpa [residual, tangent, Function.comp_def] using ho

theorem correction_covariance (T D : E ≃L[𝕜] E) (b x : E) (f : E → E) :
    (tangent T D).symm (residual T b f (coord T b x)) = T (D.symm (f x)) := by
  simp [residual]

theorem newton_covariance (T D : E ≃L[𝕜] E) (b x : E) (f : E → E) :
    newton (residual T b f) (tangent T D) (coord T b x) =
      coord T b (newton f D x) := by
  unfold newton
  rw [correction_covariance]
  simp only [coord, map_sub]
  abel

-- The derivative assumptions are genuine analytic premises, not an assumed covariance.
theorem actual_newton_step (T D : E ≃L[𝕜] E) (b x : E) (f : E → E)
    (hf : HasFDerivAt f (D : E →L[𝕜] E) x) :
    HasFDerivAt (residual T b f) (tangent T D : E →L[𝕜] E) (coord T b x) ∧
    newton (residual T b f) (tangent T D) (coord T b x) =
      coord T b (newton f D x) :=
  ⟨transformed_derivative T D b x f hf, newton_covariance T D b x f⟩

def step (f : E → E) (D : E → E ≃L[𝕜] E) (x : E) : E := newton f (D x) x
def transformedStep (T : E ≃L[𝕜] E) (b : E) (f : E → E)
    (D : E → E ≃L[𝕜] E) (y : E) : E :=
  newton (residual T b f) (tangent T (D (invCoord T b y))) y

theorem step_covariance (T : E ≃L[𝕜] E) (b x : E) (f : E → E)
    (D : E → E ≃L[𝕜] E) :
    transformedStep T b f D (coord T b x) = coord T b (step f D x) := by
  simp only [transformedStep, inv_coord, step]
  exact newton_covariance T (D x) b x f

def orbit (N : E → E) (x : E) : ℕ → E
  | 0 => x
  | n + 1 => N (orbit N x n)

theorem orbit_covariance (T : E ≃L[𝕜] E) (b x : E) (f : E → E)
    (D : E → E ≃L[𝕜] E) (n : ℕ) :
    orbit (transformedStep T b f D) (coord T b x) n =
      coord T b (orbit (step f D) x n) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [orbit, ih] using
      step_covariance T b (orbit (step f D) x n) f D

theorem orbit_derivative (T : E ≃L[𝕜] E) (b x : E) (f : E → E)
    (D : E → E ≃L[𝕜] E) (n : ℕ)
    (hf : HasFDerivAt f (D (orbit (step f D) x n) : E →L[𝕜] E)
      (orbit (step f D) x n)) :
    HasFDerivAt (residual T b f)
      (tangent T (D (orbit (step f D) x n)) : E →L[𝕜] E)
      (orbit (transformedStep T b f D) (coord T b x) n) := by
  rw [orbit_covariance]
  exact transformed_derivative T _ b _ f hf

theorem tangent_identity (T : E ≃L[𝕜] E) :
    tangent T (ContinuousLinearEquiv.refl 𝕜 E) = ContinuousLinearEquiv.refl 𝕜 E := by
  ext v
  simp

theorem tangent_composition (T D F : E ≃L[𝕜] E) :
    tangent T (D.trans F) = (tangent T D).trans (tangent T F) := by
  ext v
  simp

theorem coordinate_composition (T S : E ≃L[𝕜] E) (b c x : E) :
    coord S c (coord T b x) = coord (T.trans S) (S b + c) x := by
  simp [coord, map_add, add_assoc]

theorem roots_covariance (T : E ≃L[𝕜] E) (b x : E) (f : E → E) :
    residual T b f (coord T b x) = 0 ↔ f x = 0 := by simp [residual]
end AffineNewton

#print axioms AffineNewton.transformed_derivative
#print axioms AffineNewton.actual_newton_step
#print axioms AffineNewton.orbit_covariance
#print axioms AffineNewton.orbit_derivative
#print axioms AffineNewton.tangent_identity
#print axioms AffineNewton.tangent_composition
#print axioms AffineNewton.coordinate_composition
#print axioms AffineNewton.roots_covariance
