import RationalDerivative
import DifferentialMatrix
import PointClosure
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

namespace Concrete8502

noncomputable section
open scoped RatFunc

abbrev Base := RatFunc ℂ

instance baseDifferential : Differential Base := Rational8502.differentialInstance

def t : Base := Rational8502.embed (Polynomial.X : Polynomial ℂ)
def U : Matrix (Fin 2) (Fin 2) Base := Differential8502.fundamental t

theorem Dt : Differential.deriv t = 1 := Rational8502.concrete_D_X

theorem base_constants (x : Base) :
    Differential.deriv x = 0 ↔ exists c : ℂ, algebraMap ℂ Base c = x :=
  Rational8502.concrete_constants x

theorem algebraically_closed_constants : IsAlgClosed ℂ := inferInstance

def companion {K : Type*} [Field K] (a : K) : Matrix (Fin 2) (Fin 2) K := !![0, 1; a, 0]

def fundamentalGenerators {K : Type*} [Field K] (Y : Matrix (Fin 2) (Fin 2) K) : Set K :=
  Set.range (fun ij : Fin 2 × Fin 2 => Y ij.1 ij.2) ∪ {Y.det⁻¹}

structure SecondOrderPV (K L : Type*) [Field K] [Field L] [Differential K] [Differential L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [DifferentialAlgebra K L] where
  a : K
  matrix : Matrix (Fin 2) (Fin 2) L
  determinant_nonzero : matrix.det ≠ 0
  equation : matrix.map Differential.deriv = companion (algebraMap K L a) * matrix
  base_constants : forall x : K, Differential.deriv x = 0 ↔ exists c : ℂ, algebraMap ℂ K c = x
  extension_constants : forall x : L, Differential.deriv x = 0 ↔ exists c : ℂ, algebraMap ℂ L c = x
  generates : IntermediateField.adjoin K (fundamentalGenerators matrix) = ⊤

theorem self_field_generated :
    IntermediateField.adjoin Base (fundamentalGenerators U) = ⊤ := by
  apply top_unique
  intro x _
  exact (IntermediateField.adjoin Base (fundamentalGenerators U)).algebraMap_mem x

theorem U_det : U.det = 1 := Differential8502.fundamental_det t

theorem U_equation : U.map Differential.deriv = companion (0 : Base) * U := by
  exact Differential8502.fundamental_equation t Dt

def identityPV : SecondOrderPV Base Base where
  a := 0
  matrix := U
  determinant_nonzero := by rw [U_det]; exact one_ne_zero
  equation := by simpa using U_equation
  base_constants := base_constants
  extension_constants := base_constants
  generates := self_field_generated

def generatedPVRing : Subalgebra Base Base := Algebra.adjoin Base (fundamentalGenerators U)

theorem generatedPVRing_eq_top : generatedPVRing = ⊤ := by
  apply top_unique
  intro x _
  exact generatedPVRing.algebraMap_mem x

theorem self_ring_differential_simple (I : Ideal Base)
    (_ : ∀ x ∈ I, Differential.deriv x ∈ I) : I = ⊥ ∨ I = ⊤ :=
  I.eq_bot_or_top

def differentialGaloisGroup (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Differential L] : Subgroup (L ≃ₐ[K] L) where
  carrier := {g | forall x : L, g (Differential.deriv x) = Differential.deriv (g x)}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro g h hg hh x
    change g (h (Differential.deriv x)) = Differential.deriv (g (h x))
    rw [hh, hg]
  inv_mem' := by
    intro g hg x
    apply g.injective
    change g (g.symm (Differential.deriv x)) = g (Differential.deriv (g.symm x))
    rw [AlgEquiv.apply_symm_apply, hg, AlgEquiv.apply_symm_apply]

def matrixAction {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Differential L] (Y : Matrix (Fin 2) (Fin 2) L) (g : differentialGaloisGroup K L) :
    Matrix (Fin 2) (Fin 2) L := Y⁻¹ * Y.map g.val

structure PVRepresentation {K L : Type*} [Field K] [Field L] [Differential K] [Differential L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [DifferentialAlgebra K L] (pv : SecondOrderPV K L) where
  hom : differentialGaloisGroup K L →* Matrix.GeneralLinearGroup (Fin 2) ℂ
  correct : forall g, (hom g).val.map (algebraMap ℂ L) = matrixAction pv.matrix g

theorem self_automorphism_identity (g : differentialGaloisGroup Base Base) :
    g.val = AlgEquiv.refl := Differential8502.self_base_automorphism g.val

theorem self_action_identity (g : differentialGaloisGroup Base Base) : matrixAction U g = 1 := by
  have hmap : U.map g.val = U := by
    ext i j
    change g.val (U i j) = U i j
    rw [self_automorphism_identity]
    rfl
  rw [matrixAction, hmap]
  apply Matrix.nonsing_inv_mul
  rw [U_det]
  exact isUnit_one

def selfRepresentation : PVRepresentation identityPV where
  hom := 1
  correct := by
    intro g
    change (1 : Matrix (Fin 2) (Fin 2) ℂ).map (algebraMap ℂ Base) = matrixAction U g
    rw [self_action_identity]
    simp

def invertiblePoint (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) : PointClosure8502.InvertibleMatrices :=
  ⟨g.val, Matrix.GeneralLinearGroup.det_ne_zero g⟩

def representedImage {K L : Type*} [Field K] [Field L] [Differential K] [Differential L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [DifferentialAlgebra K L] {pv : SecondOrderPV K L} (rep : PVRepresentation pv) :
    Set PointClosure8502.InvertibleMatrices := Set.range (fun g => invertiblePoint (rep.hom g))

theorem self_represented_image :
    representedImage selfRepresentation = {PointClosure8502.identityInvertibleMatrix} := by
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    apply Set.mem_singleton_iff.mpr
    rfl
  · intro hM
    rw [Set.mem_singleton_iff] at hM
    subst M
    exact ⟨1, rfl⟩

def galoisDimension {K L : Type*} [Field K] [Field L] [Differential K] [Differential L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [DifferentialAlgebra K L] {pv : SecondOrderPV K L} (rep : PVRepresentation pv) :=
  ringKrullDim (PointClosure8502.CoordinateRing
    (PointClosure8502.glPointCoords '' PointClosure8502.glZariskiClosure (representedImage rep)))

theorem self_galois_dimension_zero : galoisDimension selfRepresentation = 0 := by
  rw [galoisDimension, self_represented_image]
  exact PointClosure8502.identity_GL_closure_coordinateRing_krullDim

def AssertedSpectrum {K L : Type*} [Field K] [Field L] [Differential K] [Differential L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [DifferentialAlgebra K L] {pv : SecondOrderPV K L} (rep : PVRepresentation pv) : Prop :=
  galoisDimension rep = 1 ∨ galoisDimension rep = 2 ∨
    galoisDimension rep = 3 ∨ galoisDimension rep = 4

theorem counterexample_not_in_asserted_spectrum : ¬ AssertedSpectrum selfRepresentation := by
  simp [AssertedSpectrum, self_galois_dimension_zero]

theorem no_uniform_second_order_spectrum :
    ¬ (forall (K L : Type) [Field K] [Field L]
      [Differential K] [Differential L] [Algebra ℂ K] [Algebra ℂ L]
      [Algebra K L] [IsScalarTower ℂ K L] [DifferentialAlgebra K L]
      (pv : SecondOrderPV K L) (rep : PVRepresentation pv), AssertedSpectrum rep) := by
  intro h
  exact counterexample_not_in_asserted_spectrum
    (h Base Base identityPV selfRepresentation)

end
end Concrete8502
