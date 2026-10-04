import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open scoped Classical
namespace TraceCritical

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ
instance : NormedAddCommGroup Mat := inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℝ))
instance : NormedSpace ℝ Mat := inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℝ))
def objective (M : Mat) : ℝ := (Matrix.trace M)^2
def jordan : Mat := fun i j => if i = 0 ∧ j = 1 then 1 else 0
def Normal (M : Mat) : Prop := M * M.transpose = M.transpose * M

-- Equality of characteristic polynomials means equality of eigenvalues with multiplicity.
def Spectral (f : Mat → ℝ) : Prop :=
  ∀ A B, A.charpoly = B.charpoly → f A = f B

theorem objective_spectral : Spectral objective := by
  intro A B h
  unfold objective
  rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h]

theorem objective_similarity (P : Matˣ) (M : Mat) :
    objective ((P : Mat) * M * (↑P⁻¹ : Mat)) = objective M := by
  unfold objective
  rw [Matrix.trace_units_conj]

theorem objective_convex : ConvexOn ℝ Set.univ objective := by
  refine ⟨convex_univ, ?_⟩
  intro M _ N _ a b ha hb hab
  have hpos := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (Matrix.trace M - Matrix.trace N))
  have hid : a * objective M + b * objective N -
      objective (a • M + b • N) = a*b*(Matrix.trace M - Matrix.trace N)^2 := by
    unfold objective
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
    simp only [smul_eq_mul]
    have he : b = 1-a := by linarith
    rw [he]
    ring
  simp only [smul_eq_mul]
  linarith

theorem objective_nonconstant : objective (0 : Mat) ≠ objective (1 : Mat) := by
  norm_num [objective, Matrix.trace, Fin.sum_univ_two]

def traceCLM : Mat →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin 2) ℝ ℝ).toContinuousLinearMap

@[simp] theorem traceCLM_apply (M : Mat) : traceCLM M = Matrix.trace M := rfl

theorem objective_derivative (M : Mat) :
    HasFDerivAt objective ((2 * Matrix.trace M) • traceCLM) M := by
  have h := (traceCLM.hasFDerivAt (x := M)).mul (traceCLM.hasFDerivAt (x := M))
  convert h using 1
  · ext N
    simp [objective, pow_two]
  · simp [← add_smul, two_mul]

theorem jordan_trace : Matrix.trace jordan = 0 := by
  have hd (i : Fin 2) : jordan i i = 0 := by fin_cases i <;> norm_num [jordan]
  simp [Matrix.trace, hd]

theorem jordan_critical : HasFDerivAt objective (0 : Mat →L[ℝ] ℝ) jordan := by
  simpa [jordan_trace] using objective_derivative jordan

theorem jordan_not_normal : ¬ Normal jordan := by
  intro h
  have hh := congrArg (fun M : Mat => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, jordan] at hh

theorem counterexample :
    Spectral objective ∧ ConvexOn ℝ Set.univ objective ∧
    objective (0 : Mat) ≠ objective (1 : Mat) ∧
    HasFDerivAt objective (0 : Mat →L[ℝ] ℝ) jordan ∧ ¬ Normal jordan :=
  ⟨objective_spectral, objective_convex, objective_nonconstant,
    jordan_critical, jordan_not_normal⟩

#print axioms objective_spectral
#print axioms objective_similarity
#print axioms objective_convex
#print axioms objective_nonconstant
#print axioms objective_derivative
#print axioms jordan_critical
#print axioms jordan_not_normal
#print axioms counterexample
end TraceCritical
