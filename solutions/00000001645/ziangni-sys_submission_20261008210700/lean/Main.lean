import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Tactic

noncomputable section
namespace TrivialGroupDeterminant
abbrev G := Multiplicative (ZMod 1)
abbrev GroupRing := MonoidAlgebra ℚ G
abbrev H := G → ℂ
lemma group_trivial (g : G) : g = 1 := by
  apply Subsingleton.elim
lemma torsion_free (g : G) (n : ℕ) (_ : 0 < n) (_ : g^n = 1) : g = 1 := group_trivial g

-- For the trivial group its group von Neumann algebra is C, its canonical
-- trace is the identity, and the von Neumann dimension is ordinary dimension.
def trivialVonNeumannDimension {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  (Module.finrank ℂ (LinearMap.ker A.mulVecLin) : ℝ)
theorem strong_Atiyah (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ d : ℕ, trivialVonNeumannDimension A = d :=
  ⟨Module.finrank ℂ (LinearMap.ker A.mulVecLin), rfl⟩

def a : GroupRing := MonoidAlgebra.single 1 (1/2)
def regular (b : GroupRing) (f : H) (x : G) : ℂ :=
  ∑ g : G, (b g : ℂ) * f (g⁻¹*x)
lemma regular_action (f : H) (x : G) : regular a f x = (1/2 : ℂ)*f x := by
  simp [regular, a, group_trivial]

-- Coordinates in the delta_e basis of l2({e}); the rational matrix is [a].
def regularMatrix (b : GroupRing) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => b 1
def delta : H := fun _ => 1
lemma regular_matrix_entry : regularMatrix a 0 0 = regular a delta 1 := by
  rw [regular_action]
  simp [regularMatrix, a, delta]
lemma matrix_value : regularMatrix a = fun _ _ => (1/2 : ℂ) := by
  ext i j
  simp [regularMatrix, a]

def canonicalTrace (T : Matrix (Fin 1) (Fin 1) ℂ) : ℂ := Matrix.trace T
lemma trace_normalized : canonicalTrace (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  simp [canonicalTrace, Matrix.trace]
-- The one-dimensional spectral calculus: |T| has eigenvalue ||T_00||,
-- so log |T| has the single eigenvalue log ||T_00||.
def logAbsolute (T : Matrix (Fin 1) (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => (Real.log ‖T 0 0‖ : ℂ)
def fugledeKadison (T : Matrix (Fin 1) (Fin 1) ℂ) : ℝ :=
  Real.exp (canonicalTrace (logAbsolute T)).re
lemma canonical_log_trace (T : Matrix (Fin 1) (Fin 1) ℂ) :
    (canonicalTrace (logAbsolute T)).re = Real.log ‖T 0 0‖ := by
  simp [canonicalTrace, logAbsolute, Matrix.trace]
theorem determinant_value : fugledeKadison (regularMatrix a) = 1/2 := by
  rw [fugledeKadison, canonical_log_trace, matrix_value]
  norm_num [Complex.norm_def, Real.exp_log]

theorem rational_half_not_integral : ¬ IsIntegral ℤ (1/2 : ℚ) := by
  intro h
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff).mp h
  have heq : (2:ℚ)*z = 1 := by
    change (z : ℚ) = 1/2 at hz
    linarith
  have hint : 2*z = (1:ℤ) := by exact_mod_cast heq
  omega
theorem real_half_not_integral : ¬ IsIntegral ℤ (1/2 : ℝ) := by
  intro h
  have hq : IsIntegral ℤ (1/2 : ℚ) := by
    apply (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℝ)
      (algebraMap ℚ ℝ).injective).mp
    simpa using h
  exact rational_half_not_integral hq
theorem counterexample : ¬ IsIntegral ℤ (fugledeKadison (regularMatrix a)) := by
  rw [determinant_value]
  exact real_half_not_integral

#print axioms torsion_free
#print axioms strong_Atiyah
#print axioms regular_action
#print axioms regular_matrix_entry
#print axioms trace_normalized
#print axioms canonical_log_trace
#print axioms determinant_value
#print axioms rational_half_not_integral
#print axioms counterexample
end TrivialGroupDeterminant
