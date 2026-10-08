import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

noncomputable section
open scoped Matrix ComplexOrder
namespace TraceSupport

abbrev M := Matrix (Fin 2) (Fin 2) ℂ
def P : M := Matrix.diagonal ![1, 0]
def Q : M := Matrix.diagonal ![0, 1]

theorem gram_positive (A : M) : (Aᴴ * A).PosSemidef := by
  simpa using (Matrix.PosSemidef.one : (1 : M).PosSemidef).conjTranspose_mul_mul_same A

/-- The canonical positive square root, not a chosen square-root certificate. -/
def modulus (A : M) : M := (gram_positive A).sqrt
/-- The Schatten one-norm: the real trace of the positive modulus. -/
def traceNorm (A : M) : ℝ := (Matrix.trace (modulus A)).re
/-- In finite dimension the support subspace is the range of the modulus. -/
def support (A : M) : Set (Fin 2 → ℂ) := Set.range ((modulus A).mulVec)

theorem P_positive : P.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

theorem Q_positive : Q.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

theorem modulus_positive (A : M) (h : A.PosSemidef) : modulus A = A := by
  symm
  apply h.eq_sqrt_of_sq_eq (gram_positive A)
  rw [h.isHermitian.eq, pow_two]

theorem modulus_P : modulus P = P := modulus_positive P P_positive
theorem modulus_Q : modulus Q = Q := modulus_positive Q Q_positive

theorem sum_identity : P + Q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [P, Q, Matrix.diagonal]

theorem trace_norms : traceNorm P = 1 ∧ traceNorm Q = 1 ∧ traceNorm (P + Q) = 2 := by
  have h : modulus (P + Q) = P + Q := modulus_positive _ (P_positive.add Q_positive)
  unfold traceNorm
  rw [modulus_P, modulus_Q, h]
  norm_num [P, Q, Matrix.trace, Fin.sum_univ_two]

theorem triangle_equality : traceNorm (P + Q) = traceNorm P + traceNorm Q := by
  rw [trace_norms.1, trace_norms.2.1, trace_norms.2.2]
  norm_num

theorem support_P (v : Fin 2 → ℂ) : v ∈ support P ↔ v 1 = 0 := by
  simp only [support, modulus_P, Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    simp [P, Matrix.mulVec_diagonal]
  · intro hv
    refine ⟨v, ?_⟩
    ext i
    fin_cases i <;> simp [P, Matrix.mulVec_diagonal, hv]

theorem support_Q (v : Fin 2 → ℂ) : v ∈ support Q ↔ v 0 = 0 := by
  simp only [support, modulus_Q, Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    simp [Q, Matrix.mulVec_diagonal]
  · intro hv
    refine ⟨v, ?_⟩
    ext i
    fin_cases i <;> simp [Q, Matrix.mulVec_diagonal, hv]

theorem supports_distinct : support P ≠ support Q := by
  intro h
  have hp : (![1, 0] : Fin 2 → ℂ) ∈ support P := (support_P _).mpr (by simp)
  rw [h] at hp
  have := (support_Q _).mp hp
  norm_num at this

theorem support_intersection : support P ∩ support Q = {0} := by
  ext v
  simp only [Set.mem_inter_iff, support_P, support_Q, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h₁, h₀⟩
    ext i
    fin_cases i <;> simp [h₀, h₁]
  · rintro rfl
    simp

/-- The supported polar partial isometries are the projections themselves. -/
theorem polar_factors : P * modulus P = P ∧ Pᴴ * P = P ∧
    Q * modulus Q = Q ∧ Qᴴ * Q = Q := by
  rw [modulus_P, modulus_Q]
  simp only [P, Q, Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  constructor <;> (ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal])

local instance : MeasurableSpace (Fin 2) := ⊤
local instance : MeasurableSingletonClass (Fin 2) := ⟨fun _ => trivial⟩

/-- The positive polar measures in the diagonal two-point model. -/
def muP : MeasureTheory.Measure (Fin 2) := MeasureTheory.Measure.dirac 0
def muQ : MeasureTheory.Measure (Fin 2) := MeasureTheory.Measure.dirac 1

theorem atomic_measure_bridge (i : Fin 2) :
    (muP {i}).toReal = (P i i).re ∧ (muQ {i}).toReal = (Q i i).re := by
  fin_cases i <;> norm_num [muP, muQ, MeasureTheory.Measure.dirac_apply, P, Q]

theorem atomic_supports : {i : Fin 2 | muP {i} ≠ 0} = {0} ∧
    {i : Fin 2 | muQ {i} ≠ 0} = {1} := by
  constructor <;> (ext i; fin_cases i <;>
    simp [muP, muQ, MeasureTheory.Measure.dirac_apply])

theorem projections_nonzero : P ≠ 0 ∧ Q ≠ 0 := by
  constructor
  · intro h
    have := congrArg (fun A : M => A 0 0) h
    norm_num [P] at this
  · intro h
    have := congrArg (fun A : M => A 1 1) h
    norm_num [Q] at this

/-- The same-support requirement fails for nonzero complex operators. -/
theorem counterexample : ∃ A B : M, A ≠ 0 ∧ B ≠ 0 ∧
    traceNorm (A + B) = traceNorm A + traceNorm B ∧ support A ≠ support B :=
  ⟨P, Q, projections_nonzero.1, projections_nonzero.2, triangle_equality, supports_distinct⟩

theorem no_same_support_necessity : ¬ (∀ A B : M,
    traceNorm (A + B) = traceNorm A + traceNorm B → support A = support B) := by
  intro h
  exact supports_distinct (h P Q triangle_equality)

#print axioms gram_positive
#print axioms modulus_positive
#print axioms trace_norms
#print axioms triangle_equality
#print axioms support_P
#print axioms support_Q
#print axioms supports_distinct
#print axioms support_intersection
#print axioms polar_factors
#print axioms atomic_measure_bridge
#print axioms atomic_supports
#print axioms counterexample
#print axioms no_same_support_necessity
end TraceSupport
