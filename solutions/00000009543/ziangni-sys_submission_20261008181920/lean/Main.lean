import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic

noncomputable section
open scoped Matrix ComplexOrder
namespace IdentityAVQC

abbrev M := Matrix (Fin 2) (Fin 2) ℂ
abbrev Superoperator := M →ₗ[ℂ] M

/-- The block-matrix realization of id_n tensor Phi. -/
def amplify (n : ℕ) (Phi : Superoperator)
    (X : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  fun i j => Phi (fun a b => X (i.1, a) (j.1, b)) i.2 j.2

def CompletelyPositive (Phi : Superoperator) : Prop :=
  ∀ n X, X.PosSemidef → (amplify n Phi X).PosSemidef

def TracePreserving (Phi : Superoperator) : Prop :=
  ∀ X, Matrix.trace (Phi X) = Matrix.trace X

def IsChannel (Phi : Superoperator) : Prop := CompletelyPositive Phi ∧ TracePreserving Phi

def identityChannel : Superoperator := LinearMap.id
def family : Fin 1 → Superoperator := fun _ => identityChannel

theorem amplification_identity (n : ℕ)
    (X : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    amplify n identityChannel X = X := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rfl

theorem identity_completely_positive : CompletelyPositive identityChannel := by
  intro n X hX
  rwa [amplification_identity]

theorem identity_trace_preserving : TracePreserving identityChannel := by
  intro X
  rfl

theorem identity_is_channel : IsChannel identityChannel :=
  ⟨identity_completely_positive, identity_trace_preserving⟩

def Density (rho : M) : Prop := rho.PosSemidef ∧ Matrix.trace rho = 1
def rho0 : M := Matrix.diagonal ![1, 0]
def rho1 : M := Matrix.diagonal ![0, 1]

theorem rho0_density : Density rho0 := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  · norm_num [rho0, Matrix.trace, Fin.sum_univ_two]

theorem rho1_density : Density rho1 := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  · norm_num [rho1, Matrix.trace, Fin.sum_univ_two]

theorem densities_distinct : rho0 ≠ rho1 := by
  intro h
  have := congrArg (fun X : M => X 0 0) h
  norm_num [rho0, rho1] at this

/-- An actual probability distribution on the finite adversarial state set. -/
structure Distribution (S : Type*) [Fintype S] where
  weight : S → ℝ
  nonnegative : ∀ s, 0 ≤ weight s
  total : ∑ s, weight s = 1

def averaged {S : Type*} [Fintype S] (channels : S → Superoperator)
    (p : Distribution S) (rho : M) : M :=
  ∑ s, (p.weight s : ℂ) • channels s rho

/-- The standard one-use finite-ensemble symmetrization condition.
The distribution may depend on the input state. -/
def OneSymmetrizable {S : Type*} [Fintype S] (channels : S → Superoperator) : Prop :=
  ∀ (k : ℕ) (rho : Fin k → M), (∀ i, Density (rho i)) →
    ∃ p : Fin k → Distribution S, ∀ i j,
      averaged channels (p i) (rho j) = averaged channels (p j) (rho i)

theorem singleton_weight (p : Distribution (Fin 1)) : p.weight 0 = 1 := by
  simpa using p.total

theorem identity_average (p : Distribution (Fin 1)) (rho : M) :
    averaged family p rho = rho := by
  simp [averaged, family, identityChannel, singleton_weight]

def ensemble : Fin 2 → M := ![rho0, rho1]

theorem ensemble_density (i : Fin 2) : Density (ensemble i) := by
  fin_cases i
  · exact rho0_density
  · exact rho1_density

theorem identity_not_one_symmetrizable : ¬ OneSymmetrizable family := by
  intro h
  obtain ⟨p, hp⟩ := h 2 ensemble ensemble_density
  have eq := hp 0 1
  rw [identity_average, identity_average] at eq
  exact densities_distinct eq.symm

theorem identity_in_channel_span : identityChannel ∈
    Submodule.span ℂ (Set.range family) :=
  Submodule.subset_span ⟨0, rfl⟩

/-- A genuine family of quantum channels violates the claimed span criterion
already at the necessary one-use symmetrization condition. -/
theorem counterexample : (∀ s, IsChannel (family s)) ∧
    identityChannel ∈ Submodule.span ℂ (Set.range family) ∧
    ¬ OneSymmetrizable family :=
  ⟨fun _ => identity_is_channel, identity_in_channel_span, identity_not_one_symmetrizable⟩

theorem span_does_not_imply_one_symmetrizable : ¬ (∀ channels : Fin 1 → Superoperator,
    (∀ s, IsChannel (channels s)) →
    identityChannel ∈ Submodule.span ℂ (Set.range channels) → OneSymmetrizable channels) := by
  intro h
  exact identity_not_one_symmetrizable
    (h family (fun _ => identity_is_channel) identity_in_channel_span)

#print axioms amplification_identity
#print axioms identity_is_channel
#print axioms rho0_density
#print axioms rho1_density
#print axioms densities_distinct
#print axioms singleton_weight
#print axioms identity_average
#print axioms identity_not_one_symmetrizable
#print axioms identity_in_channel_span
#print axioms counterexample
#print axioms span_does_not_imply_one_symmetrizable
end IdentityAVQC
