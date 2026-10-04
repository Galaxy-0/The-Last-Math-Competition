import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section

namespace Conjecture9028

/-- An even integer, regarded as a real number. The witness is integral. -/
def IntegerEven (t : ℝ) : Prop := ∃ k : ℤ, t = 2 * (k : ℝ)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Integrality of the actual Euclidean pairing on the lattice. -/
def IntegralLattice (L : Submodule ℤ E) : Prop :=
  ∀ x y : L, ∃ k : ℤ, @inner ℝ E _ (x : E) (y : E) = (k : ℝ)

/-- Every actual squared length is an even integer. -/
def EvenLattice (L : Submodule ℤ E) : Prop :=
  ∀ x : L, IntegerEven (@inner ℝ E _ (x : E) (x : E))

/-- Gram matrix of an actual real basis. Its integer span is a full lattice. -/
def gramMatrix {n : ℕ} (b : Basis (Fin n) ℝ E) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => @inner ℝ E _ (b i) (b j)

/-- Parity of the Gram determinant, with an integer witness. -/
def EvenDeterminant {n : ℕ} (b : Basis (Fin n) ℝ E) : Prop :=
  IntegerEven (gramMatrix b).det

/-- The necessity direction of the asserted determinant criterion. -/
def EvenDeterminantNecessary : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (b : Basis (Fin n) ℝ E),
    IntegralLattice (Submodule.span ℤ (Set.range b)) →
    EvenLattice (Submodule.span ℤ (Set.range b)) → EvenDeterminant b

/-- The sufficiency direction of the asserted determinant criterion. -/
def EvenDeterminantSufficient : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (b : Basis (Fin n) ℝ E),
    IntegralLattice (Submodule.span ℤ (Set.range b)) →
    EvenDeterminant b → EvenLattice (Submodule.span ℤ (Set.range b))

/-- The explicit lattice-evenness clause, without adding a theta hypothesis. -/
def ClaimedEvennessCriterion : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (b : Basis (Fin n) ℝ E),
    IntegralLattice (Submodule.span ℤ (Set.range b)) →
    (EvenLattice (Submodule.span ℤ (Set.range b)) ↔ EvenDeterminant b)

end Conjecture9028
