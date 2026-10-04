import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace UnifierDepth

inductive Term where
  | var : Fin 6 → Term
  | constant : Term
  | unary : Term → Term
  deriving DecidableEq

abbrev Substitution := Fin 6 → Term

def applySubst (σ : Substitution) : Term → Term
  | .var i => σ i
  | .constant => .constant
  | .unary t => .unary (applySubst σ t)

def termVars : Term → Finset (Fin 6)
  | .var i => {i}
  | .constant => ∅
  | .unary t => termVars t

def height : Term → ℕ
  | .var _ => 0
  | .constant => 0
  | .unary t => height t + 1

def equations : Finset (Term × Term) :=
  {(.var 0, .var 1), (.var 2, .var 3), (.var 4, .var 5)}

def occurring : Finset (Fin 6) :=
  equations.biUnion (fun p => termVars p.1 ∪ termVars p.2)

def theta (i : Fin 6) : Term :=
  if i = 0 then .var 1 else if i = 2 then .var 3
  else if i = 4 then .var 5 else .var i

def Unifies (σ : Substitution) : Prop :=
  ∀ p ∈ equations, applySubst σ p.1 = applySubst σ p.2

-- Actual universal substitution factorization on every term.
def MostGeneral (σ : Substitution) : Prop :=
  Unifies σ ∧ ∀ τ, Unifies τ →
    ∃ δ, ∀ t, applySubst τ t = applySubst δ (applySubst σ t)

theorem occurring_count : occurring = Finset.univ ∧ occurring.card = 6 := by decide

theorem nontrivial_equations : equations.card = 3 ∧
    ∀ p ∈ equations, p.1 ≠ p.2 := by decide

theorem theta_unifies : Unifies theta := by
  intro p hp
  simp only [equations, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem factor_variables (τ : Substitution) (h : Unifies τ) (i : Fin 6) :
    τ i = applySubst τ (theta i) := by
  have h01 := h (.var 0, .var 1) (by decide)
  have h23 := h (.var 2, .var 3) (by decide)
  have h45 := h (.var 4, .var 5) (by decide)
  change τ 0 = τ 1 at h01
  change τ 2 = τ 3 at h23
  change τ 4 = τ 5 at h45
  fin_cases i <;> simp [theta, applySubst, h01, h23, h45]

theorem theta_most_general : MostGeneral theta := by
  refine ⟨theta_unifies, ?_⟩
  intro τ h
  refine ⟨τ, ?_⟩
  intro t
  induction t with
  | var i => exact factor_variables τ h i
  | constant => rfl
  | unary t ih => simpa [applySubst] using congrArg Term.unary ih

theorem theta_idempotent (t : Term) :
    applySubst theta (applySubst theta t) = applySubst theta t := by
  induction t with
  | var i => fin_cases i <;> simp [applySubst, theta]
  | constant => rfl
  | unary t ih => simpa [applySubst] using congrArg Term.unary ih

def depthZero (σ : Substitution) : ℕ := Finset.univ.sup (fun i => height (σ i))
def depthOne (σ : Substitution) : ℕ := Finset.univ.sup (fun i => height (σ i) + 1)
def support (σ : Substitution) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => σ i ≠ .var i)

theorem theta_depths : depthZero theta = 0 ∧ depthOne theta = 1 := by decide
theorem support_count : (support theta).card = 3 := by decide

theorem counterexample :
    MostGeneral theta ∧ occurring.card = 6 ∧ (support theta).card = 3 ∧
    depthZero theta = 0 ∧ depthOne theta = 1 ∧
    2 * depthOne theta < occurring.card ∧
    2 * depthOne theta < (support theta).card := by
  refine ⟨theta_most_general, occurring_count.2, support_count,
    theta_depths.1, theta_depths.2, ?_, ?_⟩ <;> decide

#print axioms occurring_count
#print axioms nontrivial_equations
#print axioms theta_unifies
#print axioms factor_variables
#print axioms theta_most_general
#print axioms theta_idempotent
#print axioms theta_depths
#print axioms support_count
#print axioms counterexample
end UnifierDepth
