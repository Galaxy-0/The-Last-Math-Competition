import Std

namespace Tlmc8304

/-- Bijection to a standard finite type, expanded using injectivity and
    surjectivity so the project needs no library beyond the Lean toolchain. -/
def EquivToFin (α : Type) (k : Nat) : Prop :=
  ∃ f : α → Fin k,
    (∀ a b, f a = f b → a = b) ∧
    (∀ y : Fin k, ∃ a, f a = y)

/-- A type is finite when it is equivalent to some standard finite type. -/
def IsFiniteType (α : Type) : Prop :=
  ∃ k : Nat, EquivToFin α k

/-- Infinite means not equivalent to any finite standard type. -/
def IsInfiniteType (α : Type) : Prop := ¬ IsFiniteType α

variable (Breakpoints : Nat → Type)

/-- The source's explicit finite-cardinality assertion. -/
def ExactBreakpointCount : Prop :=
  ∀ n : Nat, EquivToFin (Breakpoints n) (2 ^ n - n - 1)

theorem stated_count_at_24 : 2 ^ 24 - 24 - 1 = 16777191 := by decide

/-- The source's stated infinite-breakpoint threshold. -/
def InfiniteBreakpointThreshold : Prop :=
  ∀ n : Nat, 24 ≤ n → IsInfiniteType (Breakpoints n)

theorem finite_count_conflicts_with_threshold :
    ¬ (ExactBreakpointCount Breakpoints ∧
       InfiniteBreakpointThreshold Breakpoints) := by
  rintro ⟨hCount, hInfinite⟩
  have hAt24 : EquivToFin (Breakpoints 24) (2 ^ 24 - 24 - 1) := hCount 24
  have hFinite : IsFiniteType (Breakpoints 24) :=
    ⟨2 ^ 24 - 24 - 1, hAt24⟩
  exact hInfinite 24 (by decide) hFinite

/-- The remaining conjecture clauses are represented by arbitrary propositions:
    they cannot make the contradictory finite/infinite clauses consistent. -/
def SourceClaim (ehzRatioLaw e8DualityLaw : Prop) : Prop :=
  ExactBreakpointCount Breakpoints ∧
    ehzRatioLaw ∧
    InfiniteBreakpointThreshold Breakpoints ∧
    e8DualityLaw

theorem source_claim_false (ehzRatioLaw e8DualityLaw : Prop) :
    ¬ SourceClaim Breakpoints ehzRatioLaw e8DualityLaw := by
  intro h
  exact finite_count_conflicts_with_threshold Breakpoints
    ⟨h.1, h.2.2.1⟩

end Tlmc8304
