import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

namespace PuiseuxCounterexample

def naturalMonoid : AddSubmonoid ℚ where
  carrier := {x | ∃ n : ℕ, x = n}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by simp⟩

def generated : AddSubmonoid ℚ := AddSubmonoid.closure ({1, 2} : Set ℚ)

theorem generated_eq : generated = naturalMonoid := by
  apply le_antisymm
  · apply AddSubmonoid.closure_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
  · rintro x ⟨n, rfl⟩
    induction n with
    | zero => exact generated.zero_mem
    | succ n ih =>
      have h1 : (1 : ℚ) ∈ generated := AddSubmonoid.subset_closure (by simp)
      simpa [Nat.cast_add, Nat.cast_one] using generated.add_mem ih h1

theorem nonnegative (x : ℚ) (hx : x ∈ generated) : 0 ≤ x := by
  rw [generated_eq] at hx
  rcases hx with ⟨n, rfl⟩
  positivity

theorem zero_sum (a b : ℚ) (ha : a ∈ generated) (hb : b ∈ generated)
    (h : a + b = 0) : a = 0 ∧ b = 0 := by
  have := nonnegative a ha
  have := nonnegative b hb
  constructor <;> linarith

/-- In this reduced additive monoid, the only unit is zero. -/
def Atom (x : ℚ) : Prop := x ∈ generated ∧ x ≠ 0 ∧
  ∀ a ∈ generated, ∀ b ∈ generated, a + b = x → a = 0 ∨ b = 0

theorem one_atom : Atom 1 := by
  refine ⟨AddSubmonoid.subset_closure (by simp), by norm_num, ?_⟩
  intro a ha b hb hab
  rw [generated_eq] at ha hb
  rcases ha with ⟨m, rfl⟩
  rcases hb with ⟨n, rfl⟩
  have hmn : m + n = 1 := by exact_mod_cast hab
  have hz : m = 0 ∨ n = 0 := by omega
  rcases hz with h | h
  · left; simp [h]
  · right; simp [h]

def Atomic : Prop := ∀ x ∈ generated, ∃ n : ℕ, ∃ f : Fin n → ℚ,
  (∀ i, Atom (f i)) ∧ (∑ i, f i) = x

theorem atomic : Atomic := by
  intro x hx
  rw [generated_eq] at hx
  rcases hx with ⟨n, rfl⟩
  exact ⟨n, fun _ => 1, fun _ => one_atom, by simp⟩

def integerSpan : Submodule ℤ ℚ := Submodule.span ℤ ({1, 2} : Set ℚ)

theorem integerSpan_eq : integerSpan = ℤ ∙ (1 : ℚ) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.mem_span_singleton_self 1
    · have h : (2 : ℚ) = (2 : ℤ) • (1 : ℚ) := by norm_num
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self 1)
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact Submodule.subset_span (by simp)

noncomputable def spanEquiv : ℤ ≃ₗ[ℤ] integerSpan :=
  (LinearEquiv.toSpanNonzeroSingleton ℤ ℚ 1 (by norm_num)).trans
    (LinearEquiv.ofEq _ _ integerSpan_eq.symm)

theorem integer_rank : Module.rank ℤ integerSpan = 1 := by
  calc
    Module.rank ℤ integerSpan = Module.rank ℤ ℤ := spanEquiv.rank_eq.symm
    _ = 1 := Module.rank_self ℤ

theorem counterexample : Atomic ∧ Module.rank ℤ integerSpan = 1 ∧
    ¬ (2 ≤ Module.rank ℤ integerSpan) := by
  refine ⟨atomic, integer_rank, ?_⟩
  rw [integer_rank]
  norm_num

end PuiseuxCounterexample

#print axioms PuiseuxCounterexample.generated_eq
#print axioms PuiseuxCounterexample.zero_sum
#print axioms PuiseuxCounterexample.one_atom
#print axioms PuiseuxCounterexample.atomic
#print axioms PuiseuxCounterexample.integer_rank
#print axioms PuiseuxCounterexample.counterexample
