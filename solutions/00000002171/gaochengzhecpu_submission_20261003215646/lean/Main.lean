import Std

namespace Conjecture2171

abbrev Subset (n : Nat) := Fin n → Bool
abbrev Family (n : Nat) := List (Subset n)

def union {n} (A B : Subset n) : Subset n := fun x => A x || B x

def UnionClosed {n} (F : Family n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, union A B ∈ F

/-- Fin n is exactly the union of the family, and at least one set is
nonempty. Nodup makes this a set family, not a multiset. -/
def Admissible {n} (F : Family n) : Prop :=
  F.Nodup ∧ UnionClosed F ∧
  (∀ x : Fin n, ∃ A ∈ F, A x = true) ∧
  ∃ A ∈ F, ∃ x : Fin n, A x = true

def frequency {n} (F : Family n) (x : Fin n) : Nat :=
  (F.filter (fun A => A x)).length

def FranklWitness {n} (F : Family n) : Prop :=
  ∃ x : Fin n, F.length ≤ 2 * frequency F x

def Counterexample {n} (F : Family n) : Prop :=
  Admissible F ∧ ∀ x : Fin n, 2 * frequency F x < F.length

theorem counterexample_iff {n} (F : Family n) :
    Counterexample F ↔ Admissible F ∧ ¬FranklWitness F := by
  constructor
  · rintro ⟨had, hsmall⟩
    refine ⟨had, ?_⟩
    rintro ⟨x,hx⟩
    have := hsmall x
    omega
  · rintro ⟨had, hnone⟩
    refine ⟨had, ?_⟩
    intro x
    have hnot : ¬ F.length ≤ 2 * frequency F x := by
      intro hx
      exact hnone ⟨x,hx⟩
    omega

def FranklConjecture : Prop :=
  ∀ n, ∀ F : Family n, Admissible F → FranklWitness F

def MinimalGroundCounterexample (n : Nat) (F : Family n) : Prop :=
  Counterexample F ∧ ∀ m, m < n → ∀ G : Family m, ¬Counterexample G

def TwelveAttained : Prop :=
  ∃ F : Family 12, MinimalGroundCounterexample 12 F

def StatedConjunction : Prop := FranklConjecture ∧ TwelveAttained

/-- General incompatibility, with actual finite union-closed families and
their occurrence counts rather than an uninterpreted proposition. -/
theorem frankl_excludes_every_counterexample (h : FranklConjecture)
    (n : Nat) (F : Family n) : ¬Counterexample F := by
  intro hc
  have hw := h n F hc.1
  exact ((counterexample_iff F).mp hc).2 hw

theorem conjecture2171_false : ¬StatedConjunction := by
  rintro ⟨hfrankl, F, hcounter, _⟩
  exact frankl_excludes_every_counterexample hfrankl 12 F hcounter

#print axioms counterexample_iff
#print axioms frankl_excludes_every_counterexample
#print axioms conjecture2171_false
end Conjecture2171
