import Std

/-!
Counterexample to TLMC 00000008420's minimum-order clause.
The points, blocks, and resolution classes are independently indexed finite sets.
All design and automorphism axioms below are actual incidence conditions.
No mathlib, native_decide, sorry, or additional axioms are used.
-/
namespace TLMC8420

/-- Every indexed block consists of exactly three distinct points. -/
def TripleBlocks (v b : Nat) (inc : Fin b → Fin v → Bool) : Prop :=
  ∀ t, ∃ x y z : Fin v, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ∀ p, inc t p = true ↔ p = x ∨ p = y ∨ p = z

/-- Every pair of distinct points lies in exactly one indexed block. -/
def PairOnce (v b : Nat) (inc : Fin b → Fin v → Bool) : Prop :=
  ∀ x y : Fin v, x ≠ y → ∃ t : Fin b,
    (inc t x = true ∧ inc t y = true) ∧
    ∀ u : Fin b, (inc u x = true ∧ inc u y = true) → u = t

/-- The function cls partitions blocks into classes; each class partitions points. -/
def Resolves (v b r : Nat) (inc : Fin b → Fin v → Bool)
    (cls : Fin b → Fin r) : Prop :=
  ∀ c : Fin r, ∀ x : Fin v, ∃ t : Fin b,
    (cls t = c ∧ inc t x = true) ∧
    ∀ u : Fin b, (cls u = c ∧ inc u x = true) → u = t

def IsKTS (v b r : Nat) (inc : Fin b → Fin v → Bool)
    (cls : Fin b → Fin r) : Prop :=
  3 ≤ v ∧ TripleBlocks v b inc ∧ PairOnce v b inc ∧ Resolves v b r inc cls

/-- Explicit bijectivity, avoiding any implicit assumption that a map permutes. -/
def BijectiveFin {n : Nat} (f : Fin n → Fin n) : Prop :=
  (∀ x y, f x = f y → x = y) ∧ (∀ y, ∃ x, f x = y)

/-- A resolution-preserving automorphism permutes points, blocks and classes. -/
def IsAutomorphism {v b r : Nat} (inc : Fin b → Fin v → Bool)
    (cls : Fin b → Fin r) (p : Fin v → Fin v)
    (q : Fin b → Fin b) (s : Fin r → Fin r) : Prop :=
  BijectiveFin p ∧ BijectiveFin q ∧ BijectiveFin s ∧
    (∀ t x, inc (q t) (p x) = inc t x) ∧
    (∀ t, cls (q t) = s (cls t))

def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterate f n x)

/-- One automorphism itself generates a point-transitive cyclic action. -/
def CyclicTransitive {v : Nat} (p : Fin v → Fin v) : Prop :=
  ∀ x y : Fin v, ∃ k : Fin v, iterate p k.val x = y

def HasTransitiveAutomorphism {v b r : Nat}
    (inc : Fin b → Fin v → Bool) (cls : Fin b → Fin r) : Prop :=
  ∃ p : Fin v → Fin v, ∃ q : Fin b → Fin b, ∃ s : Fin r → Fin r,
    IsAutomorphism inc cls p q s ∧ CyclicTransitive p

/-- The singleton block is the entire three-point set. -/
def inc3 : Fin 1 → Fin 3 → Bool := fun _ _ => true
def cls3 : Fin 1 → Fin 1 := fun _ => 0

/-- The cycle (0 1 2), not just an unspecified transitive automorphism group. -/
def cycle3 (x : Fin 3) : Fin 3 :=
  ⟨(x.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

theorem kts3_valid : IsKTS 3 1 1 inc3 cls3 := by
  unfold IsKTS TripleBlocks PairOnce Resolves
  decide

theorem cycle3_automorphism : IsAutomorphism inc3 cls3 cycle3 id id := by
  unfold IsAutomorphism BijectiveFin
  decide

theorem cycle3_transitive : CyclicTransitive cycle3 := by
  unfold CyclicTransitive
  decide

theorem cycle3_exact_order :
    (∀ x : Fin 3, iterate cycle3 3 x = x) ∧
    iterate cycle3 1 0 ≠ 0 ∧ iterate cycle3 2 0 ≠ 0 := by
  decide

theorem kts3_has_transitive_automorphism : HasTransitiveAutomorphism inc3 cls3 :=
  ⟨cycle3, id, id, cycle3_automorphism, cycle3_transitive⟩

/-- A necessary consequence of claiming that the smallest possible order is 15. -/
def MinimumOrderAtLeast15 : Prop :=
  ∀ v b r : Nat, ∀ inc : Fin b → Fin v → Bool, ∀ cls : Fin b → Fin r,
    IsKTS v b r inc cls → HasTransitiveAutomorphism inc cls → 15 ≤ v

/-- Formal version of the exact minimum-order clause, including attainment. -/
def MinimumOrderIs15 : Prop :=
  (∃ b r : Nat, ∃ inc : Fin b → Fin 15 → Bool, ∃ cls : Fin b → Fin r,
    IsKTS 15 b r inc cls ∧ HasTransitiveAutomorphism inc cls) ∧
  MinimumOrderAtLeast15

theorem minimum_order_lower_bound_false : ¬ MinimumOrderAtLeast15 := by
  intro h
  have bad : 15 ≤ 3 := h 3 1 1 inc3 cls3 kts3_valid kts3_has_transitive_automorphism
  exact (by decide : ¬ (15 ≤ 3)) bad

theorem minimum_order_clause_false : ¬ MinimumOrderIs15 := by
  intro h
  exact minimum_order_lower_bound_false h.2

/-- Refuting one conjunct refutes the whole conjunction, regardless of other clauses. -/
theorem conjecture_conjunction_false (otherClauses : Prop) :
    ¬ (otherClauses ∧ MinimumOrderIs15) := by
  intro h
  exact minimum_order_clause_false h.2

#print axioms minimum_order_clause_false
#print axioms conjecture_conjunction_false
end TLMC8420
