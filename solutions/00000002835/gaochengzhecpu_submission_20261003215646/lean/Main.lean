import Std
import Std.Internal.Rat

namespace Conjecture2835
set_option maxRecDepth 100000

abbrev Scalar := Std.Internal.Rat
abbrev Matrix := Fin 2 → Fin 2 → Scalar
abbrev Support := Fin 2 → Fin 2 → Bool

/-- The determinant of any selected 2-by-2 minor. -/
def minor (M : Matrix) (i k j l : Fin 2) : Scalar :=
  M i j * M k l - M i l * M k j

def determinant (M : Matrix) : Scalar := minor M 0 1 0 1

/-- Determinantal rank for 2-by-2 matrices: the largest order of a
nonzero minor. The only possible positive orders are one and two. -/
def rank (M : Matrix) : Nat :=
  if determinant M ≠ 0 then 2 else if ∀ i j, M i j = 0 then 0 else 1

def rowDegree (G : Support) (i : Fin 2) : Nat :=
  ((List.finRange 2).filter (fun j => G i j)).length
def columnDegree (G : Support) (j : Fin 2) : Nat :=
  ((List.finRange 2).filter (fun i => G i j)).length

def Regular (G : Support) (r : Nat) : Prop :=
  (∀ i, rowDegree G i = r) ∧ ∀ j, columnDegree G j = r

/-- The observed bipartite graph has two row vertices and two disjoint
column vertices. This definition allows nonspanning subgraphs as well. -/
def ContainsRegularSubgraph (G : Support) (r : Nat) : Prop :=
  ∃ left right : Fin 2 → Bool, ∃ H : Support,
    (∃ i, left i = true) ∧ (∃ j, right j = true) ∧
    (∀ i j, H i j = true → G i j = true ∧ left i = true ∧ right j = true) ∧
    (∀ i, left i = true → rowDegree H i = r) ∧
    (∀ j, right j = true → columnDegree H j = r)

def SameObservations (G : Support) (M N : Matrix) : Prop :=
  ∀ i j, G i j = true → M i j = N i j

def UniquelyRecoverable (G : Support) (M : Matrix) : Prop :=
  ∀ N : Matrix, rank N = rank M → SameObservations G M N → N = M

def diagonal : Support := fun i j => decide (i = j)
def A : Matrix := fun _ _ => 1
def B : Matrix := fun i j => if i = j then 1 else -1

theorem diagonal_one_regular : Regular diagonal 1 := by
  unfold Regular
  decide

theorem diagonal_contains_one_regular : ContainsRegularSubgraph diagonal 1 := by
  refine ⟨(fun _ => true), (fun _ => true), diagonal, ⟨0,rfl⟩, ⟨0,rfl⟩, ?_, ?_, ?_⟩
  · intro i j h
    exact ⟨h,rfl,rfl⟩
  · intro i _
    exact diagonal_one_regular.1 i
  · intro j _
    exact diagonal_one_regular.2 j

theorem all_two_minors_zero :
    (∀ i k j l, minor A i k j l = 0) ∧
    (∀ i k j l, minor B i k j l = 0) := by decide

theorem nonzero_one_minors : A 0 0 ≠ 0 ∧ B 0 0 ≠ 0 := by decide
theorem both_rank_one : rank A = 1 ∧ rank B = 1 := by decide

/-- Explicit outer-product descriptions supply a second check of rank one. -/
def sign (i : Fin 2) : Scalar := if i = 0 then 1 else -1
theorem outer_products :
    (∀ i j, A i j = (1 : Scalar) * 1) ∧
    (∀ i j, B i j = sign i * sign j) := by decide

theorem same_observations : SameObservations diagonal A B := by
  unfold SameObservations
  decide

theorem distinct_completions : B ≠ A := by
  intro h
  have e : B 0 1 = A 0 1 := congrFun (congrFun h 0) 1
  have ne : B 0 1 ≠ A 0 1 := by decide
  exact ne e

theorem not_uniquely_recoverable : ¬UniquelyRecoverable diagonal A := by
  intro h
  exact distinct_completions (h B (both_rank_one.2.trans both_rank_one.1.symm) same_observations)

/-- A necessary 2-by-2, rank-one instance of the source's iff claim. -/
def ClaimedCriterion : Prop :=
  ∀ G : Support, ∀ M : Matrix, rank M = 1 →
    (UniquelyRecoverable G M ↔ ContainsRegularSubgraph G 1)

theorem conjecture2835_false : ¬ClaimedCriterion := by
  intro h
  exact not_uniquely_recoverable
    ((h diagonal A both_rank_one.1).mpr diagonal_contains_one_regular)

#print axioms diagonal_contains_one_regular
#print axioms all_two_minors_zero
#print axioms both_rank_one
#print axioms not_uniquely_recoverable
#print axioms conjecture2835_false
end Conjecture2835
