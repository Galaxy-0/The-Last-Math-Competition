import Std

/-! Conjecture 425: the cube with side length two already violates log-concavity.
All four entries range over 0,1,2.  Enumeration completeness, monotonicity,
volumes, and the coefficient inequality are checked by the Lean kernel. -/
namespace Conjecture425

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Entries are top-left, top-right, bottom-left, bottom-right. -/
abbrev Grid := Fin 3 × Fin 3 × Fin 3 × Fin 3

/-- Standard weak decrease along rows and columns of a plane partition. -/
def IsPlanePartition (g : Grid) : Prop :=
  g.1 ≥ g.2.1 ∧ g.1 ≥ g.2.2.1 ∧ g.2.1 ≥ g.2.2.2 ∧ g.2.2.1 ≥ g.2.2.2

instance (g : Grid) : Decidable (IsPlanePartition g) := inferInstanceAs
  (Decidable (_ ∧ _ ∧ _ ∧ _))

def volume (g : Grid) : Nat :=
  g.1.val + g.2.1.val + g.2.2.1.val + g.2.2.2.val

def allGrids : List Grid :=
  (List.finRange 3).flatMap fun a =>
  (List.finRange 3).flatMap fun b =>
  (List.finRange 3).flatMap fun c =>
  (List.finRange 3).map fun d => (a,b,c,d)

/-- The enumeration contains every possible bounded 2 by 2 array. -/
theorem allGrids_complete : ∀ a b c d : Fin 3, (a,b,c,d) ∈ allGrids := by decide

/-- Each array is counted once. -/
theorem allGrids_nodup : allGrids.Nodup := by decide

def planePartitions : List Grid := allGrids.filter (fun g => decide (IsPlanePartition g))

/-- The filtered objects are exactly the plane partitions in the 2 by 2 by 2 box. -/
theorem membership_exact : ∀ a b c d : Fin 3,
    ((a,b,c,d) ∈ planePartitions ↔ IsPlanePartition (a,b,c,d)) := by decide

/-- Coefficient of q^k in the volume generating function of this cubic box. -/
def coefficient (k : Nat) : Nat :=
  (planePartitions.filter (fun g => decide (volume g = k))).length

def LogConcave (a : Nat → Nat) : Prop :=
  ∀ k : Nat, 1 ≤ k → a k * a k ≥ a (k-1) * a (k+1)

theorem full_coefficient_list :
    (List.range 9).map coefficient = [1,1,3,3,4,3,3,1,1] := by decide

theorem coefficient_zero : coefficient 0 = 1 := by decide
theorem coefficient_one : coefficient 1 = 1 := by decide
theorem coefficient_two : coefficient 2 = 3 := by decide

/-- A diagonal (equal side lengths) box with a coefficient sequence
that fails the claimed universal log-concavity. -/
theorem conjecture425_counterexample : ¬ LogConcave coefficient := by
  intro h
  have bad := h 1 (by decide)
  have impossible : ¬ (coefficient 1 * coefficient 1 ≥
      coefficient (1-1) * coefficient (1+1)) := by decide
  exact impossible bad

#print axioms allGrids_complete
#print axioms allGrids_nodup
#print axioms membership_exact
#print axioms full_coefficient_list
#print axioms conjecture425_counterexample
end Conjecture425
