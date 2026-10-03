import Std

namespace Conjecture2610
universe u

/-- The standard equational axioms for a nonempty lattice. -/
structure LatticeModel where
  Carrier : Type u
  point : Carrier
  meet : Carrier → Carrier → Carrier
  join : Carrier → Carrier → Carrier
  meet_comm : ∀ x y, meet x y = meet y x
  join_comm : ∀ x y, join x y = join y x
  meet_assoc : ∀ x y z, meet (meet x y) z = meet x (meet y z)
  join_assoc : ∀ x y z, join (join x y) z = join x (join y z)
  meet_idem : ∀ x, meet x x = x
  join_idem : ∀ x, join x x = x
  meet_absorb : ∀ x y, meet x (join x y) = x
  join_absorb : ∀ x y, join x (meet x y) = x

inductive Term where
  | var : Nat → Term
  | meet : Term → Term → Term
  | join : Term → Term → Term

def evaluate (L : LatticeModel) (v : Nat → L.Carrier) : Term → L.Carrier
  | .var n => v n
  | .meet s t => L.meet (evaluate L v s) (evaluate L v t)
  | .join s t => L.join (evaluate L v s) (evaluate L v t)

structure Identity where
  lhs : Term
  rhs : Term

def Satisfies (L : LatticeModel) (e : Identity) : Prop :=
  ∀ v : Nat → L.Carrier, evaluate L v e.lhs = evaluate L v e.rhs

/-- Semantic strength is proper inclusion of classes of nonempty lattices. -/
def StrictlyStronger (new old : Identity) : Prop :=
  (∀ L : LatticeModel.{u}, Satisfies L new → Satisfies L old) ∧
  ∃ L : LatticeModel.{u}, Satisfies L old ∧ ¬Satisfies L new

def collapse : Identity := ⟨.var 0, .var 1⟩

theorem collapse_forces_singleton (L : LatticeModel) (h : Satisfies L collapse)
    (x y : L.Carrier) : x = y := by
  have hh := h (fun i => if i = 0 then x else y)
  simpa [collapse, evaluate] using hh

theorem collapse_implies_every_identity (L : LatticeModel) (h : Satisfies L collapse)
    (e : Identity) : Satisfies L e := by
  intro v
  exact collapse_forces_singleton L h (evaluate L v e.lhs) (evaluate L v e.rhs)

theorem collapse_has_no_strict_refinement (e : Identity) :
    ¬StrictlyStronger.{u} e collapse := by
  rintro ⟨_, L, hcollapse, hnew⟩
  exact hnew (collapse_implies_every_identity L hcollapse e)

def ClaimedRefinement : Prop :=
  ∀ old : Identity, ∃ new : Identity, StrictlyStronger.{u} new old

theorem conjecture2610_false : ¬ClaimedRefinement.{u} := by
  intro h
  obtain ⟨e, he⟩ := h collapse
  exact collapse_has_no_strict_refinement e he

/-- The counteridentity is satisfiable; the argument does not exploit an
inconsistent axiom or an empty universe. -/
def singleton : LatticeModel where
  Carrier := Unit
  point := ()
  meet _ _ := ()
  join _ _ := ()
  meet_comm := by intros; rfl
  join_comm := by intros; rfl
  meet_assoc := by intros; rfl
  join_assoc := by intros; rfl
  meet_idem := by intro x; cases x; rfl
  join_idem := by intro x; cases x; rfl
  meet_absorb := by intro x y; cases x; rfl
  join_absorb := by intro x y; cases x; rfl

theorem singleton_satisfies_collapse : Satisfies singleton collapse := by
  intro v
  change (v 0 : Unit) = (v 1 : Unit)
  have hu : ∀ x y : Unit, x = y := by
    intro x y
    cases x
    cases y
    rfl
  exact hu (v 0) (v 1)

#print axioms collapse_implies_every_identity
#print axioms collapse_has_no_strict_refinement
#print axioms conjecture2610_false
#print axioms singleton_satisfies_collapse
end Conjecture2610
