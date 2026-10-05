import Mathlib.RingTheory.Flat.Basic
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Disproof of conjecture 00000004289

Source SHA256:
c58010cd76af9ed661fa22e252ba1561223305e879cfeb20b69ea0af3f8a7359

All groups below are actual additive abelian groups with their canonical
integer-module structure. Subgroup size is a strict cardinal bound.
The threshold and the carrier cardinality are kept independent.
-/

namespace Conjecture4289

universe u

/-- The source's non-free group whose every subgroup below the threshold is free. -/
def AlmostFree (kappa : Cardinal.{u}) (G : Type u) [AddCommGroup G] : Prop :=
  (¬ Module.Free ℤ G) ∧
    ∀ H : AddSubgroup G, Cardinal.mk H < kappa → Module.Free ℤ H

/-- Every additive subgroup below the same threshold is a flat integer module. -/
def FlatFree (kappa : Cardinal.{u}) (G : Type u) [AddCommGroup G] : Prop :=
  ∀ H : AddSubgroup G, Cardinal.mk H < kappa → Module.Flat ℤ H

/-- The almost-free but not flat-free separation asserted in the source. -/
def Separation (kappa : Cardinal.{u}) (G : Type u) [AddCommGroup G] : Prop :=
  AlmostFree kappa G ∧ ¬ FlatFree kappa G

/-- Actual existence with threshold `kappa` and carrier cardinality `lambda`. -/
def SeparationExists (kappa lambda : Cardinal.{u}) : Prop :=
  ∃ (G : Type u) (group : AddCommGroup G),
    Cardinal.mk G = lambda ∧ @Separation kappa G group

/-- The diagonal convention for the cardinals at which separation occurs. -/
def SeparationCardinals : Set Cardinal.{u} :=
  {lambda | SeparationExists lambda lambda}

/-- Every free abelian group is flat for its canonical integer-module structure. -/
theorem free_abelian_is_flat (G : Type u) [AddCommGroup G]
    (h : Module.Free ℤ G) : Module.Flat ℤ G := by
  letI : Module.Free ℤ G := h
  exact Module.Flat.of_free

/-- The implication holds at every threshold, without any size or infinitude assumption. -/
theorem almostFree_implies_flatFree (kappa : Cardinal.{u}) (G : Type u)
    [AddCommGroup G] (h : AlmostFree kappa G) : FlatFree kappa G := by
  intro H hH
  exact free_abelian_is_flat H (h.2 H hH)

/-- No actual abelian group separates these two properties at any threshold. -/
theorem no_separation (kappa : Cardinal.{u}) (G : Type u) [AddCommGroup G] :
    ¬ Separation kappa G := by
  intro h
  exact h.2 (almostFree_implies_flatFree kappa G h.1)

/-- Nonexistence holds independently of the threshold versus size convention. -/
theorem no_separation_exists (kappa lambda : Cardinal.{u}) :
    ¬ SeparationExists kappa lambda := by
  rintro ⟨G, group, _, h⟩
  exact @no_separation kappa G group h

/-- The whole diagonal class of possible separation cardinals is empty. -/
theorem separationCardinals_empty : SeparationCardinals.{u} = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro lambda h
  exact no_separation_exists lambda lambda h

/-- There is no least separation cardinal, because there is no separation cardinal. -/
theorem no_least_separation_cardinal (lambda : Cardinal.{u}) :
    ¬ IsLeast SeparationCardinals lambda := by
  intro h
  exact no_separation_exists lambda lambda h.1

/-- In particular the existence asserted at aleph omega is false. -/
theorem no_separation_at_aleph_omega :
    ¬ SeparationExists (Cardinal.aleph Ordinal.omega0)
      (Cardinal.aleph Ordinal.omega0 : Cardinal.{u}) :=
  no_separation_exists _ _

/-- The source's aleph one implication holds even without a carrier-size restriction. -/
theorem almostFree_aleph_one_implies_flatFree (G : Type u) [AddCommGroup G]
    (h : AlmostFree (Cardinal.aleph 1) G) : FlatFree (Cardinal.aleph 1) G :=
  almostFree_implies_flatFree _ G h

/-- Exact negation of the source's necessary minimum-cardinality assertion. -/
theorem conjecture4289_disproof :
    ¬ IsLeast SeparationCardinals (Cardinal.aleph Ordinal.omega0 : Cardinal.{u}) :=
  no_least_separation_cardinal _

end Conjecture4289
