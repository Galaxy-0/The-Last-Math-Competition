import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.NormNum

set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
namespace KernelIdealCounterexample
abbrev Chain := Fin 3
abbrev Relation := Chain → Chain → Bool
example : BoundedOrder Chain := inferInstance
example : Lattice Chain := inferInstance

def IsCongruence (r : Relation) : Prop :=
  (∀ x, r x x = true) ∧
  (∀ x y, r x y = true → r y x = true) ∧
  (∀ x y z, r x y = true → r y z = true → r x z = true) ∧
  (∀ x x' y y', r x x' = true → r y y' = true →
    r (min x y) (min x' y') = true) ∧
  (∀ x x' y y', r x x' = true → r y y' = true →
    r (max x y) (max x' y') = true)
instance (r : Relation) : Decidable (IsCongruence r) := by unfold IsCongruence; infer_instance

-- Genuine bounded-lattice homomorphism laws (meet, join, bottom and top).
def BoundedHom {n : ℕ} (q : Chain → Fin (n+1)) : Prop :=
  (∀ x y, q (min x y) = min (q x) (q y)) ∧
  (∀ x y, q (max x y) = max (q x) (q y)) ∧
  q 0 = 0 ∧ q 2 = Fin.last n
instance {n : ℕ} (q : Chain → Fin (n+1)) : Decidable (BoundedHom q) := by
  unfold BoundedHom; infer_instance

def identityQuotient : Chain → Fin 3 := fun x => x
def upperQuotient (x : Chain) : Fin 2 := if x = 0 then 0 else 1
def lowerQuotient (x : Chain) : Fin 2 := if x = 2 then 1 else 0
def trivialQuotient (_ : Chain) : Fin 1 := 0

theorem quotient_homomorphisms : BoundedHom identityQuotient ∧
    BoundedHom upperQuotient ∧ BoundedHom lowerQuotient ∧ BoundedHom trivialQuotient := by decide

theorem quotient_surjections : Function.Surjective identityQuotient ∧
    Function.Surjective upperQuotient ∧ Function.Surjective lowerQuotient ∧
    Function.Surjective trivialQuotient := by decide

def kernelRelation {n : ℕ} (q : Chain → Fin (n+1)) : Relation :=
  fun x y => decide (q x = q y)
def equalityRelation : Relation := kernelRelation identityQuotient
def upperRelation : Relation := kernelRelation upperQuotient
def lowerRelation : Relation := kernelRelation lowerQuotient
def universalRelation : Relation := kernelRelation trivialQuotient

theorem quotient_congruences : IsCongruence equalityRelation ∧ IsCongruence upperRelation ∧
    IsCongruence lowerRelation ∧ IsCongruence universalRelation := by decide

theorem congruences_classified : ∀ r : Relation, IsCongruence r →
    r = equalityRelation ∨ r = upperRelation ∨ r = lowerRelation ∨ r = universalRelation := by decide

-- The kernel ideal is the actual zero class of the congruence.
def kernel (r : Relation) : Finset Chain := Finset.univ.filter (fun x => r 0 x = true)
def zeroPreimage {n : ℕ} (q : Chain → Fin (n+1)) : Finset Chain :=
  Finset.univ.filter (fun x => q x = 0)
def IsIdeal (K : Finset Chain) : Prop :=
  0 ∈ K ∧ (∀ x y, x ≤ y → y ∈ K → x ∈ K) ∧
  (∀ x y, x ∈ K → y ∈ K → max x y ∈ K)
instance (K : Finset Chain) : Decidable (IsIdeal K) := by unfold IsIdeal; infer_instance

theorem quotient_zero_classes : kernel equalityRelation = zeroPreimage identityQuotient ∧
    kernel upperRelation = zeroPreimage upperQuotient ∧
    kernel lowerRelation = zeroPreimage lowerQuotient ∧
    kernel universalRelation = zeroPreimage trivialQuotient := by decide

theorem distinct_same_kernel : equalityRelation ≠ upperRelation ∧
    kernel equalityRelation = kernel upperRelation ∧
    kernel equalityRelation = {0} ∧ IsIdeal (kernel equalityRelation) := by decide

def congruences : Finset Relation := Finset.univ.filter IsCongruence
-- Enumerate actual ideals, not an asserted list of their sizes.
def ideals : Finset (Finset Chain) := Finset.univ.filter IsIdeal
def kernelIdeals : Finset (Finset Chain) := congruences.image kernel

theorem congruence_count : congruences.card = 4 := by decide
theorem ideal_count : ideals.card = 3 := by decide
theorem every_ideal_is_kernel : kernelIdeals = ideals := by decide
theorem kernel_ideal_count : kernelIdeals.card = 3 := by rw [every_ideal_is_kernel]; exact ideal_count

theorem all_ideals_realized : ∀ K : Finset Chain, IsIdeal K →
    K = zeroPreimage identityQuotient ∨ K = zeroPreimage lowerQuotient ∨
    K = zeroPreimage trivialQuotient := by decide

theorem natural_correspondence_not_injective : ¬ Function.Injective kernel := by
  intro h
  exact distinct_same_kernel.1 (h distinct_same_kernel.2.1)

theorem conjecture_00000008550_correspondence_false :
    ¬ Nonempty (↥congruences ≃ ↥kernelIdeals) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  simp only [Fintype.card_coe, congruence_count, kernel_ideal_count] at h
  norm_num at h

#print axioms quotient_homomorphisms
#print axioms quotient_surjections
#print axioms congruences_classified
#print axioms distinct_same_kernel
#print axioms every_ideal_is_kernel
#print axioms conjecture_00000008550_correspondence_false
end KernelIdealCounterexample
