import Std
namespace Conjecture04274
set_option maxHeartbeats 0
abbrev C7 := Fin 7

def Additive (f : C7 → C7) : Prop := ∀ a b, f (a+b) = f a + f b

def Injective (f : C7 → C7) : Prop := ∀ a b, f a = f b → a = b

def Surjective (f : C7 → C7) : Prop := ∀ b, ∃ a, f a = b

abbrev Aut := {f : C7 → C7 // Additive f ∧ Injective f ∧ Surjective f}

def multiples (a : C7) : Nat → C7
  | 0 => 0
  | n+1 => multiples a n + a

theorem additive_zero (f : C7 → C7) (hf : Additive f) : f 0 = 0 := by
  have h : f 0 = f 0 + f 0 := hf 0 0
  exact (by decide : ∀ a : C7, a = a + a → a = 0) (f 0) h

theorem additive_multiples (f : C7 → C7) (hf : Additive f) (n : Nat) :
    f (multiples 1 n) = multiples (f 1) n := by
  induction n with
  | zero => exact additive_zero f hf
  | succ n ih => exact (hf (multiples 1 n) 1).trans (congrArg (fun z => z + f 1) ih)

theorem generated_by_one (f : C7 → C7) (hf : Additive f) (x : C7) :
    f x = x * f 1 := by
  have h1 : multiples 1 x.val = x := (by decide : ∀ x : C7, multiples 1 x.val = x) x
  have hx := additive_multiples f hf x.val
  rw [h1] at hx
  rw [hx]
  exact (by decide : ∀ a x : C7, multiples a x.val = x * a) (f 1) x

theorem aut_one_nonzero (a : Aut) : a.val 1 ≠ 0 := by
  intro h
  have h0 := additive_zero a.val a.property.1
  have h10 : a.val 1 = a.val 0 := h.trans h0.symm
  have bad : (1 : C7) = 0 := a.property.2.1 1 0 h10
  exact (by decide : (1 : C7) ≠ 0) bad

def unitValue (k : Fin 6) : C7 := ⟨k.val+1, by omega⟩

def inverseUnit (k : Fin 6) : C7 :=
  match k.val with
  | 0 => 1
  | 1 => 4
  | 2 => 5
  | 3 => 2
  | 4 => 3
  | _ => 6

theorem unit_inverse : ∀ k : Fin 6, ∀ x : C7,
    (x * unitValue k) * inverseUnit k = x := by decide

theorem inverse_unit : ∀ k : Fin 6, ∀ x : C7,
    (x * inverseUnit k) * unitValue k = x := by decide

def autOfUnit (k : Fin 6) : Aut :=
  ⟨fun x => x * unitValue k,
    (by intro a b; exact (by decide : ∀ k : Fin 6, ∀ a b : C7,
      (a+b) * unitValue k = a * unitValue k + b * unitValue k) k a b),
    (by
      intro a b h
      have hm := congrArg (fun x => x * inverseUnit k) h
      simpa only [unit_inverse] using hm),
    (by intro b; exact ⟨b * inverseUnit k, inverse_unit k b⟩)⟩

def unitIndex (a : Aut) : Fin 6 :=
  ⟨(a.val 1).val - 1, by
    have hp := (a.val 1).isLt
    have hn : (a.val 1).val ≠ 0 := by
      intro h
      apply aut_one_nonzero a
      exact Fin.ext h
    omega⟩

theorem unitValue_unitIndex (a : Aut) : unitValue (unitIndex a) = a.val 1 := by
  apply Fin.ext
  change (a.val 1).val - 1 + 1 = (a.val 1).val
  have hn : (a.val 1).val ≠ 0 := by
    intro h
    exact aut_one_nonzero a (Fin.ext h)
  omega

theorem aut_reconstruction (a : Aut) : autOfUnit (unitIndex a) = a := by
  apply Subtype.ext
  funext x
  change x * unitValue (unitIndex a) = a.val x
  rw [unitValue_unitIndex]
  exact (generated_by_one a.val a.property.1 x).symm

theorem unit_roundtrip : ∀ k : Fin 6, unitIndex (autOfUnit k) = k := by decide

def Central (a : Aut) : Prop := ∀ b : Aut, ∀ x, a.val (b.val x) = b.val (a.val x)

theorem all_automorphisms_central (a : Aut) : Central a := by
  intro b x
  calc
    a.val (b.val x) = b.val x * a.val 1 := generated_by_one a.val a.property.1 (b.val x)
    _ = (x * b.val 1) * a.val 1 := congrArg (fun z => z * a.val 1)
      (generated_by_one b.val b.property.1 x)
    _ = (x * a.val 1) * b.val 1 :=
      (by decide : ∀ x y z : C7, (x*y)*z = (x*z)*y) x (b.val 1) (a.val 1)
    _ = a.val x * b.val 1 := congrArg (fun z => z * b.val 1)
      (generated_by_one a.val a.property.1 x).symm
    _ = b.val (a.val x) := (generated_by_one b.val b.property.1 (a.val x)).symm

abbrev Center := {a : Aut // Central a}

def centerOfUnit (k : Fin 6) : Center := ⟨autOfUnit k, all_automorphisms_central (autOfUnit k)⟩

def centerIndex (a : Center) : Fin 6 := unitIndex a.val

theorem center_reconstruction (a : Center) : centerOfUnit (centerIndex a) = a := by
  apply Subtype.ext
  exact aut_reconstruction a.val

theorem center_roundtrip (k : Fin 6) : centerIndex (centerOfUnit k) = k := unit_roundtrip k

structure Bijection (A B : Type) where
  forward : A → B
  backward : B → A
  left_inverse : ∀ a, backward (forward a) = a
  right_inverse : ∀ b, forward (backward b) = b

def center_has_six_elements : Bijection Center (Fin 6) where
  forward := centerIndex
  backward := centerOfUnit
  left_inverse := center_reconstruction
  right_inverse := center_roundtrip

-- Verify that the carrier really is a countable abelian 7-group.
theorem cyclic_group_laws :
    (∀ a b c : C7, (a+b)+c = a+(b+c)) ∧
    (∀ a : C7, 0+a=a ∧ a+0=a ∧ (0-a)+a=0) ∧
    (∀ a b : C7, a+b=b+a) := by decide

theorem seven_annihilates : ∀ a : C7, multiples a 7 = 0 := by decide

theorem carrier_countable : ∃ code : C7 → Nat, ∀ a b, code a=code b → a=b := by
  exact ⟨Fin.val, fun _ _ h => Fin.ext h⟩

theorem seven_prime : 2 ≤ (7 : Nat) ∧ ∀ d : Nat, d ∣ 7 → d=1 ∨ d=7 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have hle : d ≤ 7 := Nat.le_of_dvd (by decide) hd
  exact (by decide : ∀ d : Fin 8, d.val ∣ 7 → d.val=1 ∨ d.val=7) ⟨d,by omega⟩ hd

def centerEnumeration : List Center := (List.finRange 6).map centerOfUnit

theorem centerEnumeration_complete : ∀ a : Center, a ∈ centerEnumeration := by
  intro a
  apply List.mem_map.mpr
  exact ⟨centerIndex a, (by decide : ∀ k : Fin 6, k ∈ List.finRange 6) (centerIndex a),
    center_reconstruction a⟩

theorem centerEnumeration_nodup : centerEnumeration.Nodup := by
  unfold centerEnumeration List.Nodup
  apply List.Pairwise.map centerOfUnit ?_ (by decide :
    List.Pairwise (fun a b : Fin 6 => a ≠ b) (List.finRange 6))
  intro a b hab heq
  apply hab
  have h := congrArg centerIndex heq
  simpa only [center_roundtrip] using h

theorem centerEnumeration_cardinality : centerEnumeration.length = 6 := by
  simp only [centerEnumeration, List.length_map, List.length_finRange]

theorem six_not_power_of_two : ∀ n : Nat, 6 ≠ 2^n := by
  intro n
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      cases n with
      | zero => decide
      | succ n =>
        intro h
        have hp : 2^(n+3) = 2^n * 8 := by rw [Nat.pow_add]
        change 6 = 2^(n+3) at h
        rw [hp] at h
        omega

def powerProduct : List Nat → Nat
  | [] => 1
  | e::es => 2^e * powerProduct es

theorem powerProduct_is_power (es : List Nat) : powerProduct es = 2^es.sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [powerProduct, List.sum_cons, ih, Nat.pow_add]

-- This is the numerical assertion about the ACTUAL center enumeration,
-- accompanied above by completeness and no-duplicates proofs.
def ClaimedCenterPowerProduct : Prop :=
  ∀ elements : List Center, (∀ a, a ∈ elements) → elements.Nodup →
    ∃ es : List Nat, elements.length = powerProduct es

theorem conjecture04274_false : ¬ ClaimedCenterPowerProduct := by
  intro h
  obtain ⟨es, he⟩ := h centerEnumeration centerEnumeration_complete centerEnumeration_nodup
  rw [centerEnumeration_cardinality, powerProduct_is_power] at he
  exact six_not_power_of_two es.sum he

theorem center_count_not_power_of_two : ¬ ∃ n, centerEnumeration.length = 2^n := by
  rintro ⟨n, he⟩
  rw [centerEnumeration_cardinality] at he
  exact six_not_power_of_two n he

theorem full_conjecture_false (OtherAssertions : Prop) :
    ¬ (OtherAssertions ∧ ClaimedCenterPowerProduct) := by
  intro h
  exact conjecture04274_false h.2

#print axioms centerEnumeration_complete
#print axioms centerEnumeration_nodup
#print axioms seven_prime
#print axioms conjecture04274_false
#print axioms full_conjecture_false
#print axioms center_has_six_elements
end Conjecture04274




