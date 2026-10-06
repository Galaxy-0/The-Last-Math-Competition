/-!
Formal contradiction in conjecture 00000004383.

The first nonzero group is asserted both to be a direct sum of prime-field
additive groups and to have a generator of order four.  The first assertion
implies annihilation by the characteristic prime p; the second then forces
4 | p, impossible for a prime.
-/

namespace Conjecture04383

/-- Repeated addition, including zero repetitions. -/
def nsmul {A : Type} (zero : A) (add : A → A → A) (x : A) : Nat → A
  | 0 => zero
  | n + 1 => add x (nsmul zero add x n)

/-- The additive data of a prime-field vector space, abstracted to the two
facts needed here. `characteristic_kills` is the characteristic-p law. -/
structure PrimeCharacteristicAdditive (p : Nat) where
  Carrier : Type
  zero : Carrier
  add : Carrier → Carrier → Carrier
  characteristic_kills : ∀ x, nsmul zero add x p = zero

/-- A finite direct sum is represented as a function into each summand, with
pointwise addition. -/
def directSum {p : Nat} (V : PrimeCharacteristicAdditive p) (n : Nat) := Fin n → V.Carrier

def directSumZero {p : Nat} (V : PrimeCharacteristicAdditive p) {n : Nat} : directSum V n :=
  fun _ => V.zero

def directSumAdd {p : Nat} (V : PrimeCharacteristicAdditive p) {n : Nat}
    (x y : directSum V n) : directSum V n :=
  fun i => V.add (x i) (y i)

theorem repeat_directSum_at {p : Nat} (V : PrimeCharacteristicAdditive p)
    {d : Nat} (x : directSum V d) (n : Nat) (i : Fin d) :
    nsmul (directSumZero (V := V) (n := d))
      (directSumAdd (V := V) (n := d)) x n i = nsmul V.zero V.add (x i) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nsmul, directSumAdd, ih]

/-- The bridge from an F_p-additive direct sum to the exponent-p property. -/
theorem directSum_characteristic_kills {p : Nat} (V : PrimeCharacteristicAdditive p)
    {d : Nat} (x : directSum V d) :
    nsmul (directSumZero (V := V) (n := d))
      (directSumAdd (V := V) (n := d)) x p = directSumZero (V := V) (n := d) := by
  funext i
  rw [repeat_directSum_at V x p i]
  exact V.characteristic_kills (x i)

/-- A fully elementary primality predicate used to keep the arithmetic proof
independent of any imported primality theorem. -/
def ElementaryPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ a b, p = a * b → a = 1 ∨ b = 1

def DivisibleByFour (n : Nat) : Prop := ∃ k, n = 4 * k

theorem no_elementary_prime_divisible_by_four {p : Nat}
    (hp : ElementaryPrime p) : ¬ DivisibleByFour p := by
  intro h
  rcases h with ⟨k, hk⟩
  cases k with
  | zero =>
      have hle := hp.1
      rw [hk] at hle
      contradiction
  | succ k =>
      cases k with
      | zero =>
          have hp4 : p = 4 := by
            simp at hk
            exact hk
          have hfactor : p = 2 * 2 := by simp [hp4]
          rcases hp.2 2 2 hfactor with hleft | hright
          · cases hleft
          · cases hright
      | succ k =>
          rcases hp.2 4 (Nat.succ (Nat.succ k)) hk with hleft | hright
          · cases hleft
          · cases hright

/-- A cyclic order-four generator: its n-fold sum vanishes exactly when
four divides n. -/
def OrderFourGenerator {A : Type} (zero : A) (add : A → A → A) (g : A) : Prop :=
  ∀ n, nsmul zero add g n = zero ↔ DivisibleByFour n

/-- The common first-nonzero-group description is impossible.  This theorem
connects the field-direct-sum property to the order-four generator itself. -/
theorem no_prime_field_sum_can_be_cyclic_four
    {p : Nat} (hp : ElementaryPrime p)
    (V : PrimeCharacteristicAdditive p) {d : Nat}
    (g : directSum V d)
    (hg : OrderFourGenerator (directSumZero (V := V) (n := d))
      (directSumAdd (V := V) (n := d)) g) : False := by
  have hpzero := directSum_characteristic_kills V g
  have hdiv : DivisibleByFour p := (hg p).mp hpzero
  exact no_elementary_prime_divisible_by_four hp hdiv

end Conjecture04383
