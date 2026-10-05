import Conjecture106

set_option pp.all true

#check @Conjecture106.largestPrimeFactor_spec
#check @Conjecture106.threshold_iff_prime_divisor
#check @Conjecture106.dyadic_primes
#check @Conjecture106.bounded_representative
#check @Conjecture106.unbounded_good
#check @Conjecture106.conjecture
#print Real.instLT
#print Real.instNatCast
#print Real.instInv
#print instLENat
#print instLTNat
#print Nat.instDvd
#print Nat.primeFactors
#print Set.Finite

example : ∀ k : Nat, 2 ≤ k → ∃ c : Real, 0 < c ∧
    Set.Infinite {n : Nat | 2 ≤ n ∧ ∀ i : Nat, 1 ≤ i → i ≤ k →
      Real.rpow (Nat.cast n) c < Nat.cast (Conjecture106.largestPrimeFactor (Nat.add n i))} :=
  Conjecture106.conjecture

example {m : Nat} (hm : 2 ≤ m) :
    2 ≤ Conjecture106.largestPrimeFactor m ∧
    (∀ q : Nat, q ∣ Conjecture106.largestPrimeFactor m → q = 1 ∨ q = Conjecture106.largestPrimeFactor m) ∧
    Conjecture106.largestPrimeFactor m ∣ m ∧
    ∀ q : Nat, Nat.Prime q → q ∣ m → q ≤ Conjecture106.largestPrimeFactor m := by
  obtain ⟨hp, hd, hmax⟩ := Conjecture106.largestPrimeFactor_spec hm
  exact ⟨(Nat.prime_def.mp hp).1, (Nat.prime_def.mp hp).2, hd, hmax⟩
