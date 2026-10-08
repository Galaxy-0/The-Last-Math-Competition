import Std

/-!
# Counterexample to TLMC 00000008196: dependent Staudt-prime hits

A Staudt hit of a prime p at index k means exactly p - 1 divides k,
as specified in the conjecture itself. For primes 5 and 17, the second
hit implies the first. Among the first 8m positive even indices their
counts are 4m and m, and the intersection count is m. Consequently the
joint probability is 1/8, whereas the product of marginal probabilities
is 1/16. The discrepancy persists at arbitrarily large sample sizes.

The proof uses only Lean's bundled standard library. Finite base facts
are checked with `decide`; all formulas in the unbounded parameter m
are proved symbolically.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace TLMC8196

/-- Elementary prime predicate, using the usual characterization by divisors.
Only divisors up to p need to be considered. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Fin (p+1), d.val ∣ p → d.val = 1 ∨ d.val = p

instance (p : Nat) : Decidable (IsPrime p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem five_prime : IsPrime 5 := by decide
theorem seventeen_prime : IsPrime 17 := by decide
theorem primes_distinct : (5 : Nat) ≠ 17 := by decide

/-- The exact Staudt-hit definition in the source statement. -/
def hit (p k : Nat) : Bool := k % (p-1) == 0

theorem hit_iff_dvd (p k : Nat) : hit p k = true ↔ p-1 ∣ k := by
  simp [hit, Nat.dvd_iff_mod_eq_zero]

/-- The nesting of the two events holds at every index, independently of
which probability distribution might be placed on the indices. -/
theorem hit17_implies_hit5 (k : Nat) (h : hit 17 k = true) :
    hit 5 k = true := by
  simp [hit] at h ⊢
  omega

/-- A block of eight consecutive positive even indices. -/
def evenBlock (b : Nat) : List Nat :=
  (List.range 8).map (fun r => 2 * (8*b + r + 1))

/-- The first 8m positive even indices, split into consecutive blocks. -/
def evenSample (m : Nat) : List Nat := (List.range m).flatMap evenBlock

def hitCount (p : Nat) (sample : List Nat) : Nat := sample.countP (hit p)
def jointCount (p q : Nat) (sample : List Nat) : Nat :=
  sample.countP (fun k => hit p k && hit q k)

/-- Independence for uniform sampling of the list positions, with all
fractions cross-multiplied. This is exactly P(A∩B)=P(A)P(B) when nonempty. -/
def IndependentOn (p q : Nat) (sample : List Nat) : Prop :=
  jointCount p q sample * sample.length = hitCount p sample * hitCount q sample

/-- Each residue pattern repeats in every block, not only the first one. -/
theorem hit5_periodic (b r : Nat) :
    hit 5 (2 * (8*b+r+1)) = hit 5 (2*(r+1)) := by
  have hmod : (2*(8*b+r+1)) % 4 = (2*(r+1)) % 4 := by omega
  simp only [hit, Nat.reduceSub, hmod]

theorem hit17_periodic (b r : Nat) :
    hit 17 (2 * (8*b+r+1)) = hit 17 (2*(r+1)) := by
  have hmod : (2*(8*b+r+1)) % 16 = (2*(r+1)) % 16 := by omega
  simp only [hit, Nat.reduceSub, hmod]

theorem block_length (b : Nat) : (evenBlock b).length = 8 := by
  simp [evenBlock]

theorem block_hit5 (b : Nat) : hitCount 5 (evenBlock b) = 4 := by
  unfold hitCount evenBlock
  rw [List.countP_map]
  have hf : (fun r => hit 5 (2 * (8*b+r+1))) = (fun r => hit 5 (2*(r+1))) :=
    funext (hit5_periodic b)
  change (List.range 8).countP (fun r => hit 5 (2*(8*b+r+1))) = 4
  rw [hf]
  decide

theorem block_hit17 (b : Nat) : hitCount 17 (evenBlock b) = 1 := by
  unfold hitCount evenBlock
  rw [List.countP_map]
  have hf : (fun r => hit 17 (2 * (8*b+r+1))) = (fun r => hit 17 (2*(r+1))) :=
    funext (hit17_periodic b)
  change (List.range 8).countP (fun r => hit 17 (2*(8*b+r+1))) = 1
  rw [hf]
  decide

/-- Nested events have exactly the smaller event as their intersection. -/
theorem joint_eq_hit17 (sample : List Nat) :
    jointCount 5 17 sample = hitCount 17 sample := by
  have hf : (fun k => hit 5 k && hit 17 k) = hit 17 := by
    funext k
    cases h17 : hit 17 k with
    | false => simp
    | true => simp [hit17_implies_hit5 k h17]
  unfold jointCount hitCount
  rw [hf]

theorem evenSample_succ (m : Nat) :
    evenSample (m+1) = evenSample m ++ evenBlock m := by
  simp [evenSample, List.range_succ, List.flatMap_append]

/-- The sample is exactly the initial segment claimed in the mathematical
argument, with each positive even index listed once in increasing order. -/
theorem evenSample_initial_segment (m : Nat) :
    evenSample m = (List.range (8*m)).map (fun j => 2*(j+1)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [evenSample_succ, ih, Nat.mul_add, Nat.mul_one,
      List.range_add, List.map_append, List.map_map]
    rfl

/-- Exact counts on arbitrarily long uniform samples of even indices. -/
theorem exact_counts (m : Nat) :
    (evenSample m).length = 8*m ∧
    hitCount 5 (evenSample m) = 4*m ∧
    hitCount 17 (evenSample m) = m ∧
    jointCount 5 17 (evenSample m) = m := by
  induction m with
  | zero => decide
  | succ m ih =>
    rcases ih with ⟨hlen, h5, h17, _⟩
    have hlen' : (evenSample (m+1)).length = 8*(m+1) := by
      rw [evenSample_succ, List.length_append, hlen, block_length]
      omega
    have h5' : hitCount 5 (evenSample (m+1)) = 4*(m+1) := by
      rw [evenSample_succ]
      unfold hitCount
      rw [List.countP_append]
      change hitCount 5 (evenSample m) + hitCount 5 (evenBlock m) = _
      rw [h5, block_hit5]
      omega
    have h17' : hitCount 17 (evenSample (m+1)) = m+1 := by
      rw [evenSample_succ]
      unfold hitCount
      rw [List.countP_append]
      change hitCount 17 (evenSample m) + hitCount 17 (evenBlock m) = _
      rw [h17, block_hit17]
    exact ⟨hlen', h5', h17', by rw [joint_eq_hit17, h17']⟩

/-- The independence equation fails for every positive number of blocks. -/
theorem not_independent (m : Nat) (hm : 0 < m) :
    ¬ IndependentOn 5 17 (evenSample m) := by
  intro h
  rcases exact_counts m with ⟨hlen, h5, h17, hj⟩
  unfold IndependentOn at h
  rw [hlen, h5, h17, hj] at h
  have hc : 8*m = 4*m := Nat.mul_right_cancel hm (by
    simpa [Nat.mul_comm m (8*m)] using h)
  have h84 : 8 = 4 := Nat.mul_right_cancel hm hc
  omega

/-- In every nonempty list, independence is impossible whenever the hit at
17 has positive frequency and the hit at 5 is not certain. This isolates
the obstruction without assuming any specific distribution on indices. -/
theorem nested_obstruction (sample : List Nat)
    (hpos : 0 < hitCount 17 sample)
    (hnotall : hitCount 5 sample < sample.length) :
    ¬ IndependentOn 5 17 sample := by
  intro h
  unfold IndependentOn at h
  rw [joint_eq_hit17] at h
  have hc : sample.length = hitCount 5 sample :=
    Nat.mul_left_cancel hpos (by simpa [Nat.mul_comm (hitCount 5 sample) (hitCount 17 sample)] using h)
  omega

/-- Unbounded counterexamples: after every requested sample-size threshold,
a larger uniform even-index sample still violates independence. -/
theorem arbitrarily_large_counterexamples (N : Nat) :
    ∃ m : Nat, N < (evenSample m).length ∧
      ¬ IndependentOn 5 17 (evenSample m) := by
  refine ⟨N+1, ?_, not_independent (N+1) (by omega)⟩
  rw [(exact_counts (N+1)).1]
  omega

/-- A precise universal independent-hit law under uniform sampling of
positive even indices. It is refuted by the two distinct actual primes. -/
def IndependentHitLaw : Prop :=
  ∀ p q, IsPrime p → IsPrime q → p ≠ q →
    ∀ m, 0 < m → IndependentOn p q (evenSample m)

theorem conjecture8196_false : ¬ IndependentHitLaw := by
  intro h
  exact not_independent 1 (by decide)
    (h 5 17 five_prime seventeen_prime primes_distinct 1 (by decide))

#print axioms exact_counts
#print axioms not_independent
#print axioms arbitrarily_large_counterexamples
#print axioms conjecture8196_false

end TLMC8196
