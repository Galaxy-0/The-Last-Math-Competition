import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
Conjecture 00000009978 asserts finite termination of Jacobson-radical power
intersections for fully bounded Noetherian rings. The actual ring Q[[X]] is
commutative FBN and refutes finite termination at every natural-number stage.
The infinite intersection is also proved to be zero, to distinguish the two claims.
-/

namespace Conjecture9978

noncomputable section

/-- Essentiality of an ideal in a commutative ring: it intersects every nonzero
ideal nontrivially. These are exactly the right ideals, since the ring is commutative. -/
def IsEssentialIdeal {A : Type*} [CommRing A] (I : Ideal A) : Prop :=
  ∀ L : Ideal A, L ≠ ⊥ → I ⊓ L ≠ ⊥

/-- Standard FBN condition specialized to commutative rings. For every prime
quotient, each essential right ideal contains a nonzero two-sided ideal.
In a commutative ring Mathlib's ideals are simultaneously left and right ideals. -/
def CommFBN (A : Type*) [CommRing A] : Prop :=
  IsNoetherianRing A ∧
    ∀ (P : Ideal A), P.IsPrime →
      ∀ (I : Ideal (A ⧸ P)), IsEssentialIdeal I →
        ∃ K : Ideal (A ⧸ P), K ≠ ⊥ ∧ K ≤ I

/-- Explicit right-multiplication closure of the ordinary ideals used above. -/
theorem ideal_right_mul_closed {A : Type*} [CommRing A]
    (I : Ideal A) (a b : A) (ha : a ∈ I) : a * b ∈ I := by
  simpa only [mul_comm] using I.mul_mem_left b ha

theorem essential_ideal_nonzero {A : Type*} [CommRing A] [Nontrivial A]
    {I : Ideal A} (hI : IsEssentialIdeal I) : I ≠ ⊥ := by
  have h := hI ⊤ (show (⊤ : Ideal A) ≠ ⊥ from top_ne_bot)
  simpa only [inf_top_eq] using h

theorem comm_noetherian_fbn (A : Type*) [CommRing A] [IsNoetherianRing A] :
    CommFBN A := by
  refine ⟨inferInstance, ?_⟩
  intro P hP I hI
  letI : P.IsPrime := hP
  exact ⟨I, essential_ideal_nonzero hI, le_rfl⟩

/-- The actual formal power series ring, with untruncated infinite coefficient sequences. -/
abbrev Ring := PowerSeries ℚ

/-- The Jacobson radical as Mathlib's intersection of maximal ideals. -/
def radical : Ideal Ring := (⊥ : Ideal Ring).jacobson

theorem ring_noetherian : IsNoetherianRing Ring := inferInstance

theorem ring_fbn : CommFBN Ring := comm_noetherian_fbn Ring

theorem radical_eq_span_X : radical = Ideal.span {(PowerSeries.X : Ring)} := by
  unfold radical
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  exact PowerSeries.maximalIdeal_eq_span_X

theorem radical_pow_eq (n : ℕ) :
    radical ^ n = Ideal.span {((PowerSeries.X : Ring) ^ n)} := by
  rw [radical_eq_span_X, Ideal.span_singleton_pow]

theorem X_mem_radical : (PowerSeries.X : Ring) ∈ radical := by
  rw [radical_eq_span_X]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem X_pow_mem_radical_pow (n : ℕ) : (PowerSeries.X : Ring) ^ n ∈ radical ^ n :=
  Ideal.pow_mem_pow X_mem_radical n

theorem X_pow_nonzero (n : ℕ) : (PowerSeries.X : Ring) ^ n ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.coeff ℚ n) h
  simp only [PowerSeries.coeff_X_pow_self, map_zero, one_ne_zero] at hc

theorem radical_pow_nonzero (n : ℕ) : radical ^ n ≠ ⊥ := by
  intro h
  have hx := X_pow_mem_radical_pow n
  rw [h] at hx
  change (PowerSeries.X : Ring) ^ n = 0 at hx
  exact X_pow_nonzero n hx

theorem X_pow_not_mem_next_power (n : ℕ) :
    (PowerSeries.X : Ring) ^ n ∉ radical ^ (n + 1) := by
  intro h
  rw [radical_pow_eq] at h
  have hd : (PowerSeries.X : Ring) ^ (n + 1) ∣ (PowerSeries.X : Ring) ^ n :=
    Ideal.mem_span_singleton.mp h
  have hc := PowerSeries.X_pow_dvd_iff.mp hd n (Nat.lt_succ_self n)
  simp only [PowerSeries.coeff_X_pow_self, one_ne_zero] at hc

theorem radical_powers_strictly_descend (n : ℕ) : radical ^ (n + 1) < radical ^ n := by
  apply lt_of_le_of_ne (Ideal.pow_le_pow_right (Nat.le_succ n))
  intro h
  apply X_pow_not_mem_next_power n
  rw [h]
  exact X_pow_mem_radical_pow n

/-- Intersection of the first n+1 powers, including J^0 = R. Including or
omitting J^0 does not change the intersection at any positive stage. -/
def prefixIntersection (n : ℕ) : Ideal Ring :=
  ⨅ i : Fin (n + 1), radical ^ (i : ℕ)

theorem prefixIntersection_eq_power (n : ℕ) : prefixIntersection n = radical ^ n := by
  unfold prefixIntersection
  apply le_antisymm
  · exact iInf_le (fun i : Fin (n + 1) => radical ^ (i : ℕ)) ⟨n, Nat.lt_succ_self n⟩
  · exact le_iInf (fun i => Ideal.pow_le_pow_right (Nat.le_of_lt_succ i.isLt))

theorem finite_intersection_nonzero (n : ℕ) : prefixIntersection n ≠ ⊥ := by
  rw [prefixIntersection_eq_power]
  exact radical_pow_nonzero n

/-- Nontermination holds for all natural stages, not just a checked finite range. -/
theorem no_finite_termination : ¬ ∃ n : ℕ, prefixIntersection n = ⊥ := by
  rintro ⟨n, hn⟩
  exact finite_intersection_nonzero n hn

/-- Infinite intersection is zero: membership in J^(n+1) kills the n-th coefficient. -/
theorem infinite_intersection_zero : (⨅ n : ℕ, radical ^ n) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  change f = 0
  apply PowerSeries.ext
  intro n
  have hm : f ∈ radical ^ (n + 1) := (Ideal.mem_iInf.mp hf) (n + 1)
  rw [radical_pow_eq] at hm
  have hd : (PowerSeries.X : Ring) ^ (n + 1) ∣ f := Ideal.mem_span_singleton.mp hm
  have hc : PowerSeries.coeff ℚ n f = 0 :=
    PowerSeries.X_pow_dvd_iff.mp hd n (Nat.lt_succ_self n)
  simpa only [map_zero] using hc

/-- The actual ring meets the FBN hypothesis and has zero infinite intersection,
but none of its finite-stage power intersections is zero. -/
theorem counterexample :
    CommFBN Ring ∧
    (∀ n : ℕ, prefixIntersection n ≠ ⊥) ∧
    (⨅ n : ℕ, radical ^ n) = ⊥ :=
  ⟨ring_fbn, finite_intersection_nonzero, infinite_intersection_zero⟩

#print axioms comm_noetherian_fbn
#print axioms ring_noetherian
#print axioms ring_fbn
#print axioms radical_eq_span_X
#print axioms radical_pow_eq
#print axioms X_pow_nonzero
#print axioms radical_pow_nonzero
#print axioms radical_powers_strictly_descend
#print axioms prefixIntersection_eq_power
#print axioms no_finite_termination
#print axioms infinite_intersection_zero
#print axioms counterexample

end

end Conjecture9978
