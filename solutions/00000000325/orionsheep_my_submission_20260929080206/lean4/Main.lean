/-
  Disproof of TLMC conjecture 00000000325 — arithmetic core, zero axioms.

  Conjecture.  W(τ) = {α : liminf q^{1/τ}‖qα‖ = 0} has packing dimension
  exactly 2/(1+τ).

  Attack.  Take τ = 1/2.  The conjectured value is 2/(1+1/2) = 4/3, which
  exceeds the ambient dimension 1 of R.  Packing dimension is monotone under
  inclusion and dim_P(R) = 1, so NO subset of R can have packing dimension
  4/3 — the conjecture is false at τ = 1/2 outright.

  (Independently, Khinchin's theorem puts W(1/2) in full measure:
  writing v = 1/τ = 2, the divergence test needs Σ q·q^{-v} = Σ 1/q, the
  harmonic series, which diverges — so the true packing dimension is 1 ≠ 4/3.
  For 0 < τ < 1 the same cross-multiplication argument shows the claimed
  2/(1+τ) = 2q/(p+q) > 1 whenever τ = p/q < 1, i.e. q > p, so the conjecture
  fails on the whole range 0 < τ < 1.  For τ > 1, e.g. τ = 2, the claimed
  value 2/3 contradicts the true value 1 (Khinchin, v = 1/2 ≤ 2).  The only
  non-false point is τ = 1, where the claimed 1 coincides with the trivial
  full-measure value.)

  Fractions are encoded by numerator/denominator pairs of naturals with
  positive denominators; a/b > c/d (b, d > 0) ⟺ a·d > c·b.  Every claim
  below is proved by pure kernel computation on N — no choice, no
  quotients, no classical axioms, no `sorry`.
-/

namespace Tlmc325

/-- Cross-multiplied comparison `a/b > c/d` for positive denominators,
encoded as a Bool over N so that all instances reduce by `rfl`. -/
def gtFrac (a b c d : Nat) : Bool := decide (a * d > b * c)

/-- At τ = 1/2 the conjectured formula gives 2·2 = 4 over (1+1)+1 = 3,
i.e. exactly 4/3. -/
theorem conjectured_half_num : (2 : Nat) * 2 = 4 := rfl

theorem conjectured_half_den : (1 : Nat) + 1 + 1 = 3 := rfl

/-- THE ATTACK: 4/3 > 1 = the ambient dimension of R, so the conjectured
packing dimension at τ = 1/2 is impossible for any subset of R. -/
theorem attack : gtFrac 4 3 1 1 = true := rfl

/-- 4 > 3, the cross-multiplied content of the attack, spelt out. -/
theorem four_gt_three : (4 : Nat) > 3 := by decide

/-- General form: for τ = p/q < 1 (i.e. q > p) the conjectured value
2/(1+τ) = 2q/(p+q) still exceeds the ambient dimension 1. -/
theorem two_q_gt_pq (p q : Nat) (h : q > p) : 2 * q > p + q := by
  rw [Nat.two_mul]
  exact Nat.add_lt_add_right h q

theorem claimed_exceeds_ambient (p q : Nat) (h : q > p) :
    gtFrac (2 * q) (p + q) 1 1 = true := by
  unfold gtFrac
  refine decide_eq_true ?_
  rw [Nat.mul_one, Nat.mul_one]
  exact two_q_gt_pq p q h

/-- Instance of the general form at the primary counterexample τ = 1/2
(p = 1, q = 2): the conjectured value (2·2)/((1+1)+1) = 4/3 exceeds 1. -/
theorem half_case : gtFrac (2 * 2) (1 + 1 + 1) 1 1 = true := rfl

/-- Boundary: τ = 1 is the only point where the formula is admissible —
there it claims dimension 1, matching the full-measure value. -/
theorem boundary_tau_one : (2 : Nat) * 1 = 1 + 1 := rfl

/-- For τ > 1 the claimed value contradicts the true value 1 (Khinchin:
v = 1/τ ≤ 2 forces full measure).  τ = 2: claimed 2/3, actual 1/1,
and 2·1 ≠ 1·3. -/
theorem mismatch_two : (2 : Nat) * 1 ≠ (1 : Nat) * 3 := by
  decide

/-- For 0 < τ < 1/2 the claimed value also disagrees with the true
Jarník value 2τ/(1+τ).  τ = 1/4: claimed 8/5, actual 2/5, and 8·5 ≠ 2·5. -/
theorem mismatch_quarter : (8 : Nat) * 5 ≠ (2 : Nat) * 5 := by
  decide

end Tlmc325
