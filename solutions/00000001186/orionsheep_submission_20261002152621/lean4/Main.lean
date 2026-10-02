/-
  Disproof of TLMC conjecture 00000001186.

  The conjecture asserts m(4) = 504 (PSL_2(8)) where m(k) is the minimal
  order of a nonabelian simple group with exactly k distinct prime factors,
  and that m(k)/m(k-1) <= 4 for all k, with equality at k = 4.

  Refutation from the conjecture's OWN numeric claims (no external facts):

    m(3) = 60 and m(4) = 504 are asserted by the conjecture itself, so its
    ratio clause demands 504 <= 4 * 60 = 240 — false. Moreover 504 > 240
    means the ratio is 8.4, so the "equality at k = 4" clause fails too.

  Independently (documented in README/tex, factorization certified here):
    504 = 2^3 * 3^2 * 7 has exactly THREE distinct prime factors, so 504
    cannot witness the definition of m(4) ("exactly 4 distinct prime
    factors") — the conjecture's own witness does not meet its definition.

  Every theorem below is axiom-free (verified by #print axioms).
-/

namespace Tlmc1186

/-- The prime factorization of 504: 2^3 * 3^2 * 7 — three distinct primes. -/
theorem fact504 : (504 : Nat) = 2^3 * 3^2 * 7 := rfl

/-- The three distinct prime factors, multiplied back, give 504. -/
theorem factors_product : (2 : Nat) * 2 * 2 * 3 * 3 * 7 = 504 := by decide

/-- Refutation: the conjecture's own values violate its ratio clause.
    504 > 4 * 60 = 240, so m(4)/m(3) > 4 and equality at k = 4 fails. -/
theorem ratio_violation : ¬ ((504 : Nat) ≤ 4 * 60) := by decide

/-- The ratio is 504/60 = 42/5 = 8.4. -/
theorem ratio_numerator : (504 : Nat) = 42 * 12 := by decide

/-- Even the weakened bound m(4) <= 3 * m(3) = 180 fails. -/
theorem stronger_violation : ¬ ((504 : Nat) ≤ 3 * 60) := by decide

end Tlmc1186
