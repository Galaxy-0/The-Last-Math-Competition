import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Conjecture 00000001066: failure of exact attainment

The conjecture's `p^(1/2)` is interpreted as the nonnegative real square root.
The phrase "is attained" means exact equality, without rounding or an
asymptotic qualifier. The main statement below includes both the proposed
upper bound and exact attainment for each prime. A separate statement covers
the weaker reading that exact attainment occurs for some prime.

For prime `p`, `ZMod p` is the usual prime field. Sidon differences below are
ordered and exclude diagonal pairs. The obstruction to exact attainment is
stronger than required: no finite subset has cardinality exactly `sqrt p`,
whether or not it is Sidon.
-/

namespace Conjecture1066

/-- The difference map is injective on ordered, nondiagonal pairs in `B`. -/
def IsSidon {p : ℕ} (B : Finset (ZMod p)) : Prop :=
  ∀ ⦃a b c d : ZMod p⦄,
    a ∈ B → b ∈ B → c ∈ B → d ∈ B →
    a ≠ b → c ≠ d → a - b = c - d → a = c ∧ b = d

/-- The upper-bound clause, with cardinality and `p` cast to the reals. -/
def UpperBound (p : ℕ) : Prop :=
  ∀ B : Finset (ZMod p),
    IsSidon B → (B.card : ℝ) ≤ Real.sqrt (p : ℝ) + 1

/-- Literal exact attainment of the displayed real square root. -/
def ExactAttainment (p : ℕ) : Prop :=
  ∃ B : Finset (ZMod p),
    IsSidon B ∧ (B.card : ℝ) = Real.sqrt (p : ℝ)

/-- The conjecture under its universally quantified prime reading. -/
def UniversalConjecture : Prop :=
  ∀ p : ℕ, p.Prime → UpperBound p ∧ ExactAttainment p

/-- The weaker reading: the bound for all primes and attainment for some prime. -/
def ExistentialPrimeConjecture : Prop :=
  (∀ p : ℕ, p.Prime → UpperBound p) ∧
    ∃ p : ℕ, p.Prime ∧ ExactAttainment p

/-- A prime's real square root cannot equal any natural number. -/
theorem nat_cast_ne_sqrt_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (n : ℝ) ≠ Real.sqrt (p : ℝ) := by
  intro h
  have hreal : (n : ℝ) ^ 2 = (p : ℝ) := by
    rw [h]
    exact Real.sq_sqrt (Nat.cast_nonneg p)
  have hnat : n ^ 2 = p := by
    exact_mod_cast hreal
  have hprime : (n ^ 2).Prime := hnat.symm ▸ hp
  exact Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) hprime

/-- The cardinality obstruction applies to every finite subset of the prime field. -/
theorem cardinality_ne_sqrt_prime {p : ℕ} (hp : p.Prime)
    (B : Finset (ZMod p)) : (B.card : ℝ) ≠ Real.sqrt (p : ℝ) :=
  nat_cast_ne_sqrt_prime hp B.card

/-- Exact attainment fails for every prime, even before imposing the Sidon condition. -/
theorem no_exact_attainment {p : ℕ} (hp : p.Prime) : ¬ ExactAttainment p := by
  rintro ⟨B, _hSidon, hcard⟩
  exact cardinality_ne_sqrt_prime hp B hcard

/-- For every prime, the bound-and-exact-attainment conjunction is false. -/
theorem no_prime_conjunction {p : ℕ} (hp : p.Prime) :
    ¬ (UpperBound p ∧ ExactAttainment p) := by
  intro h
  exact no_exact_attainment hp h.2

/-- Negation of the complete universal reading of the written conjecture. -/
theorem universal_conjecture_false : ¬ UniversalConjecture := by
  intro h
  exact no_prime_conjunction Nat.prime_two (h 2 Nat.prime_two)

/-- No prime realizes even the existential exact-attainment clause. -/
theorem no_prime_exact_attainment :
    ¬ ∃ p : ℕ, p.Prime ∧ ExactAttainment p := by
  rintro ⟨p, hp, h⟩
  exact no_exact_attainment hp h

/-- Negation of the weaker existential-prime reading of the complete conjecture. -/
theorem existential_prime_conjecture_false : ¬ ExistentialPrimeConjecture := by
  intro h
  exact no_prime_exact_attainment h.2

end Conjecture1066
