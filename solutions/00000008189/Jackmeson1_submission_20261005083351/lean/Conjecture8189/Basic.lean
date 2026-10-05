import Mathlib

/-!
# Conjecture 00000008189: the Poisson(1/2) law contradicts the stated density for index >= 3

Conjecture text: "... the irregularity index of p (the number of zeros) is Poisson(1/2) (a
half-Poisson law); the density of primes with large irregularity index (at least 3) is
e^{-1/2} (1/2)^3/3! ..." (Chinese: `≥3`).

Definitions. The irregularity index `i(p)` of a prime `p` is the number of even `k` with
`2 <= k <= p - 3` and `p ∣ numerator(B_k)` (Mathlib's `bernoulli`; only even `k >= 2` occur, so
the `B_1` sign convention is irrelevant). Densities are relative natural densities among the
primes: `#{p <= X prime, P p} / #{p <= X prime} → d`. "The index is Poisson(1/2)" is read as:
for every `k`, the primes with `i(p) = k` have density `Po(1/2){k} = e^{-1/2} (1/2)^k / k!`, where
`Po(1/2)` is Mathlib's `ProbabilityTheory.poissonMeasure (1/2)`.

Since the classes `i = 0, 1, 2, >= 3` partition the primes, finite additivity forces
`density(i >= 3) = 1 - (1 + 1/2 + 1/8) e^{-1/2}`, which differs from `e^{-1/2}/48` because
`e^{1/2} ≠ 79/48` (indeed `e > 2.7182818283 > (79/48)^2`). The proof uses no property of
Bernoulli numbers. The clause "expected number of counterexamples ... is 0.00" is not
formalized.
-/

open Filter Topology Real

namespace C8189

/-- The irregularity index of `p`: the number of even `k`, `2 <= k <= p - 3`, with
`p ∣ numerator(B_k)`, i.e. the number of irregular pairs `(p, k)`. -/
def irregIndex (p : ℕ) : ℕ :=
  ((Finset.range (p - 2)).filter
    (fun k => Even k ∧ 2 ≤ k ∧ (p : ℤ) ∣ (bernoulli k).num)).card

/-- The primes `p <= X`. -/
def primesUpTo (X : ℕ) : Finset ℕ := (Finset.range (X + 1)).filter Nat.Prime

/-- Relative natural density among the primes of the primes satisfying `P`. -/
def HasPrimeDensity (P : ℕ → Prop) [DecidablePred P] (d : ℝ) : Prop :=
  Tendsto (fun X : ℕ => (((primesUpTo X).filter P).card : ℝ) / ((primesUpTo X).card : ℝ))
    atTop (𝓝 d)

/-- The half-Poisson law: for every `k`, the primes of irregularity index `k` have density
`Po(1/2){k} = e^{-1/2} (1/2)^k / k!` (Mathlib's Poisson measure with rate `1/2`). -/
def HalfPoissonLaw : Prop :=
  ∀ k : ℕ, HasPrimeDensity (fun p => irregIndex p = k)
    ((ProbabilityTheory.poissonMeasure (1/2)).real {k})

/-- The clause "the density of primes with irregularity index at least 3 is
`e^{-1/2} (1/2)^3 / 3!`". -/
def LargeIndexClause : Prop :=
  HasPrimeDensity (fun p => 3 ≤ irregIndex p) (exp (-(1/2)) * (1/2) ^ 3 / (Nat.factorial 3))

/-- The first clause: irregular primes (index `>= 1`) have density `1 - e^{-1/2}`. -/
def IrregularClause : Prop := HasPrimeDensity (fun p => 1 ≤ irregIndex p) (1 - exp (-(1/2)))

/-- Finite additivity of counts over the partition `f = 0, 1, 2, >= 3`. -/
theorem card_partition (s : Finset ℕ) (f : ℕ → ℕ) :
    (s.filter (fun p => f p = 0)).card + (s.filter (fun p => f p = 1)).card +
      (s.filter (fun p => f p = 2)).card + (s.filter (fun p => 3 ≤ f p)).card = s.card := by
  rw [Finset.card_eq_sum_ones s]
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> omega

/-- Arithmetic core (valid for any finitely additive density): if densities `d0, d1, d2`
agree with Poisson(1/2) and `d0 + d1 + d2 + d3 = 1`, then `d3 ≠ e^{-1/2} (1/2)^3 / 3!`. -/
theorem tail_ne (d3 : ℝ)
    (h : (ProbabilityTheory.poissonMeasure (1/2)).real {0} +
      (ProbabilityTheory.poissonMeasure (1/2)).real {1} +
      (ProbabilityTheory.poissonMeasure (1/2)).real {2} + d3 = 1) :
    d3 ≠ exp (-(1/2)) * (1/2) ^ 3 / (Nat.factorial 3) := by
  intro h3
  simp only [ProbabilityTheory.poissonMeasure_real_singleton, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat, Nat.factorial, Nat.cast_one, Nat.succ_eq_add_one] at h h3
  set t := exp (-(1/2) : ℝ) with ht
  have h79 : t = 48 / 79 := by rw [h3] at h; push_cast at h; linarith
  have hsq : exp 1 * (t * t) = 1 := by
    rw [ht, ← exp_add, ← exp_add]; norm_num
  rw [h79] at hsq
  have := exp_one_gt_d9
  nlinarith

/-- The relative-density ratios of the four index classes add up to `1` for `X >= 2`. -/
theorem ratio_sum (X : ℕ) (hX : 2 ≤ X) :
    let r := fun (P : ℕ → Prop) [DecidablePred P] =>
      (((primesUpTo X).filter P).card : ℝ) / ((primesUpTo X).card : ℝ)
    r (fun p => irregIndex p = 0) + r (fun p => irregIndex p = 1) +
      r (fun p => irregIndex p = 2) + r (fun p => 3 ≤ irregIndex p) = 1 := by
  intro r
  have hpos : (0 : ℝ) < (primesUpTo X).card := by
    have : 2 ∈ primesUpTo X :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
    exact_mod_cast Finset.card_pos.mpr ⟨2, this⟩
  have hc := card_partition (primesUpTo X) irregIndex
  simp only [r, ← add_div]
  rw [div_eq_one_iff_eq hpos.ne']
  exact_mod_cast hc

/-- Main theorem: the half-Poisson law and the stated density of primes with irregularity
index at least 3 cannot both hold. -/
theorem halfPoisson_contradicts_largeIndex : ¬ (HalfPoissonLaw ∧ LargeIndexClause) := by
  rintro ⟨hP, hL⟩
  have hsum := ((hP 0).add (hP 1)).add (hP 2) |>.add hL
  have hone : Tendsto (fun X : ℕ =>
      (((primesUpTo X).filter (fun p => irregIndex p = 0)).card : ℝ) / (primesUpTo X).card +
      (((primesUpTo X).filter (fun p => irregIndex p = 1)).card : ℝ) / (primesUpTo X).card +
      (((primesUpTo X).filter (fun p => irregIndex p = 2)).card : ℝ) / (primesUpTo X).card +
      (((primesUpTo X).filter (fun p => 3 ≤ irregIndex p)).card : ℝ) / (primesUpTo X).card)
      atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨2, fun X hX => (ratio_sum X hX).symm⟩)
  exact tail_ne _ (tendsto_nhds_unique hsum hone) rfl

/-- Capstone: the conjunction of the three mathematical clauses of the conjecture (density
`1 - e^{-1/2}` of irregular primes, the half-Poisson law, and the `>= 3` density) is false. -/
theorem conjecture_8189_false : ¬ (IrregularClause ∧ HalfPoissonLaw ∧ LargeIndexClause) :=
  fun h => halfPoisson_contradicts_largeIndex h.2

end C8189
