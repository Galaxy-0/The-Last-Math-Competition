import Mathlib

/-!
# Conjecture 00000000741 is false

Conjecture 00000000741 reads:

> Definition: Let n(p) denote the number of periodic points (counting distinct periodic orbits) of
> f(x) = x² on Z_p. Conjecture: For a density-one set of primes, n(p) = 3 (the fixed points 0, 1
> and −1); the exceptional primes (with extra periodic points) have count ≤ x^{1/2+ε}, and all
> exceptions are characterized by p² − 1 containing large power factors.

(Chinese: n(p) counts the distinct points on periodic orbits, 计相异周期轨道点.)

`n(p)` is the number of periodic points of the squaring map, i.e. the cardinality of Mathlib's
`Function.periodicPts (fun x => x ^ 2)`, the set of `x` with `f^[k] x = x` for some `k > 0`.
We take `Z_p = ZMod p` (`n`) and also the `p`-adic integers `ℤ_[p]` (`nPadic`).

The conjecture is a conjunction whose first clause is `DensityOneClause`: there is a set `S` of
relative density one among the primes (`#{p < N : p prime, p ∈ S} / #{p < N : p prime} → 1`) with
`n(p) = 3` for every prime `p ∈ S`. We refute it, so the conjunction with any further clauses `Q`
is false.

Key fact (`card_periodicPts_ne_three`): in every integral domain the squaring map never has exactly
three periodic points. If `P = {0, 1, x}`, then `x` is a unit whose inverse is periodic too, so
`x⁻¹ = x`, `x = -1`, and `-1` is periodic only when `-1 = 1`. Hence `n(p) ≠ 3` for every prime `p`,
in `ZMod p` and in `ℤ_[p]`, and no set of primes on which `n(p) = 3` can have density one. We also
prove that the fixed points are exactly `0` and `1`, and that `-1` is not periodic for odd `p`.
-/

namespace Conjecture741

open Function Filter Topology

/-- The number of periodic points of `x ↦ x ^ 2` on `R`. -/
noncomputable def numPeriodic (R : Type*) [Monoid R] : ℕ :=
  Nat.card (periodicPts (fun x : R => x ^ 2))

/-- `n(p)` on `Z/pZ`. -/
noncomputable def n (p : ℕ) : ℕ := numPeriodic (ZMod p)

/-- `n(p)` on the `p`-adic integers `ℤ_[p]` (defined for primes `p`; `0` otherwise). -/
noncomputable def nPadic (p : ℕ) : ℕ :=
  if h : p.Prime then (haveI : Fact p.Prime := ⟨h⟩; numPeriodic ℤ_[p]) else 0

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
lemma iterate_sq (k : ℕ) (x : R) : (fun y : R => y ^ 2)^[k] x = x ^ 2 ^ k := by
  rw [pow_iterate]

omit [IsDomain R] in
lemma mem_periodicPts_sq {x : R} :
    x ∈ periodicPts (fun y : R => y ^ 2) ↔ ∃ k > 0, x ^ 2 ^ k = x := by
  rw [mem_periodicPts]
  simp only [IsPeriodicPt, IsFixedPt, iterate_sq]

omit [IsDomain R] in
lemma zero_mem_periodicPts : (0 : R) ∈ periodicPts (fun y : R => y ^ 2) :=
  mem_periodicPts_sq.mpr ⟨1, one_pos, by simp⟩

omit [IsDomain R] in
lemma one_mem_periodicPts : (1 : R) ∈ periodicPts (fun y : R => y ^ 2) :=
  mem_periodicPts_sq.mpr ⟨1, one_pos, by simp⟩

/-- The fixed points of `x ↦ x ^ 2` are exactly `0` and `1`. -/
theorem fixedPoints_sq : fixedPoints (fun y : R => y ^ 2) = {0, 1} := by
  ext x
  simp only [mem_fixedPoints, IsFixedPt, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have : x * (x - 1) = 0 := by rw [mul_sub, ← sq, h]; ring
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · rintro (rfl | rfl) <;> simp

omit [IsDomain R] in
/-- `-1` is a periodic point only when `-1 = 1`. -/
theorem neg_one_mem_periodicPts_iff :
    (-1 : R) ∈ periodicPts (fun y : R => y ^ 2) ↔ (-1 : R) = 1 := by
  rw [mem_periodicPts_sq]
  constructor
  · rintro ⟨k, hk, h⟩
    have heven : Even (2 ^ k) := (Nat.even_pow' hk.ne').mpr even_two
    rw [heven.neg_one_pow] at h
    exact h.symm
  · intro h
    exact ⟨1, one_pos, by rw [h]; simp⟩

/-- The inverse of a nonzero periodic point is a periodic point. -/
lemma exists_inv_periodic {x : R} (hx : x ∈ periodicPts (fun y : R => y ^ 2)) (hx0 : x ≠ 0) :
    ∃ y, x * y = 1 ∧ y ∈ periodicPts (fun y : R => y ^ 2) := by
  obtain ⟨k, hk, hxk⟩ := mem_periodicPts_sq.mp hx
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  -- `x ^ (2^k - 1) = 1` by cancelling `x`
  have hunit : x ^ (2 ^ k - 1) = 1 := by
    have h' : x * x ^ (2 ^ k - 1) = x * 1 := by
      rw [mul_one, ← pow_succ', Nat.sub_add_cancel (by omega), hxk]
    exact mul_left_cancel₀ hx0 h'
  refine ⟨x ^ (2 ^ k - 2), ?_, mem_periodicPts_sq.mpr ⟨k, hk, ?_⟩⟩
  · rw [← pow_succ', show 2 ^ k - 2 + 1 = 2 ^ k - 1 by omega, hunit]
  · set y := x ^ (2 ^ k - 2) with hy
    have hxy : x * y = 1 := by
      rw [hy, ← pow_succ', show 2 ^ k - 2 + 1 = 2 ^ k - 1 by omega, hunit]
    have h' : x * y ^ 2 ^ k = x * y := by
      calc x * y ^ 2 ^ k = x ^ 2 ^ k * y ^ 2 ^ k := by rw [hxk]
        _ = (x * y) ^ 2 ^ k := (mul_pow x y _).symm
        _ = x * y := by rw [hxy, one_pow]
    exact mul_left_cancel₀ hx0 h'

/-- **Key lemma.** In an integral domain, `x ↦ x ^ 2` never has exactly three periodic points. -/
theorem card_periodicPts_ne_three : numPeriodic R ≠ 3 := by
  intro h
  set P := periodicPts (fun y : R => y ^ 2) with hP
  have hcard : P.ncard = 3 := h
  have hfin : P.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have h01 : ({0, 1} : Set R) ⊆ P := by
    intro z hz
    rcases hz with rfl | rfl
    · exact zero_mem_periodicPts
    · exact one_mem_periodicPts
  have hlt : ({0, 1} : Set R).ncard < P.ncard := by
    rw [Set.ncard_pair zero_ne_one, hcard]; norm_num
  obtain ⟨x, hxP, hx01⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx01
  obtain ⟨hx0, hx1⟩ := hx01
  -- `P = {0, 1, x}`
  have hPeq : ({0, 1, x} : Set R) = P := by
    apply Set.eq_of_subset_of_ncard_le _ _ hfin
    · intro z hz
      rcases hz with rfl | rfl | rfl
      · exact zero_mem_periodicPts
      · exact one_mem_periodicPts
      · exact hxP
    · rw [hcard, Set.ncard_eq_three.mpr ⟨0, 1, x, zero_ne_one, Ne.symm hx0, Ne.symm hx1, rfl⟩]
  obtain ⟨y, hxy, hyP'⟩ := exists_inv_periodic hxP hx0
  have hyP : y ∈ P := hyP'
  rw [← hPeq] at hyP
  have hyx : y = x := by
    rcases hyP with rfl | rfl | rfl
    · simp at hxy
    · exact absurd (by simpa using hxy) hx1
    · rfl
  subst hyx
  -- `y * y = 1`, so `y = -1`
  rcases mul_self_eq_one_iff.mp hxy with h1 | hm1
  · exact hx1 h1
  · have := neg_one_mem_periodicPts_iff.mp (hm1 ▸ hxP)
    exact hx1 (hm1.trans this)

end Domain

/-- `n(p) ≠ 3` for every prime `p` (`Z/pZ`). -/
theorem n_ne_three (p : ℕ) (hp : p.Prime) : n p ≠ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  exact card_periodicPts_ne_three

/-- `n(p) ≠ 3` for every prime `p` (`p`-adic integers). -/
theorem nPadic_ne_three (p : ℕ) (hp : p.Prime) : nPadic p ≠ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [nPadic, dif_pos hp]
  exact card_periodicPts_ne_three

/-- For odd primes `-1` is not a periodic point of `x ↦ x ^ 2` on `Z/pZ`. -/
theorem neg_one_not_periodic (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (-1 : ZMod p) ∉ periodicPts (fun y : ZMod p => y ^ 2) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  rw [neg_one_mem_periodicPts_iff]
  exact ZMod.neg_one_ne_one

/-! ## Density -/

/-- `#{p < N : p prime, p ∈ S} / #{p < N : p prime}`. -/
noncomputable def primeRatio (S : Set ℕ) (N : ℕ) : ℝ :=
  ({p | p < N ∧ p.Prime ∧ p ∈ S} : Set ℕ).ncard / (Nat.primeCounting' N : ℝ)

/-- `S` has relative density one among the primes. -/
def HasPrimeDensityOne (S : Set ℕ) : Prop := Tendsto (primeRatio S) atTop (𝓝 1)

/-- First clause of the conjecture for a count function `m`: for a density-one set of primes,
`m(p) = 3`. -/
def DensityOneClause (m : ℕ → ℕ) : Prop :=
  ∃ S : Set ℕ, HasPrimeDensityOne S ∧ ∀ p ∈ S, p.Prime → m p = 3

/-- If `m(p) ≠ 3` for every prime, the density-one clause fails. -/
theorem not_densityOneClause {m : ℕ → ℕ} (hm : ∀ p, p.Prime → m p ≠ 3) :
    ¬ DensityOneClause m := by
  rintro ⟨S, hS, hS3⟩
  have hzero : primeRatio S = fun _ => 0 := by
    funext N
    have : ({p | p < N ∧ p.Prime ∧ p ∈ S} : Set ℕ) = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hp hpS
      exact hm p hp (hS3 p hpS hp)
    simp [primeRatio, this]
  rw [HasPrimeDensityOne, hzero] at hS
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hS)

/-- **Conjecture 00000000741 is false.** For every formalization `Q` of its remaining clauses, the
conjunction fails, both for `Z_p = Z/pZ` and for the `p`-adic integers; moreover `n(p) ≠ 3` for
every prime, the fixed points of `x ↦ x ^ 2` on `Z/pZ` are exactly `0, 1`, and `-1` is not periodic
for odd `p`. -/
theorem conjecture_00000000741_false (Q : Prop) :
    ¬ (DensityOneClause n ∧ Q) ∧ ¬ (DensityOneClause nPadic ∧ Q) ∧
    (∀ p, p.Prime → n p ≠ 3) ∧
    (∀ p, p.Prime → fixedPoints (fun y : ZMod p => y ^ 2) = {0, 1}) ∧
    (∀ p, p.Prime → p ≠ 2 → (-1 : ZMod p) ∉ periodicPts (fun y : ZMod p => y ^ 2)) :=
  ⟨fun h => not_densityOneClause n_ne_three h.1, fun h => not_densityOneClause nPadic_ne_three h.1,
    n_ne_three, fun p hp => by have : Fact p.Prime := ⟨hp⟩; exact fixedPoints_sq,
    neg_one_not_periodic⟩

end Conjecture741
