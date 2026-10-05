import Mathlib

/-!
# Conjecture 00000000027: `r₃(N) = N · exp(-O(√(log N)))`

`r₃(N)` is the maximal size of a subset of `[N] = {1, …, N}` containing no three-term arithmetic
progression `a, a + d, a + 2d` with common difference `d ≥ 1`.

Read literally, the statement says that `r₃(N) = N · exp(-g(N))` for some function
`g(N) = O(√(log N))`.  Since trivially `r₃(N) ≤ N`, this is Behrend's (1946) lower bound
`r₃(N) ≥ N · exp(-C √(log N))`.  Mathlib already contains Behrend's construction in the explicit
form `Behrend.roth_lower_bound : N * exp (-4 * √(log N)) ≤ rothNumberNat N` (by Yaël Dillies and
Bhavik Mehta, file `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean`).  This file

* defines `r₃(N)` from scratch, as a maximum over subsets of `{1, …, N}` with an explicit
  "no three-term AP" predicate;
* proves that it agrees with Mathlib's `rothNumberNat N` (the `{0, …, N-1}` convention), so the
  value does not depend on whether `[N]` starts at `0` or at `1`;
* proves `r₃(N) = N · exp(-g(N))` with `0 ≤ g(N) ≤ 4 √(log N)` for every `N ≥ 1`, and hence the
  asymptotic statement `g =O[atTop] √(log N)`.

The matching upper bound `r₃(N) ≤ N · exp(-c √(log N))` (sharpness of Behrend's bound) is *not*
claimed or proved here; the conjecture's one-sided `-O(·)` notation does not assert it.
-/

open Real Filter Finset Asymptotics

namespace C27

/-- `A` contains a (non-trivial) three-term arithmetic progression `a, a + d, a + 2d`,
with common difference `d ≥ 1`. -/
def HasThreeAP (A : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A

open Classical in
/-- `r₃(N)`: the maximal size of a subset of `[N] = {1, …, N}` with no three-term arithmetic
progression.  (The empty set always qualifies, so the maximum is over a nonempty family.) -/
noncomputable def r3 (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter (fun A => ¬ HasThreeAP A)).sup Finset.card

/-- Our "no three-term AP" predicate is exactly Mathlib's `ThreeAPFree`. -/
theorem not_hasThreeAP_iff (A : Finset ℕ) : ¬ HasThreeAP A ↔ ThreeAPFree (A : Set ℕ) := by
  constructor
  · intro h a ha b hb c hc habc
    by_contra hab
    apply h
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · refine ⟨a, b - a, by omega, ha, ?_, ?_⟩
      · rwa [Nat.add_sub_cancel' hlt.le]
      · have : a + 2 * (b - a) = c := by omega
        rwa [this]
    · refine ⟨c, b - c, by omega, hc, ?_, ?_⟩
      · have : c + (b - c) = b := by omega
        rwa [this]
      · have : c + 2 * (b - c) = a := by omega
        rwa [this]
  · rintro h ⟨a, d, hd, ha, had, ha2d⟩
    have := h (mem_coe.2 ha) (mem_coe.2 had) (mem_coe.2 ha2d) (by ring)
    omega

/-- `r₃(N)` equals Mathlib's additive Roth number of `{1, …, N}`. -/
theorem r3_eq_addRothNumber (N : ℕ) : r3 N = addRothNumber (Icc 1 N) := by
  classical
  apply le_antisymm
  · unfold r3
    refine Finset.sup_le fun A hA => ?_
    rw [mem_filter, mem_powerset] at hA
    exact ((not_hasThreeAP_iff A).1 (by convert hA.2)).le_addRothNumber hA.1
  · obtain ⟨t, ht, hcard, hfree⟩ := addRothNumber_spec (Icc 1 N)
    rw [← hcard]
    unfold r3
    apply Finset.le_sup
    rw [mem_filter, mem_powerset]
    exact ⟨ht, (not_hasThreeAP_iff t).2 hfree⟩

/-- `r₃(N)` (on `{1, …, N}`) equals Mathlib's `rothNumberNat N` (on `{0, …, N - 1}`). -/
theorem r3_eq_rothNumberNat (N : ℕ) : r3 N = rothNumberNat N := by
  rw [r3_eq_addRothNumber, ← Finset.Ico_add_one_right_eq_Icc, addRothNumber_Ico,
    Nat.add_sub_cancel]

/-- Trivial upper bound: `r₃(N) ≤ N`. -/
theorem r3_le (N : ℕ) : r3 N ≤ N := r3_eq_rothNumberNat N ▸ rothNumberNat_le N

/-- Behrend's lower bound, from Mathlib's `Behrend.roth_lower_bound`:
`N · exp(-4 √(log N)) ≤ r₃(N)` for every `N`. -/
theorem behrend_r3 (N : ℕ) : (N : ℝ) * exp (-4 * √(log N)) ≤ r3 N := by
  rw [r3_eq_rothNumberNat]; exact Behrend.roth_lower_bound

theorem r3_pos {N : ℕ} (hN : 1 ≤ N) : 0 < (r3 N : ℝ) :=
  lt_of_lt_of_le (mul_pos (by exact_mod_cast hN) (exp_pos _)) (behrend_r3 N)

/-- The exponent `g(N) = log (N / r₃(N))`. -/
noncomputable def g (N : ℕ) : ℝ := log ((N : ℝ) / r3 N)

/-- **Explicit form.** For every `N ≥ 1`, `r₃(N) = N · exp(-g(N))` with
`0 ≤ g(N) ≤ 4 √(log N)`. -/
theorem r3_explicit {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ g N ∧ g N ≤ 4 * √(log N) ∧ (r3 N : ℝ) = N * exp (-g N) := by
  have hr := r3_pos hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 < (N : ℝ) / r3 N := div_pos hNpos hr
  refine ⟨?_, ?_, ?_⟩
  · apply log_nonneg
    rw [le_div_iff₀ hr, one_mul]; exact_mod_cast r3_le N
  · unfold g
    rw [log_le_iff_le_exp hq, div_le_iff₀ hr]
    have h := behrend_r3 N
    have h4 : (N : ℝ) = N * exp (-4 * √(log N)) * exp (4 * √(log N)) := by
      rw [mul_assoc, ← exp_add]; simp
    have := mul_le_mul_of_nonneg_right h (exp_pos (4 * √(log N))).le
    calc (N : ℝ) = N * exp (-4 * √(log N)) * exp (4 * √(log N)) := h4
      _ ≤ r3 N * exp (4 * √(log N)) := this
      _ = _ := mul_comm _ _
  · unfold g
    rw [exp_neg, exp_log hq]
    field_simp

/-- **Main theorem (conjecture 00000000027).** There is a function `g` with
`g(N) = O(√(log N))` (in fact `0 ≤ g(N) ≤ 4 √(log N)` for all `N ≥ 1`) such that
`r₃(N) = N · exp(-g(N))` for all `N ≥ 1`. -/
theorem conjecture_27 :
    ∃ g : ℕ → ℝ, (g =O[atTop] fun N : ℕ => √(log N)) ∧
      (∀ N, 1 ≤ N → 0 ≤ g N ∧ g N ≤ 4 * √(log N)) ∧
      ∀ N, 1 ≤ N → (r3 N : ℝ) = N * exp (-g N) := by
  refine ⟨g, ?_, fun N hN => ⟨(r3_explicit hN).1, (r3_explicit hN).2.1⟩,
    fun N hN => (r3_explicit hN).2.2⟩
  refine IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨h0, h4, -⟩ := r3_explicit hN
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (sqrt_nonneg _)]
  exact h4

/-- Equivalent two-sided form: `N · exp(-4 √(log N)) ≤ r₃(N) ≤ N` for every `N`. -/
theorem r3_two_sided (N : ℕ) :
    (N : ℝ) * exp (-4 * √(log N)) ≤ r3 N ∧ (r3 N : ℝ) ≤ N :=
  ⟨behrend_r3 N, by exact_mod_cast r3_le N⟩

end C27
