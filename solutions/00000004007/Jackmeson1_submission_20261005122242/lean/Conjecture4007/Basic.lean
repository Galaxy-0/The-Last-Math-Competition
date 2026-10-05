import Mathlib

/-!
# Conjecture 00000004007: the "optimal subadditivity" of the p-variation is false

The conjecture defines the p-variation of a path `X` as the p-th root of the supremum, over
partitions, of the sum of the p-th powers of the increments, and claims

  `‖X + Y‖ ≤ (‖X‖^q + ‖Y‖^q)^(1/q)`,  `q` the conjugate exponent of `p`.

We define the p-variation on an interval `[a, b]` literally (partitions
`a = t₀ < t₁ < ... < tₙ = b`, values in `ℝ≥0∞` so that the supremum always exists), prove that
it is positively homogeneous of degree one, and deduce that the inequality fails at `Y = X`
for every path `X` with finite nonzero p-variation, for every `p > 1` (`q = p/(p-1)`, Mathlib's
`Real.HolderConjugate p q`) and also for `p = 1` with `q = ∞` (right side `max ‖X‖ ‖Y‖`).
The path `X t = t` on `[0, 1]` has p-variation exactly `1` for every `p ≥ 1`, so the
counterexample is a genuine continuous path. The same paths also refute the variant in which
`‖X‖` is the supremum itself, without the p-th root (`raw_version_false`), and the variant in
which `X + Y` is read as the concatenation of two paths (`concat_version_false`).
-/

open scoped ENNReal
open Finset

namespace Tlmc4007

/-- A partition of `[a, b]`: points `a = t 0 < t 1 < ... < t n = b`. -/
structure Partition (a b : ℝ) where
  n : ℕ
  t : Fin (n + 1) → ℝ
  strictMono : StrictMono t
  first : t 0 = a
  last : t (Fin.last n) = b

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `∑ᵢ ‖X(tᵢ₊₁) - X(tᵢ)‖^p` along a partition `π`. -/
noncomputable def incrSum (p : ℝ) (X : ℝ → E) {a b : ℝ} (π : Partition a b) : ℝ≥0∞ :=
  ∑ i : Fin π.n, ‖X (π.t i.succ) - X (π.t i.castSucc)‖ₑ ^ p

/-- The p-variation of `X` on `[a, b]`: the p-th root of the supremum over partitions of the
sum of the p-th powers of the increments. -/
noncomputable def pVar (p a b : ℝ) (X : ℝ → E) : ℝ≥0∞ :=
  (⨆ π : Partition a b, incrSum p X π) ^ (1 / p)

/-- Scaling a path scales each increment sum by `‖c‖^p`. -/
lemma incrSum_smul {p : ℝ} (hp : 0 ≤ p) (c : ℝ) (X : ℝ → E) {a b : ℝ} (π : Partition a b) :
    incrSum p (fun s => c • X s) π = ‖c‖ₑ ^ p * incrSum p X π := by
  unfold incrSum
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← smul_sub, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hp]

/-- **Homogeneity.** For `p > 0` the p-variation is positively homogeneous of degree one:
`pVar (c • X) = |c| · pVar X`. -/
theorem pVar_smul {p : ℝ} (hp : 0 < p) (c : ℝ) (X : ℝ → E) (a b : ℝ) :
    pVar p a b (fun s => c • X s) = ‖c‖ₑ * pVar p a b X := by
  unfold pVar
  simp_rw [incrSum_smul hp.le]
  rw [← ENNReal.mul_iSup, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- `pVar (X + X) = 2 · pVar X`. -/
theorem pVar_add_self {p : ℝ} (hp : 0 < p) (X : ℝ → E) (a b : ℝ) :
    pVar p a b (fun s => X s + X s) = 2 * pVar p a b X := by
  have h := pVar_smul hp (2 : ℝ) X a b
  simp only [two_smul] at h
  rw [h]
  congr 1
  simp [Real.enorm_eq_ofReal_abs]

/-- **The inequality fails at `Y = X`** (case `1 < p < ∞`, `q = p/(p-1)`): for every path with
finite nonzero p-variation, `‖X + X‖ > (‖X‖^q + ‖X‖^q)^(1/q)`. -/
theorem fails_at_diagonal {p q : ℝ} (hpq : p.HolderConjugate q) (X : ℝ → E) (a b : ℝ)
    (h0 : pVar p a b X ≠ 0) (htop : pVar p a b X ≠ ∞) :
    (pVar p a b X ^ q + pVar p a b X ^ q) ^ (1 / q) < pVar p a b (fun s => X s + X s) := by
  have hp : 0 < p := hpq.pos
  have hq : 1 < q := hpq.symm.lt
  rw [pVar_add_self hp]
  set V := pVar p a b X
  rw [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ (by have := hpq.symm.pos; positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel (by linarith), ENNReal.rpow_one]
  have h2 : (2 : ℝ≥0∞) ^ (1 / q) < 2 := by
    calc (2 : ℝ≥0∞) ^ (1 / q) < 2 ^ (1 : ℝ) :=
          ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
            (by rw [div_lt_one (by linarith)]; exact hq)
      _ = 2 := ENNReal.rpow_one 2
  exact ENNReal.mul_lt_mul_left h0 htop h2

/-- **The inequality fails at `Y = X`** (case `p = 1`, `q = ∞`, right side `max ‖X‖ ‖Y‖`). -/
theorem fails_at_diagonal_one (X : ℝ → E) (a b : ℝ)
    (h0 : pVar 1 a b X ≠ 0) (htop : pVar 1 a b X ≠ ∞) :
    max (pVar 1 a b X) (pVar 1 a b X) < pVar 1 a b (fun s => X s + X s) := by
  rw [pVar_add_self one_pos, max_self]
  rw [two_mul]
  exact ENNReal.lt_add_right htop h0

/-! ## A non-degenerate path: `X t = t` on `[0, 1]` has p-variation `1` for `p ≥ 1`. -/

/-- Telescoping along a finite sequence. -/
lemma sum_succ_sub : ∀ (n : ℕ) (g : Fin (n + 1) → ℝ),
    ∑ i : Fin n, (g i.succ - g i.castSucc) = g (Fin.last n) - g 0
  | 0, g => by simp
  | n + 1, g => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc]
    rw [sum_succ_sub n (fun j => g j.castSucc)]
    simp only [Fin.succ_last, Fin.castSucc_zero]
    ring

/-- The two-point partition `a < b` of `[a, b]`. -/
def twoPoint (a b : ℝ) (h : a < b) : Partition a b where
  n := 1
  t := ![a, b]
  strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  first := rfl
  last := rfl

lemma incrSum_twoPoint (p : ℝ) {a b : ℝ} (h : a < b) :
    incrSum p (fun t : ℝ => t) (twoPoint a b h) = ENNReal.ofReal (b - a) ^ p := by
  show ∑ i : Fin 1, ‖(![a, b] : Fin 2 → ℝ) i.succ - ![a, b] i.castSucc‖ₑ ^ p = _
  rw [Fin.sum_univ_one]
  simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sub_nonneg.mpr h.le)]

/-- For `p ≥ 1` and an interval of length at most `1`, every increment sum of `t ↦ t` is at most
the length of the interval. -/
lemma incrSum_id_le {p : ℝ} (hp : 1 ≤ p) {a b : ℝ} (hab : b - a ≤ 1) (π : Partition a b) :
    incrSum p (fun t : ℝ => t) π ≤ ENNReal.ofReal (b - a) := by
  unfold incrSum
  have hinc : ∀ i : Fin π.n, 0 ≤ π.t i.succ - π.t i.castSucc := fun i =>
    sub_nonneg.mpr (π.strictMono.monotone (Fin.castSucc_le_succ i))
  have hle1 : ∀ i : Fin π.n, π.t i.succ - π.t i.castSucc ≤ 1 := by
    intro i
    have h1 : π.t i.succ ≤ π.t (Fin.last _) := π.strictMono.monotone (Fin.le_last _)
    have h0 : π.t 0 ≤ π.t i.castSucc := π.strictMono.monotone (Fin.zero_le _)
    rw [π.last] at h1
    rw [π.first] at h0
    linarith
  calc ∑ i : Fin π.n, ‖π.t i.succ - π.t i.castSucc‖ₑ ^ p
      ≤ ∑ i : Fin π.n, ENNReal.ofReal (π.t i.succ - π.t i.castSucc) := by
        refine sum_le_sum fun i _ => ?_
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hinc i)]
        exact ENNReal.rpow_le_self_of_le_one (ENNReal.ofReal_le_one.mpr (hle1 i)) hp
    _ = ENNReal.ofReal (∑ i : Fin π.n, (π.t i.succ - π.t i.castSucc)) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => hinc i).symm
    _ = ENNReal.ofReal (b - a) := by rw [sum_succ_sub, π.first, π.last]

/-- For `p ≥ 1` the supremum of the increment sums of `t ↦ t` over partitions of an interval
`[a, b]` of length `1` is `1`. -/
theorem iSup_incrSum_id {p : ℝ} (hp : 1 ≤ p) {a b : ℝ} (hab : b - a = 1) :
    (⨆ π : Partition a b, incrSum p (fun t : ℝ => t) π) = 1 := by
  apply le_antisymm
  · refine iSup_le fun π => (incrSum_id_le hp hab.le π).trans_eq ?_
    rw [hab, ENNReal.ofReal_one]
  · refine le_iSup_of_le (twoPoint a b (by linarith)) ?_
    rw [incrSum_twoPoint, hab, ENNReal.ofReal_one, ENNReal.one_rpow]

/-- `X t = t` has p-variation exactly `1` on `[0, 1]` for every `p ≥ 1`. -/
theorem pVar_id {p : ℝ} (hp : 1 ≤ p) : pVar p 0 1 (fun t : ℝ => t) = 1 := by
  rw [pVar, iSup_incrSum_id hp (by norm_num), ENNReal.one_rpow]

/-! ## The conjecture, refuted -/

/-- **Conjecture 00000004007 is false for every `1 < p < ∞`.** With `q` the conjugate exponent
(`1/p + 1/q = 1`), the continuous paths `X = Y = (t ↦ t)` on `[0, 1]` satisfy
`‖X + Y‖ = 2 > 2^(1/q) = (‖X‖^q + ‖Y‖^q)^(1/q)`. -/
theorem conjecture_00000004007_false {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∃ X Y : ℝ → ℝ, Continuous X ∧ Continuous Y ∧
      (pVar p 0 1 X ^ q + pVar p 0 1 Y ^ q) ^ (1 / q) < pVar p 0 1 (fun s => X s + Y s) := by
  refine ⟨fun t => t, fun t => t, continuous_id, continuous_id, ?_⟩
  have h1 := pVar_id hpq.lt.le
  exact fails_at_diagonal hpq _ 0 1 (by rw [h1]; exact one_ne_zero) (by rw [h1]; exact ENNReal.one_ne_top)

/-- **Endpoint `p = 1`, `q = ∞`** (where `(a^q + b^q)^(1/q)` is read as `max a b`): fails too. -/
theorem conjecture_00000004007_false_one :
    ∃ X Y : ℝ → ℝ, Continuous X ∧ Continuous Y ∧
      max (pVar 1 0 1 X) (pVar 1 0 1 Y) < pVar 1 0 1 (fun s => X s + Y s) := by
  refine ⟨fun t => t, fun t => t, continuous_id, continuous_id, ?_⟩
  have h1 := pVar_id le_rfl
  exact fails_at_diagonal_one _ 0 1 (by rw [h1]; exact one_ne_zero) (by rw [h1]; exact ENNReal.one_ne_top)

/-! ## Alternative normalisation: the supremum without the p-th root -/

/-- The supremum itself, without the p-th root (not the conjecture's definition; included only
to show that the failure does not depend on taking the root). -/
noncomputable def pVarRaw (p a b : ℝ) (X : ℝ → E) : ℝ≥0∞ :=
  ⨆ π : Partition a b, incrSum p X π

theorem pVarRaw_add_self {p : ℝ} (hp : 0 ≤ p) (X : ℝ → E) (a b : ℝ) :
    pVarRaw p a b (fun s => X s + X s) = 2 ^ p * pVarRaw p a b X := by
  unfold pVarRaw
  have h : ∀ π : Partition a b, incrSum p (fun s => X s + X s) π = 2 ^ p * incrSum p X π := by
    intro π
    have := incrSum_smul hp (2 : ℝ) X π
    simp only [two_smul] at this
    rw [this]
    congr 2
    simp [Real.enorm_eq_ofReal_abs]
  simp_rw [h]
  rw [ENNReal.mul_iSup]

/-- With the raw supremum in place of its p-th root the inequality fails at `Y = X` as well. -/
theorem raw_fails_at_diagonal {p q : ℝ} (hpq : p.HolderConjugate q) (X : ℝ → E) (a b : ℝ)
    (h0 : pVarRaw p a b X ≠ 0) (htop : pVarRaw p a b X ≠ ∞) :
    (pVarRaw p a b X ^ q + pVarRaw p a b X ^ q) ^ (1 / q) <
      pVarRaw p a b (fun s => X s + X s) := by
  have hq : 1 < q := hpq.symm.lt
  rw [pVarRaw_add_self hpq.pos.le]
  set R := pVarRaw p a b X
  rw [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ (by have := hpq.symm.pos; positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel (by linarith), ENNReal.rpow_one]
  have h2 : (2 : ℝ≥0∞) ^ (1 / q) < 2 ^ p :=
    ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      (by rw [div_lt_iff₀ (by linarith)]; nlinarith [hpq.lt])
  exact ENNReal.mul_lt_mul_left h0 htop h2

/-- The raw-supremum version is refuted by the same paths. -/
theorem raw_version_false {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∃ X Y : ℝ → ℝ, Continuous X ∧ Continuous Y ∧
      (pVarRaw p 0 1 X ^ q + pVarRaw p 0 1 Y ^ q) ^ (1 / q) <
        pVarRaw p 0 1 (fun s => X s + Y s) := by
  refine ⟨fun t => t, fun t => t, continuous_id, continuous_id, ?_⟩
  have h1 : pVarRaw p 0 1 (fun t : ℝ => t) = 1 := iSup_incrSum_id hpq.lt.le (by norm_num)
  exact raw_fails_at_diagonal hpq _ 0 1 (by rw [h1]; exact one_ne_zero)
    (by rw [h1]; exact ENNReal.one_ne_top)

/-! ## Alternative reading: `X + Y` as the concatenation of paths -/

/-- **Concatenation reading.** Let `Z t = t` on `[0, 2]`; it is the concatenation of
`X = Z|[0,1]` and `Y = Z|[1,2]` (which agree at the junction `t = 1`). Each piece has
p-variation `1`, while `Z` has p-variation at least `2` (two-point partition), so
`‖Z‖ > 2^(1/q) = (‖X‖^q + ‖Y‖^q)^(1/q)`. -/
theorem concat_version_false {p q : ℝ} (hpq : p.HolderConjugate q) :
    (pVar p 0 1 (fun t : ℝ => t) ^ q + pVar p 1 2 (fun t : ℝ => t) ^ q) ^ (1 / q) <
      pVar p 0 2 (fun t : ℝ => t) := by
  have hp : 1 < p := hpq.lt
  have hq : 1 < q := hpq.symm.lt
  have h01 := pVar_id hp.le
  have h12 : pVar p 1 2 (fun t : ℝ => t) = 1 := by
    rw [pVar, iSup_incrSum_id hp.le (by norm_num), ENNReal.one_rpow]
  have h02 : 2 ≤ pVar p 0 2 (fun t : ℝ => t) := by
    unfold pVar
    have hle : (2 : ℝ≥0∞) ^ p ≤ ⨆ π : Partition 0 2, incrSum p (fun t : ℝ => t) π := by
      refine le_iSup_of_le (twoPoint 0 2 (by norm_num)) ?_
      rw [incrSum_twoPoint]
      norm_num
    calc (2 : ℝ≥0∞) = ((2 : ℝ≥0∞) ^ p) ^ (1 / p) := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel (by linarith), ENNReal.rpow_one]
      _ ≤ _ := ENNReal.rpow_le_rpow hle (by positivity)
  rw [h01, h12, ENNReal.one_rpow, one_add_one_eq_two]
  refine lt_of_lt_of_le ?_ h02
  calc (2 : ℝ≥0∞) ^ (1 / q) < 2 ^ (1 : ℝ) :=
        ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
          (by rw [div_lt_one (by linarith)]; exact hq)
    _ = 2 := ENNReal.rpow_one 2

/-- The main theorem restated for each `p > 1` with `q = p / (p - 1)`. -/
theorem conjecture_00000004007_false' {p : ℝ} (hp : 1 < p) :
    ∃ X Y : ℝ → ℝ, Continuous X ∧ Continuous Y ∧
      (pVar p 0 1 X ^ (p / (p - 1)) + pVar p 0 1 Y ^ (p / (p - 1))) ^ (1 / (p / (p - 1))) <
        pVar p 0 1 (fun s => X s + Y s) :=
  conjecture_00000004007_false (Real.HolderConjugate.conjExponent hp)

end Tlmc4007
