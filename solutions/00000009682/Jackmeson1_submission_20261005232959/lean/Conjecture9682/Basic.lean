import Mathlib

/-!
# Conjecture 00000009682: two algebraically independent U-numbers

Mahler's classification, following the definitions in the Wikipedia article
"Transcendental number theory", section "Mahler's classification":

* `m(x, n, H)` is the minimum non-zero absolute value `|P(x)|` over integer polynomials `P`
  of degree at most `n` and height (maximum absolute value of a coefficient) at most `H`;
* `ω(x, n, H) = -log m(x, n, H) / (n log H)` and `ω(x, n) = limsup_{H → ∞} ω(x, n, H)`;
* a U-number is a transcendental number with `ω(x, n) = ∞` for some positive integer `n`;
* an S-number is a transcendental number for which the `ω(x, n)` are bounded.

We prove that every Liouville number is a U-number (`ω(x, 1) = ∞`), and that there are two
Liouville numbers, hence two U-numbers, that are algebraically independent over `ℚ`.
This refutes the clause "the dimension of algebraically independent subsets of U numbers is
exactly 1, with no two-dimensional U families", and hence the conjecture (a conjunction),
both for real numbers and for complex numbers.
-/

open Polynomial Filter Topology Cardinal

namespace C9682

/-- The values `|P(x)|` that are non-zero, for `P ∈ ℤ[X]` of degree `≤ n` and height `≤ H`. -/
def values (x : ℂ) (n H : ℕ) : Set ℝ :=
  {r | ∃ P : ℤ[X], P.natDegree ≤ n ∧ (∀ i, |P.coeff i| ≤ (H : ℤ)) ∧ r = ‖aeval x P‖ ∧ r ≠ 0}

/-- Mahler's `m(x, n, H)`: the minimum non-zero value of `|P(x)|` over integer polynomials of
degree at most `n` and height at most `H`. -/
noncomputable def mahlerM (x : ℂ) (n H : ℕ) : ℝ := sInf (values x n H)

/-- Mahler's `ω(x, n, H) = -log m(x, n, H) / (n log H)`. -/
noncomputable def mahlerOmegaH (x : ℂ) (n H : ℕ) : ℝ :=
  -Real.log (mahlerM x n H) / (n * Real.log H)

/-- Mahler's `ω(x, n) = limsup_{H → ∞} ω(x, n, H)`, valued in the extended reals. -/
noncomputable def mahlerOmega (x : ℂ) (n : ℕ) : EReal :=
  limsup (fun H : ℕ => (mahlerOmegaH x n H : EReal)) atTop

/-- A U-number: a transcendental number with `ω(x, n) = ∞` for some positive integer `n`. -/
def IsUNumber (x : ℂ) : Prop :=
  Transcendental ℚ x ∧ ∃ n : ℕ, 0 < n ∧ mahlerOmega x n = ⊤

/-- An S-number: a transcendental number whose `ω(x, n)` (`n ≥ 1`) are bounded. -/
def IsSNumber (x : ℂ) : Prop :=
  Transcendental ℚ x ∧ ∃ C : ℝ, ∀ n : ℕ, 0 < n → mahlerOmega x n ≤ C

/-- The conjecture for complex numbers (Lebesgue measure on `ℂ`). The third conjunct reads
"the dimension of algebraically independent subsets of U numbers is exactly 1" as: the
supremum of the sizes of the subsets of U-numbers that are algebraically independent over
`ℚ` is `1`; "no two-dimensional U families" as: no two-element such subset exists. -/
def ConjectureComplex : Prop :=
  (∀ᵐ x : ℂ, Transcendental ℚ x → IsSNumber x) ∧
  (MeasureTheory.volume {x : ℂ | IsUNumber x} = 0 ∧
    #{x : ℂ // IsUNumber x} = 𝔠) ∧
  ((⨆ s : {s : Set ℂ // s ⊆ {x | IsUNumber x} ∧ AlgebraicIndependent ℚ ((↑) : s → ℂ)},
      s.1.encard) = 1 ∧
    ¬ ∃ s : Set ℂ, s ⊆ {x | IsUNumber x} ∧ AlgebraicIndependent ℚ ((↑) : s → ℂ) ∧
      s.encard = 2)

/-- The same conjecture for real numbers (a real number is a U-number when it is one as a
complex number; Lebesgue measure on `ℝ`). -/
def ConjectureReal : Prop :=
  (∀ᵐ x : ℝ, Transcendental ℚ x → IsSNumber x) ∧
  (MeasureTheory.volume {x : ℝ | IsUNumber x} = 0 ∧
    #{x : ℝ // IsUNumber x} = 𝔠) ∧
  ((⨆ s : {s : Set ℝ // s ⊆ {x | IsUNumber x} ∧ AlgebraicIndependent ℚ ((↑) : s → ℝ)},
      s.1.encard) = 1 ∧
    ¬ ∃ s : Set ℝ, s ⊆ {x | IsUNumber x} ∧ AlgebraicIndependent ℚ ((↑) : s → ℝ) ∧
      s.encard = 2)

/-! ### `m(x, n, H)` is a minimum over a finite set -/

lemma finite_polys (n H : ℕ) :
    {P : ℤ[X] | P.natDegree ≤ n ∧ ∀ i, |P.coeff i| ≤ (H : ℤ)}.Finite := by
  apply Set.Finite.of_finite_image (f := fun P : ℤ[X] => fun i : Fin (n + 1) => P.coeff i)
  · apply (Set.Finite.pi (t := fun _ : Fin (n + 1) => Set.Icc (-(H : ℤ)) H)
      (fun _ => Set.finite_Icc _ _)).subset
    rintro _ ⟨P, hP, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    intro i
    exact abs_le.mp (hP.2 i)
  · intro P hP Q hQ h
    ext i
    by_cases hi : i ≤ n
    · exact congrFun h ⟨i, by omega⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by have := hP.1; omega),
        coeff_eq_zero_of_natDegree_lt (by have := hQ.1; omega)]

lemma values_finite (x : ℂ) (n H : ℕ) : (values x n H).Finite := by
  apply ((finite_polys n H).image (fun P => ‖aeval x P‖)).subset
  rintro r ⟨P, h1, h2, rfl, -⟩
  exact ⟨P, ⟨h1, h2⟩, rfl⟩

lemma mahlerM_spec {x : ℂ} {n H : ℕ} {P : ℤ[X]} (h1 : P.natDegree ≤ n)
    (h2 : ∀ i, |P.coeff i| ≤ (H : ℤ)) (h3 : ‖aeval x P‖ ≠ 0) :
    0 < mahlerM x n H ∧ mahlerM x n H ≤ ‖aeval x P‖ := by
  have hmem : ‖aeval x P‖ ∈ values x n H := ⟨P, h1, h2, rfl, h3⟩
  constructor
  · obtain ⟨Q, -, -, hQ, hne⟩ := Set.Nonempty.csInf_mem (⟨_, hmem⟩ : (values x n H).Nonempty)
      (values_finite x n H)
    rw [mahlerM, hQ]
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hQ ▸ hne))
  · exact csInf_le ⟨0, fun r ⟨_, _, _, hr, _⟩ => hr ▸ norm_nonneg _⟩ hmem

/-! ### Liouville numbers are U-numbers -/

theorem liouville_mahlerOmega_one {x : ℝ} (hx : Liouville x) : mahlerOmega (x : ℂ) 1 = ⊤ := by
  have key : ∀ w : ℝ, ∃ᶠ H : ℕ in atTop, w ≤ mahlerOmegaH (x : ℂ) 1 H := by
    intro w
    set k : ℕ := ⌈2 * w⌉₊ + 1 with hk
    rw [frequently_atTop]
    intro N
    obtain ⟨b, hbN, a, hne, hlt⟩ := frequently_atTop.mp (hx.frequently_exists_num k)
      (max (max N 2) (⌈|x|⌉₊ + 1))
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast (le_max_right N 2).trans ((le_max_left _ _).trans hbN)
    have hbx : |x| + 1 ≤ b := by
      have : ⌈|x|⌉₊ + 1 ≤ b := (le_max_right _ _).trans hbN
      have h' : (|x| : ℝ) ≤ ⌈|x|⌉₊ := Nat.le_ceil _
      have : ((⌈|x|⌉₊ + 1 : ℕ) : ℝ) ≤ b := by exact_mod_cast this
      push_cast at this
      linarith
    have hb0 : (0 : ℝ) < b := by linarith
    set H : ℕ := max b a.natAbs with hH
    refine ⟨H, ((le_max_left N 2).trans ((le_max_left _ _).trans hbN)).trans (le_max_left _ _), ?_⟩
    -- the linear polynomial `b X - a`
    set P : ℤ[X] := C (b : ℤ) * X + C (-a) with hP
    have hdeg : P.natDegree ≤ 1 := natDegree_linear_le
    have hheight : ∀ i, |P.coeff i| ≤ (H : ℤ) := by
      intro i
      have hHz : (H : ℤ) = max (b : ℤ) |a| := by
        rw [hH, Nat.cast_max, Int.natCast_natAbs]
      rw [hP, coeff_add, coeff_C_mul_X, coeff_C, hHz]
      rcases Nat.lt_or_ge i 2 with hi | hi
      · interval_cases i <;> simp
      · simp [show i ≠ 1 by omega, show i ≠ 0 by omega]
    have hval : ‖aeval (x : ℂ) P‖ = |b * x - a| := by
      have : aeval (x : ℂ) P = ((b * x - a : ℝ) : ℂ) := by
        simp [hP]; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    have hfac : |b * x - a| = b * |x - a / b| := by
      rw [show b * x - a = b * (x - a / b) by field_simp, abs_mul, abs_of_pos hb0]
    have hvpos : 0 < |b * x - a| := by
      rw [hfac]; exact mul_pos hb0 (abs_pos.mpr (sub_ne_zero.mpr hne))
    obtain ⟨hm0, hmle⟩ := mahlerM_spec (x := (x : ℂ)) hdeg hheight (by rw [hval]; exact hvpos.ne')
    rw [hval] at hmle
    have hbk : (1 : ℝ) ≤ (b : ℝ) ^ k := one_le_pow₀ (by linarith)
    have hvlt : |b * x - a| < b / b ^ k := by
      rw [hfac]
      calc (b : ℝ) * |x - a / b| < b * (1 / (b : ℝ) ^ k) := mul_lt_mul_of_pos_left hlt hb0
        _ = b / (b : ℝ) ^ k := by ring
    -- lower bound for `-log m`
    have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
    have hlogm : ((k : ℝ) - 1) * Real.log b < -Real.log (mahlerM (x : ℂ) 1 H) := by
      have h1 : Real.log (mahlerM (x : ℂ) 1 H) ≤ Real.log |b * x - a| := Real.log_le_log hm0 hmle
      have h2 : Real.log |b * x - a| < Real.log (b / b ^ k) := Real.log_lt_log hvpos hvlt
      rw [Real.log_div hb0.ne' (pow_pos hb0 k).ne', Real.log_pow] at h2
      nlinarith
    -- upper bound for `log H`
    have hHreal : (H : ℝ) ≤ b * (|x| + 1) := by
      rw [hH, Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
      apply max_le
      · nlinarith [abs_nonneg x]
      · have hba : |(a : ℝ)| ≤ |b * x| + |b * x - a| := by
          have := abs_sub (b * x) (b * x - a)
          simp only [sub_sub_cancel] at this
          linarith [abs_sub_comm (b * x) (b * x - a)]
        have : (b : ℝ) / (b : ℝ) ^ k ≤ b := div_le_self hb0.le hbk
        rw [abs_mul, abs_of_pos hb0] at hba
        nlinarith
    have hHpos : (2 : ℝ) ≤ H := hb2.trans (by exact_mod_cast le_max_left b a.natAbs)
    have hlogH : Real.log H ≤ 2 * Real.log b := by
      have : Real.log H ≤ Real.log (b * (|x| + 1)) := Real.log_le_log (by linarith) hHreal
      rw [Real.log_mul hb0.ne' (by positivity)] at this
      have : Real.log (|x| + 1) ≤ Real.log b := Real.log_le_log (by positivity) hbx
      linarith
    have hlogH0 : 0 < Real.log H := Real.log_pos (by linarith)
    have hk2 : 2 * w ≤ (k : ℝ) - 1 := by
      rw [hk]; push_cast; linarith [Nat.le_ceil (2 * w)]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) - 1 := by rw [hk]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈2 * w⌉₊]
    rw [mahlerOmegaH, Nat.cast_one, one_mul, le_div_iff₀ hlogH0]
    rcases le_or_gt w 0 with hw | hw
    · nlinarith
    · nlinarith
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (lt_add_one y)) ?_
  apply le_limsup_of_frequently_le'
  exact (key (y + 1)).mono fun H h => EReal.coe_le_coe_iff.mpr h

theorem liouville_transcendental_rat {x : ℝ} (hx : Liouville x) : Transcendental ℚ x := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic (R := ℤ) ℚ (nonZeroDivisors ℤ)
  exact fun h => hx.transcendental (IsAlgebraic.restrictScalars (R := ℤ) (S := ℚ) h)

/-- Every Liouville number is a U-number (`ω(x, 1) = ∞`). -/
theorem liouville_isUNumber {x : ℝ} (hx : Liouville x) : IsUNumber (x : ℂ) := by
  refine ⟨?_, 1, one_pos, liouville_mahlerOmega_one hx⟩
  rw [← Complex.coe_algebraMap, transcendental_algebraMap_iff (algebraMap ℝ ℂ).injective]
  exact liouville_transcendental_rat hx

/-! ### Two algebraically independent Liouville numbers -/

/-- For a field extension `A` of `ℝ` and a real `x`, residually many reals `y` have image in `A`
transcendental over `ℚ[x]` (the reals algebraic over `ℚ[x]` form a countable set). -/
theorem eventually_transcendental_adjoin (A : Type) [Field A] [Algebra ℚ A] [Algebra ℝ A]
    [IsScalarTower ℚ ℝ A] (x : ℝ) :
    ∀ᶠ y in residual ℝ, Transcendental (Algebra.adjoin ℚ ({algebraMap ℝ A x} : Set A))
      (algebraMap ℝ A y) := by
  set j := algebraMap ℝ A
  set K := Algebra.adjoin ℚ ({j x} : Set A)
  have : Countable K := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Algebra.cardinalMk_adjoin_le ℚ ({j x} : Set A)).trans ?_
    simp
  have hS : (j ⁻¹' {z : A | IsAlgebraic K z}).Countable :=
    (Algebraic.countable K A).preimage j.injective
  have : ∀ a ∈ j ⁻¹' {z : A | IsAlgebraic K z}, ∀ᶠ y in residual ℝ, y ≠ a := fun a _ =>
    residual_of_dense_open isOpen_compl_singleton (dense_compl_singleton a)
  exact ((eventually_countable_ball hS).mpr this).mono fun y hy hmem => hy y hmem rfl

/-- If `x` is transcendental over `ℚ` and the image of `y` is transcendental over `ℚ[x]`, then
`x ≠ y` and the images of `x, y` form an algebraically independent set over `ℚ`. -/
theorem indep_pair {A : Type} [Field A] [Algebra ℚ A] [Algebra ℝ A] [IsScalarTower ℚ ℝ A]
    {x y : ℝ} (hx : Transcendental ℚ x)
    (hy : Transcendental (Algebra.adjoin ℚ ({algebraMap ℝ A x} : Set A)) (algebraMap ℝ A y)) :
    x ≠ y ∧
      AlgebraicIndependent ℚ ((↑) : ({algebraMap ℝ A x, algebraMap ℝ A y} : Set A) → A) := by
  set j := algebraMap ℝ A
  have hxT : Transcendental ℚ (j x) := (transcendental_algebraMap_iff j.injective).mpr hx
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact hy (isAlgebraic_algebraMap
      (⟨j x, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin ℚ ({j x} : Set A)))
  have h1 : AlgebraicIndepOn ℚ id ({j x} : Set A) :=
    algebraicIndependent_unique_type_iff.mpr hxT
  have h2 := h1.insert (i := j y) (by rw [Set.image_id]; exact hy)
  rw [Set.pair_comm]
  exact h2

/-- Two real Liouville numbers (hence U-numbers) that are algebraically independent over `ℚ`,
both in `ℝ` and in `ℂ`. Here `x = liouvilleNumber 10 = ∑_{i ≥ 0} 10^(-i!)` (the sum starts at `i = 0`). -/
theorem exists_two_indep_U :
    ∃ x y : ℝ, x ≠ y ∧ IsUNumber (x : ℂ) ∧ IsUNumber (y : ℂ) ∧
      AlgebraicIndependent ℚ ((↑) : ({x, y} : Set ℝ) → ℝ) ∧
      AlgebraicIndependent ℚ ((↑) : ({(x : ℂ), (y : ℂ)} : Set ℂ) → ℂ) := by
  have hx : Liouville (liouvilleNumber 10) := liouville_liouvilleNumber (by norm_num)
  have hxT := liouville_transcendental_rat hx
  obtain ⟨y, hyL, hyR, hyC⟩ := (dense_of_mem_residual (eventually_residual_liouville.and
    ((eventually_transcendental_adjoin ℝ (liouvilleNumber 10)).and
      (eventually_transcendental_adjoin ℂ (liouvilleNumber 10))))).nonempty
  obtain ⟨hne, hR⟩ := indep_pair (A := ℝ) hxT hyR
  obtain ⟨-, hC⟩ := indep_pair (A := ℂ) hxT hyC
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Complex.coe_algebraMap] at hR hC
  exact ⟨_, y, hne, liouville_isUNumber hx, liouville_isUNumber hyL, hR, hC⟩

/-! ### Refutation of the conjecture -/

/-- A two-element algebraically independent set of complex U-numbers. -/
theorem two_dim_U_family_complex :
    ∃ s : Set ℂ, s ⊆ {x | IsUNumber x} ∧ AlgebraicIndependent ℚ ((↑) : s → ℂ) ∧
      s.encard = 2 := by
  obtain ⟨x, y, hne, hx, hy, -, hC⟩ := exists_two_indep_U
  exact ⟨_, Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hy⟩, hC,
    Set.encard_pair (by exact_mod_cast hne)⟩

/-- A two-element algebraically independent set of real U-numbers. -/
theorem two_dim_U_family_real :
    ∃ s : Set ℝ, s ⊆ {x | IsUNumber x} ∧ AlgebraicIndependent ℚ ((↑) : s → ℝ) ∧
      s.encard = 2 := by
  obtain ⟨x, y, hne, hx, hy, hR, -⟩ := exists_two_indep_U
  exact ⟨_, Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hy⟩, hR,
    Set.encard_pair hne⟩

/-- The "dimension exactly 1" sub-clause also fails: the supremum is at least `2`. -/
theorem two_le_iSup_complex :
    2 ≤ ⨆ s : {s : Set ℂ // s ⊆ {x | IsUNumber x} ∧ AlgebraicIndependent ℚ ((↑) : s → ℂ)},
      s.1.encard := by
  obtain ⟨s, hs, hi, h2⟩ := two_dim_U_family_complex
  exact le_iSup_of_le (⟨s, hs, hi⟩ : {s : Set ℂ // s ⊆ {x | IsUNumber x} ∧
    AlgebraicIndependent ℚ ((↑) : s → ℂ)}) h2.ge

theorem two_le_iSup_real :
    2 ≤ ⨆ s : {s : Set ℝ // s ⊆ {x | IsUNumber x} ∧ AlgebraicIndependent ℚ ((↑) : s → ℝ)},
      s.1.encard := by
  obtain ⟨s, hs, hi, h2⟩ := two_dim_U_family_real
  exact le_iSup_of_le (⟨s, hs, hi⟩ : {s : Set ℝ // s ⊆ {x | IsUNumber x} ∧
    AlgebraicIndependent ℚ ((↑) : s → ℝ)}) h2.ge

/-- Main theorem: the conjecture is false for complex numbers. Both sub-clauses of its third
conjunct fail. -/
theorem not_conjectureComplex : ¬ ConjectureComplex := fun h =>
  h.2.2.2 two_dim_U_family_complex

/-- Main theorem: the conjecture is false for real numbers. -/
theorem not_conjectureReal : ¬ ConjectureReal := fun h =>
  h.2.2.2 two_dim_U_family_real

end C9682
