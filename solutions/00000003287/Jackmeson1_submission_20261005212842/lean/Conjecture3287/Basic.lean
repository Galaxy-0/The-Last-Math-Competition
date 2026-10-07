import Mathlib

/-!
# Conjecture 00000003287: Gauss–Christoffel quadrature

Setting: a measure `μ` on `ℝ` with all moments finite (`x ↦ x ^ k` integrable for every `k`)
that is not concentrated on finitely many points (`μ (sᶜ) ≠ 0` for every finite `s`, i.e.
`μ` has infinite support).  This includes `μ = w dx` for every weight function `w ≥ 0` (on an
interval, or on `ℝ`) that has finite moments and is not almost everywhere zero.
-/

open Polynomial MeasureTheory Finset

namespace C3287

variable {μ : Measure ℝ}

/-- `μ` is not concentrated on any finite set (equivalently, `μ` has infinite support). -/
def NotFinitelySupported (μ : Measure ℝ) : Prop := ∀ s : Finset ℝ, μ ((↑s : Set ℝ)ᶜ) ≠ 0

/-- All moments `∫ x ^ k dμ` exist. -/
def FiniteMoments (μ : Measure ℝ) : Prop := ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ

/-- `p` is the monic orthogonal polynomial of degree `n` for `μ`: monic, of degree `n`, and
orthogonal in `L²(μ)` to every polynomial of degree `< n`. -/
def IsMonicOrthogonal (μ : Measure ℝ) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.Monic ∧ p.natDegree = n ∧ ∀ q : ℝ[X], q.degree < n → ∫ x, p.eval x * q.eval x ∂μ = 0

/-- The `n`-node quadrature rule `f ↦ ∑ i, w i * f (x i)` (nodes `x`, weights `w`) is exact
for every polynomial of degree `≤ d`. -/
def IsExactUpTo (μ : Measure ℝ) {n : ℕ} (x w : Fin n → ℝ) (d : ℕ) : Prop :=
  ∀ f : ℝ[X], f.natDegree ≤ d → ∫ t, f.eval t ∂μ = ∑ i, w i * f.eval (x i)

/-- The algebraic (polynomial) degree of precision of a quadrature rule: the largest `d`
such that the rule is exact for all polynomials of degree `≤ d`. -/
noncomputable def algebraicPrecision (μ : Measure ℝ) {n : ℕ} (x w : Fin n → ℝ) : ℕ :=
  sSup {d | IsExactUpTo μ x w d}

/-- Weight functions: if `∫⁻ ofReal (w x) dx ≠ 0` (for a weight `w ≥ 0`: `w` is not a.e. zero),
the measure `w(x) dx` is not concentrated on finitely many points.  (A weight on an interval
`[a, b]` is the case `w = 0` off `[a, b]`.) -/
theorem notFinitelySupported_withDensity {w : ℝ → ℝ}
    (hw0 : ∫⁻ x, ENNReal.ofReal (w x) ≠ 0) :
    NotFinitelySupported (volume.withDensity fun x => ENNReal.ofReal (w x)) := by
  intro s
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ ((↑s : Set ℝ)ᶜ) :=
    compl_mem_ae_iff.2 (s.finite_toSet.measure_zero volume)
  rwa [withDensity_apply _ s.finite_toSet.measurableSet.compl,
    Measure.restrict_eq_self_of_ae_mem hae]

section Functional

variable (hmom : FiniteMoments μ)
include hmom

theorem integrable_eval (p : ℝ[X]) : Integrable (fun x => p.eval x) μ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval_add]; exact hp.add hq
  | monomial n a => simpa using (hmom n).const_mul a

/-- The moment functional `p ↦ ∫ p dμ` as a linear map. -/
noncomputable def I : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x, p.eval x ∂μ
  map_add' p q := by
    simp only [eval_add]
    exact integral_add (integrable_eval hmom p) (integrable_eval hmom q)
  map_smul' c p := by simp [eval_smul, integral_const_mul]

theorem I_apply (p : ℝ[X]) : I hmom p = ∫ x, p.eval x ∂μ := rfl

variable (hsupp : NotFinitelySupported μ)
include hsupp

/-- Positivity: a nonzero polynomial that is pointwise `≥ 0` has positive integral. -/
theorem integral_pos {p : ℝ[X]} (hp : p ≠ 0) (hnn : ∀ x, 0 ≤ p.eval x) :
    0 < ∫ x, p.eval x ∂μ := by
  rcases (integral_nonneg (f := fun x => p.eval x) fun x => hnn x).lt_or_eq with h | h
  · exact h
  exfalso
  have hae := (integral_eq_zero_iff_of_nonneg (f := fun x => p.eval x) (fun x => hnn x)
    (integrable_eval hmom p)).1 h.symm
  apply hsupp p.roots.toFinset
  rw [Filter.EventuallyEq, ae_iff] at hae
  convert hae using 2
  ext x
  simp [Polynomial.mem_roots hp]

theorem eq_zero_of_I_mul_self {r : ℝ[X]} (h : I hmom (r * r) = 0) : r = 0 := by
  by_contra hr
  have := integral_pos hmom hsupp (mul_ne_zero hr hr) (fun x => by
    rw [eval_mul]; exact mul_self_nonneg _)
  rw [I_apply] at h
  linarith

end Functional

/-- Orthogonality against monomials implies orthogonality against all lower-degree
polynomials. -/
theorem orth_of_monomials (hmom : FiniteMoments μ) {n : ℕ} {p : ℝ[X]}
    (h : ∀ i < n, I hmom (p * X ^ i) = 0) {q : ℝ[X]} (hq : q.degree < n) :
    I hmom (p * q) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  have hnd : q.natDegree < n := (natDegree_lt_iff_degree_lt hq0).2 hq
  rw [q.as_sum_range_C_mul_X_pow, mul_sum, map_sum]
  refine sum_eq_zero fun i hi => ?_
  have hi' : i < n := lt_of_lt_of_le (mem_range.1 hi) hnd
  rw [mul_left_comm, ← smul_eq_C_mul, map_smul, h i hi', smul_zero]

theorem orth_I (hmom : FiniteMoments μ) {n : ℕ} {p q : ℝ[X]}
    (hp : IsMonicOrthogonal μ n p) (hq : q.degree < n) : I hmom (p * q) = 0 := by
  rw [I_apply]; simpa [eval_mul] using hp.2.2 q hq

variable (hmom : FiniteMoments μ) (hsupp : NotFinitelySupported μ)

include hmom hsupp in
/-- Existence of the monic orthogonal polynomial of every degree. -/
theorem exists_monicOrthogonal (n : ℕ) : ∃ p, IsMonicOrthogonal μ n p := by
  let e := degreeLTEquiv ℝ n
  let Φ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun i =>
    (I hmom).comp ((LinearMap.mulRight ℝ (X ^ (i : ℕ))).comp
      ((degreeLT ℝ n).subtype.comp e.symm.toLinearMap))
  have hΦ : ∀ c i, Φ c i = I hmom ((e.symm c : ℝ[X]) * X ^ (i : ℕ)) := fun c i => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hr : (e.symm c : ℝ[X]).degree < n := mem_degreeLT.1 (e.symm c).2
    have h0 : I hmom ((e.symm c : ℝ[X]) * (e.symm c : ℝ[X])) = 0 :=
      orth_of_monomials hmom (fun i hi => by rw [← hΦ c ⟨i, hi⟩, hc]; rfl) hr
    have := eq_zero_of_I_mul_self hmom hsupp h0
    have : e.symm c = 0 := Subtype.ext this
    simpa using congrArg e this
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.1 hinj)
    (fun i => - I hmom (X ^ n * X ^ (i : ℕ)))
  have hr : (e.symm c : ℝ[X]).degree < n := mem_degreeLT.1 (e.symm c).2
  refine ⟨X ^ n + (e.symm c : ℝ[X]), monic_X_pow_add hr, ?_, ?_⟩
  · rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  · intro q hq
    have := orth_of_monomials hmom (p := X ^ n + (e.symm c : ℝ[X])) (fun i hi => by
      have := congrFun hc ⟨i, hi⟩
      rw [hΦ] at this
      rw [add_mul, map_add, this]; ring) hq
    simpa [I_apply, eval_mul] using this

include hmom hsupp in
/-- Uniqueness of the monic orthogonal polynomial. -/
theorem monicOrthogonal_unique {n : ℕ} {p q : ℝ[X]} (hp : IsMonicOrthogonal μ n p)
    (hq : IsMonicOrthogonal μ n q) : p = q := by
  have hdeg : (p - q).degree < n := by
    rcases eq_or_ne (p - q) 0 with h | h
    · rw [h, degree_zero]; exact WithBot.bot_lt_coe n
    have hpd := degree_eq_natDegree hp.1.ne_zero
    have := degree_sub_lt_left (p := p) (q := q)
      (by rw [hpd, degree_eq_natDegree hq.1.ne_zero, hp.2.1, hq.2.1])
      hp.1.ne_zero (by rw [hp.1.leadingCoeff, hq.1.leadingCoeff])
    rwa [hpd, hp.2.1] at this
  have h0 : I hmom ((p - q) * (p - q)) = 0 := by
    rw [sub_mul, map_sub, orth_I hmom hp hdeg, orth_I hmom hq hdeg, sub_zero]
  exact sub_eq_zero.1 (eq_zero_of_I_mul_self hmom hsupp h0)

include hmom hsupp in
/-- `p * s` cannot be pointwise `≥ 0` for a nonzero `s` of degree `< n`. -/
theorem not_nonneg_mul {n : ℕ} {p s : ℝ[X]} (hp : IsMonicOrthogonal μ n p) (hs : s ≠ 0)
    (hsd : s.degree < n) (hnn : ∀ x, 0 ≤ (p * s).eval x) : False := by
  have h1 := integral_pos hmom hsupp (mul_ne_zero hp.1.ne_zero hs) hnn
  have h2 := orth_I hmom hp hsd
  rw [I_apply] at h2
  linarith

/-- A real polynomial without real zeros has constant sign (intermediate value theorem). -/
theorem const_sign {f : ℝ[X]} (hf : ∀ x, f.eval x ≠ 0) :
    (∀ x, 0 < f.eval x) ∨ (∀ x, f.eval x < 0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
  obtain ⟨t, -, ht⟩ := intermediate_value_uIcc (f := fun x => f.eval x)
    f.continuous.continuousOn (Set.mem_uIcc.2 (Or.inl ⟨hx, hy⟩))
  exact hf t ht

include hmom hsupp in
/-- The monic orthogonal polynomial of degree `n` has `n` real zeros counted with
multiplicity. -/
theorem roots_card_eq {n : ℕ} {p : ℝ[X]} (hp : IsMonicOrthogonal μ n p) :
    Multiset.card p.roots = n := by
  obtain ⟨q, hpq, -, hq⟩ := exists_prod_multiset_X_sub_C_mul p
  set P := (p.roots.map fun a => X - C a).prod with hP
  have hP0 : P ≠ 0 := (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a).ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; exact hp.1.ne_zero (by rw [← hpq, mul_zero])
  have hqr : ∀ x, q.eval x ≠ 0 := fun x hx => by
    have : x ∈ q.roots := (mem_roots hq0).2 hx
    rw [hq] at this; simp at this
  by_contra hne
  have hlt : Multiset.card p.roots < n := lt_of_le_of_ne (hp.2.1 ▸ card_roots' p) hne
  have hPd : P.degree < n := by
    rw [degree_eq_natDegree hP0, hP, natDegree_multiset_prod_X_sub_C_eq_card]; exact_mod_cast hlt
  have hev : ∀ x, (p * P).eval x = q.eval x * (P.eval x * P.eval x) := fun x => by
    rw [← hpq]; simp only [eval_mul]; ring
  rcases const_sign hqr with hpos | hneg
  · exact not_nonneg_mul hmom hsupp hp hP0 hPd fun x => by
      rw [hev]; exact mul_nonneg (hpos x).le (mul_self_nonneg _)
  · refine not_nonneg_mul hmom hsupp hp (neg_ne_zero.2 hP0) (by rwa [degree_neg]) fun x => ?_
    rw [mul_neg, eval_neg, hev]
    nlinarith [hneg x, mul_self_nonneg (P.eval x)]

include hmom hsupp in
/-- The zeros of the monic orthogonal polynomial are simple. -/
theorem roots_nodup {n : ℕ} {p : ℝ[X]} (hp : IsMonicOrthogonal μ n p) : p.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  by_contra h
  push Not at h
  rw [count_roots] at h
  obtain ⟨s, hs⟩ := (le_rootMultiplicity_iff hp.1.ne_zero).1
    (show 2 ≤ rootMultiplicity a p by omega)
  have hs0 : s ≠ 0 := by rintro rfl; exact hp.1.ne_zero (by rw [hs, mul_zero])
  have hsd : s.degree < n := by
    have := congrArg natDegree hs
    rw [natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero a)) hs0, natDegree_pow, natDegree_X_sub_C,
      hp.2.1] at this
    rw [degree_eq_natDegree hs0]; exact_mod_cast (by omega : s.natDegree < n)
  exact not_nonneg_mul hmom hsupp hp hs0 hsd fun x => by
    rw [hs]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    rw [mul_assoc]; exact mul_nonneg (sq_nonneg _) (mul_self_nonneg _)

/-- The Christoffel number `λ_i = ∫ ℓ_i dμ`, where `ℓ_i` is the Lagrange basis polynomial
of the nodes `x` at the node `x i`. -/
noncomputable def christoffelWeight (μ : Measure ℝ) {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∫ t, (Lagrange.basis univ x i).eval t ∂μ

include hmom in
/-- Exactness through degree `2n - 1` of the interpolatory rule at the zeros of `p_n`. -/
theorem exact_of_roots {n : ℕ} (hn : 0 < n) {p : ℝ[X]} (hp : IsMonicOrthogonal μ n p)
    {x : Fin n → ℝ} (hx : Function.Injective x) (hroot : ∀ i, p.eval (x i) = 0) :
    IsExactUpTo μ x (christoffelWeight μ x) (2 * n - 1) := by
  intro f hf
  have hdiv := modByMonic_add_div f p
  have hrd : (f %ₘ p).degree < #(univ : Finset (Fin n)) := by
    have := degree_modByMonic_lt f hp.1
    rwa [degree_eq_natDegree hp.1.ne_zero, hp.2.1, ← Fintype.card_fin n, ← card_univ] at this
  have hdd : (f /ₘ p).degree < n := by
    have := natDegree_divByMonic f hp.1
    rw [hp.2.1] at this
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast (by omega : (f /ₘ p).natDegree < n))
  have hr := Lagrange.eq_interpolate (s := univ) (v := x) hx.injOn hrd
  have hfe : ∀ i, f.eval (x i) = (f %ₘ p).eval (x i) := fun i => by
    conv_lhs => rw [← hdiv]
    rw [eval_add, eval_mul, hroot i, zero_mul, add_zero]
  conv_lhs => rw [← I_apply hmom, ← hdiv, map_add, orth_I hmom hp hdd, add_zero, hr]
  rw [Lagrange.interpolate_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul, I_apply, hfe i, mul_comm, christoffelWeight]

include hmom hsupp in
/-- Every rule of precision `≥ 2n - 1` with distinct nodes has positive weights. -/
theorem weight_pos {n : ℕ} {x w : Fin n → ℝ} (hx : Function.Injective x)
    (h : IsExactUpTo μ x w (2 * n - 1)) (i : Fin n) : 0 < w i := by
  set b := Lagrange.basis univ x i
  have hb : b.natDegree = n - 1 := by simp [b, Lagrange.natDegree_basis hx.injOn (mem_univ i)]
  have hbi : b.eval (x i) = 1 := Lagrange.eval_basis_self hx.injOn (mem_univ i)
  have hb0 : b ≠ 0 := fun h0 => by rw [h0, eval_zero] at hbi; exact zero_ne_one hbi
  have key := h (b * b) ((natDegree_mul_le).trans (by omega))
  have hsum : ∑ j, w j * (b * b).eval (x j) = w i := by
    rw [sum_eq_single i]
    · rw [eval_mul, hbi]; ring
    · intro j _ hj; rw [eval_mul, Lagrange.eval_basis_of_ne (Ne.symm hj) (mem_univ j)]; ring
    · simp
  rw [← hsum, ← key]
  exact integral_pos hmom hsupp (mul_ne_zero hb0 hb0) fun t => by
    rw [eval_mul]; exact mul_self_nonneg _

theorem nodePoly_spec {n : ℕ} (x : Fin n → ℝ) :
    (∏ i, (X - C (x i))).Monic ∧ (∏ i, (X - C (x i))).natDegree = n ∧
      ∀ i, (∏ j, (X - C (x j))).eval (x i) = 0 := by
  refine ⟨monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i), by simp, fun i => ?_⟩
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  exact prod_eq_zero (mem_univ i) (sub_self _)

include hmom hsupp in
/-- Maximality: no `n`-node rule (any nodes, any weights) is exact in degree `2n`. -/
theorem not_exact_two_mul {n : ℕ} (x w : Fin n → ℝ) : ¬ IsExactUpTo μ x w (2 * n) := by
  intro h
  obtain ⟨hm, hd, hz⟩ := nodePoly_spec x
  set ω : ℝ[X] := ∏ i, (X - C (x i))
  have key := h (ω * ω) ((natDegree_mul_le).trans (by omega))
  have hpos := integral_pos hmom hsupp (mul_ne_zero hm.ne_zero hm.ne_zero) fun t => by
    rw [eval_mul]; exact mul_self_nonneg _
  rw [key] at hpos
  simp [eval_mul, hz] at hpos

theorem exactUpTo_mono {n : ℕ} {x w : Fin n → ℝ} {d d' : ℕ} (h : IsExactUpTo μ x w d)
    (hd : d' ≤ d) : IsExactUpTo μ x w d' := fun f hf => h f (hf.trans hd)

include hmom hsupp in
/-- The precision of every `n`-node rule is at most `2n - 1`. -/
theorem precision_le {n : ℕ} (x w : Fin n → ℝ) {d : ℕ} (h : IsExactUpTo μ x w d) :
    d ≤ 2 * n - 1 := by
  by_contra hlt
  exact not_exact_two_mul hmom hsupp x w (exactUpTo_mono h (by omega))

include hmom hsupp in
theorem precision_eq {n : ℕ} {x w : Fin n → ℝ} (h : IsExactUpTo μ x w (2 * n - 1)) :
    algebraicPrecision μ x w = 2 * n - 1 :=
  IsGreatest.csSup_eq ⟨h, fun _ hd => precision_le hmom hsupp x w hd⟩

include hmom hsupp in
/-- The nodes of any `n`-node rule of precision `≥ 2n - 1` are the zeros of `p_n`. -/
theorem nodes_eq {n : ℕ} (hn : 0 < n) {p : ℝ[X]} (hp : IsMonicOrthogonal μ n p)
    (x w : Fin n → ℝ) (h : IsExactUpTo μ x w (2 * n - 1)) : p = ∏ i, (X - C (x i)) := by
  obtain ⟨hm, hd, hz⟩ := nodePoly_spec x
  refine monicOrthogonal_unique hmom hsupp hp ⟨hm, hd, fun q hq => ?_⟩
  have hqn : q.natDegree < n := by
    rcases eq_or_ne q 0 with rfl | hq0
    · simpa using hn
    exact (natDegree_lt_iff_degree_lt hq0).2 hq
  have := h ((∏ i, (X - C (x i))) * q) ((natDegree_mul_le).trans (by omega))
  simp only [eval_mul] at this
  rw [this]; simp [hz]

/-! ### The three-term recurrence -/

theorem degree_lt_of_natDegree_lt {q : ℝ[X]} {m : ℕ} (h : q.natDegree < m) : q.degree < m :=
  (degree_le_natDegree).trans_lt (by exact_mod_cast h)

theorem I_C_mul (hmom : FiniteMoments μ) (c : ℝ) (f : ℝ[X]) : I hmom (C c * f) = c * I hmom f := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

/-- Removing the top coefficient of `r` (degree `≤ m`) with a monic `p` of degree `m`. -/
theorem degree_sub_lead {m : ℕ} {r p : ℝ[X]} (hr : r.degree < (m + 1 : ℕ)) (hp : p.Monic)
    (hpd : p.natDegree = m) : (r - C (r.coeff m) * p).degree < m := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  rw [coeff_sub, coeff_C_mul]
  rcases hk.lt_or_eq with hk | rfl
  · rw [coeff_eq_zero_of_degree_lt (hr.trans_le (by exact_mod_cast hk)),
      coeff_eq_zero_of_natDegree_lt (p := p) (by omega)]; ring
  · rw [← hpd, hp.coeff_natDegree, hpd]; ring

/-- `X * p - q` has degree `< m + 1` for monic `p, q` of degrees `m`, `m + 1`. -/
theorem degree_X_mul_sub {m : ℕ} {p q : ℝ[X]} (hp : p.Monic) (hpd : p.natDegree = m)
    (hq : q.Monic) (hqd : q.natDegree = m + 1) :
    (X * p - q).degree < ((m + 1 : ℕ) : WithBot ℕ) := by
  have hXd : (X * p).natDegree = m + 1 := by rw [natDegree_X_mul hp.ne_zero, hpd]
  have hX : (X * p).Monic := monic_X.mul hp
  have := degree_sub_lt_left (p := X * p) (q := q)
    (by rw [degree_eq_natDegree hX.ne_zero, degree_eq_natDegree hq.ne_zero, hXd, hqd])
    hX.ne_zero (by rw [hX.leadingCoeff, hq.leadingCoeff])
  rwa [degree_eq_natDegree hX.ne_zero, hXd] at this

include hmom hsupp in
/-- **Three-term recurrence.**  Consecutive monic orthogonal polynomials satisfy
`p_{n+2} = (X - a) p_{n+1} - b p_n` with `b > 0`. -/
theorem three_term_recurrence {n : ℕ} {p₀ p₁ p₂ : ℝ[X]} (h₀ : IsMonicOrthogonal μ n p₀)
    (h₁ : IsMonicOrthogonal μ (n + 1) p₁) (h₂ : IsMonicOrthogonal μ (n + 2) p₂) :
    ∃ a b : ℝ, 0 < b ∧ p₂ = (X - C a) * p₁ - C b * p₀ := by
  have hr := degree_X_mul_sub h₁.1 h₁.2.1 h₂.1 h₂.2.1
  set a := (X * p₁ - p₂).coeff (n + 1)
  have hu := degree_sub_lead hr h₁.1 h₁.2.1
  set b := (X * p₁ - p₂ - C a * p₁).coeff n
  have hv := degree_sub_lead hu h₀.1 h₀.2.1
  have hv0 : X * p₁ - p₂ - C a * p₁ - C b * p₀ = 0 := by
    refine eq_zero_of_I_mul_self hmom hsupp ?_
    refine orth_of_monomials hmom (fun i hi => ?_) hv
    have hq : (X ^ i : ℝ[X]).degree < n := by rw [degree_X_pow]; exact_mod_cast hi
    have e : (X * p₁ - p₂ - C a * p₁ - C b * p₀) * X ^ i = p₁ * X ^ (i + 1) - p₂ * X ^ i -
        C a * (p₁ * X ^ i) - C b * (p₀ * X ^ i) := by ring
    rw [e, map_sub, map_sub, map_sub, I_C_mul, I_C_mul, orth_I hmom h₂ (hq.trans (by norm_cast; omega)),
      orth_I hmom h₁ (hq.trans (by norm_cast; omega)), orth_I hmom h₀ hq,
      orth_I hmom h₁ (by rw [degree_X_pow]; exact_mod_cast (by omega : i + 1 < n + 1))]
    ring
  refine ⟨a, b, ?_, by linear_combination -hv0⟩
  -- `b ∫ p_n² = ∫ p_{n+1}²`
  have hp0 : 0 < I hmom (p₀ * p₀) := integral_pos hmom hsupp (mul_ne_zero h₀.1.ne_zero
    h₀.1.ne_zero) fun t => by rw [eval_mul]; exact mul_self_nonneg _
  have hp1 : 0 < I hmom (p₁ * p₁) := integral_pos hmom hsupp (mul_ne_zero h₁.1.ne_zero
    h₁.1.ne_zero) fun t => by rw [eval_mul]; exact mul_self_nonneg _
  have e1 : I hmom (p₁ * (X * p₀)) = I hmom (p₁ * p₁) := by
    have := orth_I hmom h₁ (degree_X_mul_sub h₀.1 h₀.2.1 h₁.1 h₁.2.1)
    rw [mul_sub, map_sub, sub_eq_zero] at this
    exact this
  have e2 : I hmom (p₁ * (X * p₀)) = b * I hmom (p₀ * p₀) := by
    have hX : X * p₁ = p₂ + C a * p₁ + C b * p₀ := by linear_combination hv0
    have e : p₁ * (X * p₀) = p₂ * p₀ + C a * (p₁ * p₀) + C b * (p₀ * p₀) := by
      linear_combination p₀ * hX
    have hd0 : p₀.degree < (n + 1 : ℕ) := degree_lt_of_natDegree_lt (by rw [h₀.2.1]; omega)
    rw [e, map_add, map_add, I_C_mul, I_C_mul, orth_I hmom h₁ hd0,
      orth_I hmom h₂ (hd0.trans (by norm_cast; omega))]
    ring
  nlinarith

/-! ### Main theorem -/

/-- **Gauss–Christoffel quadrature** for a measure `μ` with finite moments and infinite
support, and `n ≥ 1`:
1. the monic orthogonal polynomial `p_n` of degree `n` exists and is unique;
2. `p_n` has `n` real zeros, all simple;
3. the Gauss rule — nodes the zeros `x_1 < ⋯ < x_n` of `p_n`, weights the Christoffel numbers
   `λ_i = ∫ ℓ_i dμ` — has positive weights, is exact for all polynomials of degree `≤ 2n - 1`,
   is not exact in degree `2n`, so its algebraic precision is exactly `2n - 1`;
4. conversely, the nodes of every `n`-node rule of precision `≥ 2n - 1` are the zeros of `p_n`
   (`p_n = ∏ (X - x_i)`);
5. no `n`-node rule (arbitrary real nodes and weights) is exact beyond degree `2n - 1`. -/
theorem gauss_christoffel (hmom : FiniteMoments μ) (hsupp : NotFinitelySupported μ) {n : ℕ}
    (hn : 0 < n) :
    (∃! p : ℝ[X], IsMonicOrthogonal μ n p) ∧
    ∀ p : ℝ[X], IsMonicOrthogonal μ n p →
      (Multiset.card p.roots = n ∧ p.roots.Nodup) ∧
      (∃ x : Fin n → ℝ, StrictMono x ∧ (∀ a : ℝ, p.IsRoot a ↔ a ∈ Set.range x) ∧
        (∀ i, 0 < christoffelWeight μ x i) ∧
        IsExactUpTo μ x (christoffelWeight μ x) (2 * n - 1) ∧
        ¬ IsExactUpTo μ x (christoffelWeight μ x) (2 * n) ∧
        algebraicPrecision μ x (christoffelWeight μ x) = 2 * n - 1) ∧
      (∀ x w : Fin n → ℝ, IsExactUpTo μ x w (2 * n - 1) → p = ∏ i, (X - C (x i))) ∧
      (∀ x w : Fin n → ℝ, ∀ d, IsExactUpTo μ x w d → d ≤ 2 * n - 1) := by
  obtain ⟨p₀, hp₀⟩ := exists_monicOrthogonal hmom hsupp n
  refine ⟨⟨p₀, hp₀, fun q hq => monicOrthogonal_unique hmom hsupp hq hp₀⟩, fun p hp => ?_⟩
  have hcard := roots_card_eq hmom hsupp hp
  have hnd := roots_nodup hmom hsupp hp
  have hR : p.roots.toFinset.card = n := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  have hrange : ∀ a, p.IsRoot a ↔ a ∈ Set.range (p.roots.toFinset.orderEmbOfFin hR) := fun a => by
    rw [Finset.range_orderEmbOfFin, Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp.1.ne_zero]
  have hinj := (p.roots.toFinset.orderEmbOfFin hR).injective
  have hex := exact_of_roots hmom hn hp hinj fun i => (hrange _).2 ⟨i, rfl⟩
  exact ⟨⟨hcard, hnd⟩, ⟨_, (p.roots.toFinset.orderEmbOfFin hR).strictMono, hrange,
    weight_pos hmom hsupp hinj hex, hex, not_exact_two_mul hmom hsupp _ _,
    precision_eq hmom hsupp hex⟩, fun y w h => nodes_eq hmom hsupp hn hp y w h,
    fun y w _ h => precision_le hmom hsupp y w h⟩

end C3287
