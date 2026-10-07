import Mathlib

/-!
# Conjecture 00000000751 (disproof)

"For iterations of rational functions over Q_p, the Fatou set ... is completely invariant and
open, and the Julia set is nonempty if and only if the degree is >= 2."

`ℙ¹(K)` carries the chordal metric `ρ(z,w) = ‖z - w‖ / (max 1 ‖z‖ * max 1 ‖w‖)`,
`ρ(z,∞) = 1 / max 1 ‖z‖`; `φ ∈ K(X)` acts through its reduced numerator and denominator and
has degree `max (deg num) (deg denom)`.  Readings of the Julia set: `juliaSet` (complement of
the equicontinuity Fatou set), `juliaSetPt` (points of non-equicontinuity), `juliaRep` (closure
of the repelling periodic points).  For each, `z ↦ z / p` (degree 1) has `0 ∈ J`, and `z ↦ z ^ 2`
(degree 2) has `J = ∅`.  The dynamics is proved over any nontrivially normed ultrametric field.
-/

open Set Filter Topology Polynomial

namespace C751

/-- The projective line `ℙ¹(K)`: `aff z` is the point `[z : 1]`, `infty` is `∞ = [1 : 0]`. -/
inductive P1 (K : Type*) where
  | aff : K → P1 K
  | infty : P1 K

namespace P1

variable {K : Type*} [NormedField K]

/-- `max 1 ‖z‖`. -/
noncomputable def M (z : K) : ℝ := max 1 ‖z‖

lemma one_le_M (z : K) : 1 ≤ M z := le_max_left _ _
lemma M_pos (z : K) : 0 < M z := lt_of_lt_of_le one_pos (one_le_M z)
lemma norm_le_M (z : K) : ‖z‖ ≤ M z := le_max_right _ _
lemma M_of_le {z : K} (h : ‖z‖ ≤ 1) : M z = 1 := max_eq_left h

/-- The chordal metric on `ℙ¹(K)`. -/
noncomputable def chordal : P1 K → P1 K → ℝ
  | aff z, aff w => ‖z - w‖ / (M z * M w)
  | aff z, infty => 1 / M z
  | infty, aff w => 1 / M w
  | infty, infty => 0

lemma tri_aff (x y z : K) :
    ‖x - z‖ / (M x * M z) ≤ ‖x - y‖ / (M x * M y) + ‖y - z‖ / (M y * M z) := by
  have hx := M_pos x; have hy := M_pos y; have hz := M_pos z
  have key : ‖x - z‖ * M y ≤ ‖x - y‖ * M z + ‖y - z‖ * M x := by
    have h1 : ‖x - z‖ ≤ ‖x - y‖ * M z + ‖y - z‖ * M x := by
      have := norm_sub_le_norm_sub_add_norm_sub x y z
      nlinarith [one_le_M x, one_le_M z, norm_nonneg (x - y), norm_nonneg (y - z)]
    have h2 : ‖x - z‖ * ‖y‖ ≤ ‖x - y‖ * M z + ‖y - z‖ * M x := by
      have e : (x - z) * y = (x - y) * z + (y - z) * x := by ring
      have : ‖x - z‖ * ‖y‖ ≤ ‖x - y‖ * ‖z‖ + ‖y - z‖ * ‖x‖ := by
        rw [← norm_mul, e, ← norm_mul, ← norm_mul]
        exact norm_add_le _ _
      nlinarith [norm_le_M x, norm_le_M z, norm_nonneg (x - y), norm_nonneg (y - z)]
    rw [M, mul_max_of_nonneg _ _ (norm_nonneg _), mul_one]
    exact max_le h1 h2
  rw [div_add_div _ _ (mul_pos hx hy).ne' (mul_pos hy hz).ne',
    div_le_div_iff₀ (mul_pos hx hz) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key (mul_pos (mul_pos hx hy) hz).le]

lemma tri_inf_right (x y : K) : 1 / M x ≤ ‖x - y‖ / (M x * M y) + 1 / M y := by
  have hx := M_pos x; have hy := M_pos y
  have key : M y ≤ ‖x - y‖ + M x := by
    refine max_le (by linarith [one_le_M x, norm_nonneg (x - y)]) ?_
    have := norm_sub_norm_le y x
    rw [norm_sub_rev] at this
    linarith [norm_le_M x]
  rw [div_add_div _ _ (mul_pos hx hy).ne' hy.ne', div_le_div_iff₀ hx (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key (mul_pos hx hy).le]

lemma tri_inf_left (y z : K) : 1 / M z ≤ 1 / M y + ‖y - z‖ / (M y * M z) := by
  have := tri_inf_right z y
  rwa [norm_sub_rev, mul_comm, add_comm] at this

lemma tri_inf_mid (x z : K) : ‖x - z‖ / (M x * M z) ≤ 1 / M x + 1 / M z := by
  have hx := M_pos x; have hz := M_pos z
  have key : ‖x - z‖ ≤ M z + M x := by
    linarith [norm_sub_le x z, norm_le_M x, norm_le_M z]
  rw [div_add_div _ _ hx.ne' hz.ne', div_le_div_iff₀ (mul_pos hx hz) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key (mul_pos hx hz).le]

noncomputable instance : MetricSpace (P1 K) where
  dist := chordal
  dist_self a := by cases a <;> simp [chordal]
  dist_comm a b := by
    cases a <;> cases b <;> simp only [chordal]
    rw [norm_sub_rev, mul_comm]
  dist_triangle a b c := by
    cases a <;> cases b <;> cases c <;> simp only [chordal]
    all_goals first
      | exact tri_aff _ _ _ | exact tri_inf_right _ _ | exact tri_inf_mid _ _
      | exact tri_inf_left _ _ | (simp only [M]; positivity) | simp
  eq_of_dist_eq_zero {a b} h := by
    cases a <;> cases b <;> simp only [chordal] at h
    · rename_i z w
      have := (div_eq_zero_iff.mp h).resolve_right (mul_pos (M_pos z) (M_pos w)).ne'
      rw [norm_eq_zero, sub_eq_zero] at this
      rw [this]
    · exact absurd h (one_div_pos.mpr (M_pos _)).ne'
    · exact absurd h (one_div_pos.mpr (M_pos _)).ne'
    · rfl

lemma dist_def (a b : P1 K) : dist a b = chordal a b := rfl

/-- Affine coordinate (`∞ ↦ 0`); used only to read off derivatives near finite points. -/
def toK : P1 K → K
  | aff z => z
  | infty => 0

end P1

open P1

section Dynamics

variable {K : Type*} [NontriviallyNormedField K]

open scoped Classical in
/-- Action of `φ = num / denom ∈ K(X)` (lowest terms, `denom` monic) on `ℙ¹(K)`: a zero of
`denom` goes to `∞`; `∞` goes to `∞`, `0`, or the ratio of leading coefficients according as
`deg num >`, `<`, `= deg denom`. -/
noncomputable def act (φ : RatFunc K) : P1 K → P1 K
  | aff z => if φ.denom.eval z = 0 then infty else aff (φ.num.eval z / φ.denom.eval z)
  | infty => if φ.denom.natDegree < φ.num.natDegree then infty
      else if φ.num.natDegree < φ.denom.natDegree then aff 0
      else aff (φ.num.leadingCoeff / φ.denom.leadingCoeff)

/-- Degree of a rational function: `max (deg num) (deg denom)` in lowest terms. -/
noncomputable def deg (φ : RatFunc K) : ℕ := max φ.num.natDegree φ.denom.natDegree

/-- Fatou set: points with a neighbourhood on which the iterates are equicontinuous. -/
def fatouSet (φ : RatFunc K) : Set (P1 K) :=
  {x | ∃ U ∈ 𝓝 x, EquicontinuousOn (fun n : ℕ => (act φ)^[n]) U}

/-- Julia set (reading J1): the complement of the Fatou set. -/
def juliaSet (φ : RatFunc K) : Set (P1 K) := (fatouSet φ)ᶜ

/-- Julia set (reading J2): points at which the iterates are not equicontinuous. -/
def juliaSetPt (φ : RatFunc K) : Set (P1 K) :=
  {x | ¬ EquicontinuousAt (fun n : ℕ => (act φ)^[n]) x}

open scoped Classical in
/-- `z ↦ 1 / z` on `ℙ¹(K)` (`0 ↔ ∞`). -/
noncomputable def inv : P1 K → P1 K
  | aff z => if z = 0 then infty else aff z⁻¹
  | infty => aff 0

/-- Multiplier of `φ^[n]` at `x`: the derivative of `φ^[n]` at an affine point, and at `∞` the
derivative at `0` of the conjugate `w ↦ 1 / φ^[n] (1 / w)`. -/
noncomputable def mult (φ : RatFunc K) (n : ℕ) : P1 K → K
  | aff z => deriv (fun w => toK ((act φ)^[n] (aff w))) z
  | infty => deriv (fun w => toK (inv ((act φ)^[n] (inv (aff w))))) 0

/-- Repelling periodic points: `φ^[n] x = x` for some `n > 0`, with multiplier of norm `> 1`. -/
def repelling (φ : RatFunc K) : Set (P1 K) :=
  {x | ∃ n, 0 < n ∧ Function.IsPeriodicPt (act φ) n x ∧ 1 < ‖mult φ n x‖}

/-- Julia set (reading J3): the closure of the repelling periodic points. -/
def juliaRep (φ : RatFunc K) : Set (P1 K) := closure (repelling φ)

/-- The polynomial map `z ↦ P z`, `∞ ↦ ∞`. -/
noncomputable def polyMap (P : K[X]) : P1 K → P1 K
  | aff z => aff (P.eval z)
  | infty => infty

lemma act_poly (P : K[X]) (hP : 0 < P.natDegree) :
    act (algebraMap K[X] (RatFunc K) P) = polyMap P := by
  funext a
  cases a <;> simp [act, polyMap, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, hP]

lemma deg_poly (P : K[X]) : deg (algebraMap K[X] (RatFunc K) P) = P.natDegree := by
  simp [deg, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]

lemma equicontinuousAt_of_on {F : ℕ → P1 K → P1 K} {U : Set (P1 K)} {x : P1 K}
    (hU : U ∈ 𝓝 x) (h : EquicontinuousOn F U) : EquicontinuousAt F x := by
  intro V hV
  have := h x (mem_of_mem_nhds hU) V hV
  rwa [nhdsWithin_eq_nhds.mpr hU] at this

/-! ## Degree 1: `z ↦ c⁻¹ * z` with `0 < ‖c‖ < 1` has `0` in its Julia set -/

/-- `c⁻¹ * X ∈ K(X)`. -/
noncomputable def linFun (c : K) : RatFunc K := algebraMap K[X] (RatFunc K) (C c⁻¹ * X)

variable {c : K}

lemma deg_linFun (hc : c ≠ 0) : deg (linFun c) = 1 := by
  rw [linFun, deg_poly, natDegree_C_mul_X _ (inv_ne_zero hc)]

lemma act_linFun (hc : c ≠ 0) : act (linFun c) = polyMap (C c⁻¹ * X) :=
  act_poly _ (by rw [natDegree_C_mul_X _ (inv_ne_zero hc)]; exact one_pos)

lemma lin_iterate (n : ℕ) (z : K) :
    (polyMap (C c⁻¹ * X))^[n] (aff z) = aff (c⁻¹ ^ n * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    show aff (eval _ (C c⁻¹ * X)) = _
    rw [eval_mul, eval_C, eval_X, pow_succ', mul_assoc]

theorem not_equicontinuousAt_lin (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) :
    ¬ EquicontinuousAt (fun n : ℕ => (act (linFun c))^[n]) (aff 0) := by
  rw [Metric.equicontinuousAt_iff]
  push Not
  refine ⟨1, one_pos, fun δ hδ => ?_⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hc1
  have hcn : ‖c ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc1.le
  refine ⟨aff (c ^ n), ?_, n, ?_⟩
  · show ‖c ^ n - 0‖ / (M (c ^ n) * M 0) < δ
    rw [sub_zero, M_of_le hcn, M_of_le (by simp), norm_pow]
    simpa using hn
  · simp only [act_linFun hc0, lin_iterate, mul_zero, ← mul_pow, inv_mul_cancel₀ hc0, one_pow]
    show 1 ≤ ‖(0 : K) - 1‖ / (M 0 * M 1)
    rw [M_of_le (by simp), M_of_le (by simp)]
    simp

theorem zero_mem_juliaSetPt_lin (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) :
    aff 0 ∈ juliaSetPt (linFun c) :=
  not_equicontinuousAt_lin hc0 hc1

theorem zero_mem_juliaSet_lin (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) :
    aff 0 ∈ juliaSet (linFun c) := by
  rintro ⟨U, hU, h⟩
  exact not_equicontinuousAt_lin hc0 hc1 (equicontinuousAt_of_on hU h)

/-- `0` is a repelling fixed point of `z ↦ c⁻¹ * z`: multiplier `c⁻¹`, `‖c⁻¹‖ > 1`. -/
theorem zero_mem_repelling_lin (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) :
    aff 0 ∈ repelling (linFun c) := by
  refine ⟨1, one_pos, ?_, ?_⟩
  · show (act (linFun c))^[1] (aff 0) = aff 0
    rw [act_linFun hc0, lin_iterate, mul_zero]
  · have e : (fun w => toK ((act (linFun c))^[1] (aff w))) = fun w : K => c⁻¹ * w := by
      funext w
      rw [act_linFun hc0, lin_iterate, pow_one]
      rfl
    show 1 < ‖deriv _ 0‖
    rw [e, deriv_const_mul_field', deriv_id'']
    show 1 < ‖c⁻¹ * 1‖
    rw [mul_one, norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hc0)).mpr hc1

theorem zero_mem_juliaRep_lin (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) :
    aff 0 ∈ juliaRep (linFun c) :=
  subset_closure (zero_mem_repelling_lin hc0 hc1)

/-! ## Degree 2: `z ↦ z ^ 2` has empty Julia set -/

/-- `X ^ 2 ∈ K(X)`. -/
noncomputable def sqFun : RatFunc K := algebraMap K[X] (RatFunc K) (X ^ 2)

lemma deg_sqFun : deg (sqFun : RatFunc K) = 2 := by rw [sqFun, deg_poly, natDegree_X_pow]

lemma act_sqFun : act (sqFun : RatFunc K) = polyMap (X ^ 2) := act_poly _ (by simp)

lemma M_sq (x : K) : M (x ^ 2) = M x ^ 2 := by
  unfold M; rw [norm_pow]
  rcases le_total 1 ‖x‖ with h | h
  · rw [max_eq_right h, max_eq_right (one_le_pow₀ h)]
  · rw [max_eq_left h, max_eq_left (pow_le_one₀ (norm_nonneg _) h), one_pow]

lemma sq_iterate (n : ℕ) (z : K) : (polyMap (X ^ 2 : K[X]))^[n] (aff z) = aff (z ^ 2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    show aff (eval _ (X ^ 2)) = _
    rw [eval_pow, eval_X, ← pow_mul, ← pow_succ]

lemma sq_iterate_infty (n : ℕ) : (polyMap (X ^ 2 : K[X]))^[n] infty = infty :=
  Function.iterate_fixed rfl n

lemma inv_M_sq (x : K) : 1 / M (eval x (X ^ 2)) ≤ 1 / M x := by
  rw [eval_pow, eval_X, M_sq]
  exact one_div_le_one_div_of_le (M_pos x) (by nlinarith [one_le_M x])

variable [IsUltrametricDist K]

/-- `z ↦ z ^ 2` never increases chordal distances. -/
theorem lipschitz_sq : LipschitzWith 1 (act (sqFun : RatFunc K)) := by
  rw [act_sqFun]
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [NNReal.coe_one, one_mul, dist_def]
  cases a with
  | infty =>
    cases b with
    | infty => exact le_rfl
    | aff w => exact inv_M_sq w
  | aff x =>
    cases b with
    | infty => exact inv_M_sq x
    | aff y =>
      show ‖eval x (X ^ 2) - eval y (X ^ 2)‖ / (M (eval x (X ^ 2)) * M (eval y (X ^ 2))) ≤
        ‖x - y‖ / (M x * M y)
      simp only [eval_pow, eval_X]
      rw [M_sq, M_sq]
      have hx := M_pos x; have hy := M_pos y
      have key : ‖x ^ 2 - y ^ 2‖ ≤ ‖x - y‖ * (M x * M y) := by
        have e : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
        rw [e, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine (IsUltrametricDist.norm_add_le_max x y).trans (max_le ?_ ?_)
        · nlinarith [norm_le_M x, one_le_M y, norm_nonneg x]
        · nlinarith [norm_le_M y, one_le_M x, norm_nonneg y]
      rw [div_le_div_iff₀ (mul_pos (pow_pos hx 2) (pow_pos hy 2)) (mul_pos hx hy)]
      nlinarith [mul_le_mul_of_nonneg_right key (mul_pos hx hy).le]

theorem uniformEquicontinuous_sq :
    UniformEquicontinuous (fun n : ℕ => (act (sqFun : RatFunc K))^[n]) :=
  LipschitzWith.uniformEquicontinuous _ 1 fun n => by simpa using lipschitz_sq.iterate n

theorem fatouSet_sq : fatouSet (sqFun : RatFunc K) = univ := by
  ext x
  simp only [mem_univ, iff_true]
  exact ⟨univ, univ_mem, uniformEquicontinuous_sq.equicontinuous.equicontinuousOn _⟩

theorem juliaSet_sq : juliaSet (sqFun : RatFunc K) = ∅ := by
  simp [juliaSet, fatouSet_sq]

theorem juliaSetPt_sq : juliaSetPt (sqFun : RatFunc K) = ∅ := by
  ext x
  simp only [juliaSetPt, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
  exact uniformEquicontinuous_sq.equicontinuous x

theorem repelling_sq : repelling (sqFun : RatFunc K) = ∅ := by
  ext x
  simp only [repelling, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and,
    not_lt]
  intro n hn hper
  have h2 : 1 < 2 ^ n := Nat.one_lt_two_pow hn.ne'
  cases x with
  | infty =>
    have e : (fun w => toK (inv ((act (sqFun : RatFunc K))^[n] (inv (aff w))))) =
        fun w : K => w ^ 2 ^ n := by
      funext w
      rw [act_sqFun]
      by_cases hw : w = 0
      · subst hw
        simp [inv, toK, sq_iterate_infty, zero_pow (pow_ne_zero n two_ne_zero)]
      · simp [inv, toK, hw, sq_iterate, inv_pow]
    show ‖deriv _ 0‖ ≤ 1
    rw [e, deriv_pow_field, zero_pow (by omega), mul_zero, norm_zero]
    exact zero_le_one
  | aff z =>
    have e : (fun w => toK ((act (sqFun : RatFunc K))^[n] (aff w))) = fun w : K => w ^ 2 ^ n := by
      funext w
      rw [act_sqFun, sq_iterate]
      rfl
    have hz : z ^ 2 ^ n = z := by
      rw [Function.IsPeriodicPt, Function.IsFixedPt, act_sqFun, sq_iterate] at hper
      exact P1.aff.inj hper
    have hz1 : ‖z‖ ≤ 1 := by
      by_contra! h
      have := pow_lt_pow_right₀ h h2
      rw [pow_one, ← norm_pow, hz] at this
      exact lt_irrefl _ this
    show ‖deriv _ z‖ ≤ 1
    rw [e, deriv_pow_field, norm_mul, norm_pow]
    have := IsUltrametricDist.norm_natCast_le_one K (2 ^ n)
    have := pow_le_one₀ (norm_nonneg z) hz1 (n := 2 ^ n - 1)
    nlinarith [norm_nonneg ((2 ^ n : ℕ) : K), norm_nonneg z, pow_nonneg (norm_nonneg z) (2 ^ n - 1)]

theorem juliaRep_sq : juliaRep (sqFun : RatFunc K) = ∅ := by
  simp [juliaRep, repelling_sq]

end Dynamics

/-! ## The conjecture fails -/

section Conjecture

variable {K : Type*} [NontriviallyNormedField K]

/-- The conjecture for a reading `J` of the Julia set, with Fatou set `(J φ)ᶜ`: for every
rational function `φ ∈ K(X)` of degree `≥ 1`, the Fatou set is open and completely invariant,
and `J φ` is nonempty iff `deg φ ≥ 2`. -/
def Conjecture (J : RatFunc K → Set (P1 K)) : Prop :=
  ∀ φ : RatFunc K, 1 ≤ deg φ →
    (IsOpen (J φ)ᶜ ∧ act φ ⁻¹' (J φ)ᶜ = (J φ)ᶜ ∧ act φ '' (J φ)ᶜ = (J φ)ᶜ) ∧
    ((J φ).Nonempty ↔ 2 ≤ deg φ)

/-- The degree-1 map alone refutes the conjecture for any reading containing its point `0`. -/
theorem not_conjecture {c : K} (hc0 : c ≠ 0) (J : RatFunc K → Set (P1 K))
    (hJ : aff 0 ∈ J (linFun c)) : ¬ Conjecture J := fun h => by
  have := (h (linFun c) (by rw [deg_linFun hc0])).2.mp ⟨_, hJ⟩
  rw [deg_linFun hc0] at this
  omega

variable [IsUltrametricDist K]

/-- Both directions of `J ≠ ∅ ↔ deg ≥ 2` fail, for each of the three readings. -/
theorem both_directions_fail {c : K} (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1) :
    (deg (sqFun : RatFunc K) = 2 ∧ juliaSet (sqFun : RatFunc K) = ∅ ∧
      juliaSetPt (sqFun : RatFunc K) = ∅ ∧ juliaRep (sqFun : RatFunc K) = ∅) ∧
    (deg (linFun c) = 1 ∧ aff 0 ∈ juliaSet (linFun c) ∧ aff 0 ∈ juliaSetPt (linFun c) ∧
      aff 0 ∈ juliaRep (linFun c)) :=
  ⟨⟨deg_sqFun, juliaSet_sq, juliaSetPt_sq, juliaRep_sq⟩,
    ⟨deg_linFun hc0, zero_mem_juliaSet_lin hc0 hc1, zero_mem_juliaSetPt_lin hc0 hc1,
      zero_mem_juliaRep_lin hc0 hc1⟩⟩

lemma padic_p_ne_zero (p : ℕ) [Fact p.Prime] : (p : ℚ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

lemma padic_norm_p_lt_one (p : ℕ) [Fact p.Prime] : ‖(p : ℚ_[p])‖ < 1 := by
  rw [Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- **Main theorem.** For every prime `p`, the conjecture over `ℚ_[p]` is false under each of the
three readings of the Julia set; moreover `z ↦ z / p` (degree 1) has a nonempty Julia set and
`z ↦ z ^ 2` (degree 2) has an empty one, under each reading. -/
theorem conjecture751_false (p : ℕ) [Fact p.Prime] :
    (¬ Conjecture (juliaSet (K := ℚ_[p])) ∧ ¬ Conjecture (juliaSetPt (K := ℚ_[p])) ∧
      ¬ Conjecture (juliaRep (K := ℚ_[p]))) ∧
    (∃ φ : RatFunc ℚ_[p], deg φ = 1 ∧ (juliaSet φ).Nonempty ∧ (juliaSetPt φ).Nonempty ∧
      (juliaRep φ).Nonempty) ∧
    (∃ φ : RatFunc ℚ_[p], deg φ = 2 ∧ juliaSet φ = ∅ ∧ juliaSetPt φ = ∅ ∧ juliaRep φ = ∅) := by
  obtain ⟨h2, h1⟩ := both_directions_fail (padic_p_ne_zero p) (padic_norm_p_lt_one p)
  exact ⟨⟨not_conjecture (padic_p_ne_zero p) _ h1.2.1,
      not_conjecture (padic_p_ne_zero p) _ h1.2.2.1, not_conjecture (padic_p_ne_zero p) _ h1.2.2.2⟩,
    ⟨_, h1.1, ⟨_, h1.2.1⟩, ⟨_, h1.2.2.1⟩, ⟨_, h1.2.2.2⟩⟩, ⟨_, h2⟩⟩

/-- The same over `ℂ_[p]` (classical `ℙ¹(ℂ_p)`), for the same two maps `z ↦ z / p`, `z ↦ z ^ 2`. -/
theorem conjecture751_false_Cp (p : ℕ) [Fact p.Prime] :
    (¬ Conjecture (juliaSet (K := ℂ_[p])) ∧ ¬ Conjecture (juliaSetPt (K := ℂ_[p])) ∧
      ¬ Conjecture (juliaRep (K := ℂ_[p]))) ∧
    (∃ φ : RatFunc ℂ_[p], deg φ = 2 ∧ juliaSet φ = ∅ ∧ juliaSetPt φ = ∅ ∧ juliaRep φ = ∅) := by
  have e : ‖(p : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := by
    rw [← PadicComplex.norm_extends']; norm_cast
  have h0 : (p : ℂ_[p]) ≠ 0 := by
    rw [← norm_ne_zero_iff, e, norm_ne_zero_iff]; exact padic_p_ne_zero p
  obtain ⟨h2, h1⟩ := both_directions_fail h0 (e ▸ padic_norm_p_lt_one p)
  exact ⟨⟨not_conjecture h0 _ h1.2.1, not_conjecture h0 _ h1.2.2.1, not_conjecture h0 _ h1.2.2.2⟩,
    ⟨_, h2⟩⟩

end Conjecture

end C751
