import Mathlib

/-!
# Conjecture 00000002684 (DML intersection count polynomial law): a disproof

The conjecture claims that the number of intersection points of an orbit with a codimension-`r`
subvariety, counted along the iterates up to `n`, is (bounded above by) a degree-`r` polynomial in
`log n`, with coefficients explicit in the degree vector of the subvariety.

For every `r ≥ 1` we give a polynomial self-map `f` of affine `(r+1)`-space over `ℚ`, a point `x₀`
and a codimension-`r` affine-linear subvariety `V` (zero locus of `r` degree-one equations) such that
the orbit meets `V` exactly at the even times. The hit count up to `N` is at least `N/2`, which is
eventually larger than `P(log N)` for EVERY real polynomial `P`, of any degree and with any
coefficients. A second family (finite intersections) refutes the equality reading and the reading in
which the coefficients depend only on the subvariety.
-/

open Filter Real MvPolynomial

namespace Conjecture2684

/-! ## Objects -/

/-- Affine `(r+1)`-space over `ℚ`. The last coordinate `Fin.last r` is called `z`. -/
abbrev Aff (r : ℕ) := Fin (r + 1) → ℚ

/-- The polynomial self-map of affine space given by a tuple of polynomials. -/
noncomputable def polyMap {m : ℕ} (F : Fin m → MvPolynomial (Fin m) ℚ) :
    (Fin m → ℚ) → (Fin m → ℚ) :=
  fun p i => eval p (F i)

open Classical in
/-- The hitting times `n ≤ N` of the orbit of `x₀` under `f` in `V`. -/
noncomputable def hitTimes {X : Type*} (f : X → X) (x₀ : X) (V : Set X) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => f^[n] x₀ ∈ V)

open Classical in
/-- The (distinct) intersection points of the orbit segment `x₀, f x₀, ..., f^[N] x₀` with `V`. -/
noncomputable def hitPoints {X : Type*} (f : X → X) (x₀ : X) (V : Set X) (N : ℕ) : Finset X :=
  ((Finset.range (N + 1)).image (fun n => f^[n] x₀)).filter (· ∈ V)

open Classical in
lemma mem_hitTimes {X : Type*} (f : X → X) (x₀ : X) (V : Set X) (N n : ℕ) :
    n ∈ hitTimes f x₀ V N ↔ n ≤ N ∧ f^[n] x₀ ∈ V := by
  unfold hitTimes
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

open Classical in
lemma card_hitPoints_of_injective {X : Type*} (f : X → X) (x₀ : X) (V : Set X) (N : ℕ)
    (h : Function.Injective (fun n => f^[n] x₀)) :
    (hitPoints f x₀ V N).card = (hitTimes f x₀ V N).card := by
  unfold hitPoints hitTimes
  rw [Finset.filter_image, Finset.card_image_of_injective _ h]

/-! ## The asymptotic lemma: `P(log N) ≤ N/4` eventually, for every real polynomial `P` -/

lemma eval_log_isLittleO (P : Polynomial ℝ) :
    (fun x : ℝ => P.eval (Real.log x)) =o[atTop] id := by
  have h : (fun x : ℝ => P.eval (Real.log x)) =
      fun x => ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * Real.log x ^ i := by
    funext x; rw [Polynomial.eval_eq_sum_range]
  rw [h]
  refine Asymptotics.IsLittleO.fun_sum fun i _ => ?_
  exact (Real.isLittleO_pow_log_id_atTop).const_mul_left _

lemma eventually_eval_log_le (P : Polynomial ℝ) :
    ∀ᶠ N : ℕ in atTop, P.eval (Real.log N) ≤ (N : ℝ) / 4 := by
  have h1 := (eval_log_isLittleO P).def (c := 1 / 4) (by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h1] with N hN
  simp only [id, Real.norm_eq_abs, Nat.abs_cast] at hN
  linarith [le_abs_self (P.eval (Real.log N))]

/-- No polynomial in `log N` eventually bounds a count that is at least `N/2`. -/
lemma not_eventually_le_of_half (c : ℕ → ℝ) (hc : ∀ N : ℕ, (N : ℝ) / 2 ≤ c N)
    (P : Polynomial ℝ) : ¬ ∀ᶠ N : ℕ in atTop, c N ≤ P.eval (Real.log N) := by
  intro h
  obtain ⟨N, hN⟩ := (h.and ((eventually_eval_log_le P).and (eventually_ge_atTop 1))).exists
  obtain ⟨h1, h2, h3⟩ := hN
  have h4 : (1 : ℝ) ≤ N := by exact_mod_cast h3
  have := hc N
  linarith

/-! ## Vertical lines are irreducible subvarieties of codimension `r` -/

section Lines

variable {r : ℕ}

/-- The vertical line through `c`: all coordinates except `z` are fixed. -/
def line (c : Aff r) : Set (Aff r) := {p | ∀ i : Fin (r + 1), i ≠ Fin.last r → p i = c i}

/-- The point of `line c` with `z = t`. -/
def pt (c : Aff r) (t : ℚ) : Aff r := fun i => if i = Fin.last r then t else c i

/-- Restriction of polynomials to `line c`, as polynomials in `z`. -/
noncomputable def restr (c : Aff r) : MvPolynomial (Fin (r + 1)) ℚ →ₐ[ℚ] Polynomial ℚ :=
  aeval (fun i => if i = Fin.last r then Polynomial.X else Polynomial.C (c i))

lemma eval_restr (c : Aff r) (t : ℚ) (p : MvPolynomial (Fin (r + 1)) ℚ) :
    (restr c p).eval t = eval (pt c t) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [restr]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, eval_X]
    simp only [restr, aeval_X, pt]
    split_ifs <;> simp

lemma restr_surjective (c : Aff r) : Function.Surjective (restr c) := by
  have h : (restr c).comp (Polynomial.aeval (X (Fin.last r))) = AlgHom.id ℚ (Polynomial ℚ) :=
    Polynomial.algHom_ext (by simp [restr])
  intro q
  exact ⟨Polynomial.aeval (X (Fin.last r)) q, by simpa using congrArg (fun φ => φ q) h⟩

lemma ker_restr (c : Aff r) : RingHom.ker (restr c) = vanishingIdeal ℚ (line c) := by
  ext p
  rw [RingHom.mem_ker, mem_vanishingIdeal_iff]
  constructor
  · intro h x hx
    have hx' : x = pt c (x (Fin.last r)) := by
      funext i; by_cases hi : i = Fin.last r
      · subst hi; simp [pt]
      · simp [pt, hi, hx i hi]
    change eval x p = 0
    rw [hx', ← eval_restr, h, Polynomial.eval_zero]
  · intro h
    apply Polynomial.funext
    intro t
    rw [eval_restr, Polynomial.eval_zero]
    apply h
    intro i hi
    simp [pt, hi]

/-- The `r` degree-one equations `xᵢ - cᵢ` (`i ≠ z`) of `line c`. -/
noncomputable def eqns (c : Aff r) : Fin r → MvPolynomial (Fin (r + 1)) ℚ :=
  fun j => X (Fin.castSucc j) - C (c (Fin.castSucc j))

/-- The degree vector of `line c`: `r` equations, each of total degree `1`. -/
theorem eqns_totalDegree (c : Aff r) (j : Fin r) : (eqns c j).totalDegree = 1 := by
  unfold eqns
  rw [sub_eq_add_neg, ← map_neg, totalDegree_add_eq_left_of_totalDegree_lt] <;>
    simp [totalDegree_X]

/-- `line c` is the zero locus of its `r` equations. -/
theorem zeroLocus_eqns (c : Aff r) : zeroLocus ℚ (Ideal.span (Set.range (eqns c))) = line c := by
  ext p
  rw [zeroLocus_span]
  simp only [Set.forall_mem_range, eqns, map_sub, aeval_X, aeval_C, sub_eq_zero,
    Set.mem_ofPred_eq, Algebra.algebraMap_self, RingHom.id_apply]
  constructor
  · intro h i hi
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    exact h j
  · intro h j
    exact h _ (Fin.castSucc_ne_last j)

/-- The vanishing ideal of `line c` is prime, so `line c` is an irreducible closed subvariety. -/
theorem line_isPrime (c : Aff r) : (vanishingIdeal ℚ (line c)).IsPrime := by
  rw [← ker_restr]
  exact RingHom.ker_isPrime _

/-- The coordinate ring of `line c` has Krull dimension `1`. -/
theorem line_dim (c : Aff r) :
    ringKrullDim (MvPolynomial (Fin (r + 1)) ℚ ⧸ vanishingIdeal ℚ (line c)) = 1 := by
  rw [← ker_restr, show RingHom.ker (restr c) = RingHom.ker (restr c).toRingHom from rfl,
    ringKrullDim_eq_of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (f := (restr c).toRingHom) (restr_surjective c)),
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  rfl

/-- The ambient affine space `𝔸^{r+1}_ℚ` has dimension `r + 1`; so `line c` has codimension `r`. -/
theorem ambient_dim : ringKrullDim (MvPolynomial (Fin (r + 1)) ℚ) = r + 1 := by
  simp [ringKrullDim_eq_zero_of_field]

end Lines

/-! ## Witness 1 (infinite intersection): `f(x, z) = (-x₁, x₂, ..., x_r, z + 1)` -/

section Witness

variable (r : ℕ)

/-- Defining polynomials: `z ↦ z + 1`, `x₁ ↦ -x₁` (coordinate `0`), `xᵢ ↦ xᵢ` otherwise. -/
noncomputable def F : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℚ :=
  fun i => if i = Fin.last r then X i + 1 else if i = 0 then -X i else X i

/-- The polynomial self-map `f` of `𝔸^{r+1}_ℚ`. -/
noncomputable def f : Aff r → Aff r := polyMap (F r)

/-- The starting point `x₀ = (1, 0, ..., 0; z = 0)`. -/
def x₀ : Aff r := fun i => if i = 0 then 1 else 0

/-- The subvariety `V = {x₁ = 1, x₂ = ... = x_r = 0}`, the zero locus of `eqns (x₀ r)`. -/
noncomputable def V : Set (Aff r) := zeroLocus ℚ (Ideal.span (Set.range (eqns (x₀ r))))

lemma f_apply (p : Aff r) (i : Fin (r + 1)) :
    f r p i = if i = Fin.last r then p i + 1 else if i = 0 then -p i else p i := by
  unfold f polyMap F
  split_ifs <;> simp

lemma mem_V_iff (p : Aff r) : p ∈ V r ↔ ∀ i : Fin (r + 1), i ≠ Fin.last r → p i = x₀ r i := by
  unfold V; rw [zeroLocus_eqns]; rfl

variable {r}

lemma zero_ne_last (hr : 1 ≤ r) : (0 : Fin (r + 1)) ≠ Fin.last r := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- The orbit: `fⁿ(x₀) = ((-1)ⁿ, 0, ..., 0; z = n)`. -/
lemma orbit (hr : 1 ≤ r) (n : ℕ) (i : Fin (r + 1)) :
    (f r)^[n] (x₀ r) i = if i = Fin.last r then (n : ℚ) else if i = 0 then (-1) ^ n else 0 := by
  induction n generalizing i with
  | zero =>
    by_cases hi : i = Fin.last r
    · subst hi; simp [x₀, (zero_ne_last hr).symm]
    · simp [x₀, hi]
  | succ n ih =>
    rw [Function.iterate_succ_apply', f_apply]
    simp only [ih]
    by_cases hi : i = Fin.last r
    · simp [hi]
    · by_cases h0 : i = 0
      · subst h0; simp [zero_ne_last hr, pow_succ]
      · simp [hi, h0]

/-- The orbit meets `V` exactly at the even times (a single arithmetic progression, as DML says). -/
theorem mem_V_iff_even (hr : 1 ≤ r) (n : ℕ) : (f r)^[n] (x₀ r) ∈ V r ↔ Even n := by
  rw [mem_V_iff]
  constructor
  · intro h
    have := h 0 (zero_ne_last hr)
    rw [orbit hr] at this
    simp only [zero_ne_last hr, if_false, if_true, x₀] at this
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp this
  · intro h i hi
    rw [orbit hr]
    simp only [hi, if_false, x₀]
    split_ifs
    · exact h.neg_one_pow
    · rfl

/-- The orbit is injective (no periodicity), read off from the `z`-coordinate. -/
theorem orbit_injective (hr : 1 ≤ r) : Function.Injective (fun n => (f r)^[n] (x₀ r)) := by
  intro m n h
  have := congrFun h (Fin.last r)
  simp only [orbit hr, if_true] at this
  exact_mod_cast this

/-- `V` is not `f`-invariant, and the orbit is not contained in `V`. -/
theorem nondegenerate (hr : 1 ≤ r) : x₀ r ∈ V r ∧ f r (x₀ r) ∉ V r := by
  have h0 := mem_V_iff_even hr 0
  have h1 := mem_V_iff_even hr 1
  simp only [Function.iterate_zero, id, Function.iterate_one] at h0 h1
  exact ⟨h0.mpr ⟨0, rfl⟩, fun h => by simpa using h1.mp h⟩

lemma half_le_card_hitTimes (hr : 1 ≤ r) (N : ℕ) :
    (N : ℝ) / 2 ≤ ((hitTimes (f r) (x₀ r) (V r) N).card : ℝ) := by
  have hsub : (Finset.range (N / 2 + 1)).image (fun k => 2 * k) ⊆ hitTimes (f r) (x₀ r) (V r) N := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_range] at hk
    rw [mem_hitTimes, mem_V_iff_even hr]
    exact ⟨by omega, even_two_mul k⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range] at hc
  have hc' : ((N / 2 + 1 : ℕ) : ℝ) ≤ ((hitTimes (f r) (x₀ r) (V r) N).card : ℝ) := by
    exact_mod_cast hc
  have hd : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
    have : N ≤ 2 * (N / 2) + 1 := by omega
    exact_mod_cast this
  push_cast at hc'
  linarith

/-- **Main theorem (upper-bound reading).** For every `r ≥ 1` and every real polynomial `P`
(any degree, any coefficients), the number of intersection points of the orbit segment
`x₀, ..., f^N(x₀)` with the codimension-`r` subvariety `V` is NOT eventually `≤ P(log N)`;
the same holds for the number of hitting times. -/
theorem conjecture2684_false (hr : 1 ≤ r) (P : Polynomial ℝ) :
    ¬ (∀ᶠ N : ℕ in atTop,
        ((hitPoints (f r) (x₀ r) (V r) N).card : ℝ) ≤ P.eval (Real.log N)) ∧
    ¬ (∀ᶠ N : ℕ in atTop,
        ((hitTimes (f r) (x₀ r) (V r) N).card : ℝ) ≤ P.eval (Real.log N)) := by
  have hcard := fun N => card_hitPoints_of_injective (f r) (x₀ r) (V r) N (orbit_injective hr)
  refine ⟨?_, not_eventually_le_of_half _ (half_le_card_hitTimes hr) P⟩
  refine not_eventually_le_of_half _ (fun N => ?_) P
  rw [hcard]
  exact half_le_card_hitTimes hr N

/-- **Corollary (degree-`r` readings).** No degree-`r` real polynomial `P` satisfies
`#(orbit ∩ V up to N) ≤ P(log N)` for all `N ≥ 1`, and none satisfies `=` for all `N ≥ 1`. -/
theorem conjecture2684_false_degree (hr : 1 ≤ r) :
    (¬ ∃ P : Polynomial ℝ, P.natDegree = r ∧ ∀ N : ℕ, 1 ≤ N →
        ((hitPoints (f r) (x₀ r) (V r) N).card : ℝ) ≤ P.eval (Real.log N)) ∧
    (¬ ∃ P : Polynomial ℝ, P.natDegree = r ∧ ∀ N : ℕ, 1 ≤ N →
        ((hitPoints (f r) (x₀ r) (V r) N).card : ℝ) = P.eval (Real.log N)) :=
  ⟨fun ⟨P, _, hP⟩ => (conjecture2684_false hr P).1 (eventually_atTop.mpr ⟨1, hP⟩),
   fun ⟨P, _, hP⟩ => (conjecture2684_false hr P).1
     (eventually_atTop.mpr ⟨1, fun N hN => (hP N hN).le⟩)⟩

/-- **Headline.** For every `r ≥ 1` there are a polynomial self-map `polyMap F` of `𝔸^{r+1}_ℚ`, a
point `x`, and `r` equations `E` of total degree `1` whose zero locus `V` is an irreducible
subvariety (prime vanishing ideal) with coordinate ring of Krull dimension `1` (codimension `r`
in `𝔸^{r+1}`), such that the orbit meets `V` infinitely often and, for EVERY real polynomial `P`,
the number of intersection points up to iterate `N` is not eventually `≤ P(log N)`. -/
theorem conjecture2684_disproof (hr : 1 ≤ r) :
    ∃ (F : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℚ) (x : Aff r)
      (E : Fin r → MvPolynomial (Fin (r + 1)) ℚ),
      (∀ j, (E j).totalDegree = 1) ∧
      (vanishingIdeal ℚ (zeroLocus ℚ (Ideal.span (Set.range E)))).IsPrime ∧
      ringKrullDim (MvPolynomial (Fin (r + 1)) ℚ ⧸
        vanishingIdeal ℚ (zeroLocus ℚ (Ideal.span (Set.range E)))) = 1 ∧
      ringKrullDim (MvPolynomial (Fin (r + 1)) ℚ) = r + 1 ∧
      {n : ℕ | (polyMap F)^[n] x ∈ zeroLocus ℚ (Ideal.span (Set.range E))}.Infinite ∧
      ∀ P : Polynomial ℝ, ¬ ∀ᶠ N : ℕ in atTop,
        ((hitPoints (polyMap F) x (zeroLocus ℚ (Ideal.span (Set.range E))) N).card : ℝ) ≤
          P.eval (Real.log N) := by
  have hV : zeroLocus ℚ (Ideal.span (Set.range (eqns (x₀ r)))) = V r := rfl
  refine ⟨F r, x₀ r, eqns (x₀ r), eqns_totalDegree _, ?_, ?_, ambient_dim, ?_,
    fun P => (conjecture2684_false hr P).1⟩
  · rw [zeroLocus_eqns]; exact line_isPrime _
  · rw [zeroLocus_eqns]; exact line_dim _
  · have : {n : ℕ | (polyMap (F r))^[n] (x₀ r) ∈ V r} = {n | Even n} := by
      ext n; exact mem_V_iff_even hr n
    rw [hV, this]
    exact Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 * k)
      (fun a b h => by simpa using h) (fun k => even_two_mul k)

end Witness

/-! ## Witness 2 (finite intersections): `g_K(x, z) = (∏_{j<K-1} (z - j), x₂, ..., x_r, z + 1)` -/

section Finite

variable (r : ℕ)

/-- Defining polynomials of `g_K`: `z ↦ z + 1`, `x₁ ↦ ∏_{j<K-1} (z - j)`, `xᵢ ↦ xᵢ` otherwise. -/
noncomputable def G (K : ℕ) : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ℚ :=
  fun i => if i = Fin.last r then X i + 1
    else if i = 0 then ∏ j ∈ Finset.range (K - 1), (X (Fin.last r) - C (j : ℚ)) else X i

/-- The polynomial self-map `g_K` of `𝔸^{r+1}_ℚ`. -/
noncomputable def g (K : ℕ) : Aff r → Aff r := polyMap (G r K)

/-- The `z`-axis `W = {x₁ = ... = x_r = 0}` (the line through `0`), zero locus of `eqns 0`. -/
noncomputable def W : Set (Aff r) := zeroLocus ℚ (Ideal.span (Set.range (eqns (0 : Aff r))))

lemma g_apply (K : ℕ) (p : Aff r) (i : Fin (r + 1)) :
    g r K p i = if i = Fin.last r then p i + 1
      else if i = 0 then ∏ j ∈ Finset.range (K - 1), (p (Fin.last r) - j) else p i := by
  unfold g polyMap G
  split_ifs <;> simp

lemma mem_W_iff (p : Aff r) : p ∈ W r ↔ ∀ i : Fin (r + 1), i ≠ Fin.last r → p i = 0 := by
  unfold W; rw [zeroLocus_eqns]; rfl

variable {r}

lemma g_orbit_last (K n : ℕ) : (g r K)^[n] 0 (Fin.last r) = n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', g_apply, if_pos rfl, ih]; push_cast; ring

lemma g_orbit_other (K n : ℕ) (i : Fin (r + 1)) (hi : i ≠ Fin.last r) (h0 : i ≠ 0) :
    (g r K)^[n] 0 i = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', g_apply, if_neg hi, if_neg h0, ih]

lemma g_orbit_zero (hr : 1 ≤ r) (K n : ℕ) :
    (g r K)^[n + 1] 0 0 = ∏ j ∈ Finset.range (K - 1), ((n : ℚ) - j) := by
  rw [Function.iterate_succ_apply', g_apply, if_neg (zero_ne_last hr), if_pos rfl, g_orbit_last]

/-- The orbit of `0` under `g_K` meets `W` exactly at the times `n < K` (finitely many). -/
theorem g_mem_W_iff (hr : 1 ≤ r) {K : ℕ} (hK : 1 ≤ K) (n : ℕ) :
    (g r K)^[n] 0 ∈ W r ↔ n < K := by
  rw [mem_W_iff]
  cases n with
  | zero =>
    simp only [Function.iterate_zero, id, Pi.zero_apply, implies_true, true_iff]
    omega
  | succ m =>
    constructor
    · intro h
      have := h 0 (zero_ne_last hr)
      rw [g_orbit_zero hr, Finset.prod_eq_zero_iff] at this
      obtain ⟨j, hj, hj0⟩ := this
      rw [sub_eq_zero, Nat.cast_inj] at hj0
      rw [Finset.mem_range] at hj
      omega
    · intro h i hi
      by_cases h0 : i = 0
      · subst h0
        rw [g_orbit_zero hr, Finset.prod_eq_zero_iff]
        exact ⟨m, Finset.mem_range.mpr (by omega), sub_self _⟩
      · exact g_orbit_other K _ i hi h0

theorem g_orbit_injective (K : ℕ) : Function.Injective (fun n => (g r K)^[n] (0 : Aff r)) := by
  intro m n h
  have := congrFun h (Fin.last r)
  simp only [g_orbit_last] at this
  exact_mod_cast this

/-- The intersection of the orbit with `W` is finite: the return times are `{0, ..., K-1}`. -/
theorem g_returns (hr : 1 ≤ r) {K : ℕ} (hK : 1 ≤ K) :
    {n : ℕ | (g r K)^[n] 0 ∈ W r} = Set.Iio K := by
  ext n; simp [g_mem_W_iff hr hK]

lemma g_card (hr : 1 ≤ r) {K : ℕ} (hK : 1 ≤ K) {N : ℕ} (hN : K ≤ N + 1) :
    (hitPoints (g r K) 0 (W r) N).card = K := by
  rw [card_hitPoints_of_injective _ _ _ _ (g_orbit_injective K)]
  have : hitTimes (g r K) 0 (W r) N = Finset.range K := by
    ext n
    rw [mem_hitTimes, g_mem_W_iff hr hK, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

/-- **Equality reading, finite case.** If the count is eventually `P(log N)`, then `P` is the
constant `K`; in particular `P` does not have degree `r ≥ 1`. -/
theorem finite_eq_reading (hr : 1 ≤ r) {K : ℕ} (hK : 1 ≤ K) (P : Polynomial ℝ)
    (hP : ∀ᶠ N : ℕ in atTop, ((hitPoints (g r K) 0 (W r) N).card : ℝ) = P.eval (Real.log N)) :
    P = Polynomial.C (K : ℝ) ∧ P.natDegree ≠ r := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hP
  have hval : ∀ n : ℕ, P.eval (Real.log ((n + N₀ + K : ℕ) : ℝ)) = K := by
    intro n
    rw [← hN₀ _ (by omega), g_card hr hK (by omega)]
  have hpos : ∀ m : ℕ, (0 : ℝ) < ((m + N₀ + K : ℕ) : ℝ) := fun m => by positivity
  have hinj : Function.Injective (fun n : ℕ => Real.log ((n + N₀ + K : ℕ) : ℝ)) := fun a b hab => by
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (hpos a)) (Set.mem_Ioi.mpr (hpos b)) hab
    have := (Nat.cast_inj (R := ℝ)).mp this
    omega
  have hEq : P = Polynomial.C (K : ℝ) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective hinj)
    rintro x ⟨n, rfl⟩
    simp only [Set.mem_ofPred_eq, Polynomial.eval_C]
    exact hval n
  refine ⟨hEq, ?_⟩
  rw [hEq, Polynomial.natDegree_C]
  omega

/-- **Uniform upper bound, finite case.** No single real polynomial `P` (whose coefficients may
depend on the subvariety `W`, hence on its degree vector, but not on the map) satisfies
`#(orbit of 0 under g_K ∩ W up to N) ≤ P(log N)` for all `K ≥ 1` and all `N ≥ 1`, although every
one of these orbits meets `W` in only finitely many points. -/
theorem finite_uniform_bound_false (hr : 1 ≤ r) (P : Polynomial ℝ) :
    ¬ ∀ K : ℕ, 1 ≤ K → ∀ N : ℕ, 1 ≤ N →
      ((hitPoints (g r K) 0 (W r) N).card : ℝ) ≤ P.eval (Real.log N) := by
  intro h
  obtain ⟨N, hN1, hN2⟩ := ((eventually_eval_log_le P).and (eventually_ge_atTop 1)).exists
  have := h (N + 1) (by omega) N hN2
  rw [g_card hr (by omega) le_rfl] at this
  push_cast at this
  have h4 : (0 : ℝ) ≤ N := by positivity
  linarith

end Finite

end Conjecture2684
