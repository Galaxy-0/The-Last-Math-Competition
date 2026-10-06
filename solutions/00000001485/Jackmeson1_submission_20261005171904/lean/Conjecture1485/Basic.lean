import Mathlib

/-!
# Conjecture 00000001485 is false: the cat-map suspension has zeta radius `≤ 1/2`
Arnold's cat map `A = [[2,1],[1,1]]` on `T² = ℝ²/ℤ²` is hyperbolic, `#Fix(catⁿ) = |det(Aⁿ - I)|
≥ 2ⁿ - 1`, the closed orbits of its suspension flow are its periodic orbits, and the zeta function
`ζ(z) = ∏_τ (1 - z^{|τ|})⁻¹` (product over periodic orbits) has radius of convergence `≤ 1/2`.
-/

open Matrix PowerSeries

namespace C1485

/-! ## The torus `ℝ²/ℤ²` and toral endomorphisms -/
abbrev V := Fin 2 → ℝ
/-- The coordinatewise inclusion `ℤ² → ℝ²`. -/
def icast : (Fin 2 → ℤ) →+ V := AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)
lemma icast_injective : Function.Injective icast := fun v w h =>
  funext fun i => by simpa [icast] using congrFun h i
/-- The integer lattice `ℤ² ⊂ ℝ²`. -/
def Lat : AddSubgroup V := icast.range
/-- The 2-torus `T² = ℝ²/ℤ²`. -/
abbrev Torus := V ⧸ Lat
/-- An integer matrix viewed as a real matrix. -/
abbrev rl (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ := M.map (Int.cast)
lemma rl_mulVec_icast (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) :
    rl M *ᵥ icast v = icast (M *ᵥ v) := by
  ext i; exact ((Int.castRingHom ℝ).map_mulVec M v i).symm
/-- The endomorphism `x ↦ M x (mod ℤ²)` of the torus induced by an integer matrix `M`. -/
noncomputable def tmap (M : Matrix (Fin 2) (Fin 2) ℤ) : Torus →+ Torus :=
  QuotientAddGroup.map Lat Lat (Matrix.mulVecLin (rl M)).toAddMonoidHom (by
    rintro _ ⟨v, rfl⟩; exact ⟨M *ᵥ v, (rl_mulVec_icast M v).symm⟩)
lemma tmap_mk (M : Matrix (Fin 2) (Fin 2) ℤ) (x : V) :
    tmap M (x : Torus) = ((rl M *ᵥ x : V) : Torus) := rfl
lemma tmap_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) (x : Torus) :
    tmap (M * N) x = tmap M (tmap N x) := by
  induction x using QuotientAddGroup.induction_on with
  | H y => rw [tmap_mk, tmap_mk, tmap_mk, show rl (M * N) = rl M * rl N by
      ext i j; simp [Matrix.mul_apply], Matrix.mulVec_mulVec]
lemma tmap_one (x : Torus) : tmap 1 x = x := by
  induction x using QuotientAddGroup.induction_on with
  | H y => simp [tmap_mk]
lemma tmap_sub (M N : Matrix (Fin 2) (Fin 2) ℤ) (x : Torus) :
    tmap (M - N) x = tmap M x - tmap N x := by
  induction x using QuotientAddGroup.induction_on with
  | H y => rw [tmap_mk, tmap_mk, tmap_mk, show rl (M - N) = rl M - rl N by ext i j; simp,
      Matrix.sub_mulVec, QuotientAddGroup.mk_sub]
/-- For `det M ≠ 0`, the kernel of `x ↦ M x` on `T²` is finite with `|det M|` elements. -/
theorem card_ker_tmap (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    Nat.card (tmap M).ker = M.det.natAbs ∧ Finite (tmap M).ker := by
  have hu : IsUnit (rl M).det := by
    rw [isUnit_iff_ne_zero, show (rl M).det = (M.det : ℝ) from
      ((Int.castRingHom ℝ).map_det M).symm]; exact_mod_cast hM
  -- `ψ v = M⁻¹ v (mod ℤ²)` induces `ℤ² / M ℤ² ≃ ker (tmap M)`
  let ψ : (Fin 2 → ℤ) →+ Torus :=
    (QuotientAddGroup.mk' Lat).comp ((Matrix.mulVecLin (rl M)⁻¹).toAddMonoidHom.comp icast)
  have hψ : ∀ v, ψ v = (((rl M)⁻¹ *ᵥ icast v : V) : Torus) := fun v => rfl
  let N : Submodule ℤ (Fin 2 → ℤ) := LinearMap.range M.mulVecLin
  have hker : ψ.ker = N.toAddSubgroup := by
    ext v
    simp only [AddMonoidHom.mem_ker, hψ, QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup,
      N, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨w, hw⟩; refine ⟨w, icast_injective ?_⟩
      rw [← rl_mulVec_icast, hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, one_mulVec]
    · rintro ⟨w, rfl⟩
      exact ⟨w, by rw [← rl_mulVec_icast, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]⟩
  have hrange : ψ.range = (tmap M).ker := by
    ext x; constructor
    · rintro ⟨v, rfl⟩
      rw [AddMonoidHom.mem_ker, hψ, tmap_mk, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec,
        QuotientAddGroup.eq_zero_iff]
      exact ⟨v, rfl⟩
    · induction x using QuotientAddGroup.induction_on with
      | H y =>
        intro hx; rw [AddMonoidHom.mem_ker, tmap_mk, QuotientAddGroup.eq_zero_iff] at hx
        obtain ⟨v, hv⟩ := hx; exact ⟨v, by rw [hψ, hv, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]⟩
  have hinj : Function.Injective M.mulVecLin := fun v w h => sub_eq_zero.1
    (Matrix.eq_zero_of_mulVec_eq_zero hM (by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 h))
  -- Mathlib: `|det M| = #(ℤ² / M ℤ²)` (Smith normal form)
  have hcard : Nat.card ((Fin 2 → ℤ) ⧸ N) = M.det.natAbs := by
    rw [← Submodule.natAbs_det_equiv N (LinearEquiv.ofInjective M.mulVecLin hinj)]
    have : N.subtype ∘ₗ AddMonoidHom.toIntLinearMap
        (LinearEquiv.ofInjective M.mulVecLin hinj : (Fin 2 → ℤ) →+ N) = Matrix.toLin' M := by
      ext v i; simp
    rw [this, LinearMap.det_toLin']
  have e : ((Fin 2 → ℤ) ⧸ N.toAddSubgroup) ≃ (tmap M).ker :=
    (QuotientAddGroup.quotientAddEquivOfEq hker).symm.toEquiv.trans
      ((QuotientAddGroup.quotientKerEquivRange ψ).toEquiv.trans
      (Equiv.subtypeEquivRight (by intro x; rw [hrange])))
  have hc : Nat.card (tmap M).ker = M.det.natAbs := (Nat.card_congr e).symm.trans hcard
  exact ⟨hc, Nat.finite_of_card_ne_zero (by rw [hc]; exact Int.natAbs_ne_zero.2 hM)⟩

/-! ## The cat map and hyperbolicity -/
/-- A toral automorphism `M ∈ GL(2,ℤ)` is hyperbolic if no complex eigenvalue has modulus `1`. -/
def IsHyperbolic (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  IsUnit M.det ∧
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (M.map (Int.cast : ℤ → ℂ))) μ → ‖μ‖ ≠ 1
/-- Arnold's cat map matrix `A = [[2,1],[1,1]]` and its inverse. -/
def A : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 1]
def Ainv : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; -1, 2]
lemma A_mul_Ainv : A * Ainv = 1 := by decide
lemma Ainv_mul_A : Ainv * A = 1 := by decide
lemma A_sq : A * A = 3 • A - 1 := by decide
lemma det_A : A.det = 1 := by decide
theorem A_hyperbolic : IsHyperbolic A := by
  refine ⟨by rw [det_A]; exact isUnit_one, fun μ hμ h1 => ?_⟩
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin',
    Matrix.charpoly_fin_two] at hμ
  have htr : (A.map (Int.cast : ℤ → ℂ)).trace = 3 := by simp [A, Matrix.trace_fin_two]; norm_num
  have hdet : (A.map (Int.cast : ℤ → ℂ)).det = 1 := by simp [A, Matrix.det_fin_two]; norm_num
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C, htr, hdet] at hμ
  have hre := congrArg Complex.re hμ; have him := congrArg Complex.im hμ
  simp [pow_two] at hre him
  have hn := Complex.normSq_eq_norm_sq μ
  rw [h1, Complex.normSq_apply] at hn
  rcases mul_eq_zero.1 (show μ.re * (2 * μ.re - 3) = 0 by nlinarith) with h | h
  · have : μ.im = 0 := by rw [h] at him; linarith
    rw [h, this] at hn; norm_num at hn
  · nlinarith [sq_nonneg μ.im]
/-- The cat map `x ↦ A x (mod ℤ²)`, an invertible map (group automorphism) of `T²`. -/
noncomputable def cat : Torus ≃+ Torus :=
  AddMonoidHom.toAddEquiv (tmap A) (tmap Ainv)
    (AddMonoidHom.ext fun x => by simp [← tmap_mul, Ainv_mul_A, tmap_one])
    (AddMonoidHom.ext fun x => by simp [← tmap_mul, A_mul_Ainv, tmap_one])
lemma coe_cat : (⇑cat : Torus → Torus) = ⇑(tmap A) := rfl
lemma cat_iterate (n : ℕ) (x : Torus) : (⇑cat)^[n] x = tmap (A ^ n) x := by
  induction n with
  | zero => simp [tmap_one]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', tmap_mul]; rfl
lemma trace_rec (n : ℕ) : (A ^ (n + 2)).trace = 3 * (A ^ (n + 1)).trace - (A ^ n).trace := by
  rw [show A ^ (n + 2) = 3 • A ^ (n + 1) - A ^ n by
    rw [pow_add, pow_two, A_sq, mul_sub, mul_one, mul_smul_comm, pow_succ], Matrix.trace_sub,
    Matrix.trace_smul, nsmul_eq_mul]; norm_num
lemma trace_growth (n : ℕ) :
    2 * (A ^ (n + 1)).trace ≤ (A ^ (n + 2)).trace ∧ 2 ^ (n + 1) + 1 ≤ (A ^ (n + 1)).trace := by
  induction n with
  | zero =>
    rw [trace_rec, show (A ^ 1).trace = 3 by decide, show (A ^ 0).trace = 2 by decide]; norm_num
  | succ n ih =>
    have h3 := trace_rec (n + 1)
    rw [show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring] at h3 ⊢
    have h2 : (2 : ℤ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
    have h4 : (0 : ℤ) < 2 ^ (n + 1) := by positivity
    constructor <;> linarith [ih.1, ih.2]
/-- `|det(Aⁿ - I)| = tr(Aⁿ) - 2 ≥ 2ⁿ - 1` for `n ≥ 1`. -/
lemma natAbs_det_ge (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) ^ n - 1 ≤ ((A ^ n - 1).det.natAbs : ℤ) := by
  have hd : (A ^ n - 1).det = 2 - (A ^ n).trace := by
    have h := Matrix.det_pow A n
    rw [det_A, one_pow, Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two, Matrix.trace_fin_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    linarith
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have := (trace_growth m).2
  have h4 : (0 : ℤ) < 2 ^ (m + 1) := by positivity
  rw [Int.natCast_natAbs, hd, abs_of_nonpos (by linarith)]
  linarith
/-- The periodic count `#Fix(catⁿ)` equals `|det(Aⁿ - I)|`, and `Fix(catⁿ)` is finite. -/
theorem fix_cat (n : ℕ) (hn : 1 ≤ n) :
    (Function.fixedPoints (⇑cat)^[n]).ncard = (A ^ n - 1).det.natAbs ∧
      (Function.fixedPoints (⇑cat)^[n]).Finite := by
  have hdet : (A ^ n - 1).det ≠ 0 := by
    have h1 := natAbs_det_ge n hn
    have h2 : (2 : ℤ) ^ 1 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have : (1 : ℤ) ≤ ((A ^ n - 1).det.natAbs : ℤ) := by linarith
    exact Int.natAbs_ne_zero.1 (by omega)
  have hset : Function.fixedPoints (⇑cat)^[n] = ((tmap (A ^ n - 1)).ker : Set Torus) := by
    ext x; simp [Function.mem_fixedPoints, Function.IsFixedPt, cat_iterate, tmap_sub, tmap_one,
      sub_eq_zero]
  obtain ⟨h1, h2⟩ := card_ker_tmap _ hdet
  rw [hset, ← Nat.card_coe_set_eq]
  exact ⟨h1, Set.toFinite _⟩

/-! ## Periodic orbits and the zeta function `ζ(z) = ∏_τ (1 - z^{|τ|})⁻¹` -/

section Zeta
variable {α : Type*} (f : α → α)
/-- The forward orbit `{fᵏ x : k ∈ ℕ}` of `x`. -/
def orb (x : α) : Set α := Set.range fun k : ℕ => f^[k] x
/-- The periodic orbits of `f`, i.e. the orbits of periodic points. -/
abbrev PerOrbit : Type _ := {s : Set α // ∃ x ∈ Function.periodicPts f, s = orb f x}
variable {f}
/-- The period `|τ|` of a periodic orbit `τ`: its number of points. -/
noncomputable def PerOrbit.len (τ : PerOrbit f) : ℕ := τ.1.ncard
lemma PerOrbit.len_eq (τ : PerOrbit f) {x : α} (hx : x ∈ Function.periodicPts f)
    (h : τ.1 = orb f x) : τ.len = Function.minimalPeriod f x := by
  have hpos := Function.minimalPeriod_pos_of_mem_periodicPts hx
  have : orb f x = (fun k => f^[k] x) '' Set.Iio (Function.minimalPeriod f x) := by
    ext y; constructor
    · rintro ⟨k, rfl⟩; exact ⟨k % _, Nat.mod_lt _ hpos, Function.iterate_mod_minimalPeriod_eq⟩
    · rintro ⟨k, -, rfl⟩; exact ⟨k, rfl⟩
  rw [PerOrbit.len, h, this, Function.iterate_injOn_Iio_minimalPeriod.ncard_image,
    ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
lemma PerOrbit.len_pos (τ : PerOrbit f) : 0 < τ.len := by
  obtain ⟨x, hx, h⟩ := τ.2
  rw [τ.len_eq hx h]; exact Function.minimalPeriod_pos_of_mem_periodicPts hx
/-- If every `Fix(fᵐ)` (`m ≥ 1`) is finite, there are finitely many orbits of period `≤ k`. -/
lemma finite_orbits (hfix : ∀ m, 1 ≤ m → (Function.fixedPoints f^[m]).Finite) (k : ℕ) :
    {τ : PerOrbit f | τ.len ≤ k}.Finite := by
  refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
  refine (((Set.finite_Icc 1 k).biUnion fun m hm => hfix m hm.1).image (orb f)).subset ?_
  rintro _ ⟨τ, hτ, rfl⟩
  obtain ⟨x, hx, h⟩ := τ.2
  refine ⟨x, Set.mem_biUnion (x := Function.minimalPeriod f x)
    ⟨Function.minimalPeriod_pos_of_mem_periodicPts hx, τ.len_eq hx h ▸ hτ⟩
    (Function.isPeriodicPt_minimalPeriod f x), h.symm⟩
/-- The Euler factor `(1 - zᵖ)⁻¹` in `ℝ⟦z⟧`. -/
noncomputable def fac (p : ℕ) : ℝ⟦X⟧ := (1 - X ^ p)⁻¹
lemma cc_ne (p : ℕ) (hp : 0 < p) : constantCoeff (1 - X ^ p : ℝ⟦X⟧) ≠ 0 := by simp [hp.ne']
lemma fac_eq (p : ℕ) (hp : 0 < p) : fac p = mk fun j => if p ∣ j then 1 else 0 := by
  symm; rw [fac, PowerSeries.eq_inv_iff_mul_eq_one (cc_ne p hp)]
  ext j
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hp.ne']
  · rw [if_neg hj.ne']
    by_cases hpj : p ≤ j
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hpj
      rw [if_pos hpj, coeff_mk, Nat.add_sub_cancel_left]
      simp [Nat.dvd_add_right (dvd_refl p)]
    · rw [if_neg hpj, if_neg (fun h => hj.ne' (Nat.eq_zero_of_dvd_of_lt h (by omega)))]; simp

open scoped PowerSeries.WithPiTopology
variable (f) in
/-- The zeta function `ζ(z) = ∏_τ (1 - z^{|τ|})⁻¹`: the product over all periodic orbits `τ`,
in the coefficientwise topology of `ℝ⟦z⟧`. -/
noncomputable def zeta : ℝ⟦X⟧ := ∏' τ : PerOrbit f, fac τ.len
/-- The product defining `ζ` converges (`HasProd`), and the `k`-th coefficient of `ζ` is that of
the finite product over the orbits of period `≤ k`. -/
theorem hasProd_zeta (hfin : ∀ k, {τ : PerOrbit f | τ.len ≤ k}.Finite) :
    HasProd (fun τ : PerOrbit f => fac τ.len) (zeta f) ∧
      ∀ k, coeff k (zeta f) = coeff k (∏ τ ∈ (hfin k).toFinset, fac τ.len) := by
  classical
  have stab : ∀ k (S : Finset (PerOrbit f)), (hfin k).toFinset ⊆ S →
      coeff k (∏ τ ∈ S, fac τ.len) = coeff k (∏ τ ∈ (hfin k).toFinset, fac τ.len) := by
    intro k S hS
    -- the factors with `|τ| > k` are `≡ 1 mod z^(k+1)`
    have hdvd : X ^ (k + 1) ∣ (∏ τ ∈ S \ (hfin k).toFinset, fac τ.len) - 1 := by
      refine Finset.prod_induction _ (fun q => X ^ (k + 1) ∣ q - 1)
        (fun a b ⟨u, hu⟩ ⟨v, hv⟩ => ⟨u * b + v, by linear_combination b * hu + hv⟩) (by simp) ?_
      intro τ hτ
      simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset] at hτ
      have h := PowerSeries.mul_inv_cancel _ (cc_ne _ τ.len_pos)
      exact ⟨X ^ (τ.len - (k + 1)) * fac τ.len, by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Nat.lt_iff_add_one_le.1 (not_le.1 hτ.2)), fac]
        linear_combination h⟩
    obtain ⟨c, hc⟩ := hdvd
    rw [← Finset.prod_sdiff hS, mul_comm, show ∀ P : ℝ⟦X⟧, P * (∏ τ ∈ S \ (hfin k).toFinset,
      fac τ.len) = P + X ^ (k + 1) * (P * c) from fun P => by linear_combination P * hc,
      map_add, coeff_X_pow_mul', if_neg (by omega), add_zero]
  have hL : HasProd (fun τ : PerOrbit f => fac τ.len)
      (mk fun k => coeff k (∏ τ ∈ (hfin k).toFinset, fac τ.len)) := by
    unfold HasProd
    rw [SummationFilter.unconditional_filter, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    refine tendsto_nhds_of_eventually_eq (Filter.eventually_atTop.2 ⟨(hfin d).toFinset, ?_⟩)
    intro S hS; rw [coeff_mk]; exact stab d S hS
  have hz : zeta f = _ := hL.tprod_eq
  rw [hz]; exact ⟨hL, fun k => coeff_mk _ _⟩
/-- Nonnegativity of all coefficients. -/
def NN (p : ℝ⟦X⟧) : Prop := ∀ n, 0 ≤ coeff n p
lemma NN.add {p q : ℝ⟦X⟧} (hp : NN p) (hq : NN q) : NN (p + q) := fun n => by
  rw [map_add]; exact add_nonneg (hp n) (hq n)
lemma NN.mul {p q : ℝ⟦X⟧} (hp : NN p) (hq : NN q) : NN (p * q) := fun n => by
  rw [coeff_mul]; exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)
/-- `∏ (1 + hᵢ) ≥ 1 + ∑ hᵢ` coefficientwise when all `hᵢ` have nonnegative coefficients. -/
lemma prod_ge {ι : Type*} (S : Finset ι) (G : ι → ℝ⟦X⟧) (hG : ∀ i, NN (G i - 1)) :
    NN (∏ i ∈ S, G i - 1 - ∑ i ∈ S, (G i - 1)) ∧ NN (∏ i ∈ S, G i - 1) := by
  induction S using Finset.cons_induction with
  | empty => exact ⟨fun n => by simp, fun n => by simp⟩
  | cons a S ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    constructor
    · rw [show G a * ∏ i ∈ S, G i - 1 - (G a - 1 + ∑ i ∈ S, (G i - 1)) =
        (∏ i ∈ S, G i - 1 - ∑ i ∈ S, (G i - 1)) + (G a - 1) * (∏ i ∈ S, G i - 1) by ring]
      exact ih.1.add ((hG a).mul ih.2)
    · rw [show G a * ∏ i ∈ S, G i - 1 =
        (G a - 1) * (∏ i ∈ S, G i - 1) + (G a - 1) + (∏ i ∈ S, G i - 1) by ring]
      exact (((hG a).mul ih.2).add (hG a)).add ih.2
/-- `ζₖ ≥ #{τ : |τ| divides k}` for `k ≥ 1`. -/
theorem coeff_zeta_ge (hfin : ∀ k, {τ : PerOrbit f | τ.len ≤ k}.Finite) (k : ℕ) (hk : 1 ≤ k) :
    ((((hfin k).toFinset.filter (fun τ => τ.len ∣ k)).card : ℕ) : ℝ) ≤ coeff k (zeta f) := by
  classical
  have hNN : ∀ τ : PerOrbit f, NN (fac τ.len - 1) := fun τ n => by
    rw [fac_eq _ τ.len_pos, map_sub, coeff_mk, coeff_one]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne']; split_ifs <;> norm_num
  have h := (prod_ge (hfin k).toFinset (fun τ => fac τ.len) hNN).1 k
  rw [(hasProd_zeta hfin).2 k]
  rw [map_sub, map_sub, coeff_one, if_neg (show k ≠ 0 by omega), sub_zero, sub_nonneg,
    map_sum] at h
  refine le_trans (le_of_eq ?_) h
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [fac_eq _ τ.len_pos, map_sub, coeff_mk, coeff_one, if_neg (show k ≠ 0 by omega)]
  split_ifs <;> simp
/-- `#Fix(fᵏ) ≤ k · #{τ : |τ| divides k}`: each orbit inside `Fix(fᵏ)` has at most `k` points. -/
theorem fix_le_orbits (hfix : ∀ m, 1 ≤ m → (Function.fixedPoints f^[m]).Finite)
    (k : ℕ) (hk : 1 ≤ k) : (Function.fixedPoints f^[k]).ncard ≤
      k * ((finite_orbits hfix k).toFinset.filter (fun τ => τ.len ∣ k)).card := by
  have : DecidableEq (Set α) := Classical.decEq _
  have : DecidableEq α := Classical.decEq _
  rw [Set.ncard_eq_toFinset_card _ (hfix k hk)]
  set Fx := (hfix k hk).toFinset
  refine (Finset.card_le_mul_card_image (f := orb f) Fx k ?_).trans (Nat.mul_le_mul_left _ ?_)
  · intro O hO
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hO
    have hp : Function.IsPeriodicPt f k x0 := (hfix k hk).mem_toFinset.1 hx0
    calc (Fx.filter (fun x => orb f x = orb f x0)).card
        ≤ ((Finset.range k).image (fun j => f^[j] x0)).card := by
          refine Finset.card_le_card fun y hy => ?_
          obtain ⟨-, hy⟩ := Finset.mem_filter.1 hy
          obtain ⟨j, hj⟩ : y ∈ orb f x0 := hy ▸ ⟨0, rfl⟩
          exact Finset.mem_image.2 ⟨j % k, Finset.mem_range.2 (Nat.mod_lt _ hk),
            by rw [hp.iterate_mod_apply]; exact hj⟩
      _ ≤ k := Finset.card_image_le.trans (Finset.card_range k).le
  · have hsub : Fx.image (orb f) ⊆ ((finite_orbits hfix k).toFinset.filter
        (fun τ => τ.len ∣ k)).image Subtype.val := by
      intro O hO
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hO
      have hp : Function.IsPeriodicPt f k x := (hfix k hk).mem_toFinset.1 hx
      have hper := Function.mk_mem_periodicPts (by omega) hp
      let τ : PerOrbit f := ⟨orb f x, x, hper, rfl⟩
      have hlen : τ.len ∣ k := (τ.len_eq hper rfl) ▸ hp.minimalPeriod_dvd
      refine Finset.mem_image.2 ⟨τ, ?_, rfl⟩
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨Nat.le_of_dvd (by omega) hlen, hlen⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le

end Zeta

/-! ## Radius of convergence -/
/-- If `n · cₙ ≥ 2ⁿ - 1` for all `n ≥ 1`, the power series `∑ cₙ zⁿ` has radius `≤ 1/2`. -/
theorem radius_le_half (c : ℕ → ℝ) (hc : ∀ n, 1 ≤ n → (2 : ℝ) ^ n - 1 ≤ n * c n) :
    (FormalMultilinearSeries.ofScalars ℂ (fun n => (c n : ℂ))).radius ≤ 1 / 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1
    (lt_min hlt (by norm_num : (1 / 2 : ENNReal) < 1))
  obtain ⟨C, -, hC⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius _
    (hr2.trans_le (min_le_left _ _))
  have hr1' : (1 / 2 : ℝ) < r := by
    exact_mod_cast ENNReal.coe_lt_coe.1 (by simpa using hr1 : ((1 / 2 : NNReal) : ENNReal) < r)
  have hr1'' : (r : ℝ) < 1 := by
    exact_mod_cast ENNReal.coe_lt_coe.1 (by simpa using hr2.trans_le (min_le_right _ _) :
      (r : ENNReal) < ((1 : NNReal) : ENNReal))
  have key : ∀ n : ℕ, 1 ≤ n → (2 * (r : ℝ)) ^ n ≤ n * C + 1 := by
    intro n hn
    have h1 := hC n
    rw [FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 := hc n hn
    have hrn : (r : ℝ) ^ n ≤ 1 := pow_le_one₀ (NNReal.coe_nonneg r) hr1''.le
    have hrn0 : 0 ≤ (r : ℝ) ^ n := by positivity
    calc (2 * (r : ℝ)) ^ n = 2 ^ n * r ^ n := mul_pow _ _ _
      _ ≤ (n * c n + 1) * r ^ n := by gcongr; linarith
      _ ≤ n * (|c n| * r ^ n) + 1 := by
          nlinarith [mul_le_mul_of_nonneg_right (le_abs_self (c n)) hrn0]
      _ ≤ n * C + 1 := by gcongr
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 (show 1 < 2 * (r : ℝ) by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (|C| + 2) by positivity)))
  have h3 := hN (N + 1) (by omega)
  have h4 := key (N + 1) (by omega)
  rw [pow_one, div_lt_div_iff₀ (by positivity) (by positivity)] at h3
  nlinarith [mul_le_mul_of_nonneg_left (le_abs_self C) (by positivity : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ)),
    (by norm_num : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ))]

/-! ## The suspension flow -/

section Suspension
variable {α : Type*} (e : Equiv.Perm α)
/-- The suspension relation on `α × ℝ`: `(x, t) ~ (eᵏ x, t - k)` for `k ∈ ℤ`, i.e. the
equivalence relation generated by `(x, t + 1) ~ (e x, t)`. -/
def susSetoid : Setoid (α × ℝ) where
  r p q := ∃ k : ℤ, q.1 = (e ^ k) p.1 ∧ q.2 = p.2 - k
  iseqv := ⟨fun p => ⟨0, by simp⟩,
    fun ⟨k, h1, h2⟩ => ⟨-k, by rw [h1, _root_.zpow_neg]; simp, by rw [h2]; push_cast; ring⟩,
    fun ⟨k, h1, h2⟩ ⟨l, h3, h4⟩ => ⟨l + k, by rw [h3, h1, _root_.zpow_add, Equiv.Perm.mul_apply],
      by rw [h4, h2]; push_cast; ring⟩⟩
/-- The suspension (mapping torus) of `e`, `(α × ℝ) / ((x, t + 1) ~ (e x, t))`. -/
abbrev Suspension : Type _ := Quotient (susSetoid e)
/-- The point `[x, t]` of the suspension. -/
def sus (x : α) (t : ℝ) : Suspension e := Quotient.mk (susSetoid e) (x, t)
/-- The suspension flow `φₛ [x, t] = [x, t + s]`. -/
def flow (s : ℝ) : Suspension e → Suspension e :=
  Quotient.map (fun p => (p.1, p.2 + s)) fun _ _ ⟨k, h1, h2⟩ => ⟨k, h1, by simp [h2]; ring⟩
/-- Closed orbits of the suspension flow: for `s > 0`, `φₛ [x, t] = [x, t]` iff `s` is a positive
integer `n` with `eⁿ x = x`. So the closed orbits of the flow are the flow lines through the
periodic points of `e`, and the least period of the flow line through `[x, t]` is the least period
of `x` under `e`. -/
theorem flow_periodic_iff (x : α) (t s : ℝ) (hs : 0 < s) :
    flow e s (sus e x t) = sus e x t ↔ ∃ n : ℕ, 0 < n ∧ s = n ∧ (⇑e)^[n] x = x := by
  simp only [flow, sus, Quotient.map_mk]
  rw [Quotient.eq]
  constructor
  · rintro ⟨k, h1, h2⟩
    have hk : (k : ℝ) = s := by simp at h2; linarith
    have hk0 : 0 < k := by exact_mod_cast hk ▸ hs
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0.le
    refine ⟨n, by exact_mod_cast hk0, by rw [← hk]; push_cast; rfl, ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow] at h1; exact h1.symm
  · rintro ⟨n, -, rfl, h⟩
    exact ⟨n, by rw [zpow_natCast, Equiv.Perm.coe_pow, h], by simp⟩

end Suspension

/-! ## The refutation -/
/-- The radius of convergence of the zeta function of `f`. -/
noncomputable def zetaRadius {α : Type*} (f : α → α) : ENNReal :=
  (FormalMultilinearSeries.ofScalars ℂ (fun n => ((coeff n (zeta f) : ℝ) : ℂ))).radius
/-- The first clause of the conjecture, for suspensions of hyperbolic automorphisms of `T²`:
the zeta function has radius of convergence `1`. -/
def Clause1 : Prop := ∀ M : Matrix (Fin 2) (Fin 2) ℤ, IsHyperbolic M → zetaRadius ⇑(tmap M) = 1

open scoped PowerSeries.WithPiTopology in
/-- The cat map is a hyperbolic toral automorphism; its periodic counts are `|det(Aⁿ - I)|`; the
closed orbits of its suspension flow are its periodic orbits; `ζ = ∏_τ (1 - z^{|τ|})⁻¹` converges
in `ℝ⟦z⟧`; and the radius of convergence of `ζ` is `≤ 1/2`, so it is not `1`. -/
theorem conjecture_00000001485_false :
    IsHyperbolic A ∧
    (∀ n, 1 ≤ n → (Function.fixedPoints (⇑cat)^[n]).ncard = (A ^ n - 1).det.natAbs) ∧
    (∀ (x : Torus) (t s : ℝ), 0 < s → (flow cat.toEquiv s (sus _ x t) = sus _ x t ↔
      ∃ n : ℕ, 0 < n ∧ s = n ∧ (⇑cat)^[n] x = x)) ∧
    HasProd (fun τ : PerOrbit ⇑cat => fac τ.len) (zeta ⇑cat) ∧
    zetaRadius ⇑cat ≤ 1 / 2 ∧ ¬ Clause1 := by
  have hfix : ∀ m, 1 ≤ m → (Function.fixedPoints (⇑cat)^[m]).Finite := fun m hm =>
    (fix_cat m hm).2
  have hrad : zetaRadius ⇑cat ≤ 1 / 2 := by
    refine radius_le_half _ fun n hn => ?_
    have h1 := natAbs_det_ge n hn; have h2 := fix_le_orbits hfix n hn
    have h3 := coeff_zeta_ge (finite_orbits hfix) n hn
    rw [(fix_cat n hn).1] at h2
    generalize ((finite_orbits hfix n).toFinset.filter (fun τ => τ.len ∣ n)).card = c at h2 h3
    have h4 : ((2 : ℤ) ^ n - 1 : ℤ) ≤ ((n * c : ℕ) : ℤ) := h1.trans (by exact_mod_cast h2)
    have h5 : (2 : ℝ) ^ n - 1 ≤ (n : ℝ) * c := by exact_mod_cast h4
    exact h5.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  refine ⟨A_hyperbolic, fun n hn => (fix_cat n hn).1, fun x t s hs => flow_periodic_iff _ x t s hs,
    (hasProd_zeta (finite_orbits hfix)).1, hrad, fun h => ?_⟩
  have h' := h A A_hyperbolic; rw [← coe_cat] at h'; rw [h'] at hrad; norm_num at hrad

end C1485