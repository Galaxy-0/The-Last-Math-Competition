import Mathlib

/-!
# Conjecture 00000002291 is false

The conjecture claims a lower bound `|C_G(x)| ≥ c · |G|^{1/2}` with `c = 1/8` for the
centralizers of elements of finite simple groups of even order, and that `c` is tight,
"attained by low-order simple groups (e.g. involutions of A₅)". The statement does not say
which `x` the bound covers, so both readings are refuted.

* `not_lowerBoundAllElements` (reading R1: all nonidentity `x` of a nonabelian finite simple
  group of even order): in `A₉` the 9-cycle `finRotate 9` has `|C(x)| ≤ 9 < (1/8)·√181440`.
* `alternating_centralizer_ratio_small`: under R1 no constant `c > 0` works (`n`-cycles in `A_n`).
* `not_lowerBoundInvolutions` (reading R2: involutions `x` only, as in the Brauer–Fowler
  preamble): `G = PSL(2, 𝔽₁₂₈)` is simple, nonabelian and of even order, and the image `t` of
  `[[1, 1], [0, 1]]` is an involution with `|C(t)| ≤ 128 < (1/8)·√|G|`, since `|G| ≥ 127·128²`.
* `psl_centralizer_ratio_small`: under R2 no constant `c > 0` works (`PSL(2, 2^k)`, `k` large).
* `not_attainedByA5Involution` and `a5_not_near_tight`: the named attainment fails: every
  element of `A₅` has `|C(x)| > (1/8)·√60`, and every nonidentity element has
  `|C(x)| > 2 · (1/8)·√60`.

Simplicity of `PSL(2, F)` for `|F| ≥ 4` is Mathlib's
`Matrix.ProjectiveSpecialLinearGroup.rank_two_simple`. In characteristic 2 the center of
`SL(2, F)` is trivial, so `SL(2, F) ≃* PSL(2, F)` (`toPSL`), and an element of `SL(2, F)`
commuting with `[[1, 1], [0, 1]]` is `[[1, b], [0, 1]]`.

Conventions: `Subgroup.centralizer {x}` is the centralizer `C_G(x) = {g | g x = x g}`;
`Nat.card` is the order of a finite group; `Real.sqrt` is the nonnegative square root;
an involution is an element with `orderOf x = 2`.
-/

open Equiv Equiv.Perm

namespace C2291

/-- Reading R1 of the lower bound with the stated constant `c = 1/8`: for every finite group
`G` that is simple, nonabelian and of even order, every nonidentity `x ∈ G` satisfies
`(1/8) · √|G| ≤ |C_G(x)|`. -/
def LowerBoundAllElements : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    Even (Nat.card G) → ∀ x : G, x ≠ 1 →
      (1 / 8 : ℝ) * Real.sqrt (Nat.card G) ≤ (Nat.card (Subgroup.centralizer ({x} : Set G)) : ℝ)

/-- The attainment clause at `A₅`: some involution `t ∈ A₅` has `|C(t)| = (1/8) · √|A₅|`. -/
def AttainedByA5Involution : Prop :=
  ∃ t : alternatingGroup (Fin 5), orderOf t = 2 ∧
    (Nat.card (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 5)))) : ℝ) =
      (1 / 8) * Real.sqrt (Nat.card (alternatingGroup (Fin 5)))

/-! ## The n-cycle in `A_n` for odd `n` -/

/-- For odd `n`, the `n`-cycle `finRotate n` is an even permutation. -/
theorem finRotate_mem_alternatingGroup (m : ℕ) :
    finRotate (2 * m + 1) ∈ alternatingGroup (Fin (2 * m + 1)) := by
  rw [mem_alternatingGroup, sign_finRotate]
  simp [pow_mul]

/-- The `n`-cycle as an element of `A_n` (`n = 2m+1` odd). -/
def cyc (m : ℕ) : alternatingGroup (Fin (2 * m + 1)) :=
  ⟨finRotate (2 * m + 1), finRotate_mem_alternatingGroup m⟩

/-- The centralizer of an `n`-cycle in the full symmetric group `S_n` has order `n`. -/
theorem card_centralizer_finRotate_perm (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Subgroup.centralizer ({finRotate n} : Set (Perm (Fin n)))) = n := by
  rw [Equiv.Perm.nat_card_centralizer, cycleType_finRotate_of_le hn]
  simp

/-- The centralizer of the `n`-cycle in `A_n` has order at most `n`: it embeds into the
centralizer in `S_n`. -/
theorem card_centralizer_cyc_le (m : ℕ) (hm : 1 ≤ m) :
    Nat.card (Subgroup.centralizer ({cyc m} : Set (alternatingGroup (Fin (2 * m + 1))))) ≤
      2 * m + 1 := by
  have hn : 2 ≤ 2 * m + 1 := by omega
  let f : Subgroup.centralizer ({cyc m} : Set (alternatingGroup (Fin (2 * m + 1)))) →
      Subgroup.centralizer ({finRotate (2 * m + 1)} : Set (Perm (Fin (2 * m + 1)))) :=
    fun g => ⟨(g : alternatingGroup (Fin (2 * m + 1))), by
      have h := Subgroup.mem_centralizer_singleton_iff.mp g.2
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val h⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    have h := congrArg Subtype.val hab
    simpa [f] using h
  exact (Nat.card_le_card_of_injective f hf).trans
    (card_centralizer_finRotate_perm (2 * m + 1) hn).le

theorem cyc_ne_one (m : ℕ) (hm : 1 ≤ m) : cyc m ≠ 1 := by
  intro h
  have h1 : finRotate (2 * m + 1) = 1 := congrArg Subtype.val h
  have h2 := card_centralizer_finRotate_perm (2 * m + 1) (by omega)
  rw [h1] at h2
  have h3 : Subgroup.centralizer ({(1 : Perm (Fin (2 * m + 1)))} : Set _) = ⊤ := by
    ext g; simp [Subgroup.mem_centralizer_singleton_iff]
  rw [h3, Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  have h4 : 2 * m + 1 < (2 * m + 1).factorial := Nat.lt_factorial_self (by omega)
  omega

/-- `2 · |A_n| = n!` for `n = 2m+1 ≥ 3`. -/
theorem two_mul_card_A' (m : ℕ) (hm : 1 ≤ m) :
    2 * Nat.card (alternatingGroup (Fin (2 * m + 1))) = (2 * m + 1).factorial := by
  have : Nontrivial (Fin (2 * m + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- `n! ≥ n² (n - 3)` in the form needed: `(2m+1)! ≥ (2m+1)² · (2m - 2)` for `m ≥ 2`. -/
theorem factorial_lower (m : ℕ) (hm : 2 ≤ m) :
    (2 * m + 1) * (2 * m + 1) * (2 * m - 2) ≤ (2 * m + 1).factorial := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e : 2 * (k + 2) + 1 = (2 * k + 2) + 3 := by ring
  rw [e, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  have h1 : 2 * k + 2 ≤ (2 * k + 2).factorial := Nat.self_le_factorial _
  have e2 : 2 * (k + 2) - 2 = 2 * k + 2 := by omega
  rw [e2]
  have h2 : (2 * k + 2 + 3) ≤ (2 * k + 2 + 1 + 1) * (2 * k + 2 + 1) := by nlinarith
  calc (2 * k + 2 + 3) * (2 * k + 2 + 3) * (2 * k + 2)
      ≤ (2 * k + 2 + 3) * ((2 * k + 2 + 1 + 1) * (2 * k + 2 + 1)) * (2 * k + 2).factorial := by
        gcongr
    _ = (2 * k + 2 + 2 + 1) * ((2 * k + 2 + 1 + 1) * ((2 * k + 2 + 1) * (2 * k + 2).factorial)) := by
        ring

/-- The alternating group `A_n` (`n = 2m+1 ≥ 5`) is simple, nonabelian and of even order. -/
theorem A_hyps (m : ℕ) (hm : 2 ≤ m) :
    IsSimpleGroup (alternatingGroup (Fin (2 * m + 1))) ∧
    (∃ a b : alternatingGroup (Fin (2 * m + 1)), a * b ≠ b * a) ∧
    Even (Nat.card (alternatingGroup (Fin (2 * m + 1)))) := by
  refine ⟨alternatingGroup.isSimpleGroup (by simp; omega), ?_, ?_⟩
  · -- if `A_n` were abelian, the centralizer of the cycle would be all of `A_n`
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.centralizer ({cyc m} : Set (alternatingGroup (Fin (2 * m + 1)))) = ⊤ := by
      ext g; simp [Subgroup.mem_centralizer_singleton_iff, hcon]
    have hle := card_centralizer_cyc_le m (by omega)
    rw [htop, Subgroup.card_top] at hle
    have h2 := two_mul_card_A' m (by omega)
    have h3 := factorial_lower m hm
    have h5 : (2 * m + 1) * (2 * m + 1) * 2 ≤ (2 * m + 1) * (2 * m + 1) * (2 * m - 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have h6 : 2 * (2 * m + 1) < (2 * m + 1) * (2 * m + 1) * 2 := by nlinarith
    omega
  · -- `4 ∣ n!`, so `n!/2` is even
    have h2 := two_mul_card_A' m (by omega)
    have h24 : (4 : ℕ).factorial ∣ (2 * m + 1).factorial := Nat.factorial_dvd_factorial (by omega)
    obtain ⟨r, hr⟩ := h24
    refine ⟨6 * r, ?_⟩
    rw [show Nat.factorial 4 = 24 by rfl] at hr
    omega

/-- `C < c · √N` whenever `C ≤ q`, `q² r ≤ N` and `c² r > 1`. -/
theorem ratio_aux (q r C N : ℕ) (c : ℝ) (hc : 0 < c) (hq : 0 < q) (hC : C ≤ q)
    (hN : q * q * r ≤ N) (hcr : 1 < c ^ 2 * r) : (C : ℝ) < c * Real.sqrt N := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hN' : (q : ℝ) * q * r ≤ N := by exact_mod_cast hN
  have hlt : (q : ℝ) ^ 2 < c ^ 2 * N := by
    nlinarith [mul_le_mul_of_nonneg_left hN' (sq_nonneg c),
      mul_lt_mul_of_pos_right hcr (by positivity : (0 : ℝ) < q ^ 2)]
  have hsq : (q : ℝ) < c * Real.sqrt N := by
    rw [show c * Real.sqrt N = Real.sqrt (c ^ 2 * N) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]]
    exact Real.lt_sqrt (by positivity) |>.mpr hlt
  linarith [(by exact_mod_cast hC : (C : ℝ) ≤ q)]

/-! ## Reading R1 is false, and no positive constant works -/

theorem alternating_centralizer_ratio_small (c : ℝ) (hc : 0 < c) :
    ∃ n : ℕ, 5 ≤ n ∧ IsSimpleGroup (alternatingGroup (Fin n)) ∧
      (∃ a b : alternatingGroup (Fin n), a * b ≠ b * a) ∧
      Even (Nat.card (alternatingGroup (Fin n))) ∧
      ∃ x : alternatingGroup (Fin n), x ≠ 1 ∧
        (Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin n)))) : ℝ) <
          c * Real.sqrt (Nat.card (alternatingGroup (Fin n))) := by
  set m : ℕ := ⌈1 / c ^ 2⌉₊ + 2 with hmdef
  have hm : 2 ≤ m := by omega
  refine ⟨2 * m + 1, by omega, (A_hyps m hm).1, (A_hyps m hm).2.1, (A_hyps m hm).2.2,
    cyc m, cyc_ne_one m (by omega),
    ratio_aux _ (m - 1) _ _ c hc (by omega) (card_centralizer_cyc_le m (by omega)) ?_ ?_⟩
  · -- `2N = n! ≥ n² (2m - 2)`, so `N ≥ n² (m - 1)`
    have h1 := two_mul_card_A' m (by omega)
    have h2 := factorial_lower m hm
    have : (2 * m + 1) * (2 * m + 1) * (2 * m - 2) = 2 * ((2 * m + 1) * (2 * m + 1) * (m - 1)) := by
      rw [show 2 * m - 2 = 2 * (m - 1) by omega]; ring
    omega
  · have hceil : 1 / c ^ 2 ≤ (⌈1 / c ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    rw [show m - 1 = ⌈1 / c ^ 2⌉₊ + 1 by omega]
    push_cast
    have : c ^ 2 * (1 / c ^ 2) = 1 := by field_simp
    nlinarith [sq_nonneg c]

/-- Reading R1 with `c = 1/8` is false (witness: `A₉` and the 9-cycle `finRotate 9`). -/
theorem not_lowerBoundAllElements : ¬ LowerBoundAllElements := by
  intro h
  have hyps := A_hyps 4 (by norm_num)
  have hb := h (alternatingGroup (Fin (2 * 4 + 1))) hyps.1 hyps.2.1 hyps.2.2 (cyc 4)
    (cyc_ne_one 4 (by norm_num))
  have hN : Nat.card (alternatingGroup (Fin (2 * 4 + 1))) = 181440 := by
    have := two_mul_card_A' 4 (by norm_num)
    rw [show Nat.factorial (2 * 4 + 1) = 362880 by rfl] at this
    omega
  have := ratio_aux 9 2240 _ (Nat.card (alternatingGroup (Fin (2 * 4 + 1)))) (1 / 8)
    (by norm_num) (by norm_num) (card_centralizer_cyc_le 4 (by norm_num)) (by rw [hN]) (by norm_num)
  linarith

/-! ## The attainment clause at `A₅` fails -/

theorem card_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]; simp [Nat.factorial]

theorem sqrt60_div8_lt_one : (1 / 8 : ℝ) * Real.sqrt 60 < 1 := by
  have : Real.sqrt 60 < 8 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- Every nonidentity `x ∈ A₅` has `|C(x)| > 2 · (1/8) · √|A₅|`: the bound is not
nearly attained, by involutions or by any other nonidentity element. -/
theorem a5_not_near_tight (x : alternatingGroup (Fin 5)) (hx : x ≠ 1) :
    2 * ((1 / 8 : ℝ) * Real.sqrt (Nat.card (alternatingGroup (Fin 5)))) <
      (Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) : ℝ) := by
  have hnt : Nontrivial (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) :=
    ⟨⟨⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, 1, fun h => hx (congrArg Subtype.val h)⟩⟩
  have h2 : 1 < Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) :=
    Finite.one_lt_card
  have h2' : (2 : ℝ) ≤ Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) := by
    exact_mod_cast h2
  rw [card_A5]; push_cast
  linarith [sqrt60_div8_lt_one]

/-- No element of `A₅` (in particular no involution) attains `|C(x)| = (1/8) · √|A₅|`:
every centralizer has order `≥ 1 > (1/8)·√60`. -/
theorem not_attainedByA5Involution : ¬ AttainedByA5Involution := by
  rintro ⟨t, -, ht⟩
  have h1 : 0 < Nat.card (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 5)))) :=
    Nat.card_pos
  have h1' : (1 : ℝ) ≤ Nat.card (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 5)))) := by
    exact_mod_cast h1
  rw [ht, card_A5] at h1'
  push_cast at h1'
  linarith [sqrt60_div8_lt_one]

/-! ## Reading R2: involutions in `PSL(2, 2^k)` -/

open scoped MatrixGroups

section PSL

variable {F : Type} [Field F] [CharP F 2]

/-- In characteristic 2, `a² = 1` forces `a = 1`. -/
theorem eq_one_of_sq_eq_one {a : F} (h : a ^ 2 = 1) : a = 1 := by
  have h2 : (a + 1) ^ 2 = 0 := by rw [CharTwo.add_sq, h, one_pow, CharTwo.add_self_eq_zero]
  have h3 : a + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  have h4 : a = -1 := eq_neg_of_add_eq_zero_left h3
  rwa [CharTwo.neg_eq] at h4

/-- In characteristic 2 the center of `SL(2, F)` is trivial. -/
theorem center_SL_eq_bot : Subgroup.center SL(2, F) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun A hA => ?_
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  ext i j
  rw [← hA, eq_one_of_sq_eq_one hr]
  simp

/-- Hence the quotient map `SL(2, F) → PSL(2, F)` is an isomorphism. -/
noncomputable def toPSL : SL(2, F) ≃* PSL(2, F) :=
  MulEquiv.ofBijective (QuotientGroup.mk' _)
    ⟨fun a b hab => by
      have h := QuotientGroup.eq.mp hab
      rw [center_SL_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at h
      exact h, QuotientGroup.mk'_surjective _⟩

/-- The transvection `T = [[1, 1], [0, 1]]` in `SL(2, F)`. -/
def T : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

omit [CharP F 2] in
theorem coe_T : ((T : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl

theorem T_sq : (T : SL(2, F)) ^ 2 = 1 := by
  ext i j
  rw [sq, Matrix.SpecialLinearGroup.coe_mul, coe_T, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem T_ne_one : (T : SL(2, F)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [coe_T] at this

/-- An element of `SL(2, F)` commuting with `T` is `[[1, b], [0, 1]]`. -/
theorem entries_of_comm {A : SL(2, F)} (h : A * T = T * A) :
    (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  have e := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_T] at e
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have hdet := A.2
  rw [Matrix.det_fin_two, e00, mul_zero, sub_zero] at hdet
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -e01
  rw [h11, ← sq] at hdet
  have h00 := eq_one_of_sq_eq_one hdet
  exact ⟨h00, e00, h11.trans h00⟩

variable [Finite F]

omit [CharP F 2] in
/-- `|SL(2, F)| ≥ (q - 1) q²`: `(a, b, c) ↦ [[a, b], [c, a⁻¹(1 + bc)]]` embeds `Fˣ × F × F`. -/
theorem card_SL_lower : (Nat.card F - 1) * (Nat.card F * Nat.card F) ≤ Nat.card SL(2, F) := by
  let f : Fˣ × F × F → SL(2, F) := fun x =>
    ⟨!![(x.1 : F), x.2.1; x.2.2, (x.1 : F)⁻¹ * (1 + x.2.1 * x.2.2)], by
      rw [Matrix.det_fin_two_of, mul_inv_cancel_left₀ x.1.ne_zero]; ring⟩
  have key : ∀ x, ((f x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![(x.1 : F), x.2.1; x.2.2, (x.1 : F)⁻¹ * (1 + x.2.1 * x.2.2)] := fun _ => rfl
  have hf : Function.Injective f := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have e := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h
    simp only [key] at e
    have h00 := congrFun (congrFun e 0) 0
    have h01 := congrFun (congrFun e 0) 1
    have h10 := congrFun (congrFun e 1) 0
    simp at h00 h01 h10
    rw [Units.ext h00, h01, h10]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_prod, Nat.card_units] at this

/-- The centralizer of the involution `toPSL T` in `PSL(2, F)` has order at most `q`. -/
theorem card_centralizer_le :
    Nat.card (Subgroup.centralizer ({toPSL T} : Set PSL(2, F))) ≤ Nat.card F := by
  let f : Subgroup.centralizer ({toPSL T} : Set PSL(2, F)) → F :=
    fun g => ((toPSL.symm (g : PSL(2, F)) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1
  have hc : ∀ g : Subgroup.centralizer ({toPSL T} : Set PSL(2, F)),
      toPSL.symm (g : PSL(2, F)) * T = T * toPSL.symm (g : PSL(2, F)) := by
    intro g
    have h := Subgroup.mem_centralizer_singleton_iff.mp g.2
    apply toPSL.injective
    simp [map_mul, h]
  have hf : Function.Injective f := by
    intro g h hgh
    apply Subtype.ext
    apply toPSL.symm.injective
    obtain ⟨a1, a2, a3⟩ := entries_of_comm (hc g)
    obtain ⟨b1, b2, b3⟩ := entries_of_comm (hc h)
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [f]
  exact Nat.card_le_card_of_injective f hf

/-- For `q = |F| ≥ 4` (characteristic 2): `PSL(2, F)` is simple, nonabelian, of even order;
`toPSL T` is an involution with `|C(toPSL T)| ≤ q`; and `|PSL(2, F)| ≥ (q - 1) q²`. -/
theorem psl_facts (hF : 4 ≤ Nat.card F) :
    IsSimpleGroup PSL(2, F) ∧ (∃ a b : PSL(2, F), a * b ≠ b * a) ∧
    Even (Nat.card PSL(2, F)) ∧ orderOf (toPSL T : PSL(2, F)) = 2 ∧
    Nat.card (Subgroup.centralizer ({toPSL T} : Set PSL(2, F))) ≤ Nat.card F ∧
    (Nat.card F - 1) * (Nat.card F * Nat.card F) ≤ Nat.card PSL(2, F) := by
  have hcard : Nat.card PSL(2, F) = Nat.card SL(2, F) := (Nat.card_congr toPSL.toEquiv).symm
  have hord : orderOf (toPSL T : PSL(2, F)) = 2 := by
    refine orderOf_eq_prime (by rw [← map_pow, T_sq, map_one]) ?_
    rw [Ne, MulEquiv.map_eq_one_iff]
    exact T_ne_one
  have hlow := hcard ▸ card_SL_lower (F := F)
  have h2 := orderOf_dvd_natCard (toPSL T : PSL(2, F))
  rw [hord] at h2
  refine ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF, ?_, even_iff_two_dvd.mpr h2,
    hord, card_centralizer_le, hlow⟩
  by_contra hcon
  push Not at hcon
  have htop : Subgroup.centralizer ({toPSL T} : Set PSL(2, F)) = ⊤ := by
    ext g; simp [Subgroup.mem_centralizer_singleton_iff, hcon]
  have hle := card_centralizer_le (F := F)
  rw [htop, Subgroup.card_top] at hle
  obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 4 := ⟨_, (Nat.sub_add_cancel hF).symm⟩
  rw [hr] at hle hlow
  rw [show r + 4 - 1 = r + 3 by omega] at hlow
  nlinarith

end PSL

/-- Reading R2 of the lower bound with `c = 1/8`: for every finite group `G` that is simple,
nonabelian and of even order, every involution `x ∈ G` satisfies `(1/8) · √|G| ≤ |C_G(x)|`. -/
def LowerBoundInvolutions : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    Even (Nat.card G) → ∀ x : G, orderOf x = 2 →
      (1 / 8 : ℝ) * Real.sqrt (Nat.card G) ≤ (Nat.card (Subgroup.centralizer ({x} : Set G)) : ℝ)

/-- Reading R2 with `c = 1/8` is false (witness: `PSL(2, 128)` and the image of `[[1,1],[0,1]]`). -/
theorem not_lowerBoundInvolutions : ¬ LowerBoundInvolutions := by
  intro h
  have hq : Nat.card (GaloisField 2 7) = 128 := by rw [GaloisField.card 2 7 (by norm_num)]; norm_num
  obtain ⟨hs, hna, hev, hord, hC, hlow⟩ := psl_facts (F := GaloisField 2 7) (by rw [hq]; norm_num)
  have hb := h _ hs hna hev _ hord
  rw [hq] at hC hlow
  have := ratio_aux 128 127 _ (Nat.card PSL(2, GaloisField 2 7)) (1 / 8) (by norm_num)
    (by norm_num) hC (by rw [mul_comm]; exact hlow) (by norm_num)
  linarith

/-- No positive constant works under R2: for every `c > 0` some `PSL(2, 2^k)` has an involution
`t` with `|C(t)| < c · √|PSL(2, 2^k)|`. -/
theorem psl_centralizer_ratio_small (c : ℝ) (hc : 0 < c) :
    ∃ k : ℕ, IsSimpleGroup PSL(2, GaloisField 2 k) ∧
      (∃ a b : PSL(2, GaloisField 2 k), a * b ≠ b * a) ∧ Even (Nat.card PSL(2, GaloisField 2 k)) ∧
      ∃ t : PSL(2, GaloisField 2 k), orderOf t = 2 ∧
        (Nat.card (Subgroup.centralizer ({t} : Set PSL(2, GaloisField 2 k))) : ℝ) <
          c * Real.sqrt (Nat.card PSL(2, GaloisField 2 k)) := by
  set k : ℕ := ⌈1 / c ^ 2⌉₊ + 2 with hkdef
  have hq : Nat.card (GaloisField 2 k) = 2 ^ k := GaloisField.card 2 k (by omega)
  have hq4 : 4 ≤ 2 ^ k :=
    (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkq : k < 2 ^ k := Nat.lt_two_pow_self
  obtain ⟨hs, hna, hev, hord, hC, hlow⟩ := psl_facts (F := GaloisField 2 k) (hq ▸ hq4)
  refine ⟨k, hs, hna, hev, _, hord, ?_⟩
  rw [hq] at hC hlow
  refine ratio_aux _ (2 ^ k - 1) _ _ c hc (by omega) hC (by rw [mul_comm]; exact hlow) ?_
  have hceil : 1 / c ^ 2 ≤ (⌈1 / c ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hk1 : ((⌈1 / c ^ 2⌉₊ + 2 : ℕ) : ℝ) ≤ ((2 ^ k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show k ≤ 2 ^ k - 1 by omega)
  push_cast at hk1
  have : c ^ 2 * (1 / c ^ 2) = 1 := by field_simp
  nlinarith [sq_nonneg c]

/-- **Main theorem.** The conjecture is false: (1) reading R1 of the lower bound with `c = 1/8`
fails, and (2) under R1 no positive constant `c` works (alternating groups); (3) reading R2
(involutions only) with `c = 1/8` fails, and (4) under R2 no positive constant `c` works
(`PSL(2, 2^k)`); (5) no involution of `A₅` attains `c = 1/8`; (6) every nonidentity element
of `A₅` exceeds the bound by a factor greater than 2. -/
theorem conjecture_2291_false :
    ¬ LowerBoundAllElements ∧
    (∀ c : ℝ, 0 < c → ∃ n : ℕ, 5 ≤ n ∧ IsSimpleGroup (alternatingGroup (Fin n)) ∧
      (∃ a b : alternatingGroup (Fin n), a * b ≠ b * a) ∧
      Even (Nat.card (alternatingGroup (Fin n))) ∧
      ∃ x : alternatingGroup (Fin n), x ≠ 1 ∧
        (Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin n)))) : ℝ) <
          c * Real.sqrt (Nat.card (alternatingGroup (Fin n)))) ∧
    ¬ LowerBoundInvolutions ∧
    (∀ c : ℝ, 0 < c → ∃ k : ℕ, IsSimpleGroup PSL(2, GaloisField 2 k) ∧
      (∃ a b : PSL(2, GaloisField 2 k), a * b ≠ b * a) ∧ Even (Nat.card PSL(2, GaloisField 2 k)) ∧
      ∃ t : PSL(2, GaloisField 2 k), orderOf t = 2 ∧
        (Nat.card (Subgroup.centralizer ({t} : Set PSL(2, GaloisField 2 k))) : ℝ) <
          c * Real.sqrt (Nat.card PSL(2, GaloisField 2 k))) ∧
    ¬ AttainedByA5Involution ∧
    (∀ x : alternatingGroup (Fin 5), x ≠ 1 →
      2 * ((1 / 8 : ℝ) * Real.sqrt (Nat.card (alternatingGroup (Fin 5)))) <
        (Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) : ℝ)) :=
  ⟨not_lowerBoundAllElements, alternating_centralizer_ratio_small, not_lowerBoundInvolutions,
    psl_centralizer_ratio_small, not_attainedByA5Involution, a5_not_near_tight⟩

end C2291
