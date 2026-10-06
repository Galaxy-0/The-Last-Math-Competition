import Mathlib

/-!
# Conjecture 00000006120 is false

Conjecture 00000006120 reads:

> Definition: Noise stability and the spectrum are two layers. Conjecture: There exist two
> Boolean functions with identical noise stability but different spectral distributions, and the
> separation is realized by an explicit perturbation with the same stability but different
> low-degree weights.

(Chinese text: "一切噪声稳定性相同", i.e. *all* noise stabilities agree.)

Standard notions (O'Donnell, *Analysis of Boolean Functions*, 2014, Ch. 1-2):
* the Boolean cube `{-1,1}^n` is encoded as `Fin n → Bool`, with `sgn true = -1`, `sgn false = 1`;
* `fourier f S = E_x[f(x) χ_S(x)]`, where `χ_S(x) = ∏_{i ∈ S} x_i`;
* the spectral distribution of `f` gives the set `S` the weight `fourier f S ^ 2`;
* `weight f k = W^k[f] = ∑_{|S| = k} fourier f S ^ 2` is the Fourier weight at degree `k`;
* `lowWeight f k = W^{≤k}[f] = ∑_{|S| ≤ k} fourier f S ^ 2` is the low-degree weight up to `k`;
* `stab ρ f = Stab_ρ[f] = E[f(x) f(y)]`, where `x` is uniform and `y` is `ρ`-correlated with `x`:
  independently for each `i`, `y_i = x_i` with probability `(1+ρ)/2`, and `y_i = -x_i` otherwise.

Main fact (`stab_eq_fourier`): `Stab_ρ[f] = ∑_S ρ^{|S|} fourier f S ^ 2 = ∑_k W^k[f] ρ^k`. So
`ρ ↦ Stab_ρ[f]` is a polynomial whose coefficients are exactly the degree weights. Two functions
whose noise stabilities agree at infinitely many `ρ` (for instance at every `ρ ∈ [0,1]`) therefore
have the same `W^k` and the same `W^{≤k}` for every `k` (`weight_eq_of_stab_eq`,
`lowWeight_eq_of_stab_eq`). The realizing clause ("same stability but different low-degree
weights") can never hold (`no_realizing_pair`), and the conjecture is false
(`conjecture6120_false`).

The functions are real-valued and Booleanity is never used, so the impossibility also covers the
`{0,1}`-valued convention and functions with different numbers of variables.

Non-vacuity (`first_clauses_satisfiable`): the dictators `x_0`, `x_1` on `{-1,1}^2` are Boolean,
have identical noise stability for every `ρ`, and have different spectral distributions. Only the
realizing clause fails.
-/

open Finset Polynomial

namespace Conjecture6120

/-- The `±1` value of a bit: `sgn false = 1`, `sgn true = -1`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- A point of the Boolean cube `{-1,1}^n`, coordinate `i` being `sgn (x i)`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- A real-valued function on the Boolean cube. -/
abbrev BFun (n : ℕ) := Cube n → ℝ

/-- `f` is a Boolean function: it takes only the values `1` and `-1`. -/
def IsBoolean {n : ℕ} (f : BFun n) : Prop := ∀ x, f x = 1 ∨ f x = -1

/-- The character `χ_S(x) = ∏_{i ∈ S} x_i`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ S, sgn (x i)

/-- The Fourier coefficient `f̂(S) = E_x[f(x) χ_S(x)]` (uniform `x`). -/
noncomputable def fourier {n : ℕ} (f : BFun n) (S : Finset (Fin n)) : ℝ :=
  (∑ x, f x * chi S x) / 2 ^ n

/-- The spectral distribution of `f`: the set `S` has weight `f̂(S)^2`. -/
noncomputable def spectralDist {n : ℕ} (f : BFun n) : Finset (Fin n) → ℝ :=
  fun S => fourier f S ^ 2

/-- The Fourier weight at degree `k`: `W^k[f] = ∑_{|S| = k} f̂(S)^2`. -/
noncomputable def weight {n : ℕ} (f : BFun n) (k : ℕ) : ℝ :=
  ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = k), fourier f S ^ 2

/-- The low-degree weight up to degree `k`: `W^{≤k}[f] = ∑_{|S| ≤ k} f̂(S)^2`. -/
noncomputable def lowWeight {n : ℕ} (f : BFun n) (k : ℕ) : ℝ :=
  ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card ≤ k), fourier f S ^ 2

/-- The conditional law of `y` given `x` when `y` is `ρ`-correlated with `x`: coordinates are
independent, with `y_i = x_i` with probability `(1+ρ)/2` and `y_i ≠ x_i` with probability
`(1-ρ)/2`. -/
noncomputable def noiseKernel {n : ℕ} (ρ : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2

/-- Noise stability `Stab_ρ[f] = E[f(x) f(y)]`, with `x` uniform and `y` `ρ`-correlated with `x`. -/
noncomputable def stab {n : ℕ} (ρ : ℝ) (f : BFun n) : ℝ :=
  ∑ x, ∑ y, (1 / 2 ^ n) * noiseKernel ρ x y * f x * f y

/-! ### Sanity: the noise kernel is a probability distribution for `ρ ∈ [-1,1]` -/

theorem noiseKernel_nonneg {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (x y : Cube n) :
    0 ≤ noiseKernel ρ x y := by
  obtain ⟨h1, h2⟩ := hρ
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs <;> linarith

theorem noiseKernel_sum {n : ℕ} (ρ : ℝ) (x : Cube n) : ∑ y, noiseKernel ρ x y = 1 := by
  have h : ∀ i, ∑ b : Bool, (if b = x i then (1 + ρ) / 2 else (1 - ρ) / 2) = 1 := by
    intro i; cases x i <;> simp <;> ring
  calc ∑ y, noiseKernel ρ x y
      = ∏ i, ∑ b : Bool, (if b = x i then (1 + ρ) / 2 else (1 - ρ) / 2) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]; rfl
    _ = 1 := by rw [Finset.prod_congr rfl fun i _ => h i]; exact Finset.prod_const_one

/-! ### Fourier expansion of noise stability -/

theorem factor_eq (ρ : ℝ) (a b : Bool) :
    (if b = a then (1 + ρ) / 2 else (1 - ρ) / 2) = (1 + ρ * (sgn a * sgn b)) / 2 := by
  cases a <;> cases b <;> simp [sgn] <;> ring

theorem noiseKernel_expand {n : ℕ} (ρ : ℝ) (x y : Cube n) :
    noiseKernel ρ x y = (1 / 2 ^ n) * ∑ S : Finset (Fin n), ρ ^ S.card * (chi S x * chi S y) := by
  have h1 : noiseKernel ρ x y = (∏ i, (1 + ρ * (sgn (x i) * sgn (y i)))) / 2 ^ n := by
    unfold noiseKernel
    simp_rw [factor_eq]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h1, Finset.prod_one_add, Finset.powerset_univ, div_eq_inv_mul, one_div]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  simp [chi, Finset.prod_mul_distrib, Finset.prod_const]

/-- **Fourier formula for noise stability**: `Stab_ρ[f] = ∑_S ρ^{|S|} f̂(S)^2`. -/
theorem stab_eq_fourier {n : ℕ} (ρ : ℝ) (f : BFun n) :
    stab ρ f = ∑ S : Finset (Fin n), ρ ^ S.card * fourier f S ^ 2 := by
  set c : ℝ := 1 / 2 ^ n
  calc stab ρ f
      = ∑ x, ∑ y, ∑ S : Finset (Fin n), c * c * ρ ^ S.card * (f x * chi S x) * (f y * chi S y) := by
        unfold stab
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [noiseKernel_expand, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun S _ => by ring
    _ = ∑ S : Finset (Fin n), ∑ x, ∑ y, c * c * ρ ^ S.card * (f x * chi S x) * (f y * chi S y) := by
        conv_lhs => enter [2, x]; rw [Finset.sum_comm]
        exact Finset.sum_comm
    _ = ∑ S : Finset (Fin n), ρ ^ S.card * fourier f S ^ 2 := by
        refine Finset.sum_congr rfl fun S _ => ?_
        have : fourier f S = c * ∑ x, f x * chi S x := by
          simp only [fourier, c]; ring
        rw [this, mul_pow, sq (∑ x, f x * chi S x), Finset.sum_mul_sum, Finset.mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring

/-! ### Noise stability as a polynomial in `ρ` -/

/-- The stability polynomial `∑_S f̂(S)^2 X^{|S|}`. -/
noncomputable def stabPoly {n : ℕ} (f : BFun n) : ℝ[X] :=
  ∑ S : Finset (Fin n), C (fourier f S ^ 2) * X ^ S.card

theorem eval_stabPoly {n : ℕ} (f : BFun n) (ρ : ℝ) : (stabPoly f).eval ρ = stab ρ f := by
  simp [stabPoly, eval_finsetSum, stab_eq_fourier, mul_comm]

/-- The coefficients of the stability polynomial are the degree weights `W^k[f]`. -/
theorem coeff_stabPoly {n : ℕ} (f : BFun n) (k : ℕ) : (stabPoly f).coeff k = weight f k := by
  rw [weight, Finset.sum_filter, stabPoly, finsetSum_coeff]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

/-- `Stab_ρ[f] = ∑_{k ≤ n} W^k[f] ρ^k`. -/
theorem stab_eq_weights {n : ℕ} (ρ : ℝ) (f : BFun n) :
    stab ρ f = ∑ k ∈ range (n + 1), weight f k * ρ ^ k := by
  rw [← eval_stabPoly, eval_eq_sum_range' (n := n + 1)]
  · simp [coeff_stabPoly]
  · refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun S _ => ?_) (Nat.lt_succ_self n)
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    simpa using S.card_le_univ

/-- `W^{≤k}[f] = ∑_{j ≤ k} W^j[f]`. -/
theorem lowWeight_eq_sum {n : ℕ} (f : BFun n) (k : ℕ) :
    lowWeight f k = ∑ j ∈ range (k + 1), weight f j := by
  simp only [lowWeight, weight, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-! ### Identical noise stability forces identical degree weights -/

/-- If two functions (of possibly different arities) have the same noise stability at infinitely
many `ρ`, they have the same Fourier weight `W^k` at every degree `k`. -/
theorem weight_eq_of_stab_eq {n m : ℕ} (f : BFun n) (g : BFun m) {s : Set ℝ} (hs : s.Infinite)
    (h : ∀ ρ ∈ s, stab ρ f = stab ρ g) (k : ℕ) : weight f k = weight g k := by
  have hp : stabPoly f = stabPoly g :=
    Polynomial.eq_of_infinite_eval_eq _ _
      (hs.mono fun ρ hρ => by simp [eval_stabPoly, h ρ hρ])
  rw [← coeff_stabPoly, ← coeff_stabPoly, hp]

/-- ... and the same low-degree weight `W^{≤k}` for every `k`. -/
theorem lowWeight_eq_of_stab_eq {n m : ℕ} (f : BFun n) (g : BFun m) {s : Set ℝ} (hs : s.Infinite)
    (h : ∀ ρ ∈ s, stab ρ f = stab ρ g) (k : ℕ) : lowWeight f k = lowWeight g k := by
  rw [lowWeight_eq_sum, lowWeight_eq_sum]
  exact Finset.sum_congr rfl fun j _ => weight_eq_of_stab_eq f g hs h j

/-! ### Non-vacuity: the first two clauses alone are satisfiable

Noise stability is invariant under relabelling the variables, while the spectral distribution
(on sets) is not. So the two dictators `x_0` and `x_1` have identical noise stability and different
spectral distributions; by `weight_eq_of_stab_eq` they still have the same degree weights. -/

/-- Relabel the variables of `f` by a permutation `σ`. -/
def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : BFun n) : BFun n := fun x => f (x ∘ σ)

/-- Precomposition with `σ`, as a bijection of the cube. -/
def cubePerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Cube n ≃ Cube n where
  toFun x := x ∘ σ
  invFun x := x ∘ σ.symm
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

theorem stab_relabel {n : ℕ} (ρ : ℝ) (σ : Equiv.Perm (Fin n)) (f : BFun n) :
    stab ρ (relabel σ f) = stab ρ f := by
  unfold stab relabel
  refine Fintype.sum_equiv (cubePerm σ) _ _ fun x => ?_
  refine Fintype.sum_equiv (cubePerm σ) _ _ fun y => ?_
  have : noiseKernel ρ x y = noiseKernel ρ (x ∘ σ) (y ∘ σ) := by
    unfold noiseKernel
    exact (Equiv.prod_comp σ (fun i => if y i = x i then (1 + ρ) / 2 else (1 - ρ) / 2)).symm
  simp only [cubePerm, Equiv.coe_fn_mk, this]

/-- The dictator `x ↦ x_j`. -/
def dict {n : ℕ} (j : Fin n) : BFun n := fun x => sgn (x j)

theorem sgn_cases (b : Bool) : sgn b = 1 ∨ sgn b = -1 := by cases b <;> simp [sgn]

theorem first_clauses_satisfiable :
    IsBoolean (dict (0 : Fin 2)) ∧ IsBoolean (dict (1 : Fin 2)) ∧
      (∀ ρ : ℝ, stab ρ (dict (0 : Fin 2)) = stab ρ (dict (1 : Fin 2))) ∧
      spectralDist (dict (0 : Fin 2)) ≠ spectralDist (dict (1 : Fin 2)) := by
  refine ⟨fun x => sgn_cases _, fun x => sgn_cases _, fun ρ => ?_, fun h => ?_⟩
  · have : dict (1 : Fin 2) = relabel (Equiv.swap 0 1) (dict 0) := by
      ext x; simp [dict, relabel]
    rw [this, stab_relabel]
  · have h0 : fourier (dict (0 : Fin 2)) {0} = 1 := by
      have : ∀ x : Cube 2, dict 0 x * chi {0} x = 1 := fun x => by
        rcases sgn_cases (x 0) with h | h <;> simp [dict, chi, h]
      simp [fourier, this]; norm_num
    have h1 : fourier (dict (1 : Fin 2)) {0} = 0 := by
      have hp := Finset.prod_univ_sum (fun _ : Fin 2 => (univ : Finset Bool)) (fun _ b => sgn b)
      rw [Fintype.piFinset_univ] at hp
      have : ∀ x : Cube 2, dict 1 x * chi {0} x = ∏ i, sgn (x i) := fun x => by
        simp [dict, chi, Fin.prod_univ_two, mul_comm]
      simp only [fourier, this, ← hp]
      simp [sgn]
    have := congrFun h {0}
    simp [spectralDist, h0, h1] at this

/-! ### The conjecture -/

/-- The realizing clause: a pair (of possibly different arities) with the same noise stability at
every `ρ ∈ [0,1]` (a weaker requirement than equality on `[-1,1]`) but different low-degree
weights, read either as some `W^k` or as some `W^{≤k}`. -/
def RealizingPair {n m : ℕ} (f : BFun n) (g : BFun m) : Prop :=
  (∀ ρ ∈ Set.Icc (0 : ℝ) 1, stab ρ f = stab ρ g) ∧
    ((∃ k, weight f k ≠ weight g k) ∨ (∃ k, lowWeight f k ≠ lowWeight g k))

/-- No pair of real-valued functions on Boolean cubes realizes the clause. -/
theorem no_realizing_pair {n m : ℕ} (f : BFun n) (g : BFun m) : ¬ RealizingPair f g := by
  rintro ⟨h, ⟨k, hk⟩ | ⟨k, hk⟩⟩
  · exact hk (weight_eq_of_stab_eq f g (Set.Icc_infinite zero_lt_one) h k)
  · exact hk (lowWeight_eq_of_stab_eq f g (Set.Icc_infinite zero_lt_one) h k)

/-- The conjecture: two Boolean functions with identical noise stability (all `ρ ∈ [-1,1]`) and
different spectral distributions, together with an explicit pair of Boolean functions (possibly the
same pair) that has the same stability but different low-degree weights. -/
def Statement : Prop :=
  ∃ (n : ℕ) (f g : BFun n), IsBoolean f ∧ IsBoolean g ∧
    (∀ ρ ∈ Set.Icc (-1 : ℝ) 1, stab ρ f = stab ρ g) ∧ spectralDist f ≠ spectralDist g ∧
    ∃ (n' m' : ℕ) (f' : BFun n') (g' : BFun m'), IsBoolean f' ∧ IsBoolean g' ∧
      RealizingPair f' g'

/-- **Conjecture 00000006120 is false.** -/
theorem conjecture6120_false : ¬ Statement := by
  rintro ⟨_, _, _, _, _, _, _, _, _, f', g', _, _, hr⟩
  exact no_realizing_pair f' g' hr

end Conjecture6120
