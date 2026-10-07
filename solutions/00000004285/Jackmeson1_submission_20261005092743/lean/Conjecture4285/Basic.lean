import Mathlib

/-!
# Conjecture 00000004285 (minimal cardinal spectrum of n-free groups) is false

Statement (bilingual source): *n-free* means every subset of size at most `n` is contained in a
free pure subgroup. Conjecture: the smallest cardinality of a group that is `n`-free but not
`(n+1)`-free is `ℵ_{n-1}`, the cardinal spectrum is strictly increasing, and the bound is optimal.

Reading: abelian groups (purity is an abelian-group notion), `n` a natural number,
"free" = free abelian (`Module.Free ℤ`), "pure" = `mA ∩ H = mH` for all integers `m`.

We construct a countable abelian group `G ⊆ ℚ³` that is `2`-free but not `3`-free, so for
`n = 2` the least cardinality is at most `ℵ₀ < ℵ₁ = ℵ_{2-1}`.

`G = ℤ³ + Σ_k ℤ·w_k`, `w_k = (1, k, k²)/p_k`, where `p_k` is the `k³`-th prime.
* not `3`-free: a pure subgroup `H ∋ e₀, e₁, e₂` contains every `w_k`; every homomorphism
  `f : H → ℤ` then satisfies `p_k ∣ f(e₀) + k f(e₁) + k² f(e₂)` for all `k`, which forces
  `f(e₀) = 0`; so `H` is not free.
* `2`-free: two elements are orthogonal to a nonzero integer vector `N`; `H = G ∩ N^⊥` is pure,
  and its elements have bounded denominators (only the finitely many `k` with
  `p_k ∣ N·(1,k,k²)` contribute), so `H` is finitely generated and torsion-free, hence free.
-/

open Cardinal

namespace C4285

/-- `H` is a pure subgroup of `A`: `mA ∩ H ⊆ mH` for every integer `m`. (The reverse inclusion
`mH ⊆ mA ∩ H` always holds, so this says `mA ∩ H = mH`.) -/
def IsPureSubgroup {A : Type*} [AddCommGroup A] (H : AddSubgroup A) : Prop :=
  ∀ (m : ℤ) (g : A), m • g ∈ H → ∃ h ∈ H, m • h = m • g

/-- `A` is `n`-free: every subset of `A` with at most `n` elements is contained in a pure
subgroup that is a free abelian group. -/
def NFree (n : ℕ) (A : Type*) [AddCommGroup A] : Prop :=
  ∀ S : Finset A, S.card ≤ n →
    ∃ H : AddSubgroup A, (S : Set A) ⊆ H ∧ IsPureSubgroup H ∧ Module.Free ℤ H

/-! ### Arithmetic input -/

/-- `p k` is the `k³`-th prime (0-indexed). -/
noncomputable def p (k : ℕ) : ℕ := Nat.nth Nat.Prime (k ^ 3)

lemma p_prime (k : ℕ) : (p k).Prime := Nat.prime_nth_prime _

lemma p_inj : Function.Injective p := fun a b h =>
  Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0)
    ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h)

lemma p_ge (k : ℕ) : k ^ 3 ≤ p k :=
  (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le _

/-- The quadratic `a₀ + a₁ k + a₂ k²`. -/
def q (a : Fin 3 → ℤ) (k : ℕ) : ℤ := a 0 + a 1 * k + a 2 * (k : ℤ) ^ 2

lemma roots_finite (a : Fin 3 → ℤ) (ha : a ≠ 0) : {k : ℕ | q a k = 0}.Finite := by
  classical
  let P : Polynomial ℤ := Polynomial.C (a 0) + Polynomial.C (a 1) * Polynomial.X +
    Polynomial.C (a 2) * Polynomial.X ^ 2
  have hP : P ≠ 0 := by
    intro h
    apply ha
    have h0 := congrArg (fun P => Polynomial.coeff P 0) h
    have h1 := congrArg (fun P => Polynomial.coeff P 1) h
    have h2 := congrArg (fun P => Polynomial.coeff P 2) h
    simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at h0 h1 h2
    norm_num at h0 h1 h2
    funext i
    fin_cases i <;> simp [h0, h1, h2]
  refine ((Polynomial.finite_setOfPred_isRoot hP).preimage Nat.cast_injective.injOn).subset ?_
  intro k hk
  simp only [Set.mem_ofPred_eq, q] at hk
  simp [P, hk]

lemma bad_finite (a : Fin 3 → ℤ) (ha : a ≠ 0) : {k : ℕ | (p k : ℤ) ∣ q a k}.Finite := by
  set A : ℤ := |a 0| + |a 1| + |a 2| with hA
  refine ((Set.finite_lt_nat (A.toNat + 2)).union (roots_finite a ha)).subset ?_
  intro k hk
  by_cases hq : q a k = 0
  · exact Or.inr hq
  left
  by_contra hlt
  simp only [Set.mem_ofPred_eq, not_lt] at hlt hk
  have hk1 : A + 2 ≤ (k : ℤ) := by
    have := Int.self_le_toNat A
    omega
  have hdiv : (p k : ℤ) ≤ |q a k| := Int.le_of_dvd (abs_pos.2 hq) ((dvd_abs _ _).2 hk)
  have hpk : (k : ℤ) ^ 3 ≤ p k := by exact_mod_cast p_ge k
  have hk0 : (1 : ℤ) ≤ k := by
    have : 0 ≤ A := by positivity
    linarith
  have hk2 : (k : ℤ) ≤ (k : ℤ) ^ 2 := by nlinarith
  have hk3 : (1 : ℤ) ≤ (k : ℤ) ^ 2 := le_trans hk0 hk2
  have hbound : |q a k| ≤ A * (k : ℤ) ^ 2 := by
    unfold q
    have e1 : |a 1 * (k : ℤ)| = |a 1| * k := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (k : ℤ) by positivity)]
    have e2 : |a 2 * (k : ℤ) ^ 2| = |a 2| * k ^ 2 := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (k : ℤ) ^ 2 by positivity)]
    have t := (abs_add_le (a 0 + a 1 * k) (a 2 * (k : ℤ) ^ 2)).trans
      (add_le_add_left (abs_add_le (a 0) (a 1 * k)) _)
    rw [e1, e2] at t
    have f0 : |a 0| ≤ |a 0| * (k : ℤ) ^ 2 := le_mul_of_one_le_right (abs_nonneg _) hk3
    have f1 : |a 1| * (k : ℤ) ≤ |a 1| * (k : ℤ) ^ 2 := mul_le_mul_of_nonneg_left hk2 (abs_nonneg _)
    rw [hA]
    linarith
  have hlt3 : A * (k : ℤ) ^ 2 < (k : ℤ) ^ 3 := by
    have h2 : (0 : ℤ) < (k : ℤ) ^ 2 := by positivity
    have := mul_lt_mul_of_pos_right (show A < (k : ℤ) by linarith) h2
    linarith [show (k : ℤ) ^ 3 = (k : ℤ) * (k : ℤ) ^ 2 by ring]
  linarith

/-! ### The group -/

/-- The generators `w k = (1, k, k²) / p_k`. -/
noncomputable def w (k : ℕ) : Fin 3 → ℚ := fun i => (k : ℚ) ^ (i : ℕ) / p k

/-- `(z, c) ↦ z + Σ_k c_k w_k`. -/
noncomputable def φ : (Fin 3 → ℤ) × (ℕ →₀ ℤ) →+ (Fin 3 → ℚ) :=
  AddMonoidHom.coprod (AddMonoidHom.compLeft (Int.castAddHom ℚ) (Fin 3))
    (Finsupp.linearCombination ℤ w).toAddMonoidHom

lemma φ_apply (z : Fin 3 → ℤ) (c : ℕ →₀ ℤ) (i : Fin 3) :
    φ (z, c) i = z i + ∑ k ∈ c.support, (c k : ℚ) * w k i := by
  simp [φ, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]

/-- The group `G = ℤ³ + Σ_k ℤ w_k ⊆ ℚ³`. -/
noncomputable def G : AddSubgroup (Fin 3 → ℚ) := φ.range


lemma φ_E (i : Fin 3) : φ (Pi.single i 1, 0) = Pi.single i 1 := by
  funext j
  simp [φ, Pi.single_apply]

lemma φ_W (k : ℕ) : φ (0, Finsupp.single k 1) = w k := by
  simp [φ]

/-- The dot product `x ↦ Σ_i N_i x_i` as an additive map. -/
def dotN (N : Fin 3 → ℤ) : (Fin 3 → ℚ) →+ ℚ where
  toFun x := ∑ i, (N i : ℚ) * x i
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

lemma dot_φ (N z : Fin 3 → ℤ) (c : ℕ →₀ ℤ) :
    dotN N (φ (z, c)) = ((∑ i, N i * z i : ℤ) : ℚ) +
      ∑ k ∈ c.support, (c k : ℚ) * q N k / p k := by
  have hk : ∀ k ∈ c.support, (c k : ℚ) * q N k / p k =
      N 0 * ((c k : ℚ) * w k 0) + N 1 * ((c k : ℚ) * w k 1) + N 2 * ((c k : ℚ) * w k 2) := by
    intro k _
    simp only [q, w]
    push_cast
    simp
    ring
  rw [Finset.sum_congr rfl hk, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [dotN, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.sum_univ_three, φ_apply]
  push_cast
  ring

/-- Key step: if `N·g = 0` and `p_j ∤ N·(1,j,j²)` then the coefficient `c_j` is divisible by
`p_j`. -/
lemma key_dvd (N z : Fin 3 → ℤ) (c : ℕ →₀ ℤ) (h : dotN N (φ (z, c)) = 0) (j : ℕ)
    (hj : j ∈ c.support) (hbad : ¬ (p j : ℤ) ∣ q N j) : (p j : ℤ) ∣ c j := by
  classical
  set F := c.support
  set P : ℤ := ∏ k ∈ F, (p k : ℤ)
  set T : ℕ → ℤ := fun k => ∏ l ∈ F.erase k, (p l : ℤ)
  have hT : ∀ k ∈ F, ((c k * q N k * T k : ℤ) : ℚ) = (P : ℚ) * ((c k : ℚ) * q N k / p k) := by
    intro k hk
    have hp : (p k : ℚ) ≠ 0 := by exact_mod_cast (p_prime k).ne_zero
    have e : P = (p k : ℤ) * T k := (Finset.mul_prod_erase F (fun l => (p l : ℤ)) hk).symm
    rw [e]
    push_cast
    field_simp
  have hE : P * (∑ i, N i * z i) + ∑ k ∈ F, c k * q N k * T k = 0 := by
    have : ((P * (∑ i, N i * z i) + ∑ k ∈ F, c k * q N k * T k : ℤ) : ℚ) = 0 := by
      rw [Int.cast_add, Int.cast_mul, show ((∑ k ∈ F, c k * q N k * T k : ℤ) : ℚ) =
        ∑ k ∈ F, ((c k * q N k * T k : ℤ) : ℚ) from Int.cast_sum _ _,
        Finset.sum_congr rfl hT, ← Finset.mul_sum,
        ← mul_add, ← dot_φ, h, mul_zero]
    exact_mod_cast this
  rw [← Finset.add_sum_erase F _ hj] at hE
  have hpP : (p j : ℤ) ∣ P := Finset.dvd_prod_of_mem _ hj
  have hpS : (p j : ℤ) ∣ ∑ k ∈ F.erase j, c k * q N k * T k := by
    refine Finset.dvd_sum fun k hk => dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ ?_) _
    rcases Finset.mem_erase.1 hk with ⟨hkj, _⟩
    exact Finset.mem_erase.2 ⟨Ne.symm hkj, hj⟩
  have hmain : (p j : ℤ) ∣ c j * q N j * T j := by
    have e : c j * q N j * T j = -(P * ∑ i, N i * z i) - ∑ k ∈ F.erase j, c k * q N k * T k := by
      linarith
    rw [e]
    exact dvd_sub (dvd_neg.2 (dvd_mul_of_dvd_left hpP _)) hpS
  have hpj : Prime (p j : ℤ) := Nat.prime_iff_prime_int.mp (p_prime j)
  have hTj : ¬ (p j : ℤ) ∣ T j := by
    intro hd
    obtain ⟨l, hl, hdl⟩ := (Prime.dvd_finsetProd_iff hpj _).1 hd
    have := (Nat.prime_dvd_prime_iff_eq (p_prime j) (p_prime l)).1 (Int.natCast_dvd_natCast.1 hdl)
    exact (Finset.mem_erase.1 hl).1 (p_inj this).symm
  rcases hpj.dvd_or_dvd hmain with h1 | h1
  · rcases hpj.dvd_or_dvd h1 with h2 | h2
    · exact h2
    · exact absurd h2 hbad
  · exact absurd h1 hTj


/-- The integers inside `ℚ`. -/
def Zs : AddSubgroup ℚ := (Int.castAddHom ℚ).range

lemma int_mem (t : ℤ) : (t : ℚ) ∈ Zs := ⟨t, rfl⟩

/-- Bounded denominators on `G ∩ N^⊥`: only the finitely many bad `k` contribute. -/
lemma bounded_den (N : Fin 3 → ℤ) (hN : N ≠ 0) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ g ∈ G, dotN N g = 0 → ∀ i, (M : ℚ) * g i ∈ Zs := by
  classical
  set B := (bad_finite N hN).toFinset
  refine ⟨∏ k ∈ B, (p k : ℤ),
    Finset.prod_ne_zero_iff.2 fun k _ => by exact_mod_cast (p_prime k).ne_zero, ?_⟩
  rintro g ⟨⟨z, c⟩, rfl⟩ hg i
  rw [φ_apply, mul_add]
  refine add_mem (by exact_mod_cast int_mem _) ?_
  rw [Finset.mul_sum]
  refine AddSubgroup.sum_mem _ fun k hk => ?_
  have hp : (p k : ℚ) ≠ 0 := by exact_mod_cast (p_prime k).ne_zero
  by_cases hkB : k ∈ B
  · obtain ⟨T, hT⟩ : (p k : ℤ) ∣ ∏ k ∈ B, (p k : ℤ) := Finset.dvd_prod_of_mem _ hkB
    rw [hT]
    refine ⟨T * c k * (k : ℤ) ^ (i : ℕ), ?_⟩
    simp only [w, Int.coe_castAddHom]
    push_cast
    field_simp
  · have hbad : ¬ (p k : ℤ) ∣ q N k := by simpa [B] using hkB
    obtain ⟨d, hd⟩ := key_dvd N z c hg k hk hbad
    refine ⟨(∏ k ∈ B, (p k : ℤ)) * d * (k : ℤ) ^ (i : ℕ), ?_⟩
    simp only [w, Int.coe_castAddHom, hd]
    push_cast
    field_simp

/-- The group as a type. -/
abbrev GT : Type := ↥G

/-- `ψ_N : G → ℚ`, `g ↦ N·g`. -/
noncomputable def ψ (N : Fin 3 → ℤ) : GT →+ ℚ := (dotN N).comp G.subtype

lemma normal_vector (S : Finset GT) (hS : S.card ≤ 2) :
    ∃ N : Fin 3 → ℤ, N ≠ 0 ∧ ∀ s ∈ S, dotN N (s : Fin 3 → ℚ) = 0 := by
  classical
  let Mat : Matrix S (Fin 3) ℚ := Matrix.of fun s i => ((s : GT) : Fin 3 → ℚ) i
  have hlt : Module.finrank ℚ (S → ℚ) < Module.finrank ℚ (Fin 3 → ℚ) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin]
    omega
  obtain ⟨x, hx, hx0⟩ :=
    (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := Mat.mulVecLin) hlt)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) Finset.univ x
  choose N hN using fun i => (RingHom.mem_rangeS).1 (hb i (Finset.mem_univ i))
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have e : ∀ i, (N i : ℚ) = (b : ℤ) * x i := fun i => by simpa [zsmul_eq_mul] using hN i
  refine ⟨N, ?_, ?_⟩
  · intro h0
    apply hx0
    funext i
    have := e i
    simp only [h0, Pi.zero_apply, Int.cast_zero] at this
    have hb' : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hb0
    simpa [hb'] using this.symm
  · intro s hs
    have := congrFun (LinearMap.mem_ker.1 hx) ⟨s, hs⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Mat, Matrix.of_apply,
      Pi.zero_apply] at this
    simp only [dotN, AddMonoidHom.coe_mk, ZeroHom.coe_mk, e]
    calc ∑ i, ((b : ℤ) : ℚ) * x i * (s : Fin 3 → ℚ) i
        = ((b : ℤ) : ℚ) * ∑ i, (s : Fin 3 → ℚ) i * x i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [this, mul_zero]

lemma pure_ker (N : Fin 3 → ℤ) : IsPureSubgroup (ψ N).ker := by
  intro m g hg
  by_cases hm : m = 0
  · exact ⟨0, zero_mem _, by simp [hm]⟩
  · refine ⟨g, ?_, rfl⟩
    rw [AddMonoidHom.mem_ker, map_zsmul, zsmul_eq_mul] at hg
    rw [AddMonoidHom.mem_ker]
    exact (mul_eq_zero.1 hg).resolve_left (by exact_mod_cast hm)

lemma free_ker (N : Fin 3 → ℤ) (hN : N ≠ 0) : Module.Free ℤ (ψ N).ker := by
  obtain ⟨M, hM, hden⟩ := bounded_den N hN
  let Lmap : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℚ) :=
    (AddMonoidHom.compLeft (Int.castAddHom ℚ) (Fin 3)).toIntLinearMap
  let ι : (ψ N).ker →ₗ[ℤ] (Fin 3 → ℚ) :=
    M • ((G.subtype.comp (ψ N).ker.subtype).toIntLinearMap)
  have hmem : ∀ h, ι h ∈ LinearMap.range Lmap := by
    intro h
    have hg := hden ((h : GT) : Fin 3 → ℚ) (h : GT).2 h.2
    choose t ht using hg
    refine ⟨t, funext fun i => ?_⟩
    simp only [Lmap, ι, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.compLeft_apply,
      Function.comp_apply, LinearMap.smul_apply, Pi.smul_apply, zsmul_eq_mul]
    simpa using ht i
  let f := LinearMap.codRestrict (LinearMap.range Lmap) ι hmem
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    simp only [f, LinearMap.codRestrict_apply, ι, LinearMap.smul_apply,
      AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp, Function.comp_apply] at h1
    exact Subtype.ext (Subtype.ext (smul_right_injective _ hM h1))
  have : Module.Finite ℤ (ψ N).ker := Module.Finite.of_injective f hf
  have : Module.IsTorsionFree ℤ (ψ N).ker :=
    (Subtype.coe_injective.comp Subtype.coe_injective).moduleIsTorsionFree _ (fun _ _ => rfl)
  exact Module.free_of_finite_type_torsion_free'

/-- `G` is `2`-free. -/
theorem G_two_free : NFree 2 GT := by
  intro S hS
  obtain ⟨N, hN, hSN⟩ := normal_vector S hS
  exact ⟨(ψ N).ker, fun s hs => hSN s hs, pure_ker N, free_ker N hN⟩


/-- The standard basis vectors `e_i ∈ G`. -/
noncomputable def E (i : Fin 3) : GT := ⟨φ (Pi.single i 1, 0), ⟨_, rfl⟩⟩

/-- The generators `w_k ∈ G`. -/
noncomputable def W (k : ℕ) : GT := ⟨φ (0, Finsupp.single k 1), ⟨_, rfl⟩⟩

lemma rel (k : ℕ) : (p k : ℤ) • W k = E 0 + (k : ℤ) • E 1 + ((k : ℤ) ^ 2) • E 2 := by
  apply Subtype.ext
  have hp : (p k : ℚ) ≠ 0 := by exact_mod_cast (p_prime k).ne_zero
  simp only [E, W, AddSubgroup.coe_add, AddSubgroup.coe_zsmul, φ_E, φ_W]
  funext i
  fin_cases i <;> simp [w] <;> field_simp

/-- `G` is not `3`-free: no free pure subgroup contains `e₀, e₁, e₂`. -/
theorem G_not_three_free : ¬ NFree 3 GT := by
  classical
  intro h3
  obtain ⟨H, hSH, hpure, hfree⟩ := h3 {E 0, E 1, E 2} Finset.card_le_three
  have hE : ∀ i, E i ∈ H := by
    intro i
    fin_cases i <;> apply hSH <;> simp
  have : Module.IsTorsionFree ℤ GT := Subtype.coe_injective.moduleIsTorsionFree _ (fun _ _ => rfl)
  have hW : ∀ k, W k ∈ H := by
    intro k
    obtain ⟨h, hh, he⟩ := hpure (p k) (W k) (by
      rw [rel]
      exact add_mem (add_mem (hE 0) (zsmul_mem (hE 1) _)) (zsmul_mem (hE 2) _))
    have hp : (p k : ℤ) ≠ 0 := by exact_mod_cast (p_prime k).ne_zero
    have : h = W k := smul_right_injective GT hp he
    exact this ▸ hh
  let b := Module.Free.chooseBasis ℤ H
  let x0 : H := ⟨E 0, hE 0⟩
  have hx0 : x0 ≠ 0 := by
    intro h
    have := congrArg (fun y : H => ((y : GT) : Fin 3 → ℚ) 0) h
    simp [x0, E, φ_E] at this
  obtain ⟨i, hi⟩ : ∃ i, b.repr x0 i ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hx0
    exact b.repr.injective (by ext i; simp [hc i])
  set f := b.coord i
  set a : Fin 3 → ℤ := fun j => f ⟨E j, hE j⟩ with ha_def
  have hdvd : ∀ k, (p k : ℤ) ∣ q a k := by
    intro k
    refine ⟨f ⟨W k, hW k⟩, ?_⟩
    have hrel : (p k : ℤ) • (⟨W k, hW k⟩ : H) =
        ⟨E 0, hE 0⟩ + (k : ℤ) • ⟨E 1, hE 1⟩ + ((k : ℤ) ^ 2) • ⟨E 2, hE 2⟩ :=
      Subtype.ext (by simpa using rel k)
    have := congrArg f hrel
    simp only [map_add, map_zsmul, smul_eq_mul] at this
    simp only [q, a]
    linarith
  have ha : a = 0 := by
    by_contra ha
    exact Set.infinite_univ ((bad_finite a ha).subset fun k _ => hdvd k)
  have : f x0 = 0 := congrFun ha 0
  exact hi (by simpa [f] using this)

/-- A countable abelian group that is `2`-free but not `3`-free. -/
theorem exists_countable_two_free_not_three_free :
    ∃ (A : Type) (_ : AddCommGroup A), #A ≤ ℵ₀ ∧ NFree 2 A ∧ ¬ NFree 3 A :=
  ⟨GT, inferInstance, Cardinal.mk_le_aleph0, G_two_free, G_not_three_free⟩

/-- The conjecture's main claim: for every `n ≥ 1`, `ℵ_{n-1}` is the least cardinality of an
abelian group that is `n`-free but not `(n+1)`-free. -/
def MinCardClaim : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsLeast
    {κ : Cardinal.{0} | ∃ (A : Type) (_ : AddCommGroup A),
      #A = κ ∧ NFree n A ∧ ¬ NFree (n + 1) A}
    (ℵ_ ((n - 1 : ℕ) : Ordinal))

/-- **Main theorem.** The claim fails at `n = 2`: `ℵ₁` is not a lower bound, because the
countable group `G` is `2`-free but not `3`-free. -/
theorem not_minCardClaim : ¬ MinCardClaim := by
  intro h
  have hlb := (h 2 (by norm_num)).2 ⟨GT, inferInstance, rfl, G_two_free, G_not_three_free⟩
  have h1 : ℵ_ ((2 - 1 : ℕ) : Ordinal) = ℵ₁ := by norm_num
  rw [h1] at hlb
  exact absurd (hlb.trans Cardinal.mk_le_aleph0) (not_le.2 aleph0_lt_aleph_one)

end C4285
