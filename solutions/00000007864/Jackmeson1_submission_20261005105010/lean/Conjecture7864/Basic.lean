import Mathlib

/-!
# Conjecture 00000007864: the entropy deficit of the men-optimal stable matching

There are `n` men and `n` women, both indexed by `Fin n`. Every person has a strict preference list over
the other side, and all `2n` lists are independent and uniformly distributed. `σ_m` is the men-optimal
stable matching. The conjecture asserts, among other things, that the entropy deficit
`D_n = n log n - H(σ_m)` is linear with deficit constant `c* = π^2/6`, i.e. `D_n / n → π^2/6`.

We prove:
* (Gale-Shapley) every profile has a unique men-optimal stable matching (`exists_menOptimal`,
  `menOptimal_unique`);
* relabelling the women commutes with the men-optimal map, so the law of `σ_m` is exactly the uniform law
  on `S_n` (`law_menOpt_eq_uniform`);
* hence `H(σ_m) = log n!` (`entropy_menOpt`), `n - 1 - (1/2) log n ≤ D_n ≤ n` for `n ≥ 1`, and
  `D_n / n → 1`, while `π^2/6 > 1` (`conjecture_7864_false`). The same holds in bits (`bits_version`).
-/

open Finset Filter Topology

namespace C7864

/-- A preference profile. `P.1 m` is man `m`'s strict preference list over the women, encoded as a rank
function: `P.1 m w` is the position of woman `w` in his list (`0` = most preferred). `P.2 w` is woman
`w`'s rank function over the men. Rank functions `Fin n ≃ Fin n` correspond bijectively to strict total
orders (preference lists) on `Fin n`. -/
abbrev Profile (n : ℕ) := (Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n))

/-- A perfect matching: man `m` is married to woman `μ m` (so woman `w` to man `μ.symm w`). -/
abbrev Matching (n : ℕ) := Equiv.Perm (Fin n)

variable {n : ℕ}

/-- `(m, w)` blocks `μ`: `m` strictly prefers `w` to his wife and `w` strictly prefers `m` to her husband. -/
def Blocks (P : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  P.1 m w < P.1 m (μ m) ∧ P.2 w m < P.2 w (μ.symm w)

/-- A matching is stable if it has no blocking pair. -/
def IsStable (P : Profile n) (μ : Matching n) : Prop := ∀ m w, ¬ Blocks P μ m w

/-- `μ` is the men-optimal stable matching: it is stable and every man weakly prefers his wife in `μ` to
his wife in any stable matching. -/
def IsMenOptimal (P : Profile n) (μ : Matching n) : Prop :=
  IsStable P μ ∧ ∀ ν, IsStable P ν → ∀ m, P.1 m (μ m) ≤ P.1 m (ν m)

/-! ### Existence: the deferred-acceptance (Gale-Shapley) invariant -/

section GaleShapley

variable (P : Profile n)

/-- With rejected pairs `R` (`(m, w) ∈ R` means `w` has rejected `m`), man `m` currently proposes to `w`:
`w` is his most preferred woman who has not rejected him. -/
def Proposes (R : Finset (Fin n × Fin n)) (m w : Fin n) : Prop :=
  (m, w) ∉ R ∧ ∀ v, P.1 m v < P.1 m w → (m, v) ∈ R

/-- The deferred-acceptance invariant: no rejected pair is matched in any stable matching, and every
woman who rejected a man currently receives a proposal from a man she prefers to him. -/
def Inv (R : Finset (Fin n × Fin n)) : Prop :=
  (∀ m w, (m, w) ∈ R → ∀ ν, IsStable P ν → ν m ≠ w) ∧
  (∀ m w, (m, w) ∈ R → ∃ m', Proposes P R m' w ∧ P.2 w m' < P.2 w m)

variable {P}

lemma proposes_unique {R : Finset (Fin n × Fin n)} {m w w' : Fin n} (h : Proposes P R m w)
    (h' : Proposes P R m w') : w = w' := by
  by_contra hne
  rcases lt_or_gt_of_ne (fun e => hne ((P.1 m).injective e)) with hlt | hlt
  · exact h.1 (h'.2 w hlt)
  · exact h'.1 (h.2 w' hlt)

lemma exists_proposes {R : Finset (Fin n × Fin n)} (hR : Inv P R) (m : Fin n) :
    ∃ w, Proposes P R m w := by
  classical
  by_cases hne : (univ.filter fun w => (m, w) ∉ R).Nonempty
  · obtain ⟨w, hw, hmin⟩ := (univ.filter fun w => (m, w) ∉ R).exists_min_image (P.1 m) hne
    refine ⟨w, (mem_filter.1 hw).2, fun v hv => ?_⟩
    by_contra hvR
    exact absurd (hmin v (mem_filter.2 ⟨mem_univ _, hvR⟩)) (not_le.2 hv)
  · -- `m` was rejected by every woman: then `n` women hold proposals from the other `n - 1` men.
    exfalso
    have hall : ∀ w, (m, w) ∈ R := fun w => by
      by_contra h; exact hne ⟨w, mem_filter.2 ⟨mem_univ _, h⟩⟩
    choose f hf using fun w => hR.2 m w (hall w)
    have hinj : Function.Injective f := fun w w' e =>
      proposes_unique (hf w).1 (by rw [e]; exact (hf w').1)
    have hmaps : ∀ w, f w ∈ univ.erase m := fun w =>
      mem_erase.2 ⟨fun e => (hf w).1.1 (by rw [e]; exact hall w), mem_univ _⟩
    have hc := Finset.card_le_card_of_injOn f (s := univ) (t := univ.erase m)
      (fun w _ => hmaps w) (fun a _ b _ e => hinj e)
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hc
    have := m.pos
    omega

/-- **Gale-Shapley.** Every preference profile has a men-optimal stable matching. -/
theorem exists_menOptimal (P : Profile n) : ∃ μ, IsMenOptimal P μ := by
  classical
  obtain ⟨R, hRmem, hRmax⟩ := (univ.filter fun R : Finset (Fin n × Fin n) => Inv P R).exists_max_image
    Finset.card ⟨∅, mem_filter.2 ⟨mem_univ _, by simp [Inv]⟩⟩
  have hR : Inv P R := (mem_filter.1 hRmem).2
  choose p hp using exists_proposes hR
  by_cases hinj : Function.Injective p
  · -- every woman receives at most one proposal: the proposals form the men-optimal stable matching
    let μ : Matching n := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj)
    have hμ : ∀ m, μ m = p m := fun m => rfl
    have hstab : IsStable P μ := by
      rintro m w ⟨h1, h2⟩
      rw [hμ] at h1
      obtain ⟨m', hm', hlt⟩ := hR.2 m w ((hp m).2 w h1)
      have h3 : μ m' = w := by rw [hμ]; exact proposes_unique (hp m') hm'
      have h4 : μ.symm w = m' := by rw [← h3]; simp
      rw [h4] at h2
      exact lt_asymm h2 hlt
    refine ⟨μ, hstab, fun ν hν m => ?_⟩
    rw [hμ]
    by_contra hlt
    exact hR.1 m (ν m) ((hp m).2 _ (not_le.1 hlt)) ν hν rfl
  · -- two men propose to the same woman: she rejects the one she likes less, and `R` was not maximal
    exfalso
    obtain ⟨a, b, hab, hne⟩ : ∃ a b, p a = p b ∧ a ≠ b := by
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨a, b, h, hne⟩ := hinj
      exact ⟨a, b, h, hne⟩
    have hpb : Proposes P R b (p a) := by rw [hab]; exact hp b
    obtain ⟨w, l, wn, hl, hw, hneq, hlt⟩ : ∃ w l wn, Proposes P R l w ∧ Proposes P R wn w ∧
        l ≠ wn ∧ P.2 w wn < P.2 w l := by
      rcases lt_or_gt_of_ne (fun e => hne ((P.2 (p a)).injective e)) with h | h
      · exact ⟨p a, b, a, hpb, hp a, hne.symm, h⟩
      · exact ⟨p a, a, b, hp a, hpb, hne, h⟩
    have lift : ∀ m' v, m' ≠ l → Proposes P R m' v → Proposes P (insert (l, w) R) m' v := by
      intro m' v hm' h
      refine ⟨?_, fun u hu => mem_insert_of_mem (h.2 u hu)⟩
      rw [mem_insert, not_or]
      exact ⟨fun e => hm' (Prod.mk.inj e).1, h.1⟩
    have hwn' : Proposes P (insert (l, w) R) wn w := lift wn w (Ne.symm hneq) hw
    have hInv' : Inv P (insert (l, w) R) := by
      refine ⟨fun m v hmv ν hν hνmv => ?_, fun m v hmv => ?_⟩
      · rcases mem_insert.1 hmv with e | hmv
        · obtain ⟨e1, e2⟩ := Prod.mk.inj e
          rw [e1, e2] at hνmv
          -- `ν l = w`; then `(wn, w)` blocks `ν`
          have hwnw : ν wn ≠ w := fun e' => hneq (ν.injective (hνmv.trans e'.symm))
          have hnotR : (wn, ν wn) ∉ R := fun h => hR.1 wn (ν wn) h ν hν rfl
          have h1 : P.1 wn w < P.1 wn (ν wn) := by
            rcases lt_trichotomy (P.1 wn w) (P.1 wn (ν wn)) with h | h | h
            · exact h
            · exact absurd ((P.1 wn).injective h).symm hwnw
            · exact absurd (hw.2 _ h) hnotR
          have hs : ν.symm w = l := by rw [← hνmv]; simp
          exact hν wn w ⟨h1, by rw [hs]; exact hlt⟩
        · exact hR.1 m v hmv ν hν hνmv
      · rcases mem_insert.1 hmv with e | hmv
        · obtain ⟨e1, e2⟩ := Prod.mk.inj e
          rw [e1, e2]
          exact ⟨wn, hwn', hlt⟩
        · obtain ⟨m', hm', hlt'⟩ := hR.2 m v hmv
          by_cases hml : m' = l
          · rw [hml] at hm' hlt'
            have hv : w = v := proposes_unique hl hm'
            subst hv
            exact ⟨wn, hwn', hlt.trans hlt'⟩
          · exact ⟨m', lift m' v hml hm', hlt'⟩
    have hc := hRmax _ (mem_filter.2 ⟨mem_univ _, hInv'⟩)
    rw [card_insert_of_notMem hl.1] at hc
    omega

end GaleShapley

/-- The men-optimal stable matching of a profile. -/
noncomputable def menOpt (P : Profile n) : Matching n := (exists_menOptimal P).choose

lemma menOpt_spec (P : Profile n) : IsMenOptimal P (menOpt P) := (exists_menOptimal P).choose_spec

/-- The men-optimal stable matching is unique. -/
theorem menOptimal_unique {P : Profile n} {μ ν : Matching n} (hμ : IsMenOptimal P μ)
    (hν : IsMenOptimal P ν) : μ = ν :=
  Equiv.ext fun m => (P.1 m).injective (le_antisymm (hμ.2 ν hν.1 m) (hν.2 μ hμ.1 m))

/-! ### Relabelling the women -/

/-- Rename woman `w` as `τ w`: men rank the renamed women as before, and woman `τ w` gets `w`'s list. -/
def relabel (τ : Equiv.Perm (Fin n)) (P : Profile n) : Profile n :=
  (fun m => τ.symm.trans (P.1 m), fun w => P.2 (τ.symm w))

lemma relabel_relabel (τ : Equiv.Perm (Fin n)) (P : Profile n) :
    relabel τ.symm (relabel τ P) = P := by
  ext <;> simp [relabel]

lemma blocks_relabel (τ : Equiv.Perm (Fin n)) (P : Profile n) (μ : Matching n) (m w : Fin n) :
    Blocks (relabel τ P) (μ.trans τ) m w ↔ Blocks P μ m (τ.symm w) := by
  simp [Blocks, relabel]

lemma stable_relabel (τ : Equiv.Perm (Fin n)) (P : Profile n) (μ : Matching n) :
    IsStable (relabel τ P) (μ.trans τ) ↔ IsStable P μ := by
  constructor
  · intro h m w hb
    exact h m (τ w) ((blocks_relabel τ P μ m (τ w)).2 (by simpa using hb))
  · intro h m w hb
    exact h _ _ ((blocks_relabel τ P μ m w).1 hb)

lemma menOptimal_relabel (τ : Equiv.Perm (Fin n)) (P : Profile n) (μ : Matching n)
    (hμ : IsMenOptimal P μ) : IsMenOptimal (relabel τ P) (μ.trans τ) := by
  refine ⟨(stable_relabel τ P μ).2 hμ.1, fun ν hν m => ?_⟩
  have hν' : IsStable P (ν.trans τ.symm) := by
    rw [← stable_relabel τ]; simpa [Equiv.trans_assoc] using hν
  simpa [relabel] using hμ.2 _ hν' m

/-- The men-optimal map commutes with relabelling the women. -/
theorem menOpt_relabel (τ : Equiv.Perm (Fin n)) (P : Profile n) :
    menOpt (relabel τ P) = (menOpt P).trans τ :=
  menOptimal_unique (menOpt_spec _) (menOptimal_relabel τ P _ (menOpt_spec P))

/-! ### The law of `σ_m` under uniform independent preferences -/

/-- The profiles whose men-optimal matching is `σ`. -/
noncomputable def fiber (n : ℕ) (σ : Matching n) : Finset (Profile n) :=
  univ.filter fun P => menOpt P = σ

lemma card_fiber_trans (σ τ : Matching n) : (fiber n (σ.trans τ)).card = (fiber n σ).card := by
  symm
  refine Finset.card_nbij' (relabel τ) (relabel τ.symm) ?_ ?_ ?_ ?_
  · intro P hP
    simp only [fiber, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hP ⊢
    rw [menOpt_relabel, hP]
  · intro P hP
    simp only [fiber, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hP ⊢
    rw [menOpt_relabel, hP, Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl]
  · intro P _; exact relabel_relabel τ P
  · intro P _; simpa using relabel_relabel τ.symm P

lemma card_fiber_mul (σ : Matching n) :
    (fiber n σ).card * n.factorial = Fintype.card (Profile n) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := menOpt) (s := (univ : Finset (Profile n)))
    (t := (univ : Finset (Matching n))) (fun _ _ => mem_coe.2 (mem_univ _))
  have hall : ∀ σ' : Matching n, (univ.filter fun P : Profile n => menOpt P = σ').card =
      (fiber n σ).card := fun σ' => by
    have := card_fiber_trans σ (σ.symm.trans σ')
    rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans] at this
    rw [← this]; rfl
  rw [Finset.sum_congr rfl (fun σ' _ => hall σ'), sum_const, smul_eq_mul] at h
  simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [h, mul_comm]

/-- The law of `σ_m` when the profile is uniform on all `(n!)^(2n)` profiles (i.e. the `2n` preference
lists are independent and uniform). -/
noncomputable def lawMenOpt (n : ℕ) : PMF (Matching n) :=
  (PMF.uniformOfFintype (Profile n)).map menOpt

lemma lawMenOpt_toReal (σ : Matching n) : (lawMenOpt n σ).toReal = 1 / n.factorial := by
  classical
  have hval : lawMenOpt n σ = ((fiber n σ).card : ENNReal) * (Fintype.card (Profile n) : ENNReal)⁻¹ := by
    rw [lawMenOpt, PMF.map_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply]
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    congr 2
    simp only [fiber]
    congr 1; ext P; simp [eq_comm]
  have hc := card_fiber_mul σ
  have hpos : 0 < (fiber n σ).card := by
    rcases Nat.eq_zero_or_pos (fiber n σ).card with h | h
    · rw [h, zero_mul] at hc; exact absurd hc.symm Fintype.card_ne_zero
    · exact h
  rw [hval, ENNReal.toReal_mul, ENNReal.toReal_inv, ← hc, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  push_cast
  have : (0 : ℝ) < (fiber n σ).card := by exact_mod_cast hpos
  have : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  field_simp

/-- **Symmetry lemma.** Under uniform independent preferences, the men-optimal stable matching is exactly
uniformly distributed on `S_n`. -/
theorem law_menOpt_eq_uniform : lawMenOpt n = PMF.uniformOfFintype (Matching n) := by
  ext σ
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    lawMenOpt_toReal, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_perm, Fintype.card_fin, one_div]

/-! ### Entropy and the deficit -/

/-- Shannon entropy (natural logarithm) of a probability distribution on a finite type:
`H(p) = ∑ -p(a) log p(a)`, with `0 log 0 = 0` (`Real.negMulLog x = -x log x`). -/
noncomputable def entropy {α : Type*} [Fintype α] (p : PMF α) : ℝ := ∑ a, Real.negMulLog (p a).toReal

/-- The entropy deficit `D_n = n log n - H(σ_m)`. -/
noncomputable def deficit (n : ℕ) : ℝ := n * Real.log n - entropy (lawMenOpt n)

/-- `H(σ_m) = log n!`. -/
theorem entropy_menOpt (n : ℕ) : entropy (lawMenOpt n) = Real.log n.factorial := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  simp only [entropy, lawMenOpt_toReal, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, Real.negMulLog, one_div, Real.log_inv]
  field_simp

theorem deficit_eq (n : ℕ) : deficit n = n * Real.log n - Real.log n.factorial := by
  rw [deficit, entropy_menOpt]

/-- `D_n ≤ n` (from `n^n / n! ≤ e^n`). -/
theorem deficit_le (n : ℕ) : deficit n ≤ n := by
  rw [deficit_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have h := Real.log_le_log (by positivity) (Real.pow_div_factorial_le_exp _ hn'.le n)
  rw [Real.log_div (by positivity) hf.ne', Real.log_pow, Real.log_exp] at h
  linarith

/-- `D_n ≥ n - 1 - (1/2) log n` for `n ≥ 1` (from Mathlib's Stirling sequence: `stirlingSeq n ≤ e/√2`). -/
theorem deficit_ge (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) - 1 - 1 / 2 * Real.log n ≤ deficit n := by
  rw [deficit_eq]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hs : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  have hpos : 0 < Stirling.stirlingSeq (k + 1) := Stirling.stirlingSeq'_pos k
  have hlog := Real.log_le_log hpos hs
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  have h1 : Real.log (Real.exp 1 / √2) = 1 - Real.log 2 / 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_sqrt (by norm_num)]
  have h2 : Real.log (2 * ((k + 1 : ℕ) : ℝ)) = Real.log 2 + Real.log (k + 1 : ℕ) :=
    Real.log_mul (by norm_num) hk.ne'
  have h3 : Real.log (((k + 1 : ℕ) : ℝ) / Real.exp 1) = Real.log (k + 1 : ℕ) - 1 := by
    rw [Real.log_div hk.ne' (Real.exp_pos 1).ne', Real.log_exp]
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one, h1, h2, h3] at hlog
  linarith

theorem one_lt_pi_sq_div_six : (1 : ℝ) < Real.pi ^ 2 / 6 := by
  nlinarith [Real.pi_gt_three]

/-- `D_n / n → 1`. -/
theorem deficit_div_tendsto : Tendsto (fun n : ℕ => deficit n / n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hlow : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ) - 1 / 2 * (Real.log n / n)) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hinv).sub
      (hlog.const_mul (1 / 2))
    rwa [show (1 : ℝ) - 0 - 1 / 2 * 0 = 1 by ring] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn']
    have e : (1 - 1 / (n : ℝ) - 1 / 2 * (Real.log n / n)) * n = n - 1 - 1 / 2 * Real.log n := by
      field_simp
    linarith [deficit_ge n hn]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [div_le_one (by exact_mod_cast hn)]
    exact deficit_le n

/-- **Conjecture 00000007864 is false.** Under uniform independent preferences, the entropy deficit
`D_n = n log n - H(σ_m)` of the men-optimal stable matching satisfies `D_n / n ≤ 1 < π^2/6` for every
`n ≥ 1`, and `D_n / n → 1`; in particular `D_n / n` does not tend to `π^2/6`. -/
theorem conjecture_7864_false :
    (∀ n : ℕ, 1 ≤ n → deficit n / n ≤ 1 ∧ deficit n / n < Real.pi ^ 2 / 6) ∧
    Tendsto (fun n : ℕ => deficit n / n) atTop (𝓝 1) ∧
    ¬ Tendsto (fun n : ℕ => deficit n / n) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have hle : ∀ n : ℕ, 1 ≤ n → deficit n / n ≤ 1 := fun n hn => by
    rw [div_le_one (by exact_mod_cast hn)]; exact deficit_le n
  refine ⟨fun n hn => ⟨hle n hn, (hle n hn).trans_lt one_lt_pi_sq_div_six⟩, deficit_div_tendsto,
    fun h => ?_⟩
  have := tendsto_nhds_unique deficit_div_tendsto h
  linarith [one_lt_pi_sq_div_six]

/-- Shannon entropy in bits. -/
noncomputable def entropyBits {α : Type*} [Fintype α] (p : PMF α) : ℝ :=
  ∑ a, -(p a).toReal * Real.logb 2 (p a).toReal

/-- The deficit with base-2 logarithms throughout: `n log₂ n - H₂(σ_m)`. -/
noncomputable def deficitBits (n : ℕ) : ℝ := n * Real.logb 2 n - entropyBits (lawMenOpt n)

/-- With base-2 logarithms the normalised deficit tends to `1 / log 2 = log₂ e ≈ 1.4427`, again not
`π^2/6`. -/
theorem bits_version :
    Tendsto (fun n : ℕ => deficitBits n / n) atTop (𝓝 (1 / Real.log 2)) ∧
    ¬ Tendsto (fun n : ℕ => deficitBits n / n) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have heq : ∀ n : ℕ, deficitBits n / n = (deficit n / n) * (1 / Real.log 2) := fun n => by
    simp only [deficitBits, entropyBits, deficit, entropy, Real.logb, Real.negMulLog]
    rw [Finset.sum_congr rfl (fun a _ => (mul_div_assoc _ _ _).symm), ← Finset.sum_div]
    ring
  have ht : Tendsto (fun n : ℕ => deficitBits n / n) atTop (𝓝 (1 / Real.log 2)) := by
    simp only [heq]; simpa using deficit_div_tendsto.mul_const (1 / Real.log 2)
  refine ⟨ht, fun h => ?_⟩
  have h1 := tendsto_nhds_unique ht h
  have hl := Real.log_two_gt_d9
  have hp := Real.pi_gt_d2
  rw [div_eq_iff (by positivity)] at h1
  nlinarith
