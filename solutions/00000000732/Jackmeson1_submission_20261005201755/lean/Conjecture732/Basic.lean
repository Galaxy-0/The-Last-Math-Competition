import Mathlib

open NumberField InfinitePlace

namespace C732

section general

variable (K : Type*) [Field K] [NumberField K]

/-- The absolute norm `N_{K/ℚ}` restricted to the unit group `(𝓞 K)ˣ`, as a homomorphism to `ℚˣ`. -/
noncomputable def unitNorm : (𝓞 K)ˣ →* ℚˣ :=
  (Units.map (Algebra.norm ℚ : K →* ℚ)).comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

/-- The norm-one units `E₁ = {u ∈ (𝓞 K)ˣ : N_{K/ℚ}(u) = 1}`. -/
noncomputable def normOneUnits : Subgroup (𝓞 K)ˣ := (unitNorm K).ker

theorem mem_normOneUnits (u : (𝓞 K)ˣ) :
    u ∈ normOneUnits K ↔ Algebra.norm ℚ ((u : 𝓞 K) : K) = 1 := by
  simp [normOneUnits, unitNorm, MonoidHom.mem_ker, Units.ext_iff]

/-- Key lemma: in a totally complex number field the absolute norm is nonnegative.
Proof: `N(x) = ∏_σ σ(x)` over the embeddings `σ : K → ℂ`; the embeddings above a complex place
`w` are exactly `{φ_w, conj ∘ φ_w}` with `φ_w ≠ conj ∘ φ_w`, so `N(x) = ∏_w |φ_w(x)|²`. -/
theorem norm_nonneg_of_isTotallyComplex [IsTotallyComplex K] (x : K) :
    0 ≤ Algebra.norm ℚ x := by
  classical
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)) (fun φ => φ x)
    (fun σ => σ x) (fun _ => by simp [RingHom.equivRatAlgHom_apply]),
    ← Finset.prod_fiberwise Finset.univ (fun φ : K →+* ℂ => mk φ) (fun φ => φ x)] at h
  have hfib : ∀ w : InfinitePlace K, ∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => mk φ = w), φ x
      = ((Complex.normSq (w.embedding x) : ℝ) : ℂ) := by
    intro w
    have hset : Finset.univ.filter (fun φ : K →+* ℂ => mk φ = w)
        = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      conv_lhs => rw [← mk_embedding w, mk_eq_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [← h]; exact (star_star φ).symm
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [h]; exact star_star _
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
      intro h
      exact IsTotallyComplex.complexEmbedding_not_isReal w.embedding
        (ComplexEmbedding.isReal_iff.mpr h.symm)
    rw [hset, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  simp_rw [hfib] at h
  rw [← Complex.ofReal_prod, eq_ratCast, ← Complex.ofReal_ratCast, Complex.ofReal_inj] at h
  have : (0 : ℝ) ≤ (Algebra.norm ℚ x : ℝ) := by
    rw [h]; exact Finset.prod_nonneg fun w _ => Complex.normSq_nonneg _
  exact_mod_cast this

/-- In a totally complex number field every unit has absolute norm `+1`. -/
theorem norm_unit_eq_one [IsTotallyComplex K] (u : (𝓞 K)ˣ) :
    Algebra.norm ℚ ((u : 𝓞 K) : K) = 1 := by
  have h := (NumberField.isUnit_iff_norm (K := K)).mp u.isUnit
  rw [RingOfIntegers.coe_norm] at h
  have h0 := norm_nonneg_of_isTotallyComplex K ((u : 𝓞 K) : K)
  rwa [abs_of_nonneg h0] at h

theorem normOneUnits_eq_top [IsTotallyComplex K] : normOneUnits K = ⊤ := by
  ext u
  simp [mem_normOneUnits, norm_unit_eq_one K u]

/-- For every number field, `[E : E₁] ≤ 2`, since the norm of a unit is `±1`. -/
theorem index_normOneUnits_le_two : (normOneUnits K).index ≤ 2 := by
  rw [normOneUnits, Subgroup.index_ker]
  change Nat.card (((unitNorm K).range : Set ℚˣ)) ≤ 2
  rw [Nat.card_coe_set_eq]
  have hsub : ((unitNorm K).range : Set ℚˣ) ⊆ {1, -1} := by
    rintro _ ⟨u, rfl⟩
    have h := (NumberField.isUnit_iff_norm (K := K)).mp u.isUnit
    rw [RingOfIntegers.coe_norm] at h
    rcases abs_eq (zero_le_one' ℚ) |>.mp h with h1 | h1
    · left; ext; simpa [unitNorm] using h1
    · right; ext; simpa [unitNorm] using h1
  calc ((unitNorm K).range : Set ℚˣ).ncard ≤ ({1, -1} : Set ℚˣ).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le 1 {-1}).trans (by rw [Set.ncard_singleton])

end general

/-- **The statement's object.** `ε(m) = [E : E₁]`, the index in the unit group `E = (𝓞 K)ˣ` of
`K = ℚ(ζ_m)` (Mathlib's `CyclotomicField m ℚ`) of the norm-one units `E₁`. -/
noncomputable def unitIndex (m : ℕ) : ℕ := (normOneUnits (CyclotomicField m ℚ)).index

/-- `ω(m)`, the number of distinct prime divisors of `m`. -/
def omega (m : ℕ) : ℕ := m.primeFactors.card

/-- The conjectured value `φ(m) / 2^{ω(m)}` (computed in `ℚ`, so no rounding is involved). -/
noncomputable def claimed (m : ℕ) : ℚ := (Nat.totient m : ℚ) / 2 ^ omega m

theorem unitIndex_eq_one {m : ℕ} (hm : 2 < m) : unitIndex m = 1 := by
  have : NeZero m := ⟨by omega⟩
  have : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  have : IsTotallyComplex (CyclotomicField m ℚ) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (CyclotomicField m ℚ) hm
  rw [unitIndex, normOneUnits_eq_top, Subgroup.index_top]

theorem unitIndex_le_two (m : ℕ) : unitIndex m ≤ 2 :=
  index_normOneUnits_le_two _

theorem claimed_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    claimed (p ^ a) = ((p ^ (a - 1) * (p - 1) : ℕ) : ℚ) / 2 := by
  rw [claimed, omega, Nat.primeFactors_prime_pow (by omega) hp, Finset.card_singleton,
    Nat.totient_prime_pow hp (by omega), pow_one]

/-- For an odd prime power `q = p^a ≥ 7`, the claimed value is at least `3`. -/
theorem three_le_claimed {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a) (hq : 7 ≤ p ^ a) :
    (3 : ℚ) ≤ claimed (p ^ a) := by
  rw [claimed_prime_pow hp ha, le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have key : 6 ≤ p ^ (a - 1) * (p - 1) := by
    rcases Nat.eq_or_lt_of_le ha with rfl | ha2
    · simp only [pow_one] at hq; simp; omega
    · have h1 : 3 ≤ p ^ (a - 1) := h3.trans (Nat.le_self_pow (by omega) p)
      have h2 : 2 ≤ p - 1 := by omega
      nlinarith
  exact_mod_cast (by omega : 3 * 2 ≤ p ^ (a - 1) * (p - 1))

/-- The specific witness `m = 7`: `ε(7) = 1` while `φ(7)/2^{ω(7)} = 3`. -/
theorem witness_seven : unitIndex 7 = 1 ∧ claimed 7 = 3 := by
  refine ⟨unitIndex_eq_one (by norm_num), ?_⟩
  have := claimed_prime_pow (p := 7) (a := 1) (by norm_num) le_rfl
  rw [pow_one] at this
  rw [this]; norm_num

/-! ### Readings of "the supremum of ε(m)" -/

/-- Any supremum of values of `ε` (over any index set `T`, e.g. `m' ≤ m` or `m' ≥ m`) is `≤ 2`. -/
theorem sSup_unitIndex_le_two (T : Set ℕ) : sSup (unitIndex '' T) ≤ 2 :=
  csSup_le' (by rintro _ ⟨m, -, rfl⟩; exact unitIndex_le_two m)

/-- Exact-equality clause for any function `S ≤ 2` (in particular any supremum of `ε`):
it fails at every odd prime power `q = p^a ≥ 7`. -/
theorem exact_equality_fails_of_le_two (S : ℕ → ℚ) (hS : ∀ m, S m ≤ 2) {p a : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 1 ≤ a) (hq : 7 ≤ p ^ a) : S (p ^ a) ≠ claimed (p ^ a) := by
  have := three_le_claimed hp hp2 ha hq
  have := hS (p ^ a)
  intro h; linarith

/-- **Exact-equality clause, literal reading.** `ε(q) ≠ φ(q)/2^{ω(q)}` at every odd prime power
`q = p^a ≥ 7` (an infinite family). -/
theorem exact_equality_fails {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (hq : 7 ≤ p ^ a) : (unitIndex (p ^ a) : ℚ) ≠ claimed (p ^ a) :=
  exact_equality_fails_of_le_two (fun m => (unitIndex m : ℚ))
    (fun m => by exact_mod_cast unitIndex_le_two m) hp hp2 ha hq

/-! ### The Hasse unit index reading `Q = [E : W E⁺]` (Mathlib's `indexRealUnits`) -/

/-- `ℚ(ζ_m)` is a CM field for `m > 2` (Mathlib: `IsCyclotomicExtension.Rat.isCMField`). -/
theorem cmField {m : ℕ} (hm : 2 < m) : IsCMField (CyclotomicField m ℚ) := by
  have : NeZero m := ⟨by omega⟩
  have : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  exact IsCyclotomicExtension.Rat.isCMField (S := {m}) _ ⟨m, Set.mem_singleton m, hm⟩

/-- Hasse's unit index `Q(m) = [E : W E⁺]` of `ℚ(ζ_m)`, `m > 2`, as Mathlib's `indexRealUnits`. -/
noncomputable def hasseIndex (m : ℕ) (hm : 2 < m) : ℕ :=
  haveI := cmField hm
  IsCMField.indexRealUnits (CyclotomicField m ℚ)

theorem hasse_index_ne_claimed {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (hq : 7 ≤ p ^ a) : (hasseIndex (p ^ a) (by omega) : ℚ) ≠ claimed (p ^ a) := by
  have h3 := three_le_claimed hp hp2 ha hq
  have : IsCMField (CyclotomicField (p ^ a) ℚ) := cmField (by omega)
  rcases IsCMField.indexRealUnits_eq_one_or_two (CyclotomicField (p ^ a) ℚ) with h | h <;>
  · rw [hasseIndex, h]; intro h'; push_cast at h'; linarith


/-! ### The relative-norm reading `[E : ker N_{K/K⁺}]` -/

/-- Relative-norm reading: units with `N_{K/K⁺}(u) = 1`, `K⁺` the maximal real subfield. -/
noncomputable def relNormOneUnits (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    Subgroup (𝓞 K)ˣ :=
  ((Units.map (Algebra.norm (maximalRealSubfield K) : K →* maximalRealSubfield K)).comp
    (Units.map (algebraMap (𝓞 K) K).toMonoidHom)).ker

/-- In a CM field with positive unit rank, `[E : ker N_{K/K⁺}]` is infinite (`index = 0`):
a fundamental unit `η` of `K⁺` has `N_{K/K⁺}(η^n) = η^{2n} ≠ 1`. -/
theorem relNormOneUnits_index_eq_zero (K : Type*) [Field K] [NumberField K] [IsCMField K]
    (hr : 0 < Units.rank K) : (relNormOneUnits K).index = 0 := by
  rw [← IsCMField.units_rank_eq_units_rank] at hr
  set η : (𝓞 (maximalRealSubfield K))ˣ := Units.fundSystem (maximalRealSubfield K) ⟨0, hr⟩
  have hη : η ∉ Units.torsion (maximalRealSubfield K) := by
    intro h
    have h1 := Units.logEmbedding_fundSystem (maximalRealSubfield K) ⟨0, hr⟩
    rw [Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr h] at h1
    exact (Units.basisUnitLattice (maximalRealSubfield K)).ne_zero _
      ((Submodule.coe_eq_zero).mp h1.symm)
  by_contra h0
  set u : (𝓞 K)ˣ := Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)).toMonoidHom η
  have hmem := Subgroup.pow_index_mem (relNormOneUnits K) u
  set n := (relNormOneUnits K).index
  have hcoe : (((u ^ n : (𝓞 K)ˣ) : 𝓞 K) : K) =
      algebraMap (maximalRealSubfield K) K (((η ^ n : (𝓞 (maximalRealSubfield K))ˣ) :
        𝓞 (maximalRealSubfield K)) : maximalRealSubfield K) := by
    simp [u]
    rfl
  have hnorm : Algebra.norm (maximalRealSubfield K) (((u ^ n : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by
    simpa [relNormOneUnits, MonoidHom.mem_ker, Units.ext_iff] using hmem
  rw [hcoe, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K] at hnorm
  apply hη
  change η ∈ CommGroup.torsion _
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨n * 2, by positivity, ?_⟩
  rw [pow_mul]
  refine Units.ext (RingOfIntegers.ext ?_)
  simpa using hnorm

theorem rank_pos {m : ℕ} (h2 : 2 < m) (h6 : 6 ≤ Nat.totient m) :
    0 < Units.rank (CyclotomicField m ℚ) := by
  have : NeZero m := ⟨by omega⟩
  have : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  have : IsTotallyComplex (CyclotomicField m ℚ) :=
    IsCyclotomicExtension.Rat.isTotallyComplex _ h2
  have h := IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two m (CyclotomicField m ℚ)
  rw [Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, h]
  omega

/-- The relative-norm index of `ℚ(ζ_m)`, `m > 2`. -/
noncomputable def relIndex (m : ℕ) (hm : 2 < m) : ℕ :=
  haveI := cmField hm
  (relNormOneUnits (CyclotomicField m ℚ)).index

theorem rel_index_ne_claimed {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (hq : 7 ≤ p ^ a) : relIndex (p ^ a) (by omega) = 0 ∧
      (relIndex (p ^ a) (by omega) : ℚ) ≠ claimed (p ^ a) := by
  have h3 := three_le_claimed hp hp2 ha hq
  have : IsCMField (CyclotomicField (p ^ a) ℚ) := cmField (by omega)
  have h6 : 6 ≤ Nat.totient (p ^ a) := by
    have h := h3
    rw [claimed, omega, Nat.primeFactors_prime_pow (by omega) hp, Finset.card_singleton,
      pow_one, le_div_iff₀ (by norm_num : (0 : ℚ) < 2)] at h
    exact_mod_cast (by linarith : (6 : ℚ) ≤ Nat.totient (p ^ a))
  have h0 : relIndex (p ^ a) (by omega) = 0 :=
    relNormOneUnits_index_eq_zero _ (rank_pos (by omega) h6)
  refine ⟨h0, ?_⟩
  rw [h0, Nat.cast_zero]; intro h; linarith

/-! ### The asymptotic clause -/

/-- Real-valued claimed main term `f(m) = φ(m)/2^{ω(m)}`. -/
noncomputable def f (m : ℕ) : ℝ := (Nat.totient m : ℝ) / 2 ^ omega m

/-- Big-O reading: `S(m) = f(m)(1 + O(2^{-ω(m)}))` as `m → ∞`. -/
def BigOClaim (S : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ m ≥ N, |S m - f m| ≤ C * f m * (2 ^ omega m)⁻¹

/-- Asymptotic-equivalence reading: `S(m) / f(m) → 1` as `m → ∞`. -/
def EquivClaim (S : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun m => S m / f m) Filter.atTop (nhds 1)

theorem exists_primes (B k : ℕ) : ∃ t : Finset ℕ, t.card = k ∧ ∀ p ∈ t, p.Prime ∧ B ≤ p := by
  have hinf : {p | p.Prime ∧ B ≤ p}.Infinite := by
    refine (Nat.infinite_setOfPred_prime.sdiff (Set.finite_lt_nat B)).mono ?_
    rintro p ⟨hp, hpB⟩
    exact ⟨hp, not_lt.mp hpB⟩
  obtain ⟨t, ht, hcard⟩ := hinf.exists_subset_card_eq k
  exact ⟨t, hcard, fun p hp => ht hp⟩

/-- The family `m = p₁ ⋯ p_k` of `k` distinct primes `≥ max B 11`: `ω(m) = k`, `f(m) ≥ 5^k`. -/
theorem family (B k : ℕ) (hk : 1 ≤ k) : ∃ m, B ≤ m ∧ omega m = k ∧ (5 : ℝ) ^ k ≤ f m := by
  obtain ⟨t, hcard, ht⟩ := exists_primes (max B 11) k
  have hpr : ∀ p ∈ t, p.Prime := fun p hp => (ht p hp).1
  have hpf : (∏ p ∈ t, p).primeFactors = t := Nat.primeFactors_prod hpr
  refine ⟨∏ p ∈ t, p, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ : t.Nonempty := Finset.card_pos.mp (by omega)
    calc B ≤ p := (le_max_left _ _).trans (ht p hp).2
      _ ≤ ∏ p ∈ t, p := Finset.single_le_prod' (fun i hi => (hpr i hi).one_lt.le) hp
  · rw [omega, hpf, hcard]
  · have htot : Nat.totient (∏ p ∈ t, p) = ∏ p ∈ t, (p - 1) := by
      have h := Nat.totient_mul_prod_primeFactors (∏ p ∈ t, p)
      rw [hpf] at h
      have hpos : 0 < ∏ p ∈ t, p := Finset.prod_pos fun i hi => (hpr i hi).pos
      exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
    rw [f, omega, hpf, hcard, htot, le_div_iff₀ (by positivity), ← mul_pow, ← hcard,
      ← Finset.prod_const, Nat.cast_prod]
    refine Finset.prod_le_prod (fun _ _ => by norm_num) fun i hi => ?_
    have h11 : 11 ≤ i := (le_max_right _ _).trans (ht i hi).2
    have : (10 : ℝ) ≤ ((i - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 10 ≤ i - 1)
    norm_num; omega

/-- **Asymptotic clause.** No function `S` with `S ≤ 2` (in particular `ε` itself or any
supremum of its values) satisfies either reading of the asymptotic. -/
theorem asymptotic_fails (S : ℕ → ℝ) (hS : ∀ m, S m ≤ 2) :
    ¬ BigOClaim S ∧ ¬ EquivClaim S := by
  -- along `family`, `S/f ≤ 2/5^k` while `C·2^{-k}` is small
  have key : ∀ (c : ℝ) (N : ℕ), ∃ m ≥ N, 5 ≤ f m ∧ c * (2 ^ omega m)⁻¹ < 1 / 2 ∧
      S m / f m ≤ 2 / 5 := by
    intro c N
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * |c| + 1) (by norm_num : (1 : ℝ) < 2)
    obtain ⟨m, hmN, hω, hf⟩ := family N (k + 1) (by omega)
    have h5 : (5 : ℝ) ≤ f m := le_trans (le_self_pow₀ (by norm_num) (by omega)) hf
    refine ⟨m, hmN, h5, ?_, ?_⟩
    · rw [hω]
      have h2k : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hpos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
      rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
      nlinarith [le_abs_self c, abs_nonneg c]
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [hS m]
  refine ⟨?_, ?_⟩
  · rintro ⟨C, N, hC⟩
    obtain ⟨m, hm, h5, hc, hr⟩ := key C N
    have h := hC m hm
    have hfpos : 0 < f m := by linarith
    have hSm : S m ≤ 2 / 5 * f m := by
      rw [div_le_iff₀ hfpos] at hr; linarith
    have : |S m - f m| = f m - S m := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [this] at h
    have : C * f m * (2 ^ omega m)⁻¹ < f m / 2 := by
      have := mul_lt_mul_of_pos_right hc hfpos
      linarith [show C * f m * (2 ^ omega m)⁻¹ = C * (2 ^ omega m)⁻¹ * f m by ring]
    linarith
  · intro hT
    have hev := (hT.eventually (Ioi_mem_nhds (by norm_num : (2 : ℝ) / 5 < 1)))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    obtain ⟨m, hm, -, -, hr⟩ := key 0 N
    have := hN m hm
    linarith

/-! ### Main theorem -/

/-- The conjecture with the statement's own `ε`: the asymptotic (Big-O reading) together with
the exact equality `ε(m) = φ(m)/2^{ω(m)}` at every odd prime power `m`. -/
def Conjecture732 : Prop :=
  BigOClaim (fun m => (unitIndex m : ℝ)) ∧
    ∀ p a : ℕ, p.Prime → p ≠ 2 → 1 ≤ a → (unitIndex (p ^ a) : ℚ) = claimed (p ^ a)

/-- **Main theorem.** The conjecture is false (literal reading, witness `m = 7`). At `m = 7`
the other readings fail as well: any supremum of `ε`-values, Hasse's index `Q`, and the
relative-norm index (which is infinite). The asymptotic fails for `ε` and for every family
of suprema `m ↦ sup ε(T m)` (e.g. `T m = {m}`, `{m' ≤ m}`, `{m' ≥ m}`). -/
theorem conjecture732_false :
    ¬ Conjecture732 ∧
    (unitIndex 7 = 1 ∧ claimed 7 = 3) ∧
    (∀ T : Set ℕ, ((sSup (unitIndex '' T) : ℕ) : ℚ) ≠ claimed 7) ∧
    (hasseIndex 7 (by norm_num) : ℚ) ≠ claimed 7 ∧
    relIndex 7 (by norm_num) = 0 ∧
    (∀ T : ℕ → Set ℕ, ¬ BigOClaim (fun m => ((sSup (unitIndex '' T m) : ℕ) : ℝ)) ∧
      ¬ EquivClaim (fun m => ((sSup (unitIndex '' T m) : ℕ) : ℝ))) := by
  refine ⟨?_, witness_seven, fun T => ?_, ?_, ?_, fun T => ?_⟩
  · rintro ⟨-, h⟩
    have := h 7 1 (by norm_num) (by norm_num) le_rfl
    rw [pow_one, witness_seven.1, witness_seven.2] at this
    norm_num at this
  · have := exact_equality_fails_of_le_two (fun _ => ((sSup (unitIndex '' T) : ℕ) : ℚ))
      (fun _ => by exact_mod_cast sSup_unitIndex_le_two T) (p := 7) (a := 1) (by norm_num)
      (by norm_num) le_rfl (by norm_num)
    simpa using this
  · exact hasse_index_ne_claimed (p := 7) (a := 1) (by norm_num) (by norm_num) le_rfl
      (by norm_num)
  · exact (rel_index_ne_claimed (p := 7) (a := 1) (by norm_num) (by norm_num) le_rfl
      (by norm_num)).1
  · exact asymptotic_fails _ fun m => by exact_mod_cast sSup_unitIndex_le_two (T m)

end C732
