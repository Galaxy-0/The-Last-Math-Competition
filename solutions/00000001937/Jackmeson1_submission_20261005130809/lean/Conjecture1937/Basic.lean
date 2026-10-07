import Mathlib

/-!
# Conjecture 00000001937 (disproof)

*Statement.* The subgroup growth zeta function of a group `G` is the Dirichlet series
`ζ_G(s) = ∑_{n ≥ 1} a_n(G) n^{-s}`, where `a_n(G)` is the number of subgroups of index `n`.
Conjecture: the abscissa of convergence of `ζ_G` for an arithmetic linear group `G` equals
`dim G / (dim G + 1)`.

*Counterexample.* `G = U(ℤ) = { [[1, n], [0, 1]] : n ∈ ℤ } ≤ SL₂(ℤ)`, the group of integer
points of the one-dimensional unipotent algebraic group `U₂ ≅ 𝔾_a` of upper unitriangular
`2 × 2` matrices.  `U(ℤ) ≅ ℤ`, every subgroup of `ℤ` is `nℤ`, of index `n`, so `a_n(G) = 1`
for every `n` and `ζ_G` is the Riemann zeta function.  Its abscissa of convergence is `1`,
while `d / (d + 1) < 1` for every natural number `d`; in particular
`1 ≠ 1/2 = dim U₂ / (dim U₂ + 1)`.

We formalize two abscissae:
* `subgroupZetaAbscissaAbs`: Mathlib's abscissa of absolute convergence `LSeries.abscissaOfAbsConv`;
* `subgroupZetaAbscissa`: the infimum of the real `σ` at which the ordered partial sums
  `∑_{k=1}^N a_k k^{-σ}` converge (to a finite limit).
Both equal `1` for `G = U(ℤ)`.

Conventions: Mathlib's `AddSubgroup.index` is `0` for subgroups of infinite index, so
`subgroupCount G 0` counts infinite-index subgroups; the Dirichlet series ignores `n = 0`
(`LSeries.term f s 0 = 0`).  `subgroupCount` uses `Nat.card`, which is the honest count whenever
there are finitely many subgroups of index `n` (true for finitely generated groups, and checked
directly for `U(ℤ)` below, where the count is exactly `1`).
-/

open LSeries Filter Topology

namespace C1937

/-- `a_n(G)`: the number of subgroups of the group `G` of index `n`. -/
noncomputable def subgroupCount (G : Type*) [Group G] (n : ℕ) : ℕ :=
  Nat.card {H : Subgroup G // H.index = n}

/-- The subgroup growth zeta function `ζ_G(s) = ∑_{n ≥ 1} a_n(G) n^{-s}` (Mathlib `LSeries`). -/
noncomputable def subgroupZeta (G : Type*) [Group G] (s : ℂ) : ℂ :=
  LSeries (fun n => (subgroupCount G n : ℂ)) s

/-- Abscissa of absolute convergence of `ζ_G` (Mathlib's `LSeries.abscissaOfAbsConv`). -/
noncomputable def subgroupZetaAbscissaAbs (G : Type*) [Group G] : EReal :=
  abscissaOfAbsConv (fun n => (subgroupCount G n : ℂ))

/-- The `N`-th partial sum `∑_{k=1}^{N} a_k(G) k^{-σ}` of `ζ_G` at a real point `σ`. -/
noncomputable def partialSum (G : Type*) [Group G] (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (subgroupCount G (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ σ

/-- Abscissa of convergence of `ζ_G`: the infimum (in `EReal`) of the real points `σ`
at which the ordered partial sums converge to a finite limit. -/
noncomputable def subgroupZetaAbscissa (G : Type*) [Group G] : EReal :=
  sInf (Real.toEReal '' {σ : ℝ | ∃ L : ℝ, Tendsto (partialSum G σ) atTop (𝓝 L)})

/-! ### The arithmetic group `U(ℤ)` of unipotent upper triangular integer matrices -/

/-- The unipotent matrix `[[1, n], [0, 1]] ∈ SL₂(ℤ)`. -/
def unipMat (n : ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, n; 0, 1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem coe_unipMat (n : ℤ) :
    (unipMat n : Matrix (Fin 2) (Fin 2) ℤ) = !![1, n; 0, 1] := rfl

/-- `n ↦ [[1, n], [0, 1]]`, a homomorphism `ℤ → SL₂(ℤ)`. -/
def unipHom : Multiplicative ℤ →* Matrix.SpecialLinearGroup (Fin 2) ℤ where
  toFun n := unipMat n.toAdd
  map_one' := by
    apply Subtype.ext
    rw [coe_unipMat, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]; rfl
  map_mul' a b := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_unipMat, coe_unipMat, coe_unipMat,
      Matrix.mul_fin_two, toAdd_mul]
    simp [add_comm]

@[simp] theorem unipHom_apply (n : Multiplicative ℤ) : unipHom n = unipMat n.toAdd := rfl

/-- `U(ℤ) = { [[1, n], [0, 1]] : n ∈ ℤ }`: the integer points of the algebraic group `U₂` of
unipotent upper triangular `2 × 2` matrices (a copy of `𝔾_a`, of dimension `1`). -/
def U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ) := unipHom.range

/-- `U(ℤ)` is exactly the set of integer matrices of determinant one of the form `[[1, *], [0, 1]]`
(`= GL₂(ℤ) ∩ U₂(ℚ)`). -/
theorem mem_U_iff (M : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    M ∈ U ↔ M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 1 0 = 0 := by
  constructor
  · rintro ⟨n, rfl⟩
    simp
  · rintro ⟨h00, h11, h10⟩
    refine ⟨Multiplicative.ofAdd (M 0 1), ?_⟩
    apply Subtype.ext
    change (unipMat (M 0 1) : Matrix (Fin 2) (Fin 2) ℤ) = M
    rw [coe_unipMat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h10]

theorem unipHom_injective : Function.Injective unipHom := by
  intro a b h
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) ℤ => M 0 1) h
  simpa using this

/-- `U(ℤ) ≅ ℤ`. -/
noncomputable def uEquiv : Multiplicative ℤ ≃* U := MonoidHom.ofInjective unipHom_injective

/-- Subgroup counts are invariant under isomorphism, and for `G ≅ Multiplicative A` they are
the additive subgroup counts of `A`. -/
theorem subgroupCount_eq_add {G A : Type*} [Group G] [AddGroup A] (e : G ≃* Multiplicative A)
    (n : ℕ) : subgroupCount G n = Nat.card {K : AddSubgroup A // K.index = n} := by
  refine Nat.card_congr (Equiv.subtypeEquiv
    ((MulEquiv.mapSubgroup e).toEquiv.trans AddSubgroup.toSubgroup.symm.toEquiv) ?_)
  intro H
  change H.index = n ↔ (AddSubgroup.toSubgroup.symm (H.map (e : G →* Multiplicative A))).index = n
  rw [← AddSubgroup.index_toSubgroup, OrderIso.apply_symm_apply, Subgroup.index_map_equiv]

/-! ### Subgroups of `ℤ` -/

/-- Every subgroup of `ℤ` is `nℤ` with `n` its index (`n = 0` for the trivial subgroup). -/
theorem eq_zmultiples_index (H : AddSubgroup ℤ) :
    H = AddSubgroup.zmultiples (H.index : ℤ) := by
  obtain ⟨a, rfl⟩ := Int.subgroup_cyclic H
  rw [← AddSubgroup.zmultiples_eq_closure, Int.index_zmultiples, Int.zmultiples_natAbs]

/-- `U(ℤ) ≅ ℤ` has exactly one subgroup of each index `n` (the image of `nℤ`). -/
theorem subgroupCount_U (n : ℕ) : subgroupCount U n = 1 := by
  rw [subgroupCount_eq_add uEquiv.symm n]
  have hn : (AddSubgroup.zmultiples (n : ℤ)).index = n := by
    rw [Int.index_zmultiples, Int.natAbs_natCast]
  let u : Unique {H : AddSubgroup ℤ // H.index = n} :=
    { default := ⟨_, hn⟩
      uniq := fun H => by
        apply Subtype.ext
        change H.1 = AddSubgroup.zmultiples (n : ℤ)
        rw [eq_zmultiples_index H.1, H.2] }
  exact Nat.card_unique

theorem coeff_U : (fun n => (subgroupCount U n : ℂ)) = 1 := by
  funext n; simp [subgroupCount_U]

/-- `ζ_{U(ℤ)}` is the Riemann zeta function on `re s > 1`. -/
theorem subgroupZeta_U_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    subgroupZeta U s = riemannZeta s := by
  rw [subgroupZeta, coeff_U, LSeries_one_eq_riemannZeta hs]

theorem subgroupZetaAbscissaAbs_U : subgroupZetaAbscissaAbs U = 1 := by
  rw [subgroupZetaAbscissaAbs, coeff_U, LSeries.abscissaOfAbsConv_one]

/-- At a real point `σ`, the partial sums of `ζ_{U(ℤ)}` converge iff `σ > 1`. -/
theorem partialSum_U_converges_iff (σ : ℝ) :
    (∃ L : ℝ, Tendsto (partialSum U σ) atTop (𝓝 L)) ↔ 1 < σ := by
  have hps : partialSum U σ =
      fun N => ∑ n ∈ Finset.range N, (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ σ) n := by
    funext N; simp [partialSum, subgroupCount_U]
  have hnn : ∀ k : ℕ, 0 ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ σ := fun k => by positivity
  have hsum : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ σ) ↔ 1 < σ := by
    rw [← Real.summable_one_div_nat_rpow (p := σ)]
    exact summable_nat_add_iff 1 (f := fun n : ℕ => 1 / (n : ℝ) ^ σ)
  rw [hps, ← hsum]
  constructor
  · rintro ⟨L, hL⟩
    exact (summable_iff_not_tendsto_nat_atTop_of_nonneg hnn).2
      (fun h => not_tendsto_atTop_of_tendsto_nhds hL h)
  · intro h
    exact ⟨_, h.hasSum.tendsto_sum_nat⟩

theorem subgroupZetaAbscissa_U : subgroupZetaAbscissa U = 1 := by
  have hset : {σ : ℝ | ∃ L : ℝ, Tendsto (partialSum U σ) atTop (𝓝 L)} =
      {x : ℝ | LSeriesSummable 1 x} := by
    ext σ
    simp only [Set.mem_ofPred_eq, partialSum_U_converges_iff, LSeriesSummable_one_iff,
      Complex.ofReal_re]
  rw [subgroupZetaAbscissa, hset, ← LSeries.abscissaOfAbsConv_one]
  rfl

/-- The conjectured value `d / (d + 1)` is never `1`, whatever natural number `d` is. -/
theorem formula_ne_one (d : ℕ) : (((d : ℝ) / (d + 1) : ℝ) : EReal) ≠ 1 := by
  intro h
  have h' : (d : ℝ) / (d + 1) = 1 := by exact_mod_cast h
  have hlt : (d : ℝ) / (d + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  linarith

/-- **Conjecture 00000001937 is false.** For the arithmetic group
`U(ℤ) = {[[1, n], [0, 1]]} = SL₂(ℤ) ∩ U₂ ≅ ℤ` (integer points of the 1-dimensional unipotent
group `U₂ ≅ 𝔾_a`): there is exactly one subgroup of each index, the subgroup zeta function is
the Riemann zeta function, its abscissa of convergence (and of absolute convergence) is `1`,
and `1` differs from `d / (d + 1)` for every natural number `d` — in particular from `1/2`,
the value the conjecture predicts for `dim U₂ = 1`. -/
theorem conjecture_1937_false :
    (∀ M : Matrix.SpecialLinearGroup (Fin 2) ℤ, M ∈ U ↔ M 0 0 = 1 ∧ M 1 1 = 1 ∧ M 1 0 = 0) ∧
    (∀ n : ℕ, subgroupCount U n = 1) ∧
    (∀ s : ℂ, 1 < s.re → subgroupZeta U s = riemannZeta s) ∧
    subgroupZetaAbscissa U = 1 ∧ subgroupZetaAbscissaAbs U = 1 ∧
    (∀ d : ℕ, subgroupZetaAbscissa U ≠ (((d : ℝ) / (d + 1) : ℝ) : EReal) ∧
      subgroupZetaAbscissaAbs U ≠ (((d : ℝ) / (d + 1) : ℝ) : EReal)) ∧
    subgroupZetaAbscissa U ≠ (((1 : ℝ) / 2 : ℝ) : EReal) := by
  refine ⟨mem_U_iff, subgroupCount_U, fun s hs => subgroupZeta_U_eq_riemannZeta hs,
    subgroupZetaAbscissa_U, subgroupZetaAbscissaAbs_U, fun d => ?_, ?_⟩
  · rw [subgroupZetaAbscissa_U, subgroupZetaAbscissaAbs_U]
    exact ⟨(formula_ne_one d).symm, (formula_ne_one d).symm⟩
  · rw [subgroupZetaAbscissa_U]
    have := (formula_ne_one 1).symm
    norm_num at this ⊢
    exact this

end C1937
