import Mathlib

/-!
# Conjecture 00000003200: maximal regular sequences and Ext-depth (Rees)

For a Noetherian ring `R`, an ideal `J` and a finitely generated `R`-module `M` with `J M ≠ M`:

* every maximal `M`-regular sequence in `J` has the same length, namely the least `i` with
  `Ext^i_R(R/J, M) ≠ 0`;
* a maximal `M`-regular sequence in `J` exists, so this least `i` is finite;
* the supremum of the lengths of `M`-regular sequences in `J` equals that least `i`.

The key equivalence (vanishing of `Ext^i(R/J, M)` for `i < n` iff `J` contains an `M`-regular
sequence of length `n`) is Mathlib's Rees theorem (`Mathlib/RingTheory/Depth/Rees.lean`,
by Nailin Guan). We add the extension lemma for maximal sequences, existence of a maximal
sequence, the sup/min equality, and the specialization to a standard graded polynomial ring.
-/

open CategoryTheory Abelian RingTheory.Sequence Pointwise

namespace C3200

universe u

section General

variable {R : Type u} [CommRing R]

/-- `J` contains `rs` elementwise and `rs` is an `M`-regular sequence (Mathlib's
`RingTheory.Sequence.IsRegular`: weakly regular and `M ≠ (rs) M`). -/
def IsRegIn (J : Ideal R) (M : ModuleCat.{u} R) (rs : List R) : Prop :=
  (∀ r ∈ rs, r ∈ J) ∧ IsRegular M rs

/-- A maximal `M`-regular sequence in `J`: it cannot be extended by any element of `J`. -/
def IsMaximalRegIn (J : Ideal R) (M : ModuleCat.{u} R) (rs : List R) : Prop :=
  IsRegIn J M rs ∧ ∀ r ∈ J, ¬ IsRegular M (rs ++ [r])

/-- The set of lengths of `M`-regular sequences in `J`. -/
def regLengths (J : Ideal R) (M : ModuleCat.{u} R) : Set ℕ :=
  {n | ∃ rs : List R, rs.length = n ∧ IsRegIn J M rs}

/-- Supremum (in `ℕ∞`) of the lengths of `M`-regular sequences in `J`. -/
noncomputable def regDepth (J : Ideal R) (M : ModuleCat.{u} R) : ℕ∞ :=
  ⨆ (rs : List R) (_ : IsRegIn J M rs), (rs.length : ℕ∞)

/-- Ext-depth: the least `i` with `Ext^i_R(R/J, M) ≠ 0` (`⊤` if there is none). -/
noncomputable def extDepth (J : Ideal R) (M : ModuleCat.{u} R) : ℕ∞ :=
  ⨅ (i : ℕ) (_ : ¬ Subsingleton (Ext (ModuleCat.of R (R ⧸ J)) M i)), (i : ℕ∞)

lemma support_quot (J : Ideal R) :
    Module.support R (ModuleCat.of R (R ⧸ J)) = PrimeSpectrum.zeroLocus J := by
  show Module.support R (R ⧸ J) = _
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

/-- Copied from Mathlib's `Rees.lean` (a private lemma there). -/
lemma smul_top_quot_ne_top {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R} {r : R}
    (hr : r ∈ I) (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    I • (⊤ : Submodule R (QuotSMulTop r M)) ≠ ⊤ := by
  by_contra eq
  absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
  simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
    Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem I).mpr hr),
    ← Submodule.ideal_span_singleton_smul] using hI

variable [IsNoetherianRing R]

/-- Rees (Mathlib): `Ext^i(R/J, M) = 0` for all `i < n` iff `J` contains an `M`-regular sequence
of length `n`. -/
theorem rees_iff (J : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hJ : J • (⊤ : Submodule R M) < ⊤) (n : ℕ) :
    (∀ i < n, Subsingleton (Ext (ModuleCat.of R (R ⧸ J)) M i)) ↔ n ∈ regLengths J M := by
  constructor
  · intro h
    obtain ⟨rs, hl, hm, hr⟩ := ModuleCat.exists_isRegular_of_exists_subsingleton_ext J n M hJ
      (ModuleCat.of R (R ⧸ J)) (support_quot J) h
    exact ⟨rs, hl, hm, hr⟩
  · rintro ⟨rs, rfl, hm, hr⟩
    exact ModuleCat.subsingleton_ext_of_exists_isRegular J (ModuleCat.of R (R ⧸ J))
      (support_quot J).subset M hJ rs hm hr

/-- Extension lemma: if `Ext^i(R/J, M) = 0` for all `i ≤ length rs`, the regular sequence `rs`
extends inside `J`. -/
theorem exists_extend (J : Ideal R) (rs : List R) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M], J • (⊤ : Submodule R M) < ⊤ →
      IsRegIn J M rs →
      (∀ i ≤ rs.length, Subsingleton (Ext (ModuleCat.of R (R ⧸ J)) M i)) →
      ∃ r ∈ J, IsRegular M (rs ++ [r]) := by
  induction rs with
  | nil =>
    intro M _ hJ _ h
    obtain ⟨rs, hl, hm, hr⟩ := (rees_iff J M hJ 1).1 (fun i hi => h i (by simp at hi ⊢; omega))
    match rs, hl with
    | [r], _ => exact ⟨r, hm r (by simp), by simpa using hr⟩
  | cons a rs ih =>
    intro M _ hJ ⟨hm, hr⟩ h
    rw [isRegular_cons_iff] at hr
    have haJ : a ∈ J := hm a (by simp)
    let M' := ModuleCat.of R (QuotSMulTop a M)
    have hJ' : J • (⊤ : Submodule R M') < ⊤ := (smul_top_quot_ne_top haJ hJ.ne).lt_top
    have h' : ∀ i ≤ rs.length, Subsingleton (Ext (ModuleCat.of R (R ⧸ J)) M' i) := by
      intro i hi
      have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr
        (h i (by simp; omega))
      have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr
        (h (i + 1) (by simp; omega))
      exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' (ModuleCat.of R (R ⧸ J))
          hr.1.smulShortComplex_shortExact) i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
    obtain ⟨r, hrJ, hreg⟩ := ih M' hJ' ⟨fun x hx => hm x (by simp [hx]), hr.2⟩ h'
    exact ⟨r, hrJ, by rw [List.cons_append, isRegular_cons_iff]; exact ⟨hr.1, hreg⟩⟩

theorem length_le_extDepth (J : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hJ : J • (⊤ : Submodule R M) < ⊤) {rs : List R} (h : IsRegIn J M rs) :
    (rs.length : ℕ∞) ≤ extDepth J M := by
  refine le_iInf₂ fun i hi => ?_
  by_contra hlt
  exact hi ((rees_iff J M hJ rs.length).2 ⟨rs, rfl, h⟩ i (by exact_mod_cast not_le.mp hlt))

/-- Every maximal `M`-regular sequence in `J` has length equal to the Ext-depth. -/
theorem length_eq_extDepth_of_maximal (J : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hJ : J • (⊤ : Submodule R M) < ⊤) {rs : List R} (h : IsMaximalRegIn J M rs) :
    (rs.length : ℕ∞) = extDepth J M := by
  refine le_antisymm (length_le_extDepth J M hJ h.1) (iInf₂_le rs.length ?_)
  intro hsub
  have hlt := (rees_iff J M hJ rs.length).2 ⟨rs, rfl, h.1⟩
  obtain ⟨r, hrJ, hreg⟩ := exists_extend J rs M hJ h.1 fun i hi => by
    rcases hi.lt_or_eq with hi | rfl
    · exact hlt i hi
    · exact hsub
  exact h.2 r hrJ hreg

/-- A maximal `M`-regular sequence in `J` exists (Noetherianity). -/
theorem exists_maximal (J : Ideal R) (M : ModuleCat.{u} R)
    (hJ : J • (⊤ : Submodule R M) < ⊤) : ∃ rs, IsMaximalRegIn J M rs := by
  have : Nontrivial M := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ hJ)
  obtain ⟨_, ⟨rs, hrs, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R)
      (Ideal.ofList '' {rs : List R | IsRegIn J M rs}) ⟨_, [], ⟨by simp, IsRegular.nil R M⟩, rfl⟩
  refine ⟨rs, hrs, fun r hrJ hreg => ?_⟩
  have hin : Ideal.ofList (rs ++ [r]) ∈ Ideal.ofList '' {rs : List R | IsRegIn J M rs} :=
    ⟨rs ++ [r], ⟨fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hrs.1 x hx
      · simp at hx; exact hx ▸ hrJ, hreg⟩, rfl⟩
  have hle : Ideal.ofList rs ≤ Ideal.ofList (rs ++ [r]) := by simp
  have heq : Ideal.ofList rs = Ideal.ofList (rs ++ [r]) := by
    by_contra hne
    exact hmax _ hin (lt_of_le_of_ne hle hne)
  have hr : r ∈ Ideal.ofList rs := heq ▸ Ideal.subset_span (by simp)
  have hw := ((isWeaklyRegular_append_iff (M := M) rs [r]).1 hreg.toIsWeaklyRegular).2
  rw [isWeaklyRegular_singleton_iff] at hw
  have hnt := hrs.2.quot_ofList_smul_nontrivial (⊤ : Submodule R M)
  obtain ⟨y, hy⟩ := exists_ne (0 : M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M))
  apply hy
  apply hw
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  simp only [smul_zero, ← map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hr trivial)

/-- **Rees.** The maximal length of `M`-regular sequences in `J` is the least `i` with
`Ext^i(R/J, M) ≠ 0`: this least `i` is a natural number `n`, the supremum of regular-sequence
lengths is `n`, `n` is the greatest such length, and every maximal regular sequence has length
`n`. -/
theorem rees_depth (J : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hJ : J • (⊤ : Submodule R M) < ⊤) :
    ∃ n : ℕ, extDepth J M = n ∧ regDepth J M = n ∧ IsGreatest (regLengths J M) n ∧
      ∀ rs, IsMaximalRegIn J M rs → rs.length = n := by
  obtain ⟨rs0, h0⟩ := exists_maximal J M hJ
  have e0 := length_eq_extDepth_of_maximal J M hJ h0
  refine ⟨rs0.length, e0.symm, le_antisymm ?_ (le_iSup₂_of_le rs0 h0.1 le_rfl),
    ⟨⟨rs0, rfl, h0.1⟩, ?_⟩, fun rs h => ?_⟩
  · exact iSup₂_le fun rs h => e0 ▸ length_le_extDepth J M hJ h
  · rintro m ⟨rs, rfl, h⟩
    exact_mod_cast e0 ▸ length_le_extDepth J M hJ h
  · exact_mod_cast (length_eq_extDepth_of_maximal J M hJ h).trans e0.symm

end General

section Graded

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {m : ℕ}

/-- The standard grading of `k[x_1, ..., x_m]` (by total degree). -/
noncomputable abbrev 𝒜 (k : Type u) [Field k] (m : ℕ) := MvPolynomial.homogeneousSubmodule (Fin m) k

/-- The irrelevant (homogeneous maximal) ideal `(x_1, ..., x_m)`. -/
noncomputable abbrev irr (k : Type u) [Field k] (m : ℕ) : Ideal (MvPolynomial (Fin m) k) :=
  (HomogeneousIdeal.irrelevant (𝒜 k m)).toIdeal

lemma mem_irr_iff (f : MvPolynomial (Fin m) k) :
    f ∈ irr k m ↔ MvPolynomial.coeff 0 f = 0 := by
  show (GradedRing.proj (𝒜 k m) 0 f) = 0 ↔ _
  rw [GradedRing.proj_apply]
  show (MvPolynomial.decomposition.decompose' f 0 : MvPolynomial (Fin m) k) = 0 ↔ _
  rw [MvPolynomial.decomposition.decompose'_apply, MvPolynomial.homogeneousComponent_zero,
    MvPolynomial.C_eq_zero]

lemma le_irr {I : Ideal (MvPolynomial (Fin m) k)} (hI : I.IsHomogeneous (𝒜 k m))
    (hne : I ≠ ⊤) : I ≤ irr k m := by
  intro f hf
  rw [mem_irr_iff]
  by_contra hc
  have h0 := MvPolynomial.homogeneousComponent_mem_of_mem hI hf 0
  rw [MvPolynomial.homogeneousComponent_zero] at h0
  exact hne (Ideal.eq_top_of_isUnit_mem _ h0 ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C))

lemma irr_ne_top : irr k m ≠ ⊤ := by
  intro h
  have := (mem_irr_iff (k := k) (m := m) 1).1 (h ▸ Submodule.mem_top)
  simp at this

/-- The irrelevant ideal is the kernel of the constant-coefficient map `S → k`. Hence it is
maximal, and `S ⧸ irr k m` is the residue field `k`. -/
lemma irr_eq_ker : irr k m = RingHom.ker (MvPolynomial.constantCoeff (σ := Fin m) (R := k)) := by
  ext f
  rw [mem_irr_iff, RingHom.mem_ker, MvPolynomial.constantCoeff_eq]

lemma irr_isMaximal : (irr k m).IsMaximal := by
  rw [irr_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ fun c => ⟨MvPolynomial.C c, by simp⟩

/-- Reading 1 (grade): `M = S`, `J = I`, for a proper (e.g. homogeneous) ideal `I` of
`S = k[x_1, ..., x_m]`. -/
theorem grade_reading (I : Ideal (MvPolynomial (Fin m) k)) (hne : I ≠ ⊤) :
    ∃ n : ℕ, extDepth I (ModuleCat.of _ (MvPolynomial (Fin m) k)) = n ∧
      regDepth I (ModuleCat.of _ (MvPolynomial (Fin m) k)) = n ∧
      IsGreatest (regLengths I (ModuleCat.of _ (MvPolynomial (Fin m) k))) n ∧
      ∀ rs, IsMaximalRegIn I (ModuleCat.of _ (MvPolynomial (Fin m) k)) rs → rs.length = n := by
  refine rees_depth I _ ?_
  show I • (⊤ : Ideal (MvPolynomial (Fin m) k)) < ⊤
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact hne.lt_top

/-- Reading 2 (depth of `S/I` at the irrelevant ideal, i.e. Ext from the residue field
`S/(x_1, ..., x_m) = k`): `M = S/I`, `J = (x_1, ..., x_m)`, for a proper homogeneous `I`. -/
theorem quotient_reading (I : Ideal (MvPolynomial (Fin m) k)) (hI : I.IsHomogeneous (𝒜 k m))
    (hne : I ≠ ⊤) :
    ∃ n : ℕ, extDepth (irr k m) (ModuleCat.of _ (MvPolynomial (Fin m) k ⧸ I)) = n ∧
      regDepth (irr k m) (ModuleCat.of _ (MvPolynomial (Fin m) k ⧸ I)) = n ∧
      IsGreatest (regLengths (irr k m) (ModuleCat.of _ (MvPolynomial (Fin m) k ⧸ I))) n ∧
      ∀ rs, IsMaximalRegIn (irr k m) (ModuleCat.of _ (MvPolynomial (Fin m) k ⧸ I)) rs →
        rs.length = n := by
  refine rees_depth _ _ ?_
  refine lt_top_iff_ne_top.mpr fun h => irr_ne_top (k := k) (m := m) ?_
  have := congrArg (Submodule.comap (Submodule.mkQ I)) h
  rw [Submodule.comap_smul_top_of_surjective _ _ (Submodule.mkQ_surjective _),
    Submodule.comap_top, Submodule.ker_mkQ] at this
  rw [eq_top_iff, ← this]
  refine sup_le ?_ (le_irr hI hne)
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

end Graded

end C3200
