import Mathlib

/-!
# Conjecture 00000002511: symmetric tensors correspond to homogeneous polynomials

Over a field `K` of characteristic zero and a vector space `V` with a finite basis `b`
indexed by `ι` (so `n = card ι` variables):

* `symTensors K V d` is the subspace of `V^{⊗ d} = ⨂[K] _ : Fin d, V` (a genuine
  `PiTensorProduct`) of tensors fixed by every permutation `σ ∈ S_d` of the tensor factors
  (`PiTensorProduct.reindex`).
* `toPoly b d : V^{⊗ d} →ₗ[K] K[X_j | j ∈ ι]` is the linear map with
  `v₁ ⊗ ⋯ ⊗ v_d ↦ ℓ(v₁) ⋯ ℓ(v_d)`, where `ℓ(v) = ∑_j (b-coordinate j of v) X_j`.
  `eval_toPoly` shows that evaluating `toPoly b d T` at the coordinates `(φ (b j))_j` of a
  linear functional `φ` gives `T(φ, …, φ) = (φ ⊗ ⋯ ⊗ φ)(T)`.
* `symEquiv b d : symTensors K V d ≃ₗ[K] homogeneousSubmodule ι K d` is the restriction
  of `toPoly b d` (a linear isomorphism).
* `symToForm_symProd`: the symmetric product `T ⊙ U` (symmetrisation of `T ⊗ U`) is sent
  to the product of the two forms.
* `symmetric_tensors_are_forms` bundles these statements (main theorem).
-/

open PiTensorProduct MvPolynomial
open scoped TensorProduct

namespace C2511

noncomputable section

set_option linter.unusedSectionVars false

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

/-- The `d`-th tensor power `V^{⊗ d}`. -/
abbrev TPow (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (d : ℕ) : Type _ :=
  ⨂[K] _ : Fin d, V

/-- The action of `σ ∈ S_d` on `V^{⊗ d}` permuting the tensor factors. -/
def permAct (d : ℕ) (σ : Equiv.Perm (Fin d)) : TPow K V d ≃ₗ[K] TPow K V d :=
  PiTensorProduct.reindex K (fun _ : Fin d => V) σ

@[simp] lemma permAct_tprod {d : ℕ} (σ : Equiv.Perm (Fin d)) (v : Fin d → V) :
    permAct d σ (tprod K v) = tprod K (fun k => v (σ.symm k)) :=
  reindex_tprod _ _

/-- Symmetric tensors: the tensors of `V^{⊗ d}` fixed by every permutation of the factors. -/
def symTensors (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (d : ℕ) :
    Submodule K (TPow K V d) where
  carrier := {t | ∀ σ : Equiv.Perm (Fin d), permAct d σ t = t}
  add_mem' {x y} hx hy σ := by simp [map_add, hx σ, hy σ]
  zero_mem' σ := map_zero _
  smul_mem' c x hx σ := by simp [map_smul, hx σ]

/-- The generic linear form `ℓ(v) = ∑_j (b.repr v j) X_j`, i.e. `b j ↦ X_j`. -/
def linForm (b : Module.Basis ι K V) : V →ₗ[K] MvPolynomial ι K := b.constr K X

/-- The dictionary map `V^{⊗ d} → K[X]`, `v₁ ⊗ ⋯ ⊗ v_d ↦ ℓ(v₁) ⋯ ℓ(v_d)`. -/
def toPoly (b : Module.Basis ι K V) (d : ℕ) : TPow K V d →ₗ[K] MvPolynomial ι K :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra K (Fin d) (MvPolynomial ι K)).compLinearMap
      (fun _ => linForm b))

@[simp] lemma toPoly_tprod (b : Module.Basis ι K V) {d : ℕ} (v : Fin d → V) :
    toPoly b d (tprod K v) = ∏ k, linForm b (v k) := by
  simp [toPoly]

/-- Intrinsic meaning of the dictionary: evaluating the polynomial of `T` at the
coordinates `(φ (b j))_j` of a linear functional `φ` gives `T(φ, …, φ) = (φ ⊗ ⋯ ⊗ φ)(T)`. -/
theorem eval_toPoly (b : Module.Basis ι K V) {d : ℕ} (φ : Module.Dual K V) (T : TPow K V d) :
    eval (fun j => φ (b j)) (toPoly b d T) =
      PiTensorProduct.lift
        ((MultilinearMap.mkPiAlgebra K (Fin d) K).compLinearMap (fun _ => φ)) T := by
  have hφ : ∀ x, eval (fun j => φ (b j)) (linForm b x) = φ x := by
    have h : ((aeval (fun j => φ (b j))).toLinearMap ∘ₗ linForm b) = φ :=
      b.ext fun i => by simp [linForm]
    intro x
    simpa [MvPolynomial.coe_aeval_eq_eval] using LinearMap.congr_fun h x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r v => simp [map_prod, hφ]
  | add x y hx hy => simp [map_add, hx, hy]

/-- The basis of `V^{⊗ d}` made of `b (i 1) ⊗ ⋯ ⊗ b (i d)`. -/
def tBasis (b : Module.Basis ι K V) (d : ℕ) : Module.Basis (Fin d → ι) K (TPow K V d) :=
  Basis.piTensorProduct (fun _ => b)

/-- The exponent vector (content) of an index word `i : Fin d → ι`. -/
def content {d : ℕ} (i : Fin d → ι) : ι →₀ ℕ := ∑ k, Finsupp.single (i k) 1

lemma content_apply {d : ℕ} (i : Fin d → ι) (a : ι) :
    content i a = (Finset.univ.filter fun k => i k = a).card := by
  simp [content, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_boole]

lemma degree_content {d : ℕ} (i : Fin d → ι) : (content i).degree = d := by
  simp [content, map_sum]

lemma toPoly_tBasis (b : Module.Basis ι K V) {d : ℕ} (i : Fin d → ι) :
    toPoly b d (tBasis b d i) = monomial (content i) 1 := by
  simp [tBasis, linForm, content, monomial_sum_one, X]

/-- Coordinate expansion of the dictionary map. -/
lemma toPoly_eq_sum (b : Module.Basis ι K V) {d : ℕ} (T : TPow K V d) :
    toPoly b d T = ∑ i, (tBasis b d).repr T i • monomial (content i) 1 := by
  calc toPoly b d T = toPoly b d (∑ i, (tBasis b d).repr T i • tBasis b d i) := by
        rw [(tBasis b d).sum_repr]
    _ = _ := by rw [map_sum]; simp only [map_smul, toPoly_tBasis]

lemma coeff_toPoly (b : Module.Basis ι K V) {d : ℕ} (T : TPow K V d) (α : ι →₀ ℕ) :
    coeff α (toPoly b d T) =
      ∑ i ∈ Finset.univ.filter (fun i => content i = α), (tBasis b d).repr T i := by
  rw [toPoly_eq_sum, coeff_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [coeff_monomial]

/-- Permuting the factors permutes the coordinates. -/
lemma repr_permAct (b : Module.Basis ι K V) {d : ℕ} (σ : Equiv.Perm (Fin d)) (T : TPow K V d)
    (i : Fin d → ι) :
    (tBasis b d).repr (permAct d σ T) i = (tBasis b d).repr T (i ∘ σ) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, permAct_tprod, Finsupp.smul_apply, tBasis,
      Basis.piTensorProduct_repr_tprod_apply, Function.comp_apply]
    congr 1
    exact Fintype.prod_equiv σ.symm _ _ (fun k => by simp)
  | add x y hx hy => simp [map_add, hx, hy]

/-- Two index words with the same content differ by a permutation. -/
lemma exists_perm_of_content_eq {d : ℕ} {i j : Fin d → ι} (h : content i = content j) :
    ∃ σ : Equiv.Perm (Fin d), i = j ∘ σ := by
  have e : ∀ a, {k // i k = a} ≃ {k // j k = a} := fun a =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← content_apply, ← content_apply, h])
  exact ⟨Equiv.ofFiberEquiv e, funext fun k => (Equiv.ofFiberEquiv_map e k).symm⟩

lemma repr_sym_eq (b : Module.Basis ι K V) {d : ℕ} {T : TPow K V d} (hT : T ∈ symTensors K V d)
    {i j : Fin d → ι} (h : content i = content j) :
    (tBasis b d).repr T i = (tBasis b d).repr T j := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_content_eq h
  rw [← repr_permAct, hT σ]

lemma content_comp_perm {d : ℕ} (j : Fin d → ι) (σ : Equiv.Perm (Fin d)) :
    content (j ∘ σ) = content j :=
  Equiv.sum_comp σ (fun k => Finsupp.single (j k) 1)

/-- Every tensor is sent to a form of degree `d`; in particular symmetric tensors are forms. -/
lemma toPoly_mem (b : Module.Basis ι K V) {d : ℕ} (T : TPow K V d) :
    toPoly b d T ∈ homogeneousSubmodule ι K d := by
  rw [toPoly_eq_sum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (isHomogeneous_monomial _ (degree_content i))

/-- Injectivity on symmetric tensors (uses characteristic zero). -/
lemma toPoly_eq_zero [CharZero K] (b : Module.Basis ι K V) {d : ℕ} {T : TPow K V d}
    (hT : T ∈ symTensors K V d) (h0 : toPoly b d T = 0) : T = 0 := by
  refine (tBasis b d).repr.injective ?_
  ext i
  have h := congrArg (coeff (content i)) h0
  rw [coeff_toPoly, coeff_zero,
    Finset.sum_congr rfl (fun j hj => repr_sym_eq b hT (Finset.mem_filter.1 hj).2),
    Finset.sum_const, nsmul_eq_mul] at h
  have hc : ((Finset.univ.filter fun j => content j = content i).card : K) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, by simp⟩)
  simpa [hc] using h

/-- Every exponent vector of degree `d` is the content of some word of length `d`. -/
lemma exists_content_eq : ∀ (d : ℕ) (α : ι →₀ ℕ), α.degree = d → ∃ i : Fin d → ι, content i = α
  | 0, α, h => ⟨Fin.elim0, by simp [content, (Finsupp.degree_eq_zero_iff α).1 h]⟩
  | d + 1, α, h => by
    obtain ⟨a, ha⟩ : ∃ a, α a ≠ 0 := by
      by_contra hne
      push Not at hne
      have : α = 0 := Finsupp.ext hne
      simp [this] at h
    have hle : Finsupp.single a 1 ≤ α := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ha)
    obtain ⟨i, hi⟩ := exists_content_eq d (α - Finsupp.single a 1) (by
      have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
      rw [map_add, Finsupp.degree_single] at this
      omega)
    refine ⟨Fin.cons a i, ?_⟩
    rw [content, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← content, hi]
    exact add_tsub_cancel_of_le hle

/-- Each monomial `X^α` of degree `d` is the image of a symmetric tensor. -/
lemma exists_sym_monomial [CharZero K] (b : Module.Basis ι K V) {d : ℕ} (α : ι →₀ ℕ)
    (hα : α.degree = d) : ∃ T ∈ symTensors K V d, toPoly b d T = monomial α 1 := by
  obtain ⟨i₀, hi₀⟩ := exists_content_eq d α hα
  set F := Finset.univ.filter fun j : Fin d → ι => content j = α with hFdef
  have hF : (F.card : K) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i₀, by simp [F, hi₀]⟩)
  set T := (tBasis b d).equivFun.symm
    (fun j => if content j = α then (F.card : K)⁻¹ else 0) with hTdef
  have hrepr : ∀ j, (tBasis b d).repr T j = if content j = α then (F.card : K)⁻¹ else 0 :=
    fun j => by
      rw [← Module.Basis.equivFun_apply, hTdef, LinearEquiv.apply_symm_apply]
  refine ⟨T, fun σ => ?_, ?_⟩
  · refine (tBasis b d).repr.injective (Finsupp.ext fun j => ?_)
    rw [repr_permAct, hrepr, hrepr, content_comp_perm]
  · rw [toPoly_eq_sum]
    simp_rw [hrepr, ite_smul, zero_smul]
    rw [← Finset.sum_filter, ← hFdef]
    have : ∀ j ∈ F, (F.card : K)⁻¹ • monomial (content j) (1 : K) = (F.card : K)⁻¹ • monomial α 1 :=
      fun j hj => by rw [(Finset.mem_filter.1 hj).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, ← Nat.cast_smul_eq_nsmul K, smul_smul,
      mul_inv_cancel₀ hF, one_smul]

/-- Surjectivity onto forms of degree `d` (uses characteristic zero). -/
lemma exists_sym_of_mem [CharZero K] (b : Module.Basis ι K V) {d : ℕ} {p : MvPolynomial ι K}
    (hp : p ∈ homogeneousSubmodule ι K d) : ∃ T ∈ symTensors K V d, toPoly b d T = p := by
  have : homogeneousSubmodule ι K d ≤ (symTensors K V d).map (toPoly b d) := by
    rw [homogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨T, hT, h⟩ := exists_sym_monomial b α hα
    exact ⟨T, hT, by rw [h]; rfl⟩
  exact this hp

/-- The dictionary restricted to symmetric tensors, landing in the forms of degree `d`. -/
def symToForm (b : Module.Basis ι K V) (d : ℕ) :
    symTensors K V d →ₗ[K] homogeneousSubmodule ι K d :=
  ((toPoly b d).domRestrict (symTensors K V d)).codRestrict _ fun T => toPoly_mem (d := d) b T.1

@[simp] lemma symToForm_coe (b : Module.Basis ι K V) {d : ℕ} (T : symTensors K V d) :
    (symToForm b d T : MvPolynomial ι K) = toPoly b d T := rfl

theorem symToForm_bijective [CharZero K] (b : Module.Basis ι K V) (d : ℕ) :
    Function.Bijective (symToForm b d) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun T h => Subtype.ext ?_, fun p => ?_⟩
  · exact toPoly_eq_zero b T.2 (congrArg Subtype.val h)
  · obtain ⟨T, hT, h⟩ := exists_sym_of_mem b p.2
    exact ⟨⟨T, hT⟩, Subtype.ext h⟩

/-- The linear isomorphism `Sym^d V ≃ K[X]_d`. -/
def symEquiv [CharZero K] (b : Module.Basis ι K V) (d : ℕ) :
    symTensors K V d ≃ₗ[K] homogeneousSubmodule ι K d :=
  LinearEquiv.ofBijective (symToForm b d) (symToForm_bijective b d)

/-! ### Products: the dictionary is multiplicative -/

/-- The tensor product `V^{⊗ d} × V^{⊗ e} → V^{⊗ (d+e)}` (factors of the first argument first). -/
def tmulL (d e : ℕ) : TPow K V d →ₗ[K] TPow K V e →ₗ[K] TPow K V (d + e) :=
  (TensorProduct.mk K _ _).compr₂
    ((PiTensorProduct.reindex K (fun _ : Fin d ⊕ Fin e => V) finSumFinEquiv).toLinearMap ∘ₗ
      (PiTensorProduct.tmulEquiv K V).toLinearMap)

lemma toPoly_tmulL (b : Module.Basis ι K V) {d e : ℕ} (T : TPow K V d) (U : TPow K V e) :
    toPoly b (d + e) (tmulL d e T U) = toPoly b d T * toPoly b e U := by
  induction T using PiTensorProduct.induction_on generalizing U with
  | smul_tprod r v =>
    induction U using PiTensorProduct.induction_on with
    | smul_tprod s w =>
      simp [tmulL, Fin.prod_univ_add]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]
  | add x y hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, map_add, add_mul]

lemma permAct_permAct {d : ℕ} (σ τ : Equiv.Perm (Fin d)) (T : TPow K V d) :
    permAct d σ (permAct d τ T) = permAct d (σ * τ) T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r v => simp [Equiv.Perm.mul_def]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma toPoly_permAct (b : Module.Basis ι K V) {d : ℕ} (σ : Equiv.Perm (Fin d)) (T : TPow K V d) :
    toPoly b d (permAct d σ T) = toPoly b d T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, permAct_tprod, toPoly_tprod]
    rw [Equiv.prod_comp σ.symm (fun k => linForm b (v k))]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Symmetrisation `t ↦ (1/d!) ∑_σ σ·t`. -/
def symz (d : ℕ) : TPow K V d →ₗ[K] TPow K V d :=
  ((d.factorial : K)⁻¹) • ∑ σ : Equiv.Perm (Fin d), (permAct d σ).toLinearMap

lemma symz_mem {d : ℕ} (t : TPow K V d) : symz d t ∈ symTensors K V d := by
  intro τ
  simp only [symz, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearEquiv.coe_coe, map_smul, map_sum, permAct_permAct]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => permAct d σ t)

lemma symz_of_mem [CharZero K] {d : ℕ} {T : TPow K V d} (hT : T ∈ symTensors K V d) :
    symz d T = T := by
  simp only [symz, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearEquiv.coe_coe, hT _, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)), one_smul]

lemma toPoly_symz [CharZero K] (b : Module.Basis ι K V) {d : ℕ} (t : TPow K V d) :
    toPoly b d (symz d t) = toPoly b d t := by
  simp only [symz, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearEquiv.coe_coe, map_smul, map_sum, toPoly_permAct, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul K, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)), one_smul]

/-- The symmetric product `T ⊙ U = symz (T ⊗ U)` of symmetric tensors. -/
def symProd {d e : ℕ} (T : symTensors K V d) (U : symTensors K V e) : symTensors K V (d + e) :=
  ⟨symz (d + e) (tmulL d e T U), symz_mem _⟩

/-- The dictionary turns the symmetric product into the product of forms. -/
theorem symToForm_symProd [CharZero K] (b : Module.Basis ι K V) {d e : ℕ}
    (T : symTensors K V d) (U : symTensors K V e) :
    (symToForm b (d + e) (symProd T U) : MvPolynomial ι K) =
      symToForm b d T * symToForm b e U := by
  simp [symProd, toPoly_symz, toPoly_tmulL]

/-- **Main theorem (conjecture 00000002511).** Over a field `K` of characteristic zero, with a
basis `b` of `V` indexed by the finite type `ι`, for all degrees `d, e`:
1. every symmetric `d`-tensor is sent by the dictionary `toPoly b d` to a form (homogeneous
   polynomial) of degree `d`;
2. the restricted dictionary `symToForm b d : Sym^d V → K[X]_d` is a (linear) bijection;
3. it turns the symmetric product `T ⊙ U` of symmetric tensors into the product of forms;
4. conversely the product of two forms corresponds, under the inverse isomorphism, to the
   symmetric product of the corresponding symmetric tensors. -/
theorem symmetric_tensors_are_forms [CharZero K] (b : Module.Basis ι K V) :
    (∀ (d : ℕ) (T : TPow K V d), T ∈ symTensors K V d →
      toPoly b d T ∈ homogeneousSubmodule ι K d) ∧
    (∀ d : ℕ, Function.Bijective (symToForm b d)) ∧
    (∀ (d e : ℕ) (T : symTensors K V d) (U : symTensors K V e),
      (symToForm b (d + e) (symProd T U) : MvPolynomial ι K) =
        symToForm b d T * symToForm b e U) ∧
    (∀ (d e : ℕ) (p : homogeneousSubmodule ι K d) (q : homogeneousSubmodule ι K e),
      (symEquiv b (d + e)).symm ⟨p * q, p.2.mul q.2⟩ =
        symProd ((symEquiv b d).symm p) ((symEquiv b e).symm q)) := by
  refine ⟨fun d T _ => toPoly_mem b T, symToForm_bijective b, fun d e T U => symToForm_symProd b T U,
    fun d e p q => ?_⟩
  apply (symEquiv b (d + e)).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  have h := symToForm_symProd b ((symEquiv b d).symm p) ((symEquiv b e).symm q)
  have hp : symToForm b d ((symEquiv b d).symm p) = p := (symEquiv b d).apply_symm_apply p
  have hq : symToForm b e ((symEquiv b e).symm q) = q := (symEquiv b e).apply_symm_apply q
  rw [hp, hq] at h
  exact h.symm

/-- The two spaces have the same dimension (a corollary of the isomorphism). -/
theorem finrank_symTensors [CharZero K] (b : Module.Basis ι K V) (d : ℕ) :
    Module.finrank K (symTensors K V d) = Module.finrank K (homogeneousSubmodule ι K d) :=
  (symEquiv b d).finrank_eq

end

end C2511
