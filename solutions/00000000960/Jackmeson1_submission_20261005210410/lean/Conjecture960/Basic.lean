import Mathlib

/-!
# Conjecture 00000000960

*There exists a Banach space with no Schauder basis, each of whose separable subspaces has one.*

Witness: the non-separable Hilbert space `ℓ²(ℝ, 𝕜) = lp (fun _ : ℝ => 𝕜) 2` (`𝕜 = ℝ` or `ℂ`).

* "Schauder basis" is the classical, sequence-indexed notion: Mathlib's `SchauderBasis 𝕜 X`
  (`Mathlib/Analysis/Normed/Module/Bases.lean`), an `ℕ`-indexed biorthogonal system whose
  partial sums `∑_{i<n} f_i(x) e_i` converge to `x`.  We prove more than
  `IsEmpty (SchauderBasis 𝕜 X)`: `X` has no `GeneralSchauderBasis` indexed by any countable type (any non-trivial summation
  filter), and no sequence `e` such that every `x` is the sum of some convergent series
  `∑ aₙ eₙ` (no uniqueness and no continuity of coefficients assumed).
* "Separable subspace" is any linear subspace `V` (closed or not) whose underlying set is separable.
  Each such `V`, with the inherited norm, has a classical Schauder basis when it is
  infinite-dimensional, and a finite basis `UnconditionalSchauderBasis (Fin n) 𝕜 V`
  (biorthogonal system with `x = ∑_{i<n} f_i(x) e_i`) otherwise.
-/

open Filter Topology Set TopologicalSpace Submodule InnerProductSpace
open scoped lp

noncomputable section

namespace C960

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### Countable bases force separability -/

/-- If every vector lies in the closure of the span of a countable set, the space is separable. -/
theorem separableSpace_of_closure_span {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (s : Set X) (hs : s.Countable) (h : ∀ x : X, x ∈ closure (span 𝕜 s : Set X)) :
    SeparableSpace X := by
  have h1 : IsSeparable (closure (span 𝕜 s : Set X)) := hs.isSeparable.span.closure
  rwa [eq_univ_of_forall h, isSeparable_univ_iff] at h1

/-- A space with a sequence `e` such that every vector is the sum of some convergent series
`∑ aₙ eₙ` is separable (no uniqueness or continuity of the coefficients is assumed). -/
theorem separableSpace_of_series {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (e : ℕ → X)
    (h : ∀ x : X, ∃ a : ℕ → 𝕜, Tendsto (fun n => ∑ i ∈ Finset.range n, a i • e i) atTop (𝓝 x)) :
    SeparableSpace X := by
  refine separableSpace_of_closure_span (𝕜 := 𝕜) (range e) (countable_range e) fun x => ?_
  obtain ⟨a, ha⟩ := h x
  exact mem_closure_of_tendsto ha (Eventually.of_forall fun n =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span (mem_range_self i)))

/-- A space with a generalized Schauder basis indexed by a countable type (along any
non-trivial summation filter) is separable. -/
theorem separableSpace_of_generalSchauderBasis {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {ι : Type*} [Countable ι] {L : SummationFilter ι} [L.NeBot]
    (b : GeneralSchauderBasis ι 𝕜 X L) : SeparableSpace X := by
  refine separableSpace_of_closure_span (𝕜 := 𝕜) (range b.basis) (countable_range _) fun x => ?_
  refine mem_closure_of_tendsto (b.tendsto_proj x) (Eventually.of_forall fun A => ?_)
  rw [GeneralSchauderBasis.proj_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span (mem_range_self i))

/-! ### `ℓ²(ℝ, 𝕜)` is a non-separable Banach space -/

/-- `ℓ²(ℝ, 𝕜)` is not separable: Mathlib's default Hilbert basis of `ℓ²(ℝ, 𝕜)` is an orthonormal
family indexed by the uncountable set `ℝ`, whose members are at mutual distance `√2`. -/
theorem not_separableSpace_l2 : ¬ SeparableSpace ℓ²(ℝ, 𝕜) := by
  intro hsep
  let b : HilbertBasis ℝ 𝕜 ℓ²(ℝ, 𝕜) := default
  have hon := b.orthonormal
  have hdist : ∀ i j : ℝ, i ≠ j → 1 ≤ dist (b i) (b j) := by
    intro i j hij
    have h2 : dist (b i) (b j) ^ 2 = 2 := by
      rw [dist_eq_norm, @norm_sub_sq 𝕜, hon.1 i, hon.1 j, hon.2 hij]
      norm_num
    nlinarith [dist_nonneg (x := b i) (y := b j)]
  have : Countable ℝ := by
    refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (b i) (1 / 2))
      (fun i j hij => Metric.ball_disjoint_ball ?_) (fun _ => Metric.isOpen_ball)
      (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)
    linarith [hdist i j hij]
  exact not_countable this

/-- `ℓ²(ℝ, 𝕜)` has no classical (`ℕ`-indexed) Schauder basis, nor any generalized Schauder
basis indexed by a countable type, nor any representing sequence. -/
theorem l2_no_countable_basis :
    IsEmpty (SchauderBasis 𝕜 ℓ²(ℝ, 𝕜)) ∧
    (∀ (ι : Type) [Countable ι] (L : SummationFilter ι) [L.NeBot],
      IsEmpty (GeneralSchauderBasis ι 𝕜 ℓ²(ℝ, 𝕜) L)) ∧
    ¬ ∃ e : ℕ → ℓ²(ℝ, 𝕜), ∀ x, ∃ a : ℕ → 𝕜,
      Tendsto (fun n => ∑ i ∈ Finset.range n, a i • e i) atTop (𝓝 x) := by
  refine ⟨⟨fun b => not_separableSpace_l2 (separableSpace_of_generalSchauderBasis b)⟩,
    fun ι _ L _ => ⟨fun b => not_separableSpace_l2 (separableSpace_of_generalSchauderBasis b)⟩,
    fun ⟨e, he⟩ => not_separableSpace_l2 (separableSpace_of_series e he)⟩

/-! ### Separable inner product spaces have bases -/

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- In a (not necessarily complete) inner product space, an orthonormal family with dense span
expands every vector: `x = ∑ ⟪vᵢ, x⟫ vᵢ` (unconditionally).  Proof: pass to the completion,
where the family is a Hilbert basis, and pull the sum back along the isometric embedding. -/
theorem hasSum_of_orthonormal_dense {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hd : Dense (span 𝕜 (range v) : Set E)) (x : E) :
    HasSum (fun i => (inner 𝕜 (v i) x : 𝕜) • v i) x := by
  let j : E →ₗᵢ[𝕜] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  have hw : Orthonormal 𝕜 (j ∘ v) := hv.comp_linearIsometry j
  have hset : (span 𝕜 (range (j ∘ v)) : Set (UniformSpace.Completion E)) =
      j '' (span 𝕜 (range v) : Set E) := by
    rw [range_comp, ← LinearIsometry.coe_toLinearMap, Submodule.span_image, Submodule.map_coe]
  have hsp : ⊤ ≤ (span 𝕜 (range (j ∘ v))).topologicalClosure := by
    rw [top_le_iff, ← Submodule.dense_iff_topologicalClosure_eq_top, hset]
    have hj : (j : E → UniformSpace.Completion E) = ((↑) : E → UniformSpace.Completion E) :=
      UniformSpace.Completion.coe_toComplₗᵢ
    rw [hj]
    exact UniformSpace.Completion.denseRange_coe.dense_image
      (UniformSpace.Completion.continuous_coe E) hd
  let b := HilbertBasis.mk hw hsp
  have hb : ⇑b = j ∘ v := HilbertBasis.coe_mk hw hsp
  have h := b.hasSum_repr (j x)
  simp only [b.repr_apply_apply, hb, Function.comp_apply, LinearIsometry.inner_map_map] at h
  have h' : HasSum (j ∘ fun i => (inner 𝕜 (v i) x : 𝕜) • v i) (j x) := by
    simpa [Function.comp_def] using h
  exact (j.isometry.isUniformInducing.isInducing.hasSum_iff _ _).mp h'

/-- The unconditional Schauder basis `(vᵢ, ⟪vᵢ, ·⟫)` given by an orthonormal family with
dense span. -/
def onbBasis {ι : Type*} (v : ι → E) (hv : Orthonormal 𝕜 v)
    (hd : Dense (span 𝕜 (range v) : Set E)) : UnconditionalSchauderBasis ι 𝕜 E where
  basis := v
  coord i := innerSL 𝕜 (v i)
  ortho i j := by
    classical
    simpa [innerSL_apply_apply, Pi.single_apply] using orthonormal_iff_ite.mp hv i j
  expansion x := by
    simpa only [innerSL_apply_apply] using hasSum_of_orthonormal_dense hv hd x

/-- An unconditional `ℕ`-indexed basis is a classical Schauder basis (same vectors and
coordinates; convergence along all finite sets implies convergence of the partial sums). -/
def toSchauder (b : UnconditionalSchauderBasis ℕ 𝕜 E) : SchauderBasis 𝕜 E where
  basis := b.basis
  coord := b.coord
  ortho := b.ortho
  expansion x := (b.expansion x).mono_left SummationFilter.le_atTop

/-- Gram–Schmidt on a dense sequence: a separable inner product space has an orthonormal
family, indexed by a subset of `ℕ`, with dense span. -/
theorem exists_orthonormal_dense [SeparableSpace E] :
    ∃ (S : Set ℕ) (v : S → E), Orthonormal 𝕜 v ∧ Dense (span 𝕜 (range v) : Set E) := by
  obtain ⟨f, hf⟩ := exists_dense_seq E
  refine ⟨{i | gramSchmidtNormed 𝕜 f i ≠ 0}, fun i => gramSchmidtNormed 𝕜 f i,
    gramSchmidtNormed_orthonormal' f, ?_⟩
  have hspan : span 𝕜 (range fun i : {i | gramSchmidtNormed 𝕜 f i ≠ 0} =>
      gramSchmidtNormed 𝕜 f i) = span 𝕜 (range f) := by
    rw [← span_gramSchmidt 𝕜 f, ← span_gramSchmidtNormed_range f]
    apply le_antisymm
    · exact span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : gramSchmidtNormed 𝕜 f i = 0
      · rw [h]; exact zero_mem _
      · exact subset_span ⟨⟨i, h⟩, rfl⟩
  rw [hspan]
  exact hf.mono subset_span

/-- A space with a finite basis is finite-dimensional. -/
theorem finiteDimensional_of_basis {ι : Type*} [Fintype ι]
    (b : UnconditionalSchauderBasis ι 𝕜 E) : FiniteDimensional 𝕜 E := by
  refine Module.Finite.of_surjective (Fintype.linearCombination 𝕜 b.basis) fun x =>
    ⟨fun i => b.coord i x, ?_⟩
  rw [Fintype.linearCombination_apply]
  exact ((b.expansion x).unique (hasSum_fintype _)).symm

/-- A finite-dimensional inner product space has a finite basis
`UnconditionalSchauderBasis (Fin (finrank 𝕜 E))` (an orthonormal basis). -/
theorem finite_has_basis [FiniteDimensional 𝕜 E] :
    Nonempty (UnconditionalSchauderBasis (Fin (Module.finrank 𝕜 E)) 𝕜 E) := by
  let b := stdOrthonormalBasis 𝕜 E
  refine ⟨onbBasis b b.orthonormal ?_⟩
  rw [← b.coe_toBasis, b.toBasis.span_eq, Submodule.top_coe]
  exact dense_univ

/-- Every infinite-dimensional separable inner product space (complete or not) has a classical
Schauder basis (Gram–Schmidt on a dense sequence, then enumerate by `ℕ`). -/
theorem separable_has_schauderBasis [SeparableSpace E] (hE : ¬ FiniteDimensional 𝕜 E) :
    Nonempty (SchauderBasis 𝕜 E) := by
  obtain ⟨S, v, hv, hd⟩ := exists_orthonormal_dense (𝕜 := 𝕜) (E := E)
  rcases finite_or_infinite S with hS | hS
  · have := Fintype.ofFinite S
    exact absurd (finiteDimensional_of_basis (onbBasis v hv hd)) hE
  · obtain ⟨e⟩ : Nonempty (ℕ ≃ S) := nonempty_equiv_of_countable
    exact ⟨toSchauder (onbBasis (v ∘ e) (hv.comp _ e.injective)
      (by rwa [EquivLike.range_comp]))⟩

end InnerProduct

/-- Every separable linear subspace `V` of `ℓ²(ℝ, 𝕜)` (closed or not), with the inherited norm,
has a finite basis of length `dim V` if it is finite-dimensional and a classical Schauder basis
if it is infinite-dimensional. -/
theorem l2_separable_subspace_has_basis (V : Submodule 𝕜 ℓ²(ℝ, 𝕜))
    (hV : IsSeparable (V : Set ℓ²(ℝ, 𝕜))) :
    (FiniteDimensional 𝕜 V →
        Nonempty (UnconditionalSchauderBasis (Fin (Module.finrank 𝕜 V)) 𝕜 V)) ∧
      (¬ FiniteDimensional 𝕜 V → Nonempty (SchauderBasis 𝕜 V)) := by
  have : SeparableSpace V := hV.separableSpace
  exact ⟨fun _ => finite_has_basis, separable_has_schauderBasis⟩

/-- Non-vacuity: `ℓ²(ℝ, 𝕜)` has a closed, separable, infinite-dimensional subspace (the closed
span of countably many standard basis vectors). -/
theorem l2_exists_closed_separable_infinite :
    ∃ V : Submodule 𝕜 ℓ²(ℝ, 𝕜), IsClosed (V : Set ℓ²(ℝ, 𝕜)) ∧
      IsSeparable (V : Set ℓ²(ℝ, 𝕜)) ∧ ¬ FiniteDimensional 𝕜 V := by
  let b : HilbertBasis ℝ 𝕜 ℓ²(ℝ, 𝕜) := default
  let V := (span 𝕜 (range fun n : ℕ => b n)).topologicalClosure
  refine ⟨V, Submodule.isClosed_topologicalClosure _,
    ((countable_range _).isSeparable.span).closure, fun hfin => ?_⟩
  have hmem : ∀ n : ℕ, b n ∈ V := fun n =>
    Submodule.le_topologicalClosure _ (subset_span (mem_range_self n))
  have hli : LinearIndependent 𝕜 (fun n : ℕ => (⟨b n, hmem n⟩ : V)) := by
    refine LinearIndependent.of_comp V.subtype ?_
    exact b.orthonormal.linearIndependent.comp _ Nat.cast_injective
  have : Finite ℕ := hli.finite
  exact _root_.not_finite ℕ

/-- **Conjecture 00000000960.**  Over `𝕜 = ℝ` or `ℂ`, there is a Banach space `X` (namely
`ℓ²(ℝ, 𝕜)`) that is not separable, has no classical Schauder basis (indeed no countably indexed
generalized Schauder basis and no representing sequence), and each of whose separable linear
subspaces `V` has a classical Schauder basis when infinite-dimensional and a finite basis
when finite-dimensional; infinite-dimensional separable closed subspaces exist. -/
theorem conjecture960 :
    ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : NormedSpace 𝕜 X), CompleteSpace X ∧
      ¬ SeparableSpace X ∧
      IsEmpty (SchauderBasis 𝕜 X) ∧
      (∀ (ι : Type) [Countable ι] (L : SummationFilter ι) [L.NeBot],
        IsEmpty (GeneralSchauderBasis ι 𝕜 X L)) ∧
      (¬ ∃ e : ℕ → X, ∀ x, ∃ a : ℕ → 𝕜,
        Tendsto (fun n => ∑ i ∈ Finset.range n, a i • e i) atTop (𝓝 x)) ∧
      (∀ V : Submodule 𝕜 X, IsSeparable (V : Set X) →
        (FiniteDimensional 𝕜 V →
            Nonempty (UnconditionalSchauderBasis (Fin (Module.finrank 𝕜 V)) 𝕜 V)) ∧
          (¬ FiniteDimensional 𝕜 V → Nonempty (SchauderBasis 𝕜 V))) ∧
      ∃ V : Submodule 𝕜 X, IsClosed (V : Set X) ∧ IsSeparable (V : Set X) ∧
        ¬ FiniteDimensional 𝕜 V :=
  ⟨ℓ²(ℝ, 𝕜), inferInstance, inferInstance, inferInstance, not_separableSpace_l2,
    l2_no_countable_basis.1, l2_no_countable_basis.2.1, l2_no_countable_basis.2.2,
    l2_separable_subspace_has_basis, l2_exists_closed_separable_infinite⟩

/-- The real case, in the form closest to the conjecture's wording. -/
theorem conjecture960_real :
    ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X), CompleteSpace X ∧
      IsEmpty (SchauderBasis ℝ X) ∧
      ∀ V : Submodule ℝ X, IsSeparable (V : Set X) → ¬ FiniteDimensional ℝ V →
        Nonempty (SchauderBasis ℝ V) := by
  obtain ⟨X, i1, i2, hc, -, he, -, -, hV, -⟩ := conjecture960 (𝕜 := ℝ)
  exact ⟨X, i1, i2, hc, he, fun V hs => (hV V hs).2⟩

end C960
