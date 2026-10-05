import Mathlib

/-!
# Conjecture 00000000981 is false

Conjecture: there exists a compact operator `T` whose point spectrum `σ_p(T)` is dense in the
unit disk, yet every invariant subspace of `T` contains an eigenvector.

We show that no compact operator on any complex normed space has point spectrum dense in the
unit disk: for every `δ > 0` a compact operator has only finitely many eigenvalues `μ` with
`δ ≤ ‖μ‖` (`IsCompactOperator.finite_eigenvalues_ge`).  The proof is the classical one:
eigenvectors for distinct eigenvalues are linearly independent, and the Riesz lemma applied to the
increasing chain of their spans produces a bounded sequence whose images under `T` are
`δ/2`-separated, which contradicts compactness.  The eigenvector clause is never used.
-/

open Metric Filter Topology Module End

namespace C981

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The point spectrum `σ_p(T)`: the set of eigenvalues of `T`. -/
def pointSpectrum (T : E →ₗ[ℂ] E) : Set ℂ := {μ | ∃ x : E, x ≠ 0 ∧ T x = μ • x}

/-- "Every invariant subspace of `T` contains an eigenvector": every nonzero closed `T`-invariant
subspace contains a nonzero vector `x` with `T x = μ • x` for some `μ`. -/
def EveryInvariantSubspaceHasEigenvector (T : E →ₗ[ℂ] E) : Prop :=
  ∀ V : Submodule ℂ E, V ≠ ⊥ → IsClosed (V : Set E) → (∀ x ∈ V, T x ∈ V) →
    ∃ x ∈ V, x ≠ 0 ∧ ∃ μ : ℂ, T x = μ • x

/-- A compact operator has only finitely many eigenvalues of modulus at least `δ`, for every
`δ > 0`. -/
theorem finite_eigenvalues_ge {T : E →ₗ[ℂ] E} (hT : IsCompactOperator T) {δ : ℝ} (hδ : 0 < δ) :
    {μ ∈ pointSpectrum T | δ ≤ ‖μ‖}.Finite := by
  by_contra hinf
  set S := {μ ∈ pointSpectrum T | δ ≤ ‖μ‖}
  have : Infinite S := Set.infinite_coe_iff.mpr hinf
  let f : ℕ ↪ S := Infinite.natEmbedding S
  let lam : ℕ → ℂ := fun n => (f n : ℂ)
  have hlam_inj : Function.Injective lam := fun a b h => f.injective (Subtype.ext h)
  have hlam_mem (n : ℕ) : lam n ∈ S := (f n).2
  have hlam_norm (n : ℕ) : δ ≤ ‖lam n‖ := (hlam_mem n).2
  have hlam_ne (n : ℕ) : lam n ≠ 0 := by
    intro h; have := hlam_norm n; rw [h, norm_zero] at this; linarith
  choose v hv0 hv using fun n => (hlam_mem n).1
  have hli : LinearIndependent ℂ v := by
    refine Module.End.eigenvectors_linearIndependent' (T : End ℂ E) lam hlam_inj v fun n => ?_
    exact ⟨Module.End.mem_eigenspace_iff.mpr (hv n), hv0 n⟩
  -- the increasing chain of spans
  let M : ℕ → Submodule ℂ E := fun n => Submodule.span ℂ (v '' Set.Iio n)
  have hM_fd (n : ℕ) : FiniteDimensional ℂ (M n) :=
    FiniteDimensional.span_of_finite ℂ ((Set.finite_Iio n).image v)
  have hM_closed (n : ℕ) : IsClosed (M n : Set E) := Submodule.closed_of_finiteDimensional _
  have hM_mono {m n : ℕ} (h : m ≤ n) : M m ≤ M n :=
    Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))
  have hv_mem (n : ℕ) : v n ∈ M (n + 1) :=
    Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
  have hv_not (n : ℕ) : v n ∉ M n := hli.notMem_span_image (by simp)
  have hT_M (n : ℕ) : ∀ x ∈ M n, T x ∈ M n := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => T x ∈ M n) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨k, hk, rfl⟩
      rw [hv k]
      exact (M n).smul_mem _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · simp
    · intro x y _ _ hx hy; rw [map_add]; exact (M n).add_mem hx hy
    · intro a x _ hx; rw [map_smul]; exact (M n).smul_mem a hx
  have hTl_M (n : ℕ) : ∀ x ∈ M (n + 1), T x - lam n • x ∈ M n := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => T x - lam n • x ∈ M n) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨k, hk, rfl⟩
      rw [hv k, ← sub_smul]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (M n).smul_mem _ (Submodule.subset_span ⟨k, hk, rfl⟩)
      · simp
    · simp
    · intro x y _ _ hx hy
      have : T (x + y) - lam n • (x + y) = (T x - lam n • x) + (T y - lam n • y) := by
        rw [map_add, smul_add]; abel
      rw [this]; exact (M n).add_mem hx hy
    · intro a x _ hx
      have : T (a • x) - lam n • (a • x) = a • (T x - lam n • x) := by
        rw [map_smul, smul_sub, smul_comm]
      rw [this]; exact (M n).smul_mem a hx
  -- Riesz lemma inside `M (n + 1)`
  have hy (n : ℕ) : ∃ y ∈ M (n + 1), ‖y‖ = 1 ∧ ∀ z ∈ M n, (1 / 2 : ℝ) ≤ ‖y - z‖ := by
    have h₁ : IsClosed ((M n).comap (M (n + 1)).subtype : Set (M (n + 1))) := by
      exact (hM_closed n).preimage continuous_subtype_val
    have h₂ : ∃ x : M (n + 1), x ∉ (M n).comap (M (n + 1)).subtype :=
      ⟨⟨v n, hv_mem n⟩, by simpa using hv_not n⟩
    obtain ⟨⟨x, hx⟩, -, hxn, hxy⟩ := riesz_lemma_of_lt_one h₁ h₂ (r := 1 / 2) (by norm_num)
    refine ⟨x, hx, by simpa using hxn, fun z hz => ?_⟩
    have := hxy ⟨z, hM_mono (Nat.le_succ n) hz⟩ (by simpa using hz)
    simpa using this
  choose y hyM hy1 hysep using hy
  -- the images `T (y n)` are `δ/2`-separated
  have hsep {m n : ℕ} (hmn : m < n) : δ / 2 ≤ ‖T (y n) - T (y m)‖ := by
    set z : E := (lam n)⁻¹ • (lam n • y n - T (y n) + T (y m)) with hz
    have hzM : z ∈ M n := by
      refine (M n).smul_mem _ ((M n).add_mem ?_ ?_)
      · have := (M n).neg_mem (hTl_M n (y n) (hyM n))
        simpa using this
      · exact hT_M n _ (hM_mono hmn (hyM m))
    have heq : T (y n) - T (y m) = lam n • (y n - z) := by
      rw [hz, smul_sub, smul_smul, mul_inv_cancel₀ (hlam_ne n), one_smul]; abel
    rw [heq, norm_smul]
    have h1 := hysep n z hzM
    have h2 := hlam_norm n
    nlinarith [norm_nonneg (y n - z)]
  -- compactness gives a convergent subsequence: contradiction
  obtain ⟨K, hK, hTK⟩ := hT.image_subset_compact_of_bounded (isBounded_closedBall (x := (0 : E))
    (r := 1))
  have hmemK (n : ℕ) : T (y n) ∈ K := hTK ⟨y n, by simp [hy1 n], rfl⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmemK
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq (δ / 2) (by linarith)
  have := hN (N + 1) (Nat.le_succ N) N le_rfl
  rw [dist_eq_norm] at this
  have := hsep (hφ (Nat.lt_succ_self N))
  simp only [Function.comp] at *
  linarith

/-- No compact operator on a complex normed space has point spectrum dense in the open unit
disk. -/
theorem not_ball_subset_closure_pointSpectrum {T : E →ₗ[ℂ] E} (hT : IsCompactOperator T) :
    ¬ (ball (0 : ℂ) 1 ⊆ closure (pointSpectrum T)) := by
  intro h
  set F := {μ ∈ pointSpectrum T | (1 / 2 : ℝ) ≤ ‖μ‖}
  have hF : F.Finite := finite_eigenvalues_ge hT (by norm_num)
  have hinf : ((fun t : ℝ => (t : ℂ)) '' Set.Ioo (1 / 2) 1).Infinite :=
    (Set.Ioo_infinite (by norm_num)).image Complex.ofReal_injective.injOn
  obtain ⟨w, ⟨t, ht, rfl⟩, hwF⟩ := (hinf.sdiff hF).nonempty
  have ht0 : 0 < t := by linarith [ht.1]
  have hnt : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht0]
  have hw : (t : ℂ) ∈ closure (pointSpectrum T) := h (by rw [mem_ball_zero_iff, hnt]; exact ht.2)
  rw [_root_.mem_closure_iff] at hw
  have hU : IsOpen ({z : ℂ | 1 / 2 < ‖z‖} ∩ Fᶜ) :=
    (isOpen_lt continuous_const continuous_norm).inter hF.isClosed.isOpen_compl
  obtain ⟨μ, ⟨hμ1, hμF⟩, hμ⟩ := hw _ hU ⟨show (1 / 2 : ℝ) < ‖(t : ℂ)‖ by rw [hnt]; exact ht.1, hwF⟩
  exact hμF ⟨hμ, le_of_lt hμ1⟩

/-- **Conjecture 00000000981 is false** (linear-map form): on no complex normed space is there
a compact linear operator `T` whose point spectrum is dense in the open unit disk and all of whose
nonzero closed invariant subspaces contain an eigenvector. -/
theorem conjecture_false (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ¬ ∃ T : E →ₗ[ℂ] E, IsCompactOperator T ∧ ball (0 : ℂ) 1 ⊆ closure (pointSpectrum T) ∧
      EveryInvariantSubspaceHasEigenvector T := by
  rintro ⟨T, hT, hd, -⟩
  exact not_ball_subset_closure_pointSpectrum hT hd

/-- **Conjecture 00000000981 is false** (bounded-operator form, including Banach and Hilbert
spaces): no compact bounded operator `T` has point spectrum dense in the open unit disk with
every nonzero closed invariant subspace containing an eigenvector. -/
theorem conjecture_false_clm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ¬ ∃ T : E →L[ℂ] E, IsCompactOperator T ∧
      ball (0 : ℂ) 1 ⊆ closure (pointSpectrum (T : E →ₗ[ℂ] E)) ∧
      EveryInvariantSubspaceHasEigenvector (T : E →ₗ[ℂ] E) := by
  rintro ⟨T, hT, hd, -⟩
  exact not_ball_subset_closure_pointSpectrum (T := (T : E →ₗ[ℂ] E)) hT hd

/-- Density in the closed unit disk is also impossible (it implies density in the open disk). -/
theorem not_closedBall_subset_closure_pointSpectrum {T : E →ₗ[ℂ] E} (hT : IsCompactOperator T) :
    ¬ (closedBall (0 : ℂ) 1 ⊆ closure (pointSpectrum T)) := fun h =>
  not_ball_subset_closure_pointSpectrum hT (ball_subset_closedBall.trans h)

end C981
