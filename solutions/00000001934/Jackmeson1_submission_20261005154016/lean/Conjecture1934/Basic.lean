import Mathlib

/-!
# Conjecture 00000001934 (disproof of clause 1)

The conjecture states: "All actions of SL(n,Z) (n >= 3) on (n-1)-manifolds are finite (the image is a
finite group); the classification table of standard forms in n dimensions is exhausted by
fractional-linear actions on projective space."

We refute the first clause. For every `n = d + 1 >= 3`, the group `SL(n, ℤ)` acts on the unit sphere
`S^{n-1} ⊂ ℝⁿ` (a compact, connected, analytic manifold of dimension `d = n - 1`) by
`A • v = A v / ‖A v‖`. Every element acts by an analytic (`C^ω`) map, and the image of
`SL(n, ℤ)` in `Equiv.Perm S^{n-1}` is infinite: the transvections `I + k E₀₁` (`k ∈ ℤ`) act by pairwise
distinct permutations. Since analytic implies `C^r` for every `r`, this refutes clause 1 for `C^r`
actions for every regularity `r ∈ {0, 1, 2, …, ∞, ω}` (`r = 0`: continuous actions).
-/

open Metric Matrix
open scoped Manifold ContDiff

namespace C1934

noncomputable section

/-- Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The unit sphere `S^{n-1} ⊂ ℝⁿ`. -/
abbrev Sph (n : ℕ) : Type := sphere (0 : E n) 1

/-- The group `SL(n, ℤ)` of integer `n × n` matrices of determinant one. -/
abbrev SLZ (n : ℕ) : Type := SpecialLinearGroup (Fin n) ℤ

/-- The linear map `v ↦ A v` of `ℝⁿ` given by `A ∈ SL(n, ℤ)` (entries cast to `ℝ`). -/
def lin {n : ℕ} (A : SLZ n) : E n →L[ℝ] E n :=
  LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin ((A : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℝ)))

lemma lin_apply {n : ℕ} (A : SLZ n) (v : E n) :
    lin A v = WithLp.toLp 2 (((A : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℝ)) *ᵥ v.ofLp) :=
  rfl

lemma lin_mul {n : ℕ} (A B : SLZ n) (v : E n) : lin (A * B) v = lin A (lin B v) := by
  simp only [lin_apply, Matrix.mulVec_mulVec]
  congr 2
  rw [← Matrix.map_mul]
  rfl

lemma lin_one {n : ℕ} (v : E n) : lin 1 v = v := by
  simp [lin_apply]

lemma lin_ne_zero {n : ℕ} (A : SLZ n) {v : E n} (hv : v ≠ 0) : lin A v ≠ 0 := by
  intro h
  apply hv
  have := lin_mul A⁻¹ A v
  rwa [inv_mul_cancel, lin_one, h, map_zero] at this

/-- Radial projection `w ↦ w / ‖w‖`. -/
def nrm {n : ℕ} (w : E n) : E n := ‖w‖⁻¹ • w

lemma nrm_mem {n : ℕ} {w : E n} (hw : w ≠ 0) : nrm w ∈ sphere (0 : E n) 1 := by
  simp [nrm, norm_smul, hw]

lemma nrm_smul_pos {n : ℕ} {c : ℝ} (hc : 0 < c) (w : E n) : nrm (c • w) = nrm w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [nrm]
  simp only [nrm, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul, mul_inv]
  congr 1
  field_simp

/-- The action map: `A • v = A v / ‖A v‖` on the unit sphere. -/
def act {n : ℕ} (A : SLZ n) (x : Sph n) : Sph n :=
  ⟨nrm (lin A x), nrm_mem (lin_ne_zero A (ne_zero_of_mem_unit_sphere x))⟩

/-- `v ↦ A v / ‖A v‖` is a group action of `SL(n, ℤ)` on `S^{n-1}`. -/
instance instMulAction (n : ℕ) : MulAction (SLZ n) (Sph n) where
  smul := act
  one_smul x := by
    apply Subtype.ext
    show nrm (lin 1 (x : E n)) = x
    rw [lin_one, nrm, norm_eq_of_mem_sphere x, inv_one, one_smul]
  mul_smul A B x := by
    apply Subtype.ext
    show nrm (lin (A * B) (x : E n)) = nrm (lin A (nrm (lin B (x : E n))))
    have hB : 0 < ‖lin B (x : E n)‖⁻¹ :=
      inv_pos.2 (norm_pos_iff.2 (lin_ne_zero B (ne_zero_of_mem_unit_sphere x)))
    have e : nrm (lin B (x : E n)) = ‖lin B (x : E n)‖⁻¹ • lin B (x : E n) := rfl
    rw [e, map_smul, nrm_smul_pos hB, lin_mul]

lemma smul_coe {n : ℕ} (A : SLZ n) (x : Sph n) :
    ((A • x : Sph n) : E n) = ‖lin A x‖⁻¹ • lin A x := rfl

/-- Every element of `SL(d+1, ℤ)` acts on `S^d` by an analytic (`C^ω`) map. -/
theorem contMDiff_smul (d : ℕ) (A : SLZ (d + 1)) :
    ContMDiff (𝓡 d) (𝓡 d) ω (fun x : Sph (d + 1) => A • x) := by
  have : Fact (Module.finrank ℝ (E (d + 1)) = d + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hg : ∀ x : Sph (d + 1),
      ContDiffAt ℝ ω (fun w : E (d + 1) => ‖lin A w‖⁻¹ • lin A w) (x : E (d + 1)) := by
    intro x
    have h0 : lin A x ≠ 0 := lin_ne_zero A (ne_zero_of_mem_unit_sphere x)
    have hL : ContDiffAt ℝ ω (fun w => lin A w) (x : E (d + 1)) := (lin A).contDiff.contDiffAt
    exact ((hL.norm ℝ h0).inv (norm_ne_zero_iff.2 h0)).smul hL
  have hf : ContMDiff (𝓡 d) 𝓘(ℝ, E (d + 1)) ω
      (fun x : Sph (d + 1) => ‖lin A x‖⁻¹ • lin A x) :=
    fun x => (hg x).contMDiffAt.comp x (contMDiff_coe_sphere x)
  exact hf.codRestrict_sphere (fun x => (A • x).2)

/-- The transvection `I + k E_{ij}` (`i ≠ j`) as an element of `SL(n, ℤ)`. -/
def tv {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : ℤ) : SLZ n :=
  ⟨transvection i j k, det_transvection_of_ne i j hij k⟩

/-- The standard basis vector `e_j`, a point of the sphere. -/
def ePt {n : ℕ} (j : Fin n) : Sph n :=
  ⟨WithLp.toLp 2 (Pi.single j 1), by simp⟩

lemma lin_tv_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : ℤ) (a : Fin n) :
    (lin (tv hij k) (ePt j : E n)).ofLp a = if a = i then (k : ℝ) else if a = j then 1 else 0 := by
  show (((transvection i j k).map (Int.castRingHom ℝ)) *ᵥ Pi.single j 1) a = _
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply, transvection,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hai : a = i
  · subst hai; simp [hij]
  · by_cases haj : a = j
    · subst haj; simp [hai, Ne.symm hai]
    · simp [hai, haj, Ne.symm hai]

/-- Distinct `k` give distinct images of `e_j` under `I + k E_{ij}`. -/
lemma tv_smul_injective {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (fun k : ℤ => (tv hij k) • ePt j) := by
  intro k l h
  have h' := congrArg (fun x : Sph n => (x : E n)) h
  simp only [smul_coe] at h'
  have hi := congrArg (fun x : E n => x.ofLp i) h'
  have hj := congrArg (fun x : E n => x.ofLp j) h'
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, lin_tv_apply,
    if_neg hij.symm, if_true, mul_one] at hi hj
  have hl : ‖lin (tv hij l) (ePt j : E n)‖⁻¹ ≠ 0 :=
    inv_ne_zero (norm_ne_zero_iff.2 (lin_ne_zero _ (ne_zero_of_mem_unit_sphere _)))
  rw [hj] at hi
  exact_mod_cast mul_left_cancel₀ hl hi

/-- The image of `SL(n, ℤ)` in `Equiv.Perm S^{n-1}` is infinite as soon as `n ≥ 2`. -/
theorem range_toPermHom_infinite {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (Set.range (MulAction.toPermHom (SLZ n) (Sph n))).Infinite := by
  have hinj : Function.Injective (fun k : ℤ => MulAction.toPermHom (SLZ n) (Sph n) (tv hij k)) := by
    intro k l h
    apply tv_smul_injective hij
    exact congrArg (fun σ : Equiv.Perm (Sph n) => σ (ePt j)) h
  exact (Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)

/-- The sphere `S^d` (`d ≥ 1`) is connected. -/
instance connectedSpace_sph (d : ℕ) [Fact (1 ≤ d)] : ConnectedSpace (Sph (d + 1)) := by
  have h : 1 < Module.rank ℝ (E (d + 1)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast Nat.lt_succ_of_le (Fact.out : 1 ≤ d)
  exact isConnected_iff_connectedSpace.mp (isConnected_sphere h 0 zero_le_one)

/-- Clause 1 of the conjecture for a fixed `n`, at regularity `C^r`: every `C^r` action of
`SL(n, ℤ)` on a compact, connected, Hausdorff, boundaryless `C^r` manifold `M` of dimension
`d = n - 1` has finite image in `Equiv.Perm M`. (`r = 0`: continuous actions on topological manifolds;
`r = ∞`: smooth; `r = ω`: analytic.) The extra hypotheses on `M` only weaken the clause. -/
def Clause1At (r : WithTop ℕ∞) (n : ℕ) : Prop :=
  ∀ d : ℕ, d + 1 = n →
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) r M] [MulAction (SLZ n) M],
      (∀ A : SLZ n, ContMDiff (𝓡 d) (𝓡 d) r (fun x : M => A • x)) →
      (Set.range (MulAction.toPermHom (SLZ n) M)).Finite

/-- Clause 1 of the conjecture: `Clause1At r n` for every `n ≥ 3`. -/
def Clause1 (r : WithTop ℕ∞) : Prop := ∀ n : ℕ, 3 ≤ n → Clause1At r n

/-- For every `n ≥ 3` and every regularity `r`, clause 1 fails for `SL(n, ℤ)`: the action
`A • v = A v / ‖A v‖` on the sphere `S^{n-1}` is a counterexample. -/
theorem not_clause1At (r : WithTop ℕ∞) (n : ℕ) (hn : 3 ≤ n) : ¬ Clause1At r n := by
  intro h
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  have : Fact (1 ≤ d) := ⟨by omega⟩
  have : IsManifold (𝓡 d) r (Sph (d + 1)) := IsManifold.of_le le_top
  have hfin := h d rfl (Sph (d + 1)) (fun A => (contMDiff_smul d A).of_le le_top)
  have hij : (⟨0, by omega⟩ : Fin (d + 1)) ≠ ⟨1, by omega⟩ := by simp
  exact range_toPermHom_infinite hij hfin

/-- Clause 1 is false at every regularity. -/
theorem not_clause1 (r : WithTop ℕ∞) : ¬ Clause1 r :=
  fun h => not_clause1At r 3 le_rfl (h 3 le_rfl)

/-- The conjecture is the conjunction of clause 1 and clause 2; whatever clause 2 means, the
conjunction is false. -/
theorem not_conjecture (r : WithTop ℕ∞) (Clause2 : Prop) : ¬ (Clause1 r ∧ Clause2) :=
  fun h => not_clause1 r h.1

end

end C1934
