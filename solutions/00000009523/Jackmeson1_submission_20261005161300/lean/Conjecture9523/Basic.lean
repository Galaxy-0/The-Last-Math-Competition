import Mathlib

/-!
# Conjecture 00000009523 is false

The conjecture claims (main clause): except for the completely depolarizing constant channel,
every quantum channel `φ` satisfies `C_E(φ) > χ(φ)` strictly, where `C_E` is the
entanglement-assisted classical capacity (Bennett-Shor-Smolin-Thapliyal formula
`C_E(φ) = max_ρ I(ρ, φ)`, `I(ρ, φ) = S(ρ) + S(φ ρ) - S((id ⊗ φ)(|ψ⟩⟨ψ|))`, `ψ` a purification
of `ρ`) and `χ` is the Holevo capacity.

Counterexample: the completely dephasing qubit channel `deph ρ = diag(ρ₀₀, ρ₁₁)`.  It is CPTP,
non-constant on states (so it is not the completely depolarizing channel), and
`C_E(deph) = χ(deph) = log 2`.

Conventions: natural logarithm; `Real.negMulLog x = -x log x` with `negMulLog 0 = 0`;
the reference system of a purification of a state on `ℂ^d` is `ℂ^d` (first tensor factor).
-/

open Matrix Polynomial Real
open scoped ComplexOrder

namespace C9523

/-! ## Quantum-information objects -/

/-- A density matrix (quantum state): positive semidefinite with trace one. -/
def IsState {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- von Neumann entropy `S(A) = -∑ λ log λ` over the eigenvalues `λ` (with multiplicity) of a
Hermitian matrix `A`, natural logarithm. (Junk value `0` for non-Hermitian matrices; for a
channel, every matrix whose entropy enters `CE` or `chi` is positive semidefinite, hence
Hermitian.) -/
noncomputable def vnEntropy {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  if h : A.IsHermitian then ∑ i, negMulLog (h.eigenvalues i) else 0

/-- The rank-one projector `|ψ⟩⟨ψ|`. -/
def proj {m : Type*} (ψ : m → ℂ) : Matrix m m ℂ := vecMulVec ψ (star ψ)

/-- Partial trace over the first (reference) tensor factor of `ℂ^k ⊗ ℂ^n`. -/
def ptraceRef {k n : Type*} [Fintype k] (M : Matrix (k × n) (k × n) ℂ) : Matrix n n ℂ :=
  fun a b => ∑ r, M (r, a) (r, b)

/-- `(id_k ⊗ Φ)(X)`: `Φ` applied to every `n × n` block `X_{r r'}` of `X`. -/
def idTensor {k n m : Type*} (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (X : Matrix (k × n) (k × n) ℂ) : Matrix (k × m) (k × m) ℂ :=
  fun p q => Φ (Matrix.of fun a b => X (p.1, a) (q.1, b)) p.2 q.2

/-- A quantum channel: a completely positive, trace-preserving linear map. -/
def IsChannel {n m : Type*} [Fintype n] [Fintype m] (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    Prop :=
  (∀ (k : ℕ) (X : Matrix (Fin k × n) (Fin k × n) ℂ), X.PosSemidef → (idTensor Φ X).PosSemidef) ∧
    ∀ X, (Φ X).trace = X.trace

/-- Quantum mutual information `I(ρ, Φ) = S(ρ) + S(Φ ρ) - S((id ⊗ Φ)(|ψ⟩⟨ψ|))`, computed with the
purification `ψ ∈ ℂ^d ⊗ ℂ^d` of `ρ`. -/
noncomputable def mutualInfo {d d' : ℕ} (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d × Fin d → ℂ) : ℝ :=
  vnEntropy ρ + vnEntropy (Φ ρ) - vnEntropy (idTensor Φ (proj ψ))

/-- The set of values `I(ρ, Φ)` over all states `ρ` and all purifications `ψ` of `ρ`. -/
def mutualInfoSet {d d' : ℕ} (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    Set ℝ :=
  {x | ∃ ρ ψ, IsState ρ ∧ ptraceRef (proj ψ) = ρ ∧ x = mutualInfo Φ ρ ψ}

/-- Entanglement-assisted classical capacity (BSST formula): `C_E(Φ) = sup_ρ I(ρ, Φ)`. -/
noncomputable def CE {d d' : ℕ} (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    ℝ :=
  sSup (mutualInfoSet Φ)

/-- Holevo quantity of the ensemble `{p_i, ρ_i}`: `S(∑ p_i Φ ρ_i) - ∑ p_i S(Φ ρ_i)`. -/
noncomputable def holevoQ {d d' : ℕ} (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    {m : ℕ} (p : Fin m → ℝ) (ρs : Fin m → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  vnEntropy (∑ i, (p i : ℂ) • Φ (ρs i)) - ∑ i, p i * vnEntropy (Φ (ρs i))

/-- Holevo quantities of all finite ensembles of states. -/
def holevoSet {d d' : ℕ} (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    Set ℝ :=
  {x | ∃ (m : ℕ) (p : Fin m → ℝ) (ρs : Fin m → Matrix (Fin d) (Fin d) ℂ),
    (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i, IsState (ρs i)) ∧ x = holevoQ Φ p ρs}

/-- Holevo capacity `χ(Φ)`: supremum of the Holevo quantity over finite ensembles. -/
noncomputable def chi {d d' : ℕ} (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    ℝ :=
  sSup (holevoSet Φ)

/-- The completely depolarizing channel `X ↦ tr(X) · I/d`. -/
noncomputable def depol (d : ℕ) : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := (X.trace / d) • (1 : Matrix (Fin d) (Fin d) ℂ)
  map_add' X Y := by simp [trace_add, add_div, add_smul]
  map_smul' c X := by simp [trace_smul, mul_div_assoc, smul_smul]

/-- The completely dephasing qubit channel `X ↦ diag(X₀₀, X₁₁)`. -/
def deph : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := diagonal fun a => X a a
  map_add' X Y := by ext i j; by_cases h : i = j <;> simp [h]
  map_smul' c X := by ext i j; by_cases h : i = j <;> simp [h]

lemma deph_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : deph X = diagonal fun a => X a a := rfl

/-! ## Entropy computations -/

/-- If the characteristic polynomial of a Hermitian `A` is `∏ (X - w i)`, then
`S(A) = ∑ negMulLog (w i)`. -/
lemma vnEntropy_of_charpoly {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (w : n → ℝ) (hc : A.charpoly = ∏ i, (X - C ((w i : ℝ) : ℂ))) :
    vnEntropy A = ∑ i, negMulLog (w i) := by
  have h1 := hA.roots_charpoly_eq_eigenvalues
  rw [hc, Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero])] at h1
  have h2 := congrArg (fun s : Multiset ℂ => (s.map (fun z => negMulLog z.re)).sum) h1
  simp only [Multiset.map_map, Function.comp_def, Finset.sum_map_val, roots_X_sub_C,
    Multiset.bind_singleton, Complex.ofReal_re] at h2
  rw [vnEntropy, dif_pos hA, h2]
  simp

lemma isHermitian_diagonal_ofReal {n : Type*} [DecidableEq n] (w : n → ℝ) :
    (diagonal fun a => (w a : ℂ)).IsHermitian := by
  simp [IsHermitian, diagonal_conjTranspose, Pi.star_def]

lemma vnEntropy_diagonal {n : Type*} [Fintype n] [DecidableEq n] (w : n → ℝ) :
    vnEntropy (diagonal fun a => (w a : ℂ)) = ∑ a, negMulLog (w a) :=
  vnEntropy_of_charpoly (isHermitian_diagonal_ofReal w) w (charpoly_diagonal _)

lemma isState_diagonal {n : Type*} [Fintype n] [DecidableEq n] (w : n → ℝ) (h0 : ∀ a, 0 ≤ w a)
    (h1 : ∑ a, w a = 1) : IsState (diagonal fun a => (w a : ℂ)) := by
  refine ⟨posSemidef_diagonal_iff.2 fun a => by exact_mod_cast h0 a, ?_⟩
  rw [trace_diagonal]; exact_mod_cast h1

lemma negMulLog_two_le (w : Fin 2 → ℝ) (h : w 0 + w 1 = 1) : ∑ a, negMulLog (w a) ≤ log 2 := by
  rw [Fin.sum_univ_two, show w 1 = 1 - w 0 by linarith,
    ← binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  exact binEntropy_le_log_two

/-- Every qubit state has entropy at most `log 2`. -/
lemma vnEntropy_le_log_two {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hρ : IsState ρ) :
    vnEntropy ρ ≤ log 2 := by
  obtain ⟨hpsd, htr⟩ := hρ
  rw [vnEntropy, dif_pos hpsd.1]
  have ht := hpsd.1.trace_eq_sum_eigenvalues
  rw [htr, Fin.sum_univ_two] at ht
  exact negMulLog_two_le _ (by simpa using (congrArg Complex.re ht).symm)

/-- Diagonal weights of a state. -/
noncomputable def dg {n : Type*} (σ : Matrix n n ℂ) (a : n) : ℝ := (σ a a).re

lemma dg_spec {n : Type*} [Fintype n] {σ : Matrix n n ℂ} (hσ : IsState σ) :
    (∀ a, σ a a = (dg σ a : ℂ)) ∧ (∀ a, 0 ≤ dg σ a) ∧ ∑ a, dg σ a = 1 := by
  have hn : ∀ a, 0 ≤ σ a a := fun a => hσ.1.diag_nonneg
  refine ⟨fun a => Complex.ext (by simp [dg]) (by simp [(Complex.nonneg_iff.1 (hn a)).2]),
    fun a => (Complex.nonneg_iff.1 (hn a)).1, ?_⟩
  have := congrArg Complex.re hσ.2
  simpa [trace, dg] using this

lemma deph_state {σ : Matrix (Fin 2) (Fin 2) ℂ} (hσ : IsState σ) :
    deph σ = diagonal fun a => (dg σ a : ℂ) := by
  rw [deph_apply]; congr 1; funext a; exact (dg_spec hσ).1 a

/-! ## `deph` is a channel -/

lemma idTensor_deph_eq {k : ℕ} (X : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℂ) :
    idTensor deph X = ∑ a : Fin 2,
      (diagonal fun p : Fin k × Fin 2 => if p.2 = a then (1 : ℂ) else 0)ᴴ * X *
        diagonal fun p : Fin k × Fin 2 => if p.2 = a then (1 : ℂ) else 0 := by
  ext ⟨r, a⟩ ⟨r', a'⟩
  simp only [idTensor, deph_apply, of_apply, Matrix.sum_apply, diagonal_conjTranspose,
    diagonal_mul, mul_diagonal, diagonal_apply, Pi.star_apply]
  fin_cases a <;> fin_cases a' <;> simp

theorem deph_isChannel : IsChannel deph := by
  refine ⟨fun k X hX => ?_, fun X => by simp [deph_apply, trace, Fin.sum_univ_two]⟩
  rw [idTensor_deph_eq]
  exact posSemidef_sum _ fun a _ => hX.conjTranspose_mul_mul_same _

/-- `deph` is not constant on states: it fixes `|0⟩⟨0|` and `|1⟩⟨1|`. -/
theorem deph_nonconstant : ∃ ρ σ, IsState ρ ∧ IsState σ ∧ deph ρ ≠ deph σ := by
  refine ⟨diagonal fun a => ((if a = 0 then 1 else 0 : ℝ) : ℂ),
    diagonal fun a => ((if a = 1 then 1 else 0 : ℝ) : ℂ),
    isState_diagonal _ (fun a => by split_ifs <;> norm_num) (by simp),
    isState_diagonal _ (fun a => by split_ifs <;> norm_num) (by simp), fun h => ?_⟩
  have := congrFun (congrFun h 0) 0
  simp [deph_apply] at this

lemma depol_state {d : ℕ} {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsState ρ) :
    depol d ρ = ((1 : ℂ) / d) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simp [depol, hρ.2]

theorem deph_ne_depol : deph ≠ depol 2 := by
  intro h
  obtain ⟨ρ, σ, hρ, hσ, hne⟩ := deph_nonconstant
  exact hne (by rw [h, depol_state hρ, depol_state hσ])

/-! ## `C_E(deph) = log 2` -/

/-- Block weights `τ_a = ∑_r |ψ(r,a)|²` (the diagonal of the reduced state). -/
noncomputable def tau (ψ : Fin 2 × Fin 2 → ℂ) (a : Fin 2) : ℝ := ∑ r, Complex.normSq (ψ (r, a))

lemma deph_ptrace (ψ : Fin 2 × Fin 2 → ℂ) :
    deph (ptraceRef (proj ψ)) = diagonal fun a => (tau ψ a : ℂ) := by
  rw [deph_apply]; congr 1; funext a
  simp [ptraceRef, proj, vecMulVec_apply, tau, Complex.mul_conj]

/-- `(id ⊗ deph)(|ψ⟩⟨ψ|)` is block diagonal with the rank-one blocks `|ψ(·,a)⟩⟨ψ(·,a)|`. -/
lemma idTensor_deph_proj (ψ : Fin 2 × Fin 2 → ℂ) :
    idTensor deph (proj ψ) = blockDiagonal fun a => proj fun r => ψ (r, a) := by
  ext ⟨r, a⟩ ⟨r', a'⟩
  simp only [idTensor, deph_apply, of_apply, blockDiagonal_apply, diagonal_apply, proj,
    vecMulVec_apply, Pi.star_apply]

lemma charpoly_blockDiagonal {m o : Type*} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] (M : o → Matrix m m ℂ) :
    (blockDiagonal M).charpoly = ∏ a, (M a).charpoly := by
  have : charmatrix (blockDiagonal M) = blockDiagonal fun a => charmatrix (M a) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    by_cases hk : k = k' <;> by_cases hi : i = j <;>
      simp [blockDiagonal_apply, hk, hi]
  simp only [charpoly, this, det_blockDiagonal]

lemma charpoly_proj_two (v : Fin 2 → ℂ) :
    (proj v).charpoly = X * (X - C ((∑ r, Complex.normSq (v r) : ℝ) : ℂ)) := by
  have hd : (proj v).det = 0 := by
    simp [det_fin_two, proj, vecMulVec_apply]; ring
  have ht : (proj v).trace = ((∑ r, Complex.normSq (v r) : ℝ) : ℂ) := by
    simp [trace, proj, vecMulVec_apply, Complex.mul_conj, Fin.sum_univ_two]
  rw [charpoly_fin_two, hd, ht, C_0]; ring

lemma vnEntropy_omega (ψ : Fin 2 × Fin 2 → ℂ) :
    vnEntropy (idTensor deph (proj ψ)) = ∑ a, negMulLog (tau ψ a) := by
  have hH : (idTensor deph (proj ψ)).IsHermitian := by
    rw [idTensor_deph_proj, IsHermitian, blockDiagonal_conjTranspose]
    congr 1; funext a; simp [proj, conjTranspose_vecMulVec]
  rw [vnEntropy_of_charpoly hH (fun p => if p.1 = 0 then tau ψ p.2 else 0)]
  · simp [Fintype.sum_prod_type, Fin.sum_univ_two]
  · rw [idTensor_deph_proj, charpoly_blockDiagonal]
    simp only [charpoly_proj_two, Fintype.prod_prod_type, Fin.prod_univ_two, tau]
    simp; ring

/-- The key identity: for the dephasing channel, `I(ρ, deph) = S(ρ)`. -/
lemma mutualInfo_deph (ψ : Fin 2 × Fin 2 → ℂ) :
    mutualInfo deph (ptraceRef (proj ψ)) ψ = vnEntropy (ptraceRef (proj ψ)) := by
  rw [mutualInfo, deph_ptrace, vnEntropy_diagonal, vnEntropy_omega]; ring

/-- The maximally entangled vector `(|00⟩ + |11⟩)/√2`. -/
noncomputable def bell : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then ((√(1 / 2) : ℝ) : ℂ) else 0

lemma ptrace_bell : ptraceRef (proj bell) = diagonal fun _ => ((1 / 2 : ℝ) : ℂ) := by
  have h2 : ((√2 : ℂ))⁻¹ * ((√2 : ℂ))⁻¹ = 2⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  ext a b
  fin_cases a <;> fin_cases b <;> simp [ptraceRef, proj, vecMulVec_apply, bell, h2]

theorem CE_deph : IsGreatest (mutualInfoSet deph) (log 2) ∧ CE deph = log 2 := by
  have hG : IsGreatest (mutualInfoSet deph) (log 2) := by
    refine ⟨⟨_, bell, ?_, rfl, ?_⟩, ?_⟩
    · rw [ptrace_bell]; exact isState_diagonal _ (fun _ => by norm_num) (by norm_num)
    · rw [mutualInfo_deph, ptrace_bell, vnEntropy_diagonal, Fin.sum_univ_two, negMulLog,
        one_div, Real.log_inv]; ring
    · rintro x ⟨ρ, ψ, hρ, hψ, rfl⟩
      subst hψ
      rw [mutualInfo_deph]; exact vnEntropy_le_log_two hρ
  exact ⟨hG, hG.csSup_eq⟩

/-! ## `χ(deph) = log 2` -/

lemma holevoQ_deph {m : ℕ} (p : Fin m → ℝ) (ρs : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (hρs : ∀ i, IsState (ρs i)) :
    holevoQ deph p ρs = ∑ a, negMulLog (∑ i, p i * dg (ρs i) a) -
      ∑ i, p i * ∑ a, negMulLog (dg (ρs i) a) := by
  have hsum : ∑ i, (p i : ℂ) • deph (ρs i) =
      diagonal fun a => ((∑ i, p i * dg (ρs i) a : ℝ) : ℂ) := by
    simp_rw [deph_state (hρs _)]
    ext a b; by_cases h : a = b <;> simp [Matrix.sum_apply, h]
  rw [holevoQ, hsum, vnEntropy_diagonal]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [deph_state (hρs i), vnEntropy_diagonal]

lemma holevoQ_deph_le {m : ℕ} (p : Fin m → ℝ) (ρs : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (hρs : ∀ i, IsState (ρs i)) :
    holevoQ deph p ρs ≤ log 2 := by
  rw [holevoQ_deph p ρs hρs]
  have h1 : ∑ a, negMulLog (∑ i, p i * dg (ρs i) a) ≤ log 2 := by
    apply negMulLog_two_le
    rw [← Finset.sum_add_distrib]
    simp_rw [← mul_add]
    have : ∀ i, dg (ρs i) 0 + dg (ρs i) 1 = 1 := fun i => by
      simpa [Fin.sum_univ_two] using (dg_spec (hρs i)).2.2
    simp [this, hp1]
  have h2 : 0 ≤ ∑ i, p i * ∑ a, negMulLog (dg (ρs i) a) := by
    refine Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (Finset.sum_nonneg fun a _ => ?_)
    obtain ⟨-, h0, h1⟩ := dg_spec (hρs i)
    refine negMulLog_nonneg (h0 a) ?_
    rw [← h1]; exact Finset.single_le_sum (fun b _ => h0 b) (Finset.mem_univ a)
  linarith

theorem chi_deph : IsGreatest (holevoSet deph) (log 2) ∧ chi deph = log 2 := by
  have hG : IsGreatest (holevoSet deph) (log 2) := by
    let ρs : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
      fun i => diagonal fun a => ((if a = i then 1 else 0 : ℝ) : ℂ)
    have hρs : ∀ i, IsState (ρs i) := fun i =>
      isState_diagonal _ (fun a => by split_ifs <;> norm_num) (by simp)
    refine ⟨⟨2, fun _ => 1 / 2, ρs, fun _ => by norm_num, by norm_num, hρs, ?_⟩, ?_⟩
    · rw [holevoQ_deph _ _ hρs]
      simp [ρs, dg, negMulLog, Real.log_inv]
    · rintro x ⟨m, p, ρs, hp, hp1, hρs, rfl⟩
      exact holevoQ_deph_le p ρs hp hp1 hρs
  exact ⟨hG, hG.csSup_eq⟩

/-! ## Main results -/

/-- The dephasing qubit channel is a channel, differs from the completely depolarizing channel,
is non-constant on states, has `χ > 0`, and has `C_E = χ = log 2`. -/
theorem deph_counterexample :
    IsChannel deph ∧ deph ≠ depol 2 ∧ (∃ ρ σ, IsState ρ ∧ IsState σ ∧ deph ρ ≠ deph σ) ∧
      0 < chi deph ∧ CE deph = chi deph ∧ chi deph = log 2 := by
  refine ⟨deph_isChannel, deph_ne_depol, deph_nonconstant, ?_, ?_, chi_deph.2⟩
  · rw [chi_deph.2]; exact Real.log_pos (by norm_num)
  · rw [CE_deph.2, chi_deph.2]

/-- The main clause of conjecture 00000009523 is false (literal reading: the only excepted
channel is the completely depolarizing one). -/
theorem conjecture9523_false :
    ¬ ∀ Φ : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ,
      IsChannel Φ → Φ ≠ depol 2 → chi Φ < CE Φ := by
  intro h
  obtain ⟨hc, hne, -, -, heq, -⟩ := deph_counterexample
  exact (h deph hc hne).ne' heq

/-- Also false when every channel that is constant on states is excepted, and only channels
with positive Holevo capacity are considered. -/
theorem conjecture9523_false_strong :
    ¬ ∀ Φ : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ,
      IsChannel Φ → (∃ ρ σ, IsState ρ ∧ IsState σ ∧ Φ ρ ≠ Φ σ) → 0 < chi Φ → chi Φ < CE Φ := by
  intro h
  obtain ⟨hc, -, hnc, hpos, heq, -⟩ := deph_counterexample
  exact (h deph hc hnc hpos).ne' heq

end C9523
