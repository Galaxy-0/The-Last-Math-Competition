import Conjecture978.Pencil
import Mathlib.RingTheory.Nullstellensatz

noncomputable section

namespace Conjecture978

/-- The common zero locus of every polynomial vanishing on a set. -/
def algebraicClosure {k : Type*} [Field k] {σ : Type*}
    (S : Set (σ → k)) : Set (σ → k) :=
  MvPolynomial.zeroLocus (MvPolynomial.vanishingIdeal S)

theorem subset_algebraicClosure {k : Type*} [Field k] {σ : Type*}
    (S : Set (σ → k)) : S ⊆ algebraicClosure S :=
  MvPolynomial.zeroLocus_vanishingIdeal_le S

theorem algebraicClosure_mono {k : Type*} [Field k] {σ : Type*}
    {S T : Set (σ → k)} (h : S ⊆ T) : algebraicClosure S ⊆ algebraicClosure T :=
  MvPolynomial.zeroLocus_anti_mono (MvPolynomial.vanishingIdeal_anti_mono h)

/-- Every genuine polynomial zero locus is fixed by algebraic closure. -/
theorem algebraicClosure_zeroLocus {k : Type*} [Field k] {σ : Type*}
    (I : Ideal (MvPolynomial σ k)) :
    algebraicClosure (MvPolynomial.zeroLocus I) = MvPolynomial.zeroLocus I := by
  apply Set.Subset.antisymm
  · exact MvPolynomial.zeroLocus_anti_mono (MvPolynomial.le_vanishingIdeal_zeroLocus I)
  · exact subset_algebraicClosure _

/-- Nonzero scalar representatives of tangent-line coordinates at smooth projective zeros. -/
def scaledGradientImage (p : MvPolynomial (Fin 3) ℂ) : Set (Fin 3 → ℂ) :=
  {r | ∃ q : Fin 3 → ℂ, q ≠ 0 ∧ MvPolynomial.eval q p = 0 ∧
    gradient p q ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ r = c • gradient p q}

theorem scaledGradientImage_ne_zero {p : MvPolynomial (Fin 3) ℂ}
    {r : Fin 3 → ℂ} (hr : r ∈ scaledGradientImage p) : r ≠ 0 := by
  rcases hr with ⟨q, _, _, hgrad, c, hc, rfl⟩
  exact smul_ne_zero hc hgrad

/-- The construction includes every nonzero representative of each tangent line. -/
theorem scaledGradientImage_smul {p : MvPolynomial (Fin 3) ℂ}
    {r : Fin 3 → ℂ} (hr : r ∈ scaledGradientImage p) {c : ℂ} (hc : c ≠ 0) :
    c • r ∈ scaledGradientImage p := by
  rcases hr with ⟨q, hqne, hq, hgrad, d, hd, rfl⟩
  refine ⟨q, hqne, hq, hgrad, c * d, mul_ne_zero hc hd, ?_⟩
  rw [mul_smul]

/-- The affine cone representing the algebraic closure of the projective dual.
For a smooth homogeneous determinant curve this is its ordinary dual construction. -/
def dualCone (p : MvPolynomial (Fin 3) ℂ) : Set (Fin 3 → ℂ) :=
  algebraicClosure (scaledGradientImage p)

/-- The affine chart with final homogeneous coordinate one. -/
def complexAffinePoint (z : Fin 2 → ℂ) : Fin 3 → ℂ := ![z 0, z 1, 1]

def complexAffinePoints (p : MvPolynomial (Fin 3) ℂ) : Set (Fin 2 → ℂ) :=
  {z | complexAffinePoint z ∈ dualCone p}

def realAffinePoints (p : MvPolynomial (Fin 3) ℂ) : Set (Fin 2 → ℝ) :=
  {x | (fun i => (x i : ℂ)) ∈ complexAffinePoints p}

/-- The computed determinant polynomial vanishes on every actual scaled gradient. -/
theorem pencil_vanishes_on_scaledGradientImage :
    pencilPolynomial witness ∈
      MvPolynomial.vanishingIdeal (scaledGradientImage (pencilPolynomial witness)) := by
  intro r hr
  rcases hr with ⟨q, _, hq, _, c, _, rfl⟩
  rw [pencilPolynomial_witness] at hq ⊢
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X] at hq ⊢
  rw [← pencilPolynomial_witness, gradient_witness]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  calc
    (c * (2 * q 2)) ^ 2 - (c * (-2 * q 0)) ^ 2 - (c * (-2 * q 1)) ^ 2 =
        4 * c ^ 2 * ((q 2) ^ 2 - (q 0) ^ 2 - (q 1) ^ 2) := by ring
    _ = 0 := by rw [hq]; ring

/-- Algebraic closure cannot leave the actual conic equation. -/
theorem dualCone_witness_equation {r : Fin 3 → ℂ}
    (hr : r ∈ dualCone (pencilPolynomial witness)) :
    (r 2) ^ 2 - (r 0) ^ 2 - (r 1) ^ 2 = 0 := by
  have h := hr (pencilPolynomial witness) pencil_vanishes_on_scaledGradientImage
  simpa [pencilPolynomial_witness] using h

/-- Every affine point of the conic is itself a smooth tangent-line coordinate. -/
theorem affine_conic_mem_scaledGradientImage (z : Fin 2 → ℂ)
    (hz : (z 0) ^ 2 + (z 1) ^ 2 = 1) :
    complexAffinePoint z ∈ scaledGradientImage (pencilPolynomial witness) := by
  let q : Fin 3 → ℂ := ![-z 0, -z 1, 1]
  have hqne : q ≠ 0 := by
    intro h
    have htwo := congrFun h 2
    exact one_ne_zero (show (1 : ℂ) = 0 from htwo)
  have hq : MvPolynomial.eval q (pencilPolynomial witness) = 0 := by
    simp only [pencilPolynomial_witness, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
      MvPolynomial.eval_X]
    dsimp [q]
    linear_combination -hz
  refine ⟨q, hqne, hq, pencilPolynomial_witness_smooth q hqne hq,
    (1 / 2 : ℂ), by norm_num, ?_⟩
  rw [gradient_witness]
  ext i
  fin_cases i <;> dsimp [complexAffinePoint, q] <;> ring

/-- The actual projective dual, in its complex affine chart, is exactly this conic. -/
theorem complexAffinePoints_witness_eq :
    complexAffinePoints (pencilPolynomial witness) =
      {z : Fin 2 → ℂ | (z 0) ^ 2 + (z 1) ^ 2 = 1} := by
  ext z
  constructor
  · intro hz
    have h := dualCone_witness_equation hz
    change (1 : ℂ) ^ 2 - (z 0) ^ 2 - (z 1) ^ 2 = 0 at h
    change (z 0) ^ 2 + (z 1) ^ 2 = 1
    linear_combination -h
  · intro hz
    exact subset_algebraicClosure _ (affine_conic_mem_scaledGradientImage z hz)

/-- Its real points are the genuine unit circle, not a separately assigned curve. -/
theorem realAffinePoints_witness_eq :
    realAffinePoints (pencilPolynomial witness) =
      {x : Fin 2 → ℝ | (x 0) ^ 2 + (x 1) ^ 2 = 1} := by
  ext x
  change (fun i => (x i : ℂ)) ∈ complexAffinePoints (pencilPolynomial witness) ↔ _
  rw [complexAffinePoints_witness_eq]
  simp only [Set.mem_setOf_eq]
  norm_cast

end Conjecture978
