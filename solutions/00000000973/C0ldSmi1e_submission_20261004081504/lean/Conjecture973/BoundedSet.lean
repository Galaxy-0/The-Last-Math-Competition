import Conjecture973.Jordan

/-! The stated spectral-set property fails in dimension two for every nonempty bounded set. -/

noncomputable section
open Matrix Polynomial Set

namespace Conjecture973

/-- The definition in the conjecture, with the canonical Euclidean operator norm and
the real supremum of all polynomial values on the given set. -/
def SpectralSetOrder (K : Set ℂ) (n : ℕ) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℂ, spectrum ℂ A ⊆ K → ∀ p : ℂ[X],
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (Polynomial.aeval A p)‖ ≤
      sSup ((fun z : ℂ => ‖p.eval z‖) '' K)

/-- A Jordan matrix gives a strict counterexample for any nonempty bounded set.
The spectrum is genuinely contained in the set and the right-hand side is its actual supremum. -/
theorem boundedSet_spectral_counterexample (K : Set ℂ) (hne : K.Nonempty)
    (hb : ∃ B : ℝ, ∀ z ∈ K, ‖z‖ ≤ B) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (p : ℂ[X]),
      spectrum ℂ A ⊆ K ∧
        sSup ((fun z : ℂ => ‖p.eval z‖) '' K) <
          ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (Polynomial.aeval A p)‖ := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨B, hB⟩ := hb
  let r : ℝ := |B| + ‖c‖ + 1
  refine ⟨jordan c r, shiftedPolynomial c, ?_, ?_⟩
  · rw [jordan_spectrum]
    exact singleton_subset_iff.mpr hc
  · have hupper : ∀ u ∈ ((fun z : ℂ => ‖(shiftedPolynomial c).eval z‖) '' K),
        u ≤ |B| + ‖c‖ := by
      rintro u ⟨z, hz, rfl⟩
      simp only [shiftedPolynomial, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      calc
        ‖z - c‖ ≤ ‖z‖ + ‖c‖ := norm_sub_le z c
        _ ≤ B + ‖c‖ := add_le_add_right (hB z hz) _
        _ ≤ |B| + ‖c‖ := add_le_add_right (le_abs_self B) _
    have hsup : sSup ((fun z : ℂ => ‖(shiftedPolynomial c).eval z‖) '' K) ≤
        |B| + ‖c‖ :=
      csSup_le ⟨_, ⟨c, hc, rfl⟩⟩ hupper
    rw [jordan_shifted_operatorNorm, abs_of_nonneg (show 0 ≤ r by dsimp [r]; positivity)]
    exact hsup.trans_lt (lt_add_one _)

theorem boundedSet_not_spectralSetOrder_two (K : Set ℂ) (hne : K.Nonempty)
    (hb : ∃ B : ℝ, ∀ z ∈ K, ‖z‖ ≤ B) : ¬ SpectralSetOrder K 2 := by
  intro h
  obtain ⟨A, p, hspectrum, hstrict⟩ := boundedSet_spectral_counterexample K hne hb
  exact (not_le_of_gt hstrict) (h A hspectrum p)

end Conjecture973
