import Mathlib

/-!
# Conjecture 00000000489 is false

The conjecture: for the third-order character sum `S₃(n) = ∑_{λ ⊢ n} f_λ³ / n!`, where `f_λ` is
the dimension of the irreducible complex representation of the symmetric group `S_n` labelled by
the partition `λ`, one has `S₃(n) = Θ(√(n!) · n^{1/4})`, with main-term constant `2^{1/4} π^{-1/2}`.

We prove `S₃(n) ≤ √(n!)` for every `n`, so `S₃(n) / (√(n!) · n^{1/4}) ≤ n^{-1/4} → 0`.

The statement is proved for *every* family `λ ↦ V_λ`, indexed by the partitions of `n`, of
pairwise non-isomorphic simple objects of `FDRep ℂ (Equiv.Perm (Fin n))`; the Specht modules
form such a family, so the bound applies to the conjecture's `f_λ`.

Key steps:
* `trace_inv_eq_star`: for a finite group, `χ(g⁻¹) = conj χ(g)`, via an invariant positive
  definite matrix `P = ∑_h A_hᴴ A_h`.
* `sum_sq_finrank_le`: `∑ (dim V_i)² ≤ |G|` for pairwise non-isomorphic simple `V_i`
  (orthonormality of characters, `FDRep.char_orthonormal`, plus positivity of
  `∑_g |Φ(g)|²` for `Φ = ∑ dim V_i · χ_i`).
-/

open scoped ComplexOrder Matrix
open Filter Topology Asymptotics CategoryTheory Module

namespace C489

section Characters

variable {G : Type} [Group G] [Fintype G]

/-- For a matrix representation `A` of a finite group, `tr A(g⁻¹) = conj (tr A(g))`. -/
theorem trace_inv_eq_star {d : ℕ} (A : G → Matrix (Fin d) (Fin d) ℂ)
    (hmul : ∀ g h, A (g * h) = A g * A h) (hone : A 1 = 1) (g : G) :
    Matrix.trace (A g⁻¹) = star (Matrix.trace (A g)) := by
  classical
  set P : Matrix (Fin d) (Fin d) ℂ := ∑ h, (A h)ᴴ * A h with hP
  have hPdef : P.PosDef := by
    have hsplit : P = (A 1)ᴴ * A 1 + ∑ h ∈ Finset.univ.erase 1, (A h)ᴴ * A h := by
      rw [hP]
      exact (Finset.add_sum_erase Finset.univ (fun h => (A h)ᴴ * A h)
        (Finset.mem_univ (1 : G))).symm
    rw [hsplit, hone, Matrix.conjTranspose_one, Matrix.one_mul]
    exact Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_sum _ fun h _ => Matrix.posSemidef_conjTranspose_mul_self (A h))
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).mp hPdef.isUnit
  have hinv : (A g)ᴴ * P * A g = P := by
    rw [hP, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => ?_)
    simp only [Equiv.coe_mulRight, hmul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hgg : A g * A g⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
  have h2 : (A g)ᴴ * P = P * A g⁻¹ := by
    calc (A g)ᴴ * P = (A g)ᴴ * P * (A g * A g⁻¹) := by rw [hgg, Matrix.mul_one]
      _ = ((A g)ᴴ * P * A g) * A g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * A g⁻¹ := by rw [hinv]
  have h3 : (A g)ᴴ = P * A g⁻¹ * P⁻¹ := by
    rw [← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]
  rw [← Matrix.trace_conjTranspose, h3, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hPu,
    Matrix.one_mul]

/-- Characters of complex representations of a finite group satisfy `χ(g⁻¹) = conj χ(g)`. -/
theorem char_inv (V : FDRep ℂ G) (g : G) : V.character g⁻¹ = star (V.character g) := by
  let b := Module.finBasis ℂ V
  let A : G → Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ :=
    fun g => LinearMap.toMatrix b b (V.ρ g)
  have hA : ∀ g, V.character g = Matrix.trace (A g) :=
    fun g => LinearMap.trace_eq_matrix_trace ℂ b _
  rw [hA, hA]
  apply trace_inv_eq_star
  · intro g h
    simp only [A, map_mul, LinearMap.toMatrix_mul]
  · simp [A]

/-- Bessel-type bound: for pairwise non-isomorphic simple complex representations `V_i` of a
finite group `G`, `∑ (dim V_i)² ≤ |G|`. -/
theorem sum_sq_finrank_le {ι : Type*} [Fintype ι] (V : ι → FDRep ℂ G) [∀ i, Simple (V i)]
    (hV : ∀ i j, Nonempty (V i ≅ V j) → i = j) :
    ∑ i, finrank ℂ (V i) ^ 2 ≤ Fintype.card G := by
  classical
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc)
  set D : ℕ := ∑ i, finrank ℂ (V i) ^ 2 with hD
  let Φ : G → ℂ := fun g => ∑ i, (finrank ℂ (V i) : ℂ) * (V i).character g
  have horth : ∀ i j, ∑ g, (V i).character g * (V j).character g⁻¹ =
      if i = j then (Fintype.card G : ℂ) else 0 := by
    intro i j
    have h := FDRep.char_orthonormal (V i) (V j)
    have hiff : Nonempty (V i ≅ V j) ↔ i = j := ⟨hV i j, fun h => h ▸ ⟨Iso.refl _⟩⟩
    rw [Nat.card_eq_fintype_card] at h
    by_cases hij : i = j
    · rw [if_pos (hiff.mpr hij)] at h
      rw [if_pos hij]
      exact ((inv_mul_eq_one₀ (by exact_mod_cast hc)).mp h).symm
    · rw [if_neg (fun h' => hij (hiff.mp h'))] at h
      rw [if_neg hij]
      simpa [hc] using h
  have hΦinv : ∀ g, Φ g⁻¹ = star (Φ g) := by
    intro g
    simp [Φ, char_inv, star_sum]
  have hsum : ∑ g, Φ g * Φ g⁻¹ = (Fintype.card G : ℂ) * D := by
    have hexp : ∀ g, Φ g * Φ g⁻¹ = ∑ i, ∑ j, ((finrank ℂ (V i) : ℂ) * finrank ℂ (V j)) *
        ((V i).character g * (V j).character g⁻¹) := by
      intro g
      simp only [Φ, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset G)), ← Finset.mul_sum, horth]
    simp [hD, Finset.mul_sum, sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hnorm : ∀ g, Φ g * Φ g⁻¹ = (Complex.normSq (Φ g) : ℂ) := by
    intro g
    rw [hΦinv, ← Complex.mul_conj]
    rfl
  have hreal : (∑ g, Complex.normSq (Φ g) : ℝ) = Fintype.card G * D := by
    have h := hsum
    simp_rw [hnorm] at h
    exact_mod_cast h
  have hΦ1 : Φ 1 = ((D : ℝ) : ℂ) := by
    simp [Φ, hD, sq]
  have hle : Complex.normSq (Φ 1) ≤ ∑ g, Complex.normSq (Φ g) :=
    Finset.single_le_sum (f := fun g => Complex.normSq (Φ g))
      (fun g _ => Complex.normSq_nonneg _) (Finset.mem_univ 1)
  rw [hΦ1, hreal, Complex.normSq_ofReal] at hle
  rcases Nat.eq_zero_or_pos D with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hDpos : (0 : ℝ) < D := by exact_mod_cast hpos
    have : (D : ℝ) ≤ Fintype.card G := le_of_mul_le_mul_right hle hDpos
    exact_mod_cast this

/-- Consequently `∑ (dim V_i)³ ≤ √|G| · |G|`. -/
theorem sum_cube_le {ι : Type*} [Fintype ι] (V : ι → FDRep ℂ G) [∀ i, Simple (V i)]
    (hV : ∀ i j, Nonempty (V i ≅ V j) → i = j) :
    ∑ i, (finrank ℂ (V i) : ℝ) ^ 3 ≤ Real.sqrt (Fintype.card G) * Fintype.card G := by
  have hDr : ∑ i, (finrank ℂ (V i) : ℝ) ^ 2 ≤ Fintype.card G := by
    exact_mod_cast sum_sq_finrank_le V hV
  have hfi : ∀ i, (finrank ℂ (V i) : ℝ) ≤ Real.sqrt (Fintype.card G) := by
    intro i
    apply Real.le_sqrt_of_sq_le
    calc (finrank ℂ (V i) : ℝ) ^ 2 ≤ ∑ j, (finrank ℂ (V j) : ℝ) ^ 2 :=
          Finset.single_le_sum (f := fun j => (finrank ℂ (V j) : ℝ) ^ 2)
            (fun j _ => by positivity) (Finset.mem_univ i)
      _ ≤ _ := hDr
  calc ∑ i, (finrank ℂ (V i) : ℝ) ^ 3
      = ∑ i, (finrank ℂ (V i) : ℝ) * (finrank ℂ (V i) : ℝ) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ ∑ i, Real.sqrt (Fintype.card G) * (finrank ℂ (V i) : ℝ) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hfi i) (by positivity)
    _ = Real.sqrt (Fintype.card G) * ∑ i, (finrank ℂ (V i) : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt (Fintype.card G) * Fintype.card G :=
        mul_le_mul_of_nonneg_left hDr (Real.sqrt_nonneg _)

end Characters

/-- A family, indexed by the partitions `λ ⊢ n`, of pairwise non-isomorphic irreducible
finite-dimensional complex representations of the symmetric group `S_n = Equiv.Perm (Fin n)`.
(The Specht modules `S^λ` form such a family.) -/
structure IrrepFamily (n : ℕ) where
  /-- the representation labelled by `λ` -/
  V : Nat.Partition n → FDRep ℂ (Equiv.Perm (Fin n))
  /-- each `V λ` is irreducible -/
  simple : ∀ p, Simple (V p)
  /-- distinct labels give non-isomorphic representations -/
  distinct : ∀ p q, Nonempty (V p ≅ V q) → p = q

/-- `f_λ = dim V_λ`. -/
noncomputable def IrrepFamily.f {n : ℕ} (F : IrrepFamily n) (p : Nat.Partition n) : ℕ :=
  finrank ℂ (F.V p)

/-- The third-order character sum `S₃(n) = ∑_{λ ⊢ n} f_λ³ / n!`. -/
noncomputable def IrrepFamily.S3 {n : ℕ} (F : IrrepFamily n) : ℝ :=
  (∑ p, (F.f p : ℝ) ^ 3) / n.factorial

/-- `S₃(n) ≤ √(n!)`. -/
theorem S3_le_sqrt {n : ℕ} (F : IrrepFamily n) : F.S3 ≤ Real.sqrt n.factorial := by
  have := F.simple
  have h := sum_cube_le F.V F.distinct
  rw [Fintype.card_perm, Fintype.card_fin] at h
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [IrrepFamily.S3, div_le_iff₀ hpos]
  exact h

theorem S3_nonneg {n : ℕ} (F : IrrepFamily n) : 0 ≤ F.S3 := by
  unfold IrrepFamily.S3; positivity

/-- The comparison function `√(n!) · n^{1/4}` of the conjecture. -/
noncomputable def g (n : ℕ) : ℝ := Real.sqrt n.factorial * (n : ℝ) ^ (1 / 4 : ℝ)

theorem g_pos {n : ℕ} (hn : 1 ≤ n) : 0 < g n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  unfold g
  have := Real.sqrt_pos.mpr (show (0 : ℝ) < n.factorial by exact_mod_cast Nat.factorial_pos n)
  positivity

/-- The normalized ratio tends to `0`. -/
theorem ratio_tendsto_zero (F : ∀ n, IrrepFamily n) :
    Tendsto (fun n => (F n).S3 / g n) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hlim
  · by_cases hn : n = 0
    · subst hn; simp [g]
    · exact div_nonneg (S3_nonneg _) (g_pos (Nat.one_le_iff_ne_zero.mpr hn)).le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hgp := g_pos hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hsf : 0 < Real.sqrt n.factorial :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos n)
    rw [div_le_iff₀ hgp, g, Real.rpow_neg hnr.le]
    calc (F n).S3 ≤ Real.sqrt n.factorial := S3_le_sqrt _
      _ = ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ * (Real.sqrt n.factorial * (n : ℝ) ^ (1 / 4 : ℝ)) := by
        field_simp [(Real.rpow_pos_of_pos hnr (1 / 4 : ℝ)).ne']

/-- **Conjecture 00000000489 is false**, for every choice of the labelled families
`(V_λ)_{λ ⊢ n}` of pairwise non-isomorphic irreducible representations of `S_n`:
`S₃(n) ≤ √(n!)`, `S₃(n) = o(√(n!) n^{1/4})`, so `S₃(n) = Θ(√(n!) n^{1/4})` fails, the ratio
`S₃(n)/(√(n!) n^{1/4})` does not tend to `2^{1/4} π^{-1/2}`, and `S₃(n)/√(n!)` is not
asymptotically equivalent to `2^{1/4} π^{-1/2} n^{1/4}`. -/
theorem conjecture489_false (F : ∀ n, IrrepFamily n) :
    (∀ n, (F n).S3 ≤ Real.sqrt n.factorial) ∧
    Tendsto (fun n => (F n).S3 / (Real.sqrt n.factorial * (n : ℝ) ^ (1 / 4 : ℝ))) atTop (𝓝 0) ∧
    (fun n => (F n).S3) =o[atTop] (fun n => Real.sqrt n.factorial * (n : ℝ) ^ (1 / 4 : ℝ)) ∧
    ¬ (fun n => (F n).S3) =Θ[atTop] (fun n => Real.sqrt n.factorial * (n : ℝ) ^ (1 / 4 : ℝ)) ∧
    ¬ Tendsto (fun n => (F n).S3 / (Real.sqrt n.factorial * (n : ℝ) ^ (1 / 4 : ℝ))) atTop
      (𝓝 (2 ^ (1 / 4 : ℝ) / Real.sqrt Real.pi)) ∧
    ¬ (fun n => (F n).S3 / Real.sqrt n.factorial) ~[atTop]
      (fun n => 2 ^ (1 / 4 : ℝ) / Real.sqrt Real.pi * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  have hR := ratio_tendsto_zero F
  have hne : ∀ᶠ n in atTop, g n ≠ 0 :=
    (eventually_ge_atTop 1).mono fun n hn => (g_pos hn).ne'
  have ho : (fun n => (F n).S3) =o[atTop] g :=
    (isLittleO_iff_tendsto' (hne.mono fun n hn h => absurd h hn)).mpr hR
  have hC : (0 : ℝ) < 2 ^ (1 / 4 : ℝ) / Real.sqrt Real.pi :=
    div_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.sqrt_pos.mpr Real.pi_pos)
  refine ⟨fun n => S3_le_sqrt _, hR, ho, ?_, ?_, ?_⟩
  · intro hT
    have hgg : g =o[atTop] g := hT.symm.isBigO.trans_isLittleO ho
    exact isLittleO_irrefl (hne.frequently) hgg
  · intro hT
    exact hC.ne' (tendsto_nhds_unique hT hR)
  · intro hE
    have hne' : ∀ᶠ n : ℕ in atTop,
        2 ^ (1 / 4 : ℝ) / Real.sqrt Real.pi * (n : ℝ) ^ (1 / 4 : ℝ) ≠ 0 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (0 : ℝ) < n := by exact_mod_cast hn
      exact (mul_pos hC (Real.rpow_pos_of_pos this _)).ne'
    have h1 := (isEquivalent_iff_tendsto_one hne').mp hE
    have h0 : Tendsto (fun n => (F n).S3 / g n / (2 ^ (1 / 4 : ℝ) / Real.sqrt Real.pi))
        atTop (𝓝 (0 / (2 ^ (1 / 4 : ℝ) / Real.sqrt Real.pi))) := hR.div_const _
    rw [zero_div] at h0
    have heq : ((fun n => (F n).S3 / Real.sqrt n.factorial) /
        fun n : ℕ => 2 ^ (1 / 4 : ℝ) / Real.sqrt Real.pi * (n : ℝ) ^ (1 / 4 : ℝ)) =
        fun n => (F n).S3 / g n / (2 ^ (1 / 4 : ℝ) / Real.sqrt Real.pi) := by
      funext n
      simp only [Pi.div_apply, g]
      ring
    rw [heq] at h1
    exact one_ne_zero (tendsto_nhds_unique h1 h0)

end C489
