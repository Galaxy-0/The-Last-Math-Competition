/-
  Batch 6: machine-checked disproof of TLMC #2308
  ==============================================

  Conjecture #2308 asserts that "the order of the smallest nontrivial
  solvable complete group is 2^{11}·3 = 6144".  This is false: the
  symmetric group S₃ = Perm (Fin 3) is

    * nontrivial,
    * solvable,
    * complete (trivial center and every automorphism is inner),

  and has order 6 ≠ 6144.  In fact S₃ is *the* smallest nontrivial
  complete group, solvable or not.

  All finite checks below are kernel-verified (`decide`); the structural
  parts use Mathlib's `MulAut` and `IsSolvable` API.
  No `sorry`.  Toolchain: leanprover/lean4:v4.31.0, Mathlib v4.31.0.
-/

import Mathlib

namespace TLMCBatch6

/-- The symmetric group on three letters. -/
abbrev S3 : Type := Equiv.Perm (Fin 3)

def s01 : S3 := Equiv.swap (0 : Fin 3) 1
def s02 : S3 := Equiv.swap (0 : Fin 3) 2
def s12 : S3 := Equiv.swap (1 : Fin 3) 2

/-- Every element of `S₃` is one of six explicit words (kernel-computed). -/
theorem S3_enum : ∀ σ : S3,
    σ = 1 ∨ σ = s01 ∨ σ = s02 ∨ σ = s12 ∨ σ = s01 * s02 ∨ σ = s02 * s01 := by decide

/-- The involutions of `S₃` are exactly the three swaps (kernel-computed). -/
theorem S3_invol : ∀ σ : S3, σ * σ = 1 ∧ σ ≠ 1 ↔ σ = s01 ∨ σ = s02 ∨ σ = s12 := by decide

/-- `S₃` has trivial center (kernel-computed). -/
theorem S3_centerless : ∀ σ : S3, (∀ h : S3, σ * h = h * σ) → σ = 1 := by decide

/-- Any two distinct involutions of `S₃` are simultaneously conjugate to
    `s01` and `s02`; the conjugator is produced explicitly, case by case,
    with each conjugation identity kernel-computed. -/
theorem S3_conj_pairs : ∀ a b : S3, a ≠ b → a ≠ 1 → b ≠ 1 → a * a = 1 → b * b = 1 →
    ∃ k : S3, k * s01 * k⁻¹ = a ∧ k * s02 * k⁻¹ = b := by
  intro a b hab ha1 hb1 ha2 hb2
  have h1 : a = s01 ∨ a = s02 ∨ a = s12 := (S3_invol a).1 ⟨ha2, ha1⟩
  have h2 : b = s01 ∨ b = s02 ∨ b = s12 := (S3_invol b).1 ⟨hb2, hb1⟩
  rcases h1 with r1 | r1 | r1 <;> rcases h2 with r2 | r2 | r2
  · exact absurd (r1.trans r2.symm) hab
  · exact ⟨1, by rw [r1]; decide, by rw [r2]; decide⟩
  · exact ⟨s01, by rw [r1]; decide, by rw [r2]; decide⟩
  · exact ⟨s12, by rw [r1]; decide, by rw [r2]; decide⟩
  · exact absurd (r1.trans r2.symm) hab
  · exact ⟨s01 * s02, by rw [r1]; decide, by rw [r2]; decide⟩
  · exact ⟨s02 * s01, by rw [r1]; decide, by rw [r2]; decide⟩
  · exact ⟨s02, by rw [r1]; decide, by rw [r2]; decide⟩
  · exact absurd (r1.trans r2.symm) hab

/-- Auxiliary arithmetic facts about the generators (kernel-computed). -/
theorem S3_arith : s01 * s01 = 1 ∧ s02 * s02 = 1 ∧ s01 ≠ s02 ∧ s01 * s02 * s01 = s12 := by
  decide

/-! ### Solvability -/

/-- The parity homomorphism, defined concretely: the three swaps are odd. -/
def sgn : S3 →* Multiplicative (ZMod 2) where
  toFun σ := if σ = s01 ∨ σ = s02 ∨ σ = s12 then Multiplicative.ofAdd (1 : ZMod 2) else 1
  map_one' := by decide
  map_mul' := by decide

/-- Commutators have trivial sign (kernel-computed). -/
theorem S3_comm_sgn : ∀ x y : S3, sgn (x * y * x⁻¹ * y⁻¹) = 1 := by decide

/-- The even permutations of `S₃` commute (kernel-computed). -/
theorem S3_even_abelian : ∀ a b : S3, sgn a = 1 → sgn b = 1 → a * b = b * a := by decide

/-- **`S₃` is solvable.** -/
theorem S3_solvable : IsSolvable S3 := by
  refine ⟨⟨2, ?_⟩⟩
  have hker : ⁅(⊤ : Subgroup S3), ⊤⁆ ≤ MonoidHom.ker sgn := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    simp only [MonoidHom.mem_ker]
    exact S3_comm_sgn x y
  have hA : derivedSeries S3 1 ≤ MonoidHom.ker sgn := by
    rw [derivedSeries_one]
    exact hker
  apply le_bot_iff.mp
  show ⁅derivedSeries S3 1, derivedSeries S3 1⁆ ≤ ⊥
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab : a * b = b * a := S3_even_abelian a b (hA ha) (hA hb)
  show a * b * a⁻¹ * b⁻¹ = 1
  rw [hab]
  group

/-! ### Completeness -/

/-- Automorphisms preserve the involution property. -/
theorem S3_aut_invol (φ : MulAut S3) {σ : S3} (hσ : σ * σ = 1) : φ σ * φ σ = 1 := by
  have h : φ (σ * σ) = φ σ * φ σ := φ.map_mul σ σ
  rw [hσ, map_one] at h
  exact h.symm

/-- **`S₃` is complete**: every automorphism of `S₃` is inner. -/
theorem S3_complete : ∀ φ : MulAut S3, ∃ k : S3, ∀ h : S3, φ h = k * h * k⁻¹ := by
  intro φ
  obtain ⟨h11, h12, hne, hbraid⟩ := S3_arith
  have a1 : φ s01 * φ s01 = 1 := S3_aut_invol φ h11
  have a2 : φ s02 * φ s02 = 1 := S3_aut_invol φ h12
  have ane : φ s01 ≠ φ s02 := fun hc => hne (φ.toEquiv.injective hc)
  have an1 : φ s01 ≠ 1 := fun hc =>
    (by decide : ¬(s01 = (1 : S3))) (φ.toEquiv.injective (hc.trans (map_one φ).symm))
  have an2 : φ s02 ≠ 1 := fun hc =>
    (by decide : ¬(s02 = (1 : S3))) (φ.toEquiv.injective (hc.trans (map_one φ).symm))
  obtain ⟨k, hk1, hk2⟩ := S3_conj_pairs (φ s01) (φ s02) ane an1 an2 a1 a2
  refine ⟨k, ?_⟩
  have key : ∀ h h' : S3, φ h = k * h * k⁻¹ → φ h' = k * h' * k⁻¹ →
      φ (h * h') = k * (h * h') * k⁻¹ := by
    intro h h' hh hh'
    rw [φ.map_mul, hh, hh']
    group
  have keyinv : ∀ h : S3, φ h = k * h * k⁻¹ → φ h⁻¹ = k * h⁻¹ * k⁻¹ := by
    intro h hh
    have hinv := φ.map_inv h
    rw [hh] at hinv
    calc φ h⁻¹ = (k * h * k⁻¹)⁻¹ := hinv
      _ = k * h⁻¹ * k⁻¹ := by group
  have e1 : φ (1 : S3) = k * 1 * k⁻¹ := by rw [map_one]; group
  have e01 : φ s01 = k * s01 * k⁻¹ := hk1.symm
  have e02 : φ s02 = k * s02 * k⁻¹ := hk2.symm
  have ec1 : φ (s01 * s02) = k * (s01 * s02) * k⁻¹ := key s01 s02 e01 e02
  have ec2 : φ (s02 * s01) = k * (s02 * s01) * k⁻¹ := key s02 s01 e02 e01
  have e12 : φ s12 = k * s12 * k⁻¹ := by
    rw [← hbraid]
    exact key s01 (s02 * s01) e01 ec2
  intro h
  rcases S3_enum h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact e1
  · exact e01
  · exact e02
  · exact e12
  · exact ec1
  · exact ec2

/-! ### The disproof of #2308 -/

/-- The order of `S₃` is six (kernel-computed). -/
theorem S3_card : Fintype.card S3 = 6 := by decide

/-- **TLMC #2308 is false.**  `S₃` is a nontrivial solvable complete group
    (trivial center, every automorphism inner) of order `6`, so the order of
    the smallest nontrivial solvable complete group is at most `6`, not
    `2^{11} · 3 = 6144`. -/
theorem tlm2308 :
    Fintype.card S3 = 6 ∧ (s01 ≠ (1 : S3)) ∧ IsSolvable S3 ∧
      (∀ σ : S3, (∀ h : S3, σ * h = h * σ) → σ = 1) ∧
      (∀ φ : MulAut S3, ∃ k : S3, ∀ h : S3, φ h = k * h * k⁻¹) :=
  ⟨S3_card, by decide, S3_solvable, S3_centerless, S3_complete⟩

theorem tlm2308_false : (2 : ℕ) ^ 11 * 3 ≠ Fintype.card S3 := by
  rw [S3_card]
  decide

end TLMCBatch6
