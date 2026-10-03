import Mathlib

/-!
# Conjecture 00000001063 is false

A *Kakeya set* in the affine plane `F²` over a finite field `F` is a set of points
containing a full line in every direction: for every nonzero `v ∈ F²` there is a
base point `a` with `a + t • v ∈ K` for all `t ∈ F`.

Conjecture 00000001063 asserts that the minimal size of a Kakeya set in `F_q²`
is exactly `q(q+1)/2`. This fails already for `q = 3`, where `q(q+1)/2 = 6` but
every Kakeya set has at least `7` points.

The argument: a Kakeya set in `𝔽₃²` contains a line from each of the four
parallel classes, with directions `(1,0)`, `(0,1)`, `(1,1)`, `(1,2)`. Such a line
is cut out by an equation `y = c₁`, `x = c₂`, `y = x + c₃` or `y = 2x + c₄`
respectively, so the Kakeya set contains the union `fourLines c₁ c₂ c₃ c₄` of
four such lines. Each of the `3⁴ = 81` unions has at least `7` points, which the
kernel checks by evaluation (`decide`).

The bound is attained: `K7` below is a Kakeya set with `7` points, so the minimal
size over `𝔽₃` is exactly `7`, the value `q(q+1)/2 + (q-1)/2` that Blokhuis and
Mazzocca proved for every odd `q`.
-/

namespace Submission00000001063

open Finset

/-- A Kakeya set in `F²`: for every nonzero direction `v` it contains the whole
line `{a + t • v | t ∈ F}` through some base point `a`. -/
def IsKakeya {F : Type*} [Field F] (K : Set (F × F)) : Prop :=
  ∀ v : F × F, v ≠ 0 → ∃ a : F × F, ∀ t : F, a + t • v ∈ K

/-- The minimal size of a Kakeya set in `F²` is exactly `s`: some Kakeya set has
`s` points, and none has fewer. -/
def MinKakeyaSizeIs (F : Type*) [Field F] [Fintype F] (s : ℕ) : Prop :=
  (∃ K : Finset (F × F), IsKakeya (K : Set (F × F)) ∧ K.card = s) ∧
    ∀ K : Finset (F × F), IsKakeya (K : Set (F × F)) → s ≤ K.card

/-- Conjecture 00000001063: for every finite field `F_q`, the minimal size of a
Kakeya set in `F_q²` is exactly `q(q+1)/2`. -/
def ConjectureHolds : Prop :=
  ∀ (F : Type) [Field F] [Fintype F],
    MinKakeyaSizeIs F (Fintype.card F * (Fintype.card F + 1) / 2)

/-- The union of four lines of `𝔽₃²`, one from each parallel class, given by
their equations `y = c₁`, `x = c₂`, `y = x + c₃`, `y = 2x + c₄`. -/
def fourLines (c₁ c₂ c₃ c₄ : ZMod 3) : Finset (ZMod 3 × ZMod 3) :=
  univ.filter fun p => p.2 = c₁ ∨ p.1 = c₂ ∨ p.2 = p.1 + c₃ ∨ p.2 = 2 * p.1 + c₄

/-- Four lines of `𝔽₃²` in four different directions always cover at least `7`
points; checked over all `81` choices. -/
theorem seven_le_card_fourLines :
    ∀ c₁ c₂ c₃ c₄ : ZMod 3, 7 ≤ (fourLines c₁ c₂ c₃ c₄).card := by
  decide

/-- A Kakeya set in `𝔽₃²` contains four lines, one in each direction. -/
theorem exists_fourLines_subset {K : Finset (ZMod 3 × ZMod 3)}
    (hK : IsKakeya (K : Set (ZMod 3 × ZMod 3))) :
    ∃ c₁ c₂ c₃ c₄, fourLines c₁ c₂ c₃ c₄ ⊆ K := by
  obtain ⟨a₁, h₁⟩ := hK (1, 0) (by decide)
  obtain ⟨a₂, h₂⟩ := hK (0, 1) (by decide)
  obtain ⟨a₃, h₃⟩ := hK (1, 1) (by decide)
  obtain ⟨a₄, h₄⟩ := hK (1, 2) (by decide)
  refine ⟨a₁.2, a₂.1, a₃.2 - a₃.1, a₄.2 - 2 * a₄.1, ?_⟩
  intro p hp
  rw [← Finset.mem_coe]
  simp only [fourLines, mem_filter, mem_univ, true_and] at hp
  rcases hp with h | h | h | h
  · convert h₁ (p.1 - a₁.1) using 1
    refine Prod.ext ?_ ?_ <;> simp [h]
  · convert h₂ (p.2 - a₂.2) using 1
    refine Prod.ext ?_ ?_ <;> simp [h]
  · convert h₃ (p.1 - a₃.1) using 1
    refine Prod.ext (by simp) ?_
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one, h]
    ring
  · convert h₄ (p.1 - a₄.1) using 1
    refine Prod.ext (by simp) ?_
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, h]
    ring

/-- Every Kakeya set in `𝔽₃²` has at least `7` points. -/
theorem seven_le_card_of_isKakeya (K : Finset (ZMod 3 × ZMod 3))
    (hK : IsKakeya (K : Set (ZMod 3 × ZMod 3))) : 7 ≤ K.card := by
  obtain ⟨c₁, c₂, c₃, c₄, hsub⟩ := exists_fourLines_subset hK
  exact (seven_le_card_fourLines c₁ c₂ c₃ c₄).trans (card_le_card hsub)

/-- A Kakeya set in `𝔽₃²` with `7` points: the lines `y = 0`, `x = 0`, `y = x`
through the origin, together with `y = 2x + 1`, which meets each of them in a
point already listed. -/
def K7 : Finset (ZMod 3 × ZMod 3) :=
  {(0, 0), (1, 0), (2, 0), (0, 1), (0, 2), (1, 1), (2, 2)}

theorem isKakeya_K7 : IsKakeya (K7 : Set (ZMod 3 × ZMod 3)) := by
  unfold IsKakeya
  simp only [Finset.mem_coe]
  decide

theorem card_K7 : K7.card = 7 := by
  decide

/-- Over `𝔽₃` the minimal size of a Kakeya set is exactly `7`. -/
theorem minKakeyaSizeIs_zmod_three : MinKakeyaSizeIs (ZMod 3) 7 :=
  ⟨⟨K7, isKakeya_K7, card_K7⟩, seven_le_card_of_isKakeya⟩

/-- Conjecture 00000001063 is false: over `𝔽₃` it predicts minimal size
`3 · 4 / 2 = 6`, but no Kakeya set in `𝔽₃²` has `6` points. -/
theorem conjecture_00000001063_false : ¬ ConjectureHolds := by
  intro h
  obtain ⟨⟨K, hK, hcard⟩, -⟩ := h (ZMod 3)
  have h7 := seven_le_card_of_isKakeya K hK
  rw [ZMod.card] at hcard
  omega

end Submission00000001063

#print axioms Submission00000001063.conjecture_00000001063_false
