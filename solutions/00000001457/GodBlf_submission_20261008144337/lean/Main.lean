import Mathlib.Tactic

namespace Conjecture1457

abbrev Plane := ℝ × ℝ

def diamond : Set Plane := {p | |p.1| + |p.2| ≤ 1}
def triangle : Set Plane := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

-- Exact inequalities for d + l * triangle when l > 0.
def outerTriangle (l : ℝ) (d : Plane) : Set Plane :=
  {p | d.1 ≤ p.1 ∧ d.2 ≤ p.2 ∧ p.1 + p.2 ≤ l + d.1 + d.2}

theorem outerTriangle_iff {l : ℝ} (hl : 0 < l) (d p : Plane) :
    p ∈ outerTriangle l d ↔ ∃ q ∈ triangle, p = d + l • q := by
  constructor
  · intro hp
    refine ⟨((p.1 - d.1) / l, (p.2 - d.2) / l), ?_, ?_⟩
    · change 0 ≤ (p.1 - d.1) / l ∧ 0 ≤ (p.2 - d.2) / l ∧
        (p.1 - d.1) / l + (p.2 - d.2) / l ≤ 1
      refine ⟨div_nonneg (sub_nonneg.mpr hp.1) (le_of_lt hl),
        div_nonneg (sub_nonneg.mpr hp.2.1) (le_of_lt hl), ?_⟩
      rw [← add_div, div_le_iff₀ hl]
      linarith [hp.2.2]
    · apply Prod.ext <;> change _ = _ + l * ((_ - _) / l) <;>
        field_simp <;> ring
  · rintro ⟨q, hq, rfl⟩
    change d.1 ≤ d.1 + l * q.1 ∧ d.2 ≤ d.2 + l * q.2 ∧
      (d.1 + l * q.1) + (d.2 + l * q.2) ≤ l + d.1 + d.2
    rcases hq with ⟨hx, hy, hsum⟩
    constructor
    · nlinarith
    · constructor <;> nlinarith

def affineDiamond (c : Plane) (T : Plane ≃ₗ[ℝ] Plane) : Set Plane :=
  {p | ∃ q ∈ diamond, p = c + T q}

-- Allow independent translations of the middle and outer bodies.
def Admissible (l : ℝ) : Prop :=
  0 < l ∧ ∃ (c d : Plane) (T : Plane ≃ₗ[ℝ] Plane),
    triangle ⊆ affineDiamond c T ∧ affineDiamond c T ⊆ outerTriangle l d

theorem diamond_symmetric {p : Plane} (hp : p ∈ diamond) : -p ∈ diamond := by
  simpa [diamond] using hp

theorem affine_symmetric (c : Plane) (T : Plane ≃ₗ[ℝ] Plane) {p : Plane}
    (hp : p ∈ affineDiamond c T) : c + c - p ∈ affineDiamond c T := by
  obtain ⟨q, hq, rfl⟩ := hp
  refine ⟨-q, diamond_symmetric hq, ?_⟩
  rw [map_neg]
  abel

theorem admissible_lower_bound {l : ℝ} (hl : Admissible l) : 2 ≤ l := by
  obtain ⟨_, c, d, T, hinner, houter⟩ := hl
  have hv0 : ((0, 0) : Plane) ∈ triangle := by norm_num [triangle]
  have hv1 : ((1, 0) : Plane) ∈ triangle := by norm_num [triangle]
  have hv2 : ((0, 1) : Plane) ∈ triangle := by norm_num [triangle]
  have h0 := houter (affine_symmetric c T (hinner hv0))
  have h1 := houter (affine_symmetric c T (hinner hv1))
  have h2 := houter (affine_symmetric c T (hinner hv2))
  change d.1 ≤ c.1 + c.1 - 0 ∧ d.2 ≤ c.2 + c.2 - 0 ∧
    (c.1 + c.1 - 0) + (c.2 + c.2 - 0) ≤ l + d.1 + d.2 at h0
  change d.1 ≤ c.1 + c.1 - 1 ∧ d.2 ≤ c.2 + c.2 - 0 ∧
    (c.1 + c.1 - 1) + (c.2 + c.2 - 0) ≤ l + d.1 + d.2 at h1
  change d.1 ≤ c.1 + c.1 - 0 ∧ d.2 ≤ c.2 + c.2 - 1 ∧
    (c.1 + c.1 - 0) + (c.2 + c.2 - 1) ≤ l + d.1 + d.2 at h2
  linarith [h0.2.2, h1.1, h2.2.1]

theorem four_admissible : Admissible 4 := by
  refine ⟨by norm_num, (1 / 3, 1 / 3), (-2 / 3, -2 / 3),
    LinearEquiv.refl ℝ Plane, ?_, ?_⟩
  · intro p hp
    refine ⟨p - (1 / 3, 1 / 3), ?_, ?_⟩
    · rcases hp with ⟨hx, hy, hsum⟩
      change |p.1 - 1 / 3| + |p.2 - 1 / 3| ≤ 1
      rcases le_total (1 / 3) p.1 with hxp | hxn <;>
        rcases le_total (1 / 3) p.2 with hyp | hyn
      · rw [abs_of_nonneg (by linarith : 0 ≤ p.1 - 1 / 3),
          abs_of_nonneg (by linarith : 0 ≤ p.2 - 1 / 3)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ p.1 - 1 / 3),
          abs_of_nonpos (by linarith : p.2 - 1 / 3 ≤ 0)]
        linarith
      · rw [abs_of_nonpos (by linarith : p.1 - 1 / 3 ≤ 0),
          abs_of_nonneg (by linarith : 0 ≤ p.2 - 1 / 3)]
        linarith
      · rw [abs_of_nonpos (by linarith : p.1 - 1 / 3 ≤ 0),
          abs_of_nonpos (by linarith : p.2 - 1 / 3 ≤ 0)]
        linarith
    · change p = (1 / 3, 1 / 3) + (p - (1 / 3, 1 / 3))
      abel
  · rintro p ⟨q, hq, rfl⟩
    change -2 / 3 ≤ 1 / 3 + q.1 ∧ -2 / 3 ≤ 1 / 3 + q.2 ∧
      (1 / 3 + q.1) + (1 / 3 + q.2) ≤ (4 : ℝ) + -2 / 3 + -2 / 3
    change |q.1| + |q.2| ≤ 1 at hq
    have hx := le_abs_self q.1
    have hy := le_abs_self q.2
    have hnx := neg_le_abs q.1
    have hny := neg_le_abs q.2
    have ax := abs_nonneg q.1
    have ay := abs_nonneg q.2
    constructor
    · linarith
    · constructor <;> linarith

noncomputable def distance : ℝ := sInf {l : ℝ | Admissible l}

theorem distance_lower_bound : 2 ≤ distance := by
  apply le_csInf
  · exact ⟨4, four_admissible⟩
  · intro l hl
    exact admissible_lower_bound hl

theorem conjecture_false : distance ≠ (2 : ℝ) - 1 := by
  have h := distance_lower_bound
  linarith

end Conjecture1457
