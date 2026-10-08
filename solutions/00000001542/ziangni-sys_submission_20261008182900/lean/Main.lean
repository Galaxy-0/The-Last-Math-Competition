import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace PinnedTriangle
abbrev Plane := EuclideanSpace ℝ (Fin 2)
noncomputable def vertex (i : Fin 3) : Plane :=
  (![![(0:ℝ),0], ![1,0], ![(1/2:ℝ), Real.sqrt 3 / 2]] i)

theorem distances (i j : Fin 3) : dist (vertex i) (vertex j) = if i = j then 0 else 1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : ‖vertex i - vertex j‖ ^ 2 = if i = j then 0 else 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    fin_cases i <;> fin_cases j <;>
      simp [vertex, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] <;> nlinarith
  rw [dist_eq_norm]
  split_ifs at hn ⊢ <;> nlinarith [norm_nonneg (vertex i - vertex j)]

theorem vertex_injective : Function.Injective vertex := by
  intro i j hij
  by_contra hne
  have hd := distances i j
  rw [if_neg hne, hij, dist_self] at hd
  norm_num at hd

noncomputable def triangle : Finset Plane := Finset.univ.image vertex
noncomputable def pinned (s : Finset Plane) (p : Plane) : Finset ℝ := s.image (fun q => dist p q)

theorem triangle_card : triangle.card = 3 := by
  rw [triangle, Finset.card_image_of_injective _ vertex_injective]
  simp

theorem triangle_nonempty : triangle.Nonempty := by
  refine ⟨vertex 0, ?_⟩
  simp [triangle]

theorem pinned_card_le_two (p : Plane) (hp : p ∈ triangle) : (pinned triangle p).card ≤ 2 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  have hsub : pinned triangle (vertex i) ⊆ {(0:ℝ),1} := by
    intro r hr
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    rw [distances]
    split_ifs <;> simp
  have hc := Finset.card_le_card hsub
  norm_num at hc ⊢
  exact hc

theorem exponent_bound : 2 < (3:ℝ) ^ (687/1000:ℝ) := by
  have hpow : ((3:ℝ) ^ (2/3:ℝ)) ^ (3:ℕ) = 9 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have hroot : 2 < (3:ℝ) ^ (2/3:ℝ) := by
    by_contra hh
    have hh' : (3:ℝ) ^ (2/3:ℝ) ≤ 2 := le_of_not_gt hh
    have hm : ((3:ℝ) ^ (2/3:ℝ)) ^ (3:ℕ) ≤ 2^3 := by
      gcongr
    rw [hpow] at hm
    norm_num at hm
  exact hroot.trans (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num))

noncomputable def ClaimedBound : Prop := ∀ s : Finset Plane, s.Nonempty →
  ∃ p ∈ s, (s.card : ℝ) ^ (687/1000:ℝ) ≤ (pinned s p).card

theorem conjecture_false : ¬ ClaimedBound := by
  intro h
  obtain ⟨p,hp,hb⟩ := h triangle triangle_nonempty
  rw [triangle_card] at hb
  have hc : ((pinned triangle p).card : ℝ) ≤ 2 := by
    exact_mod_cast pinned_card_le_two p hp
  have := exponent_bound
  linarith

#print axioms distances
#print axioms vertex_injective
#print axioms triangle_card
#print axioms pinned_card_le_two
#print axioms exponent_bound
#print axioms conjecture_false
end PinnedTriangle
