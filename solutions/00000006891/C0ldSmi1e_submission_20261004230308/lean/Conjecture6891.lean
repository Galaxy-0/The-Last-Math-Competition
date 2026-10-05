import Conjecture6891.Rank
import Conjecture6891.Arc

noncomputable section
namespace Conjecture6891

theorem secantSpanLocus_mono {r s : ℕ} (h : r ≤ s) :
    secantSpanLocus r ⊆ secantSpanLocus s := by
  intro x hx
  have hr : RankLE r x.rep :=
    (mk_mem_secantSpanLocus_iff_rankLE r x.rep x.rep_nonzero).mp
      (by simpa only [Projectivization.mk_rep] using hx)
  have hs := (mk_mem_secantSpanLocus_iff_rankLE s x.rep x.rep_nonzero).mpr
    (rankLE_mono h hr)
  simpa only [Projectivization.mk_rep] using hs

theorem secantVariety_mono {r s : ℕ} (h : r ≤ s) : secantVariety r ⊆ secantVariety s :=
  projectiveZariskiClosure_mono (secantSpanLocus_mono h)

/-- Every projective tensor has a finite secant level, using its actual finite decomposition. -/
theorem exists_secantVariety (x : ProjectiveTensor) : ∃ r, x ∈ secantVariety r := by
  obtain ⟨r, hr⟩ := exists_rankLE x.rep
  refine ⟨r, ?_⟩
  have h := (mk_mem_secantSpanLocus_iff_rankLE r x.rep x.rep_nonzero).mpr hr
  have hc := subset_projectiveZariskiClosure (secantSpanLocus r) h
  simpa only [Projectivization.mk_rep] using hc

/-- The actual least index in the closed projective secant hierarchy. -/
def secantIndex (x : ProjectiveTensor) : ℕ := by
  classical
  exact Nat.find (exists_secantVariety x)

theorem mem_secantVariety_index (x : ProjectiveTensor) : x ∈ secantVariety (secantIndex x) := by
  classical
  exact Nat.find_spec (exists_secantVariety x)

theorem secantIndex_le_of_mem {x : ProjectiveTensor} {r : ℕ} (h : x ∈ secantVariety r) :
    secantIndex x ≤ r := by
  classical
  exact Nat.find_min' (exists_secantVariety x) h

theorem secantIndex_pos (x : ProjectiveTensor) : 0 < secantIndex x := by
  have h := mem_secantVariety_index x
  by_contra hn
  have hz : secantIndex x = 0 := by omega
  rw [hz, secantVariety_zero] at h
  exact h

theorem secantIndex_projectiveW : secantIndex projectiveW = 2 := by
  have hu := secantIndex_le_of_mem projectiveW_mem_secantVariety_two
  have hp := secantIndex_pos projectiveW
  have hn : secantIndex projectiveW ≠ 1 := by
    intro h
    have hm := mem_secantVariety_index projectiveW
    rw [h] at hm
    exact projectiveW_not_mem_secantVariety_one hm
  omega

/-- The rank/index equality that the first conjunct asserts, restricted to complex 2×2×2 tensors. -/
def RankSecantHierarchyClaim : Prop :=
  ∀ (t : Tensor) (ht : t ≠ 0),
    tensorRank t = secantIndex (Projectivization.mk ℂ t ht)

theorem rank_and_secant_index_counterexample :
    W ≠ 0 ∧ tensorRank W = 3 ∧ secantIndex projectiveW = 2 :=
  ⟨W_ne_zero, tensorRank_W, secantIndex_projectiveW⟩

/-- The first source conjunct already fails; the generic-dimension conjunct is not needed. -/
theorem conjecture_00000006891_false : ¬ RankSecantHierarchyClaim := by
  intro h
  have he := h W W_ne_zero
  change tensorRank W = secantIndex projectiveW at he
  rw [tensorRank_W, secantIndex_projectiveW] at he
  omega

end Conjecture6891
