import Conjecture7744

open MeasureTheory ProbabilityTheory Filter Conjecture7744

/-! Independent review-only checks. These do not modify the frozen submission. -/

/-- The contradiction needs neither product labels nor the block graph witness:
it holds for every sequence of nonempty uniform cubic graph spaces. -/
theorem reviewer_arbitrary_labels_no_claimed_limit
    (V : ℕ → Type) [∀ k, Fintype (V k)]
    [∀ k, Nonempty (RegularGraph (V k) 3)] (a b : ℕ → ℝ) :
    ¬ ∃ ν : ProbabilityMeasure ℝ,
      Tendsto (fun k => quadraticLaw (V k) 3 (a k) (b k)) atTop (nhds ν) ∧
      lawVariance ν = claimedVariance 3 := by
  rintro ⟨ν, hlim, hvar⟩
  have hzero : Tendsto (fun k => quadraticLaw (V k) 3 (a k) (b k))
      atTop (nhds zeroLaw) := by
    simp only [quadraticLaw_eq_zeroLaw]
    exact tendsto_const_nhds
  have heq : ν = zeroLaw := tendsto_nhds_unique hlim hzero
  rw [heq, zeroLaw_variance, claimedVariance_three] at hvar
  norm_num at hvar

/-- The proven cardinal divergence is sufficient for the ordinary subsequence
step whenever the full size-indexed family has a weak limit. -/
theorem reviewer_size_subsequence
    (laws : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hlim : Tendsto laws atTop (nhds ν)) :
    Tendsto (fun k => laws (Fintype.card (BlockVertices 3 k))) atTop (nhds ν) :=
  hlim.comp (blockVertices_card_tendsto 3)

#check reviewer_arbitrary_labels_no_claimed_limit
#print axioms reviewer_arbitrary_labels_no_claimed_limit
#check reviewer_size_subsequence
#print axioms reviewer_size_subsequence
