import Mathlib

/-!
# Conjecture 00000002158: the chromatic threshold of `C₅`-free graphs is not `1/5`

The conjecture defines the chromatic threshold as the minimum-degree ratio threshold that keeps
the chromatic number of `H`-free graphs bounded, and claims that for `H = C₅` it equals `1/5`.

We use the definition of Allen, Böttcher, Griffiths, Kohayakawa and Morris (arXiv:1108.1746):
`δ_χ(H)` is the infimum of the `d > 0` such that there is a constant `K` for which every `H`-free
graph `G` on `n` vertices with `δ(G) ≥ d n` is `K`-colourable.  (ABGKM write `χ(G) < C`; this is
`G.Colorable (C - 1)`, so the set of admissible `d` is the same.)

We show that `d = 1/6` is admissible with `K = 264` (Thomassen-style argument), hence
`δ_χ(C₅) ≤ 1/6 < 1/5`.

Proof sketch.  Let `G` be `C₅`-free with `6 δ(G) ≥ n`.  Choose a largest set `S` of vertices any
two of which have at most two common neighbours.
* If `u, u'` are adjacent, both different from `s`, and both have at least three common
  neighbours with `s`, then `G` contains a `C₅` (`s - w - u - u' - w' - s`).
* Private neighbourhoods: any `T ⊆ S` satisfies `|T| δ ≤ n + 2|T|(|T| - 1)`; with `|T| = 12` this
  forces `n ≤ 264`.  So for `n > 264` we have `|S| ≤ 11`.
* Colour `s ∈ S` by `(true, s)`, and `v ∉ S` by `(false, s)` for some `s ∈ S` sharing at least
  three common neighbours with `v` (exists by maximality).  This is a proper colouring with
  `2|S| ≤ 22` colours.
-/

open Finset SimpleGraph

namespace C2158

section Core

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Five distinct vertices `a b c d e` with `a~b~c~d~e~a` give a copy of `C₅`. -/
lemma cycle5_le {a b c d e : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hea : G.Adj e a) (hac : a ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hbe : b ≠ e)
    (hce : c ≠ e) : cycleGraph 5 ⊑ G := by
  have h1 := hab.ne; have h2 := hbc.ne; have h3 := hcd.ne; have h4 := hde.ne; have h5 := hea.ne
  refine ⟨⟨⟨![a, b, c, d, e], ?_⟩, ?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd h (by decide)
      | simp [hab, hbc, hcd, hde, hea, hab.symm, hbc.symm, hcd.symm, hde.symm, hea.symm]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- Common neighbourhood of `a` and `b`. -/
abbrev cn (a b : V) : Finset V := G.neighborFinset a ∩ G.neighborFinset b

/-- Two adjacent vertices `u, u'`, both different from `s` and both with at least three common
neighbours with `s`, produce a `C₅`. -/
lemma not_free_of_class {s u u' : V} (hu : u ≠ s) (hu' : u' ≠ s) (huu' : G.Adj u u')
    (h1 : 3 ≤ #(cn G u s)) (h2 : 3 ≤ #(cn G u' s)) : ¬ (cycleGraph 5).Free G := by
  rw [not_free]
  obtain ⟨w, hw⟩ : ((cn G u s).erase u').Nonempty := by
    rw [← card_pos]; have := pred_card_le_card_erase (s := cn G u s) (a := u'); omega
  obtain ⟨w', hw'⟩ : (((cn G u' s).erase u).erase w).Nonempty := by
    rw [← card_pos]
    have := pred_card_le_card_erase (s := (cn G u' s).erase u) (a := w)
    have := pred_card_le_card_erase (s := cn G u' s) (a := u); omega
  simp only [mem_erase, mem_inter, mem_neighborFinset] at hw hw'
  exact cycle5_le G hw.2.2 hw.2.1.symm huu' hw'.2.2.1 hw'.2.2.2.symm hu.symm hu'.symm hw.1
    hw'.1.symm hw'.2.1.symm

/-- Any two distinct members of `S` have at most two common neighbours. -/
def Good (S : Finset V) : Prop := ∀ a ∈ S, ∀ b ∈ S, a ≠ b → #(cn G a b) ≤ 2

/-- Private-neighbourhood counting: `|T| δ ≤ n + |T| · 2(|T| - 1)` for a good set `T`. -/
lemma card_mul_minDegree_le {T : Finset V} (hT : Good G T) :
    #T * G.minDegree ≤ Fintype.card V + #T * (2 * (#T - 1)) := by
  set P : V → Finset V := fun s => G.neighborFinset s \ (T.erase s).biUnion fun t => G.neighborFinset t
  have hP : ∀ s ∈ T, G.minDegree ≤ #(P s) + 2 * (#T - 1) := by
    intro s hs
    have e := card_sdiff_add_card_inter (G.neighborFinset s) ((T.erase s).biUnion fun t => G.neighborFinset t)
    rw [inter_biUnion] at e
    have b1 := card_biUnion_le (s := T.erase s) (t := fun t => G.neighborFinset s ∩ G.neighborFinset t)
    have b2 : ∑ t ∈ T.erase s, #(G.neighborFinset s ∩ G.neighborFinset t) ≤ ∑ t ∈ T.erase s, 2 :=
      sum_le_sum fun t ht => hT s hs t (mem_of_mem_erase ht) (ne_of_mem_erase ht).symm
    rw [sum_const, card_erase_of_mem hs, smul_eq_mul] at b2
    have := G.minDegree_le_degree s
    rw [← card_neighborFinset_eq_degree] at this
    simp only [P]; nlinarith
  have hdisj : (T : Set V).PairwiseDisjoint P := by
    intro a ha b hb hab
    simp only [Function.onFun, P]
    rw [Finset.disjoint_left]
    intro v hva hvb
    simp only [mem_sdiff, mem_biUnion, mem_erase] at hva hvb
    exact hvb.2 ⟨a, ⟨hab, ha⟩, hva.1⟩
  have hsum : ∑ s ∈ T, #(P s) ≤ Fintype.card V := by
    rw [← card_biUnion hdisj]; exact card_le_univ _
  have := sum_le_sum hP
  rw [sum_const, smul_eq_mul, sum_add_distrib, sum_const, smul_eq_mul] at this
  omega

/-- Main combinatorial statement: a `C₅`-free graph with `6 δ ≥ n` and `n > 264` is
`22`-colourable. -/
theorem colorable22 (hfree : (cycleGraph 5).Free G) (hdeg : Fintype.card V ≤ 6 * G.minDegree)
    (hn : 264 < Fintype.card V) : G.Colorable 22 := by
  classical
  obtain ⟨S, hS, hmax⟩ := (univ.filter (Good G)).exists_max_image card
    ⟨∅, by simp [Good]⟩
  rw [mem_filter] at hS
  have hS := hS.2
  -- every vertex outside `S` has a partner in `S` with at least three common neighbours
  have wit : ∀ v ∉ S, ∃ s ∈ S, 3 ≤ #(cn G v s) := by
    intro v hv
    by_contra h
    simp only [not_exists, not_and, not_le] at h
    have hg : Good G (insert v S) := by
      intro a ha b hb hab
      rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · have := h b hb; omega
      · have := h a ha; simp only [cn] at this ⊢; rw [inter_comm]; omega
      · exact hS a ha b hb hab
    have := hmax (insert v S) (mem_filter.2 ⟨mem_univ _, hg⟩)
    rw [card_insert_of_notMem hv] at this; omega
  -- `S` has at most 11 elements
  have hS11 : #S ≤ 11 := by
    by_contra h
    obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq (s := S) (n := 12) (by omega)
    have := card_mul_minDegree_le G (T := T) (fun a ha b hb => hS a (hTS ha) b (hTS hb))
    rw [hT] at this; omega
  -- the colouring
  let c : V → Bool × S := fun v =>
    if h : v ∈ S then (true, ⟨v, h⟩) else (false, ⟨(wit v h).choose, (wit v h).choose_spec.1⟩)
  have hc : ∀ {u v : V}, G.Adj u v → c u ≠ c v := by
    intro u v huv
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp only [c, hu, hv, dite_true, dite_false,
      ne_eq, Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, false_and, not_false_eq_true,
      true_and, Subtype.mk.injEq]
    · exact huv.ne
    · intro heq
      have h1 := (wit u hu).choose_spec.2
      have h2 := (wit v hv).choose_spec.2
      rw [heq] at h1
      refine not_free_of_class G ?_ ?_ huv h1 h2 hfree
      · intro e; apply hu; rw [e]; exact (wit v hv).choose_spec.1
      · intro e; apply hv; rw [e]; exact (wit v hv).choose_spec.1
  have := (Coloring.mk c hc).colorable
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe] at this
  exact this.mono (by omega)

end Core

/-! ## The chromatic threshold -/

/-- The set of admissible degree ratios for `H` (ABGKM, arXiv:1108.1746): those `d > 0` for which
some `K` makes every `H`-free graph `G` on `n` vertices with `δ(G) ≥ d n` properly
`K`-colourable.  `H`-free means `G` has no subgraph (not necessarily induced) isomorphic to `H`. -/
def admissible {k : ℕ} (H : SimpleGraph (Fin k)) : Set ℝ :=
  {d | 0 < d ∧ ∃ K : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    H.Free G → d * n ≤ G.minDegree → G.Colorable K}

/-- The chromatic threshold `δ_χ(H)`: the infimum of the admissible ratios. -/
noncomputable def chromaticThreshold {k : ℕ} (H : SimpleGraph (Fin k)) : ℝ :=
  sInf (admissible H)

/-- `d = 1/6` is admissible for `C₅`, with `K = 264`. -/
theorem one_sixth_admissible : (1 / 6 : ℝ) ∈ admissible (cycleGraph 5) := by
  refine ⟨by norm_num, 264, fun n G _ hfree hdeg => ?_⟩
  have hdeg' : n ≤ 6 * G.minDegree := by
    have : (n : ℝ) ≤ 6 * (G.minDegree : ℝ) := by linarith
    exact_mod_cast this
  by_cases hn : n ≤ 264
  · exact (G.colorable_of_fintype).mono (by simpa using hn)
  · exact (colorable22 G hfree (by simpa using hdeg') (by simpa using hn)).mono (by norm_num)

/-- The chromatic threshold of `C₅` is at most `1/6`. -/
theorem chromaticThreshold_cycle5_le : chromaticThreshold (cycleGraph 5) ≤ 1 / 6 :=
  csInf_le ⟨0, fun _ hd => hd.1.le⟩ one_sixth_admissible

/-- **Disproof of conjecture 00000002158**: the chromatic threshold of `C₅`-free graphs is strictly
less than `1/5`; in particular it is not `1/5`. -/
theorem chromaticThreshold_cycle5_ne :
    chromaticThreshold (cycleGraph 5) < 1 / 5 ∧ chromaticThreshold (cycleGraph 5) ≠ 1 / 5 := by
  have := chromaticThreshold_cycle5_le
  exact ⟨by linarith, by intro h; linarith⟩

/-! ## The induced reading (for completeness)

If "`C₅`-free" were read as "no *induced* `C₅`", complete graphs would qualify as test graphs
(they contain no induced `C₅`) with `δ = n - 1` and chromatic number `n`, so the threshold is `1`,
again not `1/5`. -/

/-- Admissible ratios when `H`-free means "no induced copy of `H`". -/
def admissibleInd {k : ℕ} (H : SimpleGraph (Fin k)) : Set ℝ :=
  {d | 0 < d ∧ ∃ K : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ¬ H.IsIndContained G → d * n ≤ G.minDegree → G.Colorable K}

/-- The chromatic threshold under the induced reading. -/
noncomputable def chromaticThresholdInd {k : ℕ} (H : SimpleGraph (Fin k)) : ℝ :=
  sInf (admissibleInd H)

lemma top_not_indContains (n : ℕ) : ¬ (cycleGraph 5).IsIndContained (⊤ : SimpleGraph (Fin n)) := by
  rintro ⟨f⟩
  have h02 : (⊤ : SimpleGraph (Fin n)).Adj (f 0) (f 2) :=
    (top_adj _ _).2 (f.injective.ne (by decide))
  rw [f.map_adj_iff] at h02
  exact absurd h02 (by decide)

lemma one_mem_admissibleInd : (1 : ℝ) ∈ admissibleInd (cycleGraph 5) := by
  refine ⟨one_pos, 0, fun n G _ _ hdeg => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using G.colorable_of_fintype
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have h1 := G.minDegree_le_degree ⟨0, hn⟩
    have h2 := G.degree_lt_card_verts ⟨0, hn⟩
    rw [Fintype.card_fin] at h2
    have : (n : ℝ) ≤ G.minDegree := by linarith
    exact absurd (by exact_mod_cast this : n ≤ G.minDegree) (by omega)

lemma one_le_of_mem_admissibleInd {d : ℝ} (hd : d ∈ admissibleInd (cycleGraph 5)) : 1 ≤ d := by
  obtain ⟨-, K, hK⟩ := hd
  by_contra h
  rw [not_le] at h
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - d))
  have hm' : 1 ≤ (1 - d) * m := by
    rw [div_lt_iff₀ (by linarith)] at hm; linarith
  have hcol := hK (m + K + 1) ⊤ (top_not_indContains _) ?_
  · have := hcol.chromaticNumber_le
    rw [chromaticNumber_top, Fintype.card_fin] at this
    norm_cast at this; omega
  · have : Nonempty (Fin (m + K + 1)) := ⟨0⟩
    have hmin : m + K ≤ (⊤ : SimpleGraph (Fin (m + K + 1))).minDegree :=
      le_minDegree_of_forall_le_degree _ _ fun v => by simp [complete_graph_degree]
    have : ((m + K : ℕ) : ℝ) ≤ ((⊤ : SimpleGraph (Fin (m + K + 1))).minDegree : ℝ) := by
      exact_mod_cast hmin
    push_cast at this ⊢
    nlinarith

/-- Under the induced reading the threshold of `C₅` is exactly `1`, which is not `1/5`. -/
theorem chromaticThresholdInd_cycle5 :
    chromaticThresholdInd (cycleGraph 5) = 1 ∧ chromaticThresholdInd (cycleGraph 5) ≠ 1 / 5 := by
  have h : chromaticThresholdInd (cycleGraph 5) = 1 :=
    le_antisymm (csInf_le ⟨0, fun _ hd => hd.1.le⟩ one_mem_admissibleInd)
      (le_csInf ⟨1, one_mem_admissibleInd⟩ fun _ hd => one_le_of_mem_admissibleInd hd)
  exact ⟨h, by rw [h]; norm_num⟩

end C2158
