import Mathlib

/-!
# Conjecture 00000003482: the order clause is false

The conjecture asserts, among other things, that "the maximal order of deviation" between the
chromatic number `χ(G)` and the fractional chromatic number `χ_f(G)` of an `n`-vertex graph is
`n / (log n)^2`.

We define `maxGap n = max_{G on Fin n} (χ(G) - χ_f(G))` and show that `maxGap` is **not**
`O(n / (log n)^2)` (hence neither `Θ(n / (log n)^2)` nor asymptotically equal to it).  The witness
is the join of `t` copies of the 5-cycle (`n = 5t` vertices), for which
`χ ≥ 3t` and `χ_f ≤ 5t/2`, so `χ - χ_f ≥ t/2 = n/10`.

`χ_f` is defined by its standard linear-programming definition: the infimum of the total weight of
a nonnegative weighting of vertex subsets, supported on independent sets, giving every vertex
total weight at least `1`.
-/

open Finset Filter Asymptotics

namespace C3482

section Defs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A fractional colouring of `G`: a nonnegative weighting `w` of the vertex subsets, vanishing
off the independent sets, such that the sets containing any vertex `v` have total weight `≥ 1`. -/
def IsFracColoring (G : SimpleGraph V) (w : Finset V → ℝ) : Prop :=
  (∀ s, 0 ≤ w s) ∧ (∀ s : Finset V, ¬ G.IsIndepSet (s : Set V) → w s = 0) ∧
    ∀ v, 1 ≤ ∑ s ∈ univ.filter (fun s : Finset V => v ∈ s), w s

/-- The fractional chromatic number `χ_f(G)`: the infimum of the total weight `∑ s, w s` over all
fractional colourings `w` of `G`. -/
noncomputable def fracChromaticNumber (G : SimpleGraph V) : ℝ :=
  sInf ((fun w : Finset V → ℝ => ∑ s, w s) '' {w | IsFracColoring G w})

/-- Sanity check: every finite graph has a fractional colouring (weight `1` on each singleton), so
`χ_f` is an infimum over a nonempty set. -/
theorem fracColoring_nonempty (G : SimpleGraph V) : {w | IsFracColoring G w}.Nonempty := by
  refine ⟨fun s => if s.card = 1 then 1 else 0, fun s => by dsimp only; split_ifs <;> norm_num,
    ?_, ?_⟩
  · intro s hs
    dsimp only
    rw [if_neg]
    rintro h
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
    exact hs (by simp)
  · intro v
    calc (1 : ℝ) = ∑ s ∈ ({{v}} : Finset (Finset V)), if s.card = 1 then (1 : ℝ) else 0 := by
          rw [sum_singleton, if_pos (card_singleton v)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by intro s; simp +contextual)
          (fun s _ _ => by split_ifs <;> norm_num)

theorem fracChromaticNumber_le {G : SimpleGraph V} {w : Finset V → ℝ} (hw : IsFracColoring G w) :
    fracChromaticNumber G ≤ ∑ s, w s := by
  refine csInf_le ⟨0, ?_⟩ ⟨w, hw, rfl⟩
  rintro _ ⟨u, hu, rfl⟩
  exact sum_nonneg fun s _ => hu.1 s

/-- The deviation `χ(G) - χ_f(G)` (for a finite graph `χ(G)` is a natural number). -/
noncomputable def gap (G : SimpleGraph V) : ℝ :=
  (G.chromaticNumber.toNat : ℝ) - fracChromaticNumber G

end Defs

/-- The maximal deviation over all graphs on `n` vertices. -/
noncomputable def maxGap (n : ℕ) : ℝ := ⨆ G : SimpleGraph (Fin n), gap G

/-! ### The join of `t` copies of `C₅` -/

/-- The join of `t` disjoint copies of the 5-cycle: vertex `(i, a)` is position `a` of copy `i`;
vertices of different copies are always adjacent, and inside a copy we use `cycleGraph 5`. -/
def joinC5 (t : ℕ) : SimpleGraph (Fin t × Fin 5) where
  Adj p q := p.1 ≠ q.1 ∨ (p.1 = q.1 ∧ (SimpleGraph.cycleGraph 5).Adj p.2 q.2)
  symm := ⟨by
    intro p q h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (Ne.symm h)
    · exact Or.inr ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨by
    intro p h
    rcases h with h | ⟨_, h2⟩
    · exact h rfl
    · exact (SimpleGraph.cycleGraph 5).loopless.irrefl _ h2⟩

lemma joinC5_adj {t : ℕ} {p q : Fin t × Fin 5} :
    (joinC5 t).Adj p q ↔ p.1 ≠ q.1 ∨ (p.1 = q.1 ∧ (SimpleGraph.cycleGraph 5).Adj p.2 q.2) :=
  Iff.rfl

/-- Any proper colouring of `C₅` uses at least three colours. -/
lemma three_colors {α : Type*} [DecidableEq α] (f : Fin 5 → α)
    (hf : ∀ a b, (SimpleGraph.cycleGraph 5).Adj a b → f a ≠ f b) : 2 < (univ.image f).card := by
  have h01 := hf 0 1 (by decide)
  have h12 := hf 1 2 (by decide)
  have h23 := hf 2 3 (by decide)
  have h34 := hf 3 4 (by decide)
  have h40 := hf 4 0 (by decide)
  rw [Finset.two_lt_card]
  by_cases h02 : f 0 = f 2
  · by_cases h13 : f 1 = f 3
    · exact ⟨f 0, by simp, f 1, by simp, f 4, by simp, h01, Ne.symm h40,
        fun h => h34 (h13.symm.trans h)⟩
    · exact ⟨f 0, by simp, f 1, by simp, f 3, by simp, h01, fun h => h23 (h02.symm.trans h), h13⟩
  · exact ⟨f 0, by simp, f 1, by simp, f 2, by simp, h01, h02, h12⟩

/-- A proper colouring of the join of `t` copies of `C₅` with `k` colours has `3 t ≤ k`. -/
lemma three_mul_le_of_coloring {t k : ℕ} (f : Fin t × Fin 5 → Fin k)
    (hf : ∀ p q, (joinC5 t).Adj p q → f p ≠ f q) : 3 * t ≤ k := by
  let S : Fin t → Finset (Fin k) := fun i => univ.image (fun a => f (i, a))
  have hS : ∀ i, 3 ≤ (S i).card := fun i =>
    three_colors (fun a => f (i, a)) (fun a b h => hf _ _ (joinC5_adj.2 (Or.inr ⟨rfl, h⟩)))
  have hdisj : ((univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint S := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro c hci hcj
    simp only [S, mem_image, mem_univ, true_and] at hci hcj
    obtain ⟨a, rfl⟩ := hci
    obtain ⟨b, hb⟩ := hcj
    exact hf (j, b) (i, a) (joinC5_adj.2 (Or.inl (Ne.symm hij))) hb
  calc 3 * t = ∑ _i : Fin t, 3 := by simp [mul_comm]
    _ ≤ ∑ i, (S i).card := sum_le_sum fun i _ => hS i
    _ = (univ.biUnion S).card := (card_biUnion hdisj).symm
    _ ≤ k := by simpa using card_le_univ (univ.biUnion S)

/-- Vertex relabelling `Fin t × Fin 5 ≃ Fin (t * 5)`. -/
abbrev E (t : ℕ) : Fin t × Fin 5 ≃ Fin (t * 5) := finProdFinEquiv

/-- The witness graph on the vertex set `Fin (t * 5)`: the join of `t` copies of `C₅`. -/
def witness (t : ℕ) : SimpleGraph (Fin (t * 5)) := (joinC5 t).comap (E t).symm

lemma witness_adj {t : ℕ} (p q : Fin t × Fin 5) :
    (witness t).Adj (E t p) (E t q) ↔ (joinC5 t).Adj p q := by
  simp [witness]

/-- `χ(witness t) ≥ 3 t`. -/
theorem chromaticNumber_witness (t : ℕ) : ((3 * t : ℕ) : ℕ∞) ≤ (witness t).chromaticNumber := by
  rw [SimpleGraph.le_chromaticNumber_iff_coloring]
  intro m c
  exact three_mul_le_of_coloring (fun p => c (E t p)) (fun p q h => c.valid ((witness_adj p q).2 h))

/-- The independent pairs `{(i, a), (i, a + 2)}`. -/
def pairs (t : ℕ) : Finset (Finset (Fin (t * 5))) :=
  univ.image fun p : Fin t × Fin 5 => {E t p, E t (p.1, p.2 + 2)}

/-- Weight `1/2` on each pair `{(i, a), (i, a + 2)}`. -/
noncomputable def wt (t : ℕ) (s : Finset (Fin (t * 5))) : ℝ := if s ∈ pairs t then 1 / 2 else 0

lemma pairs_indep {t : ℕ} {s : Finset (Fin (t * 5))} (hs : s ∈ pairs t) :
    (witness t).IsIndepSet (s : Set (Fin (t * 5))) := by
  obtain ⟨⟨i, a⟩, -, rfl⟩ := mem_image.1 hs
  have key : ∀ x : Fin 5, ¬ (SimpleGraph.cycleGraph 5).Adj x (x + 2) ∧
      ¬ (SimpleGraph.cycleGraph 5).Adj (x + 2) x := by decide
  rw [SimpleGraph.IsIndepSet, Finset.coe_pair, Set.pairwise_pair]
  intro _
  rw [witness_adj, witness_adj, joinC5_adj, joinC5_adj]
  simpa using key a

lemma wt_isFracColoring (t : ℕ) : IsFracColoring (witness t) (wt t) := by
  refine ⟨fun s => by unfold wt; split_ifs <;> norm_num, fun s hs => ?_, fun v => ?_⟩
  · unfold wt
    rw [if_neg]
    exact fun h => hs (pairs_indep h)
  · obtain ⟨⟨i, a⟩, rfl⟩ := (E t).surjective v
    let s1 : Finset (Fin (t * 5)) := {E t (i, a), E t (i, a + 2)}
    let s2 : Finset (Fin (t * 5)) := {E t (i, a + 3), E t (i, a + 3 + 2)}
    have h32 : a + 3 + 2 = a := (by decide : ∀ x : Fin 5, x + 3 + 2 = x) a
    have hs1 : s1 ∈ pairs t := mem_image.2 ⟨(i, a), mem_univ _, rfl⟩
    have hs2 : s2 ∈ pairs t := mem_image.2 ⟨(i, a + 3), mem_univ _, rfl⟩
    have hne : s1 ≠ s2 := by
      intro h
      have hmem : E t (i, a + 3) ∈ s1 := by rw [h]; simp [s2]
      simp only [s1, mem_insert, mem_singleton, (E t).injective.eq_iff, Prod.mk.injEq,
        true_and] at hmem
      exact (by decide : ∀ x : Fin 5, ¬ (x + 3 = x ∨ x + 3 = x + 2)) a hmem
    have hsub : ({s1, s2} : Finset (Finset (Fin (t * 5)))) ⊆
        univ.filter (fun s => E t (i, a) ∈ s) := by
      intro s hs
      simp only [mem_insert, mem_singleton] at hs
      rcases hs with rfl | rfl
      · simp [s1]
      · simp [s2, h32]
    calc (1 : ℝ) = ∑ s ∈ ({s1, s2} : Finset (Finset (Fin (t * 5)))), wt t s := by
          rw [sum_pair hne]; simp only [wt, if_pos hs1, if_pos hs2]; norm_num
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
          (fun s _ _ => by unfold wt; split_ifs <;> norm_num)

/-- `χ_f(witness t) ≤ 5 t / 2`. -/
theorem fracChromaticNumber_witness (t : ℕ) :
    fracChromaticNumber (witness t) ≤ (t * 5 : ℝ) / 2 := by
  refine (fracChromaticNumber_le (wt_isFracColoring t)).trans ?_
  have hsum : ∑ s, wt t s = ((pairs t).card : ℝ) * (1 / 2) := by
    simp only [wt]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
  have hcard : ((pairs t).card : ℝ) ≤ t * 5 := by
    have := card_image_le (s := (univ : Finset (Fin t × Fin 5)))
      (f := fun p : Fin t × Fin 5 => ({E t p, E t (p.1, p.2 + 2)} : Finset (Fin (t * 5))))
    simp only [card_univ, Fintype.card_prod, Fintype.card_fin] at this
    exact_mod_cast this
  rw [hsum]
  linarith

/-- The witness on `n = 5 t` vertices has deviation `χ - χ_f ≥ t / 2 = n / 10`. -/
theorem gap_witness (t : ℕ) : (t : ℝ) / 2 ≤ gap (witness t) := by
  have hfin : (witness t).chromaticNumber ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) SimpleGraph.chromaticNumber_le_card
  have h1 : 3 * t ≤ (witness t).chromaticNumber.toNat := by
    simpa using ENat.toNat_le_toNat (chromaticNumber_witness t) hfin
  have h2 : ((3 * t : ℕ) : ℝ) ≤ ((witness t).chromaticNumber.toNat : ℝ) := by exact_mod_cast h1
  have h3 := fracChromaticNumber_witness t
  unfold gap
  push_cast at h2
  linarith

theorem maxGap_ge (t : ℕ) : (t : ℝ) / 2 ≤ maxGap (t * 5) :=
  (gap_witness t).trans (le_ciSup (Set.finite_range _).bddAbove (witness t))

/-! ### Asymptotics -/

/-- `maxGap` is not `O(f)` for any `f = o(n)`. -/
theorem not_isBigO_of_isLittleO {f : ℕ → ℝ} (hf : f =o[atTop] (fun n : ℕ => (n : ℝ))) :
    ¬ maxGap =O[atTop] f := by
  intro h
  have h1 := (h.trans_isLittleO hf).comp_tendsto
    (tendsto_atTop_mono (fun t : ℕ => (by omega : t ≤ t * 5)) tendsto_id)
  obtain ⟨t, ht, ht1⟩ :=
    ((h1.def (by norm_num : (0 : ℝ) < 1 / 20)).and (eventually_ge_atTop 1)).exists
  simp only [Function.comp_apply, Real.norm_eq_abs, Nat.cast_mul, Nat.cast_ofNat] at ht
  have h2 := maxGap_ge t
  have h3 : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have h4 := le_abs_self (maxGap (t * 5))
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ t * 5)] at ht
  linarith

lemma div_log_sq_isLittleO :
    (fun n : ℕ => (n : ℝ) / Real.log n ^ 2) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h0 : (fun n : ℕ => (Real.log n ^ 2)⁻¹) =o[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 (tendsto_inv_atTop_zero.comp hlog)
  have := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO h0
  simpa [div_eq_mul_inv] using this

/-- **Main theorem.** The maximal deviation `max_{|V(G)| = n} (χ(G) - χ_f(G))` is not
`O(n / (log n)^2)`. -/
theorem maxGap_not_isBigO :
    ¬ maxGap =O[atTop] (fun n : ℕ => (n : ℝ) / Real.log n ^ 2) :=
  not_isBigO_of_isLittleO div_log_sq_isLittleO

/-- Consequently it is not of exact order `Θ(n / (log n)^2)`. -/
theorem maxGap_not_isTheta :
    ¬ maxGap =Θ[atTop] (fun n : ℕ => (n : ℝ) / Real.log n ^ 2) :=
  fun h => maxGap_not_isBigO h.isBigO

/-- Nor is it asymptotically equal to `n / (log n)^2`. -/
theorem maxGap_not_isEquivalent :
    ¬ maxGap ~[atTop] (fun n : ℕ => (n : ℝ) / Real.log n ^ 2) :=
  fun h => maxGap_not_isBigO h.isBigO

end C3482
