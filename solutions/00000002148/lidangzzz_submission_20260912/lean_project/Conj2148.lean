/-
  Batch 3 (parts 1–3): walk infrastructure and the two-path lemma
  ==============================================================

  Self-contained Lean infrastructure toward machine-checked disproofs of
  TLMC #2147 and #2148 (cage order claims), culminating in:

    `exists_cycle_of_two_paths` — two distinct u→v paths of lengths a, b
    create a cycle of length ≤ a + b.

  No `sorry`. Toolchain: leanprover/lean4:v4.31.0, Mathlib v4.31.0.
-/

import Mathlib

namespace TLMCBatch3

open SimpleGraph
open SimpleGraph.Walk

variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-! ### List helpers -/

theorem mem_of_head?_eq_some {α : Type} {l : List α} {z : α}
    (h : l.head? = some z) : z ∈ l := by
  cases l with
  | nil => simp at h
  | cons a t =>
      simp only [List.head?] at h
      have : a = z := by simpa using h
      exact this ▸ List.mem_cons_self

/-- The head of a filtered list occurs in the base list no later than any
    other member of the filtered list. -/
theorem idxOf_le_of_head_filter {α : Type} [BEq α] [LawfulBEq α]
    (f : α → Bool) (l : List α) {z w : α}
    (hz : (l.filter f).head? = some z) (hw : w ∈ l.filter f) :
    l.idxOf z ≤ l.idxOf w := by
  have hzmem : z ∈ l.filter f := mem_of_head?_eq_some hz
  induction l with
  | nil => simp at hzmem
  | cons a l' ih =>
    by_cases hfa : f a
    · rw [List.filter_cons_of_pos hfa] at hz
      have hza : z = a := ((by simpa using hz : a = z)).symm
      rw [hza]; simp
    · rw [List.filter_cons_of_neg hfa] at hz hw hzmem
      have key : ∀ x : α, x ≠ a → (a :: l').idxOf x = l'.idxOf x + 1 := by
        intro x hx
        have hne : ¬ (a == x) := by
          simp only [beq_iff_eq]
          exact fun hc => hx hc.symm
        simp only [List.idxOf, List.findIdx_cons, hne, cond_false]
      have hzne : z ≠ a := by
        intro heq
        rw [heq] at hzmem
        exact hfa (List.mem_filter.1 hzmem).2
      have hwne : w ≠ a := by
        intro heq
        rw [heq] at hw
        exact hfa (List.mem_filter.1 hw).2
      rw [key w hwne, key z hzne]
      exact Nat.succ_le_succ (ih hz hw hzmem)


theorem mem_take_iff_idxOf {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    ∀ {n : ℕ}, a ∈ l → (a ∈ l.take n ↔ l.idxOf a < n) := by
  induction l with
  | nil => intro n ha; simp at ha
  | cons b l' ih =>
    intro n ha
    by_cases hb : a = b
    · subst hb
      cases n with
      | zero => simp
      | succ n' => simp
    · have hmem : a ∈ l' := (List.mem_cons.1 ha).resolve_left hb
      have hidx : (b :: l').idxOf a = l'.idxOf a + 1 := by
        have hne : ¬ (b == a) := by
          simp only [beq_iff_eq]
          exact fun hc => hb hc.symm
        simp only [List.idxOf, List.findIdx_cons, hne, cond_false]
      cases n with
      | zero => simp
      | succ n' =>
          rw [List.take_succ_cons, List.mem_cons, hidx]
          constructor
          · intro h
            rcases h with h | h
            · exact absurd h hb
            · exact Nat.succ_lt_succ_iff.mpr ((ih hmem).1 h)
          · intro h
            exact Or.inr ((ih hmem).2 (Nat.succ_lt_succ_iff.mp h))

omit [DecidableEq V] in
/-- Congruence for `List.head`, retyping the nonempty proof along an equality of lists. -/
theorem head_congr' {l l' : List V} (h : l = l') (hl : l ≠ []) :
    l.head hl = l'.head (h ▸ hl) := by
  subst h
  rfl

omit [DecidableEq V] in
/-- Two walks with the same endpoints and the same support are equal:
    a walk is determined by its vertex sequence. -/
theorem Walk.eq_of_support_eq : ∀ {u v : V} (p : G.Walk u v) (q : G.Walk u v),
    p.support = q.support → p = q := by
  intro u v p
  induction p with
  | nil =>
      intro q h
      cases q with
      | nil => rfl
      | cons h' q' =>
          simp only [Walk.support_nil, Walk.support_cons, List.cons.injEq] at h
          exact absurd h.2.symm q'.support_ne_nil
  | cons hp p' ih =>
      intro q h
      cases q with
      | nil =>
          simp only [Walk.support_nil, Walk.support_cons, List.cons.injEq] at h
          exact absurd h.2 p'.support_ne_nil
      | cons hq q' =>
          have hsup : p'.support = q'.support := by
            simp only [Walk.support_cons, List.cons.injEq] at h
            exact h.2
          have hw : _ = _ :=
            (p'.head_support).symm.trans
              ((head_congr' hsup (Walk.support_ne_nil p')).trans q'.head_support)
          subst hw
          rw [ih q' hsup]

/-! ### An edge of a path whose endpoints are only the endpoints of the path -/

omit [DecidableEq V] in
/-- If a path `p : u → z` contains an edge whose endpoints both lie in `{u, z}`,
    then `p` consists of that single edge. -/
theorem length_eq_one_of_adj_bounded {u z : V} {p : G.Walk u z} (hp : p.IsPath)
    {a b : V} (he : s(a, b) ∈ p.edges) (ha : a = u ∨ a = z) (hb : b = u ∨ b = z) :
    p.length = 1 := by
  cases p with
  | nil => simp at he
  | cons hadj p' =>
      rename_i w
      have hu : u ∉ p'.support := ((cons_isPath_iff _ _).mp hp).2
      rw [Walk.edges_cons] at he
      rcases List.mem_cons.1 he with h1 | h2
      · rcases Sym2.eq_iff.mp h1 with ⟨r1, r2⟩ | ⟨r1, r2⟩
        · rcases hb with h3 | h3
          · exact absurd (h3.symm.trans r2) hadj.ne
          · subst r1; subst r2; subst h3
            have hnil : p'.Nil := isPath_iff_nil.mp hp.of_cons
            simp [length_eq_zero_iff.mpr hnil]
        · rcases ha with h3 | h3
          · exact absurd (h3.symm.trans r1) hadj.ne
          · subst r1; subst r2; subst h3
            have hnil : p'.Nil := isPath_iff_nil.mp hp.of_cons
            simp [length_eq_zero_iff.mpr hnil]
      · have hadjab : G.Adj a b := p'.adj_of_mem_edges h2
        have hma : a ∈ p'.support :=
          Walk.mem_support_of_mem_edges h2 (Sym2.mem_iff.2 (Or.inl rfl))
        have hmb : b ∈ p'.support :=
          Walk.mem_support_of_mem_edges h2 (Sym2.mem_iff.2 (Or.inr rfl))
        rcases ha with h3 | h3
        · exact absurd (h3 ▸ hma) hu
        · rcases hb with h4 | h4
          · exact absurd (h4 ▸ hmb) hu
          · exact absurd (h3.trans h4.symm) hadjab.ne

/-! ### The two-path lemma -/

/-- **Two-path lemma.**  Two distinct paths with the same endpoints force a cycle
    whose length is at most the sum of the two path lengths. -/
theorem exists_cycle_of_two_paths :
    ∀ (n : ℕ) {u v : V} (p : G.Walk u v), p.length ≤ n → ∀ (q : G.Walk u v),
    p.IsPath → q.IsPath → p ≠ q →
    ∃ (t : V) (c : G.Walk t t), c.IsCycle ∧ c.length ≤ p.length + q.length := by
  intro n
  induction n with
  | zero =>
      intro u v p hlen q hpp hqp hpne
      cases p with
      | nil =>
          obtain rfl := (isPath_iff_nil.mp hqp).eq_nil
          exact absurd rfl hpne
      | cons hp p' =>
          have h0 : (Walk.cons hp p').length = 0 := Nat.le_zero.1 hlen
          simp [Walk.length_cons] at h0
  | succ n ih =>
      intro u v p hlen q hpp hqp hpne
      cases p with
      | nil =>
          obtain rfl := (isPath_iff_nil.mp hqp).eq_nil
          exact absurd rfl hpne
      | cons hp p' =>
          cases q with
          | nil => exact absurd (isPath_iff_nil.mp hpp) not_nil_cons
          | cons hq q' =>
              rename_i w₁ w₂
              have hpp' : p'.IsPath := hpp.of_cons
              have hqp' : q'.IsPath := hqp.of_cons
              by_cases hw : w₁ = w₂
              · subst hw
                have hp'ne : p' ≠ q' := by
                  intro h
                  exact hpne (by subst h; rfl)
                have hle : p'.length ≤ n := by
                  have e0 := Walk.length_cons hp p'
                  rw [e0] at hlen
                  exact Nat.le_of_succ_le_succ hlen
                obtain ⟨t, c, hcyc, hclen⟩ := ih p' hle q' hpp' hqp' hp'ne
                refine ⟨t, c, hcyc, ?_⟩
                have e1 : (Walk.cons hp p').length = p'.length + 1 := Walk.length_cons hp p'
                have e2 : (Walk.cons hq q').length = q'.length + 1 := Walk.length_cons hq q'
                lia
              · -- the two paths diverge immediately; build a cycle at their first common vertex
                have huv : u ≠ v := by
                  intro heq; subst heq
                  exact not_nil_cons (isPath_iff_nil.mp hpp)
                have hvt : v ∈ (Walk.cons hp p').support.tail := by
                  have hv : v ∈ (Walk.cons hp p').support := (Walk.cons hp p').end_mem_support
                  rw [Walk.support_cons, List.mem_cons] at hv
                  rcases hv with h | h
                  · exact absurd h.symm huv
                  · exact h
                have hvq : v ∈ (Walk.cons hq q').support :=
                  (Walk.cons hq q').end_mem_support
                obtain ⟨z, hz⟩ : ∃ z,
                    ((Walk.cons hp p').support.tail.filter
                      (· ∈ (Walk.cons hq q').support)).head? = some z := by
                  have hvF : v ∈ (Walk.cons hp p').support.tail.filter
                      (· ∈ (Walk.cons hq q').support) :=
                    List.mem_filter.2 ⟨hvt, by simp only [decide_eq_true_eq]; exact hvq⟩
                  by_cases hF :
                      (Walk.cons hp p').support.tail.filter
                        (· ∈ (Walk.cons hq q').support) = []
                  · rw [hF] at hvF; simp at hvF
                  · obtain ⟨z, hh⟩ := Option.ne_none_iff_exists.mp
                      (fun hnone => hF (List.head?_eq_none_iff.mp hnone))
                    exact ⟨z, hh.symm⟩
                have hzF : z ∈ (Walk.cons hp p').support.tail.filter
                    (· ∈ (Walk.cons hq q').support) := mem_of_head?_eq_some hz
                have hzt : z ∈ (Walk.cons hp p').support.tail := (List.mem_filter.1 hzF).1
                have hzq : z ∈ (Walk.cons hq q').support :=
                  of_decide_eq_true (List.mem_filter.1 hzF).2
                have hzp : z ∈ (Walk.cons hp p').support := List.mem_cons_of_mem _ hzt
                have hznu : z ≠ u := by
                  intro heq; subst heq
                  have hn : (Walk.cons hp p').support.Nodup := hpp.support_nodup
                  rw [Walk.support_cons, List.nodup_cons] at hn
                  exact hn.1 hzt
                have hz' : z ∈ p'.support := hzt
                have hzq' : z ∈ q'.support := by
                  rcases List.mem_cons.1 hzq with h | h
                  · exact absurd h hznu
                  · exact h
                -- split both walks at their first common vertex `z`
                set p₁ : G.Walk u z := (Walk.cons hp p').takeUntil z hzp
                set q₁ : G.Walk u z := (Walk.cons hq q').takeUntil z hzq
                have hp₁path : p₁.IsPath :=
                  isPath_of_isSubwalk (isSubwalk_takeUntil _ hzp) hpp
                have hq₁path : q₁.IsPath :=
                  isPath_of_isSubwalk (isSubwalk_takeUntil _ hzq) hqp
                have hp₁cons : p₁ = Walk.cons hp (p'.takeUntil z hz') :=
                  takeUntil_cons hz' (fun hc => hznu hc.symm) hp
                have hq₁cons : q₁ = Walk.cons hq (q'.takeUntil z hzq') :=
                  takeUntil_cons hzq' (fun hc => hznu hc.symm) hq
                have hlen₁ : p₁.length = (Walk.cons hp p').support.idxOf z :=
                  length_takeUntil _ hzp
                have hsup₁ : p₁.support
                    = (Walk.cons hp p').support.take ((Walk.cons hp p').support.idxOf z + 1) := by
                  have hpre : p₁.support <+: (Walk.cons hp p').support :=
                    support_takeUntil_prefix_support _ hzp
                  have hln : p₁.support.length
                      = (Walk.cons hp p').support.idxOf z + 1 := by
                    rw [Walk.length_support, hlen₁]
                  rw [← hln]
                  exact List.prefix_iff_eq_take.mp hpre
                -- the interior of `p₁` avoids `q₁`
                have keyB : ∀ x ∈ p₁.support, x ∈ q₁.support → x ≠ u → x ≠ z → False := by
                  intro x hx₁ hxq₁ hxu hxz
                  have hxLp : x ∈ (Walk.cons hp p').support :=
                    support_takeUntil_subset_support _ hzp hx₁
                  have hxt : x ∈ (Walk.cons hp p').support.tail := by
                    rcases List.mem_cons.1 hxLp with h | h
                    · exact absurd h hxu
                    · exact h
                  have hxF : x ∈ (Walk.cons hp p').support.tail.filter
                      (· ∈ (Walk.cons hq q').support) :=
                    List.mem_filter.2 ⟨hxt, by
                      simp only [decide_eq_true_eq]
                      exact support_takeUntil_subset_support _ hzq hxq₁⟩
                  have hnod2 : (Walk.cons hp p').support.Nodup := hpp.support_nodup
                  rw [Walk.support_cons, List.nodup_cons] at hnod2
                  have hidxF : ∀ y ∈ (Walk.cons hp p').support.tail,
                      (Walk.cons hp p').support.idxOf y
                        = (Walk.cons hp p').support.tail.idxOf y + 1 := by
                    intro y hy
                    have hne : ¬(u == y) := by
                      simp only [beq_iff_eq]
                      exact fun hc => hnod2.1 (hc ▸ hy)
                    simp only [Walk.support_cons, List.idxOf, List.findIdx_cons, hne,
                      cond_false, List.tail_cons]
                  have hmin : (Walk.cons hp p').support.idxOf z
                      ≤ (Walk.cons hp p').support.idxOf x := by
                    rw [hidxF z hzt, hidxF x hxt]
                    exact Nat.succ_le_succ (idxOf_le_of_head_filter _ _ hz hxF)
                  have hxi : (Walk.cons hp p').support.idxOf x
                      < (Walk.cons hp p').support.idxOf z + 1 :=
                    (mem_take_iff_idxOf hxLp).1 (by rw [← hsup₁]; exact hx₁)
                  exact hxz ((List.idxOf_inj hxLp).1
                    (Nat.le_antisymm (Nat.lt_succ_iff.1 hxi) hmin))
                have keyV : ∀ x ∈ p₁.support, x ∈ q₁.support → x = u ∨ x = z := by
                  intro x hx₁ hxq₁
                  by_cases hxu : x = u
                  · exact Or.inl hxu
                  · exact Or.inr (by_contra fun hxz => keyB x hx₁ hxq₁ hxu hxz)
                -- edges of `p₁` and `q₁` are disjoint
                have hedges : ∀ e ∈ p₁.edges, e ∉ q₁.edges := by
                  intro e he₁ he₂
                  obtain ⟨d, hd, hde⟩ := List.mem_map.mp he₁
                  have hmk : d.edge = s(d.fst, d.snd) :=
                    (dart_edge_eq_mk'_iff').2 (Or.inl ⟨rfl, rfl⟩)
                  have hs₁ : s(d.fst, d.snd) ∈ p₁.edges := by
                    rw [← hmk]; exact List.mem_map.2 ⟨d, hd, rfl⟩
                  have hs₂ : s(d.fst, d.snd) ∈ q₁.edges := by
                    rw [← hmk]
                    rw [← hde] at he₂
                    exact he₂
                  have hadj : G.Adj d.fst d.snd := p₁.adj_of_mem_edges hs₁
                  have hf₁ : d.fst ∈ p₁.support :=
                    Walk.mem_support_of_mem_edges hs₁ (Sym2.mem_iff.2 (Or.inl rfl))
                  have hf₂ : d.snd ∈ p₁.support :=
                    Walk.mem_support_of_mem_edges hs₁ (Sym2.mem_iff.2 (Or.inr rfl))
                  have hfq₁ : d.fst ∈ q₁.support :=
                    Walk.mem_support_of_mem_edges hs₂ (Sym2.mem_iff.2 (Or.inl rfl))
                  have hfq₂ : d.snd ∈ q₁.support :=
                    Walk.mem_support_of_mem_edges hs₂ (Sym2.mem_iff.2 (Or.inr rfl))
                  have hfab : d.fst = u ∨ d.fst = z := keyV d.fst hf₁ hfq₁
                  have hsab : d.snd = u ∨ d.snd = z := keyV d.snd hf₂ hfq₂
                  have hbound := length_eq_one_of_adj_bounded hp₁path hs₁ hfab hsab
                  have hbound' := length_eq_one_of_adj_bounded hq₁path hs₂ hfab hsab
                  rw [hp₁cons, Walk.length_cons] at hbound
                  rw [hq₁cons, Walk.length_cons] at hbound'
                  have hn₁ : (p'.takeUntil z hz').Nil :=
                    length_eq_zero_iff.mp (by omega)
                  have hn₂ : (q'.takeUntil z hzq').Nil :=
                    length_eq_zero_iff.mp (by omega)
                  have hw₁z : w₁ = z :=
                    (isPath_of_isSubwalk (isSubwalk_takeUntil p' hz') hpp').nil_iff_eq.mp hn₁
                  have hw₂z : w₂ = z :=
                    (isPath_of_isSubwalk (isSubwalk_takeUntil q' hzq') hqp').nil_iff_eq.mp hn₂
                  exact hw (hw₁z.trans hw₂z.symm)
                -- the cycle `p₁ ++ q₁.reverse`
                refine ⟨u, Walk.append p₁ q₁.reverse, ?_, ?_⟩
                · rw [isCycle_def]
                  refine ⟨?_, ?_, ?_⟩
                  · constructor
                    rw [edges_append, edges_reverse]
                    refine List.nodup_append'.2 ⟨hp₁path.isTrail.edges_nodup, ?_, ?_⟩
                    · rw [List.nodup_reverse]
                      exact hq₁path.isTrail.edges_nodup
                    · intro e he₁ he₂r
                      rw [List.mem_reverse] at he₂r
                      exact hedges e he₁ he₂r
                  · intro hc
                    have h0 : (Walk.append p₁ q₁.reverse).length = 0 := by
                      rw [hc]; simp
                    rw [Walk.length_append, Walk.length_reverse] at h0
                    rw [hp₁cons, Walk.length_cons] at h0
                    simp at h0
                  · have hsa : (Walk.append p₁ q₁.reverse).support
                        = p₁.support ++ (q₁.support.reverse).tail := by
                      rw [support_append, support_reverse]
                    rw [hsa, List.tail_append_of_ne_nil (Walk.support_ne_nil p₁)]
                    refine List.nodup_append'.2 ⟨hp₁path.support_nodup.tail, ?_, ?_⟩
                    · exact (List.nodup_reverse.2 hq₁path.support_nodup).tail
                    · intro x hx₁ hx₂r
                      have hxq₁ : x ∈ q₁.support := by
                        rw [← List.mem_reverse]
                        exact List.tail_subset _ hx₂r
                      have hxz : x ≠ z := by
                        intro heq
                        rw [heq] at hx₂r
                        rw [List.tail_reverse, List.mem_reverse] at hx₂r
                        have hcat : q₁.support.dropLast ++ [z] = q₁.support :=
                          (congrArg (fun z' => q₁.support.dropLast ++ [z'])
                            (Walk.getLast_support q₁)).symm.trans
                            (List.dropLast_concat_getLast (Walk.support_ne_nil q₁))
                        have hn : (q₁.support.dropLast ++ [z]).Nodup := by
                          rw [hcat]; exact hq₁path.support_nodup
                        exact ((List.nodup_append'.1 hn).2.2) hx₂r (by simp)
                      have hxu : x ≠ u := by
                        intro heq
                        rw [heq, hp₁cons, Walk.support_cons, List.tail_cons] at hx₁
                        have hn : p₁.support.Nodup := hp₁path.support_nodup
                        rw [hp₁cons, Walk.support_cons, List.nodup_cons] at hn
                        exact hn.1 hx₁
                      exact keyB x (List.mem_of_mem_tail hx₁) hxq₁ hxu hxz
                · rw [Walk.length_append, Walk.length_reverse]
                  exact Nat.add_le_add (length_takeUntil_le_length _ hzp)
                    (length_takeUntil_le_length _ hzq)

/-! ### Moore-bound infrastructure -/

section Moore

variable [Fintype V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Two paths with the same endpoints whose total length is below the girth coincide. -/
theorem eq_of_two_paths_of_lt_girth {x y : V} {p q : G.Walk x y}
    (hpp : p.IsPath) (hqp : q.IsPath) (hlen : p.length + q.length < G.girth) : p = q := by
  by_contra hpq
  obtain ⟨t, c, hcyc, hclen⟩ :=
    exists_cycle_of_two_paths p.length p (Nat.le_refl _) q hpp hqp hpq
  exact Nat.lt_irrefl G.girth
    (((G.girth_le_length hcyc).trans hclen).trans_lt hlen)

omit [Fintype V] in
/-- The cardinality of a disjoint indexed union of finsets. -/
theorem card_disj_bUnion {ι : Type} [DecidableEq ι] {s : Finset ι} {t : ι → Finset V}
    (hdis : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (t i) (t i')) :
    (Finset.biUnion s t).card = ∑ i ∈ s, (t i).card := by
  classical
  revert hdis
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      intro hdis
      have hda : Disjoint (t a) (Finset.biUnion s t) := by
        rw [Finset.disjoint_left]
        intro w hw hwb
        rcases Finset.mem_biUnion.1 hwb with ⟨i, hi, h2⟩
        exact (Finset.disjoint_left.mp
          (hdis a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
            (fun heq => ha (heq ▸ hi)))) hw h2
      rw [Finset.biUnion_insert, Finset.sum_insert ha, Finset.card_union_of_disjoint hda,
        ih fun i hi i' hi' hne => hdis i (Finset.mem_insert_of_mem hi)
          i' (Finset.mem_insert_of_mem hi') hne]

section SphereDef

variable (G)

/-- The sphere of radius `j` around `x`: the vertices at distance exactly `j`. -/
noncomputable def sphere (x : V) (j : ℕ) : Finset V :=
  Finset.univ.filter (fun y => G.dist x y = j)

end SphereDef

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem mem_sphere {x y : V} {j : ℕ} : y ∈ sphere G x j ↔ G.dist x y = j := by
  show y ∈ Finset.univ.filter (fun y => G.dist x y = j) ↔ G.dist x y = j
  exact ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ y, h⟩⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Vertices strictly inside a geodesic are strictly closer to the start. -/
theorem dist_lt_of_mem_support {x y : V} {q : G.Walk x y} (hq : q.length = G.dist x y)
    {w : V} (hw : w ∈ q.support) (hwne : w ≠ y) : G.dist x w < q.length := by
  have h1 : (q.takeUntil w hw).length = G.dist x w :=
    length_eq_dist_of_subwalk hq (isSubwalk_takeUntil q hw)
  have h2 : (q.takeUntil w hw).length + (q.dropUntil w hw).length = q.length := by
    have e := congrArg Walk.length (q.take_spec hw)
    rwa [Walk.length_append] at e
  have h3 : 1 ≤ (q.dropUntil w hw).length := by
    by_contra h0
    have h0' : (q.dropUntil w hw).length = 0 := by omega
    exact hwne (length_eq_zero_iff.mp h0').eq
  omega

omit [DecidableEq V] in
/-- The sphere of radius one is the neighborhood, so its size is the degree. -/
theorem card_sphere_one (x : V) : (sphere G x 1).card = G.degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have heq : sphere G x 1 = G.neighborFinset x := Finset.ext fun y =>
    (mem_sphere.trans (dist_eq_one_iff_adj)).trans (G.mem_neighborFinset x y).symm
  rw [heq]

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- A geodesic exists as a path for reachable vertices. -/
theorem exists_path_dist {x y : V} {j : ℕ} (hy : G.dist x y = j) (hre : G.Reachable x y) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.length = j := by
  obtain ⟨p, hp⟩ := hre.exists_walk_length_eq_dist
  exact ⟨p, p.isPath_of_length_eq_dist hp, hp.trans hy⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Concatenating an edge from the end of a geodesic to a vertex that is at least
    as far from the start yields a path. -/
theorem isPath_concat {x y w : V} {q : G.Walk x y} (hq : q.length = G.dist x y)
    (hadj : G.Adj y w) (hle : q.length ≤ G.dist x w) : (q.concat hadj).IsPath := by
  refine (concat_isPath_iff hadj).2 ⟨q.isPath_of_length_eq_dist hq, ?_⟩
  intro hmem
  have h1 := dist_lt_of_mem_support hq hmem hadj.ne.symm
  omega

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
theorem getLast?_support {x y : V} (q : G.Walk x y) : q.support.getLast? = some y := by
  induction q with
  | nil => simp [Walk.support_nil]
  | cons h p ih =>
      simp only [Walk.support_cons, List.getLast?_cons]
      rw [ih]
      simp

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in
/-- Concatenated walks with different final vertices are different. -/
theorem concat_ne_of_ne {x y w₁ w₂ : V} {q₁ : G.Walk x w₁} {q₂ : G.Walk x w₂}
    (hne : w₁ ≠ w₂) (ha₁ : G.Adj w₁ y) (ha₂ : G.Adj w₂ y) :
    q₁.concat ha₁ ≠ q₂.concat ha₂ := by
  intro he
  apply hne
  have e : (q₁.concat ha₁).support = (q₂.concat ha₂).support := by rw [he]
  rw [Walk.support_concat, Walk.support_concat, List.append_left_inj] at e
  have e5 := congrArg List.getLast? e
  rw [getLast?_support q₁, getLast?_support q₂, Option.some.injEq] at e5
  exact e5

omit [Fintype V] [DecidableRel G.Adj] in
/-- No two neighbors of a vertex at distance `j ≥ 1` both sit at distance `j - 1`. -/
theorem no_two_adj_lower_sphere {x y : V} {j : ℕ} (hj1 : 1 ≤ j) (hy : G.dist x y = j)
    {w₁ w₂ : V} (hne : w₁ ≠ w₂) (h1 : G.Adj w₁ y) (hd1 : G.dist x w₁ = j - 1)
    (h2 : G.Adj w₂ y) (hd2 : G.dist x w₂ = j - 1)
    (hg : 2 * j < G.girth) : False := by
  have hrey : G.Reachable x y := Reachable.of_dist_ne_zero (by rw [hy]; omega)
  have hre1 : G.Reachable x w₁ := hrey.trans h1.symm.reachable
  have hre2 : G.Reachable x w₂ := hrey.trans h2.symm.reachable
  obtain ⟨q₁, hp₁, hl₁⟩ := exists_path_dist hd1 hre1
  obtain ⟨q₂, hp₂, hl₂⟩ := exists_path_dist hd2 hre2
  have hR1 : (q₁.concat h1).IsPath :=
    isPath_concat (hl₁.trans hd1.symm) h1 (by omega)
  have hR2 : (q₂.concat h2).IsPath :=
    isPath_concat (hl₂.trans hd2.symm) h2 (by omega)
  exact (concat_ne_of_ne hne h1 h2) (eq_of_two_paths_of_lt_girth hR1 hR2
    (by rw [Walk.length_concat, Walk.length_concat, hl₁, hl₂]; omega))

omit [Fintype V] [DecidableRel G.Adj] in
/-- A neighbor of a vertex at distance `j ≥ 1` cannot sit at the same distance `j`
    (when the girth is large enough). -/
theorem no_adj_same_sphere {x y : V} {j : ℕ} (hj1 : 1 ≤ j) (hy : G.dist x y = j)
    {w : V} (hw : G.Adj y w) (hwj : G.dist x w = j) (hg : 2 * j + 1 < G.girth) : False := by
  have hrey : G.Reachable x y := Reachable.of_dist_ne_zero (by rw [hy]; omega)
  have hrew : G.Reachable x w := hrey.trans hw.reachable
  obtain ⟨qw, hqw, hql⟩ := exists_path_dist hwj hrew
  obtain ⟨qy, hqy, hqyl⟩ := exists_path_dist hy hrey
  have hR : (qw.concat hw.symm).IsPath :=
    isPath_concat (hql.trans hwj.symm) hw.symm (by omega)
  have hne : qw.concat hw.symm ≠ qy := by
    intro he
    have e := congrArg Walk.length he
    rw [Walk.length_concat, hql, hqyl] at e
    omega
  exact hne (eq_of_two_paths_of_lt_girth hR hqy
    (by rw [Walk.length_concat, hql, hqyl]; omega))

omit [Fintype V] [DecidableRel G.Adj] in
/-- Every vertex at distance `j ≥ 1` has a neighbor at distance `j - 1`
    (the geodesic predecessor). -/
theorem exists_pred {x y : V} {j : ℕ} (hj1 : 1 ≤ j) (hy : G.dist x y = j) :
    ∃ z : V, G.Adj z y ∧ G.dist x z + 1 = j := by
  have hrey : G.Reachable x y := Reachable.of_dist_ne_zero (by rw [hy]; omega)
  obtain ⟨p, hpp, hpl⟩ := exists_path_dist hy hrey
  cases hpr : p.reverse with
  | nil =>
      exfalso
      have e := congrArg Walk.length hpr
      have e0 : p.length = 0 := by simpa [Walk.length_reverse] using e
      omega
  | cons hq r =>
      rename_i z
      refine ⟨z, hq.symm, ?_⟩
      have hz : z ∈ p.support := by
        have h1 : z ∈ r.support := r.start_mem_support
        have h2 : z ∈ (Walk.cons hq r).support := List.mem_cons_of_mem _ h1
        rw [← hpr] at h2
        rwa [Walk.support_reverse, List.mem_reverse] at h2
      have h1 : (p.takeUntil z hz).length = G.dist x z :=
        length_eq_dist_of_subwalk (hpl.trans hy.symm) (isSubwalk_takeUntil p hz)
      have h2 : (p.takeUntil z hz).length + (p.dropUntil z hz).length = p.length := by
        have e := congrArg Walk.length (p.take_spec hz)
        rwa [Walk.length_append] at e
      have h3 : 1 ≤ (p.dropUntil z hz).length := by
        by_contra h0
        have h0' : (p.dropUntil z hz).length = 0 := by omega
        exact hq.symm.ne (length_eq_zero_iff.mp h0').eq
      have htri : G.dist x y ≤ G.dist x z + G.dist z y :=
        (hq.symm.reachable).dist_triangle_right x
      have hzy : G.dist z y = 1 := dist_eq_one_iff_adj.mpr hq.symm
      omega

section FiberDef

variable (G)

/-- The forward fiber of `y ∈ S j`: neighbors of `y` lying on `S (j+1)`. -/
noncomputable def fiber (x y : V) (j : ℕ) : Finset V :=
  G.neighborFinset y ∩ sphere G x (j + 1)

end FiberDef

theorem mem_fiber {x y w : V} {j : ℕ} :
    w ∈ fiber G x y j ↔ (G.Adj y w ∧ G.dist x w = j + 1) := by
  show w ∈ (G.neighborFinset y ∩ sphere G x (j + 1)) ↔ (G.Adj y w ∧ G.dist x w = j + 1)
  rw [Finset.mem_inter, G.mem_neighborFinset, mem_sphere]

/-- Every vertex of `S j` has exactly one fewer neighbor on `S (j+1)` than its degree. -/
theorem card_fiber {x y : V} {j : ℕ} (hj1 : 1 ≤ j) (hg : 2 * j + 2 < G.girth)
    (hy : G.dist x y = j) {d : ℕ} (hreg : ∀ v, G.degree v = d) :
    (fiber G x y j).card = d - 1 := by
  obtain ⟨z, hz, hdz⟩ := exists_pred hj1 hy
  have hcat : fiber G x y j ∪ {z} = G.neighborFinset y := by
    refine Finset.ext fun w => ?_
    rw [Finset.mem_union, Finset.mem_singleton, mem_fiber, G.mem_neighborFinset y w]
    constructor
    · rintro (⟨ha, _⟩ | rfl)
      · exact ha
      · exact hz.symm
    · intro hadj
      rcases Adj.diff_dist_adj hadj with h3 | h3 | h3 <;> rw [hy] at h3
      · exact (no_adj_same_sphere hj1 hy hadj h3 (by omega)).elim
      · exact Or.inl ⟨hadj, h3⟩
      · refine Or.inr ?_
        by_contra hwne
        exact no_two_adj_lower_sphere hj1 hy hwne hadj.symm h3 hz (by omega) (by omega)
  have hzd : z ∉ fiber G x y j := by
    intro hmem
    have h1 := (mem_fiber.1 hmem).2
    omega
  have hdis : Disjoint (fiber G x y j) ({z} : Finset V) := by
    rw [Finset.disjoint_left]
    intro w hw hm
    exact hzd (by rw [← Finset.mem_singleton.1 hm]; exact hw)
  have e0 : (fiber G x y j ∪ {z}).card = d := by
    rw [hcat, SimpleGraph.card_neighborFinset_eq_degree, hreg y]
  rw [Finset.card_union_of_disjoint hdis, Finset.card_singleton] at e0
  omega

/-- Fibers of distinct vertices of `S j` are disjoint. -/
theorem fiber_disjoint {x y₁ y₂ : V} {j : ℕ} (hj1 : 1 ≤ j) (hg : 2 * j + 2 < G.girth)
    (h1 : G.dist x y₁ = j) (h2 : G.dist x y₂ = j) (hne : y₁ ≠ y₂) :
    Disjoint (fiber G x y₁ j) (fiber G x y₂ j) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  obtain ⟨ha1, hd1⟩ := mem_fiber.1 hw1
  obtain ⟨ha2, hd2⟩ := mem_fiber.1 hw2
  have hre1 : G.Reachable x y₁ := Reachable.of_dist_ne_zero (by rw [h1]; omega)
  have hre2 : G.Reachable x y₂ := Reachable.of_dist_ne_zero (by rw [h2]; omega)
  obtain ⟨q₁, hp₁, hl₁⟩ := exists_path_dist h1 hre1
  obtain ⟨q₂, hp₂, hl₂⟩ := exists_path_dist h2 hre2
  have hR1 : (q₁.concat ha1).IsPath := isPath_concat (hl₁.trans h1.symm) ha1 (by omega)
  have hR2 : (q₂.concat ha2).IsPath := isPath_concat (hl₂.trans h2.symm) ha2 (by omega)
  exact (concat_ne_of_ne hne ha1 ha2) (eq_of_two_paths_of_lt_girth hR1 hR2
    (by rw [Walk.length_concat, Walk.length_concat, hl₁, hl₂]; omega))

/-- The sphere growth inequality. -/
theorem sphere_growth {x : V} {j : ℕ} (hj1 : 1 ≤ j) (hg : 2 * j + 2 < G.girth)
    {d : ℕ} (hreg : ∀ v, G.degree v = d) :
    (d - 1) * (sphere G x j).card ≤ (sphere G x (j + 1)).card := by
  have hsub : Finset.biUnion (sphere G x j) (fun y => fiber G x y j) ⊆ sphere G x (j + 1) := by
    intro w hw
    obtain ⟨y, hy, hwy⟩ := Finset.mem_biUnion.1 hw
    exact mem_sphere.2 (mem_fiber.1 hwy).2
  have hsum : ∑ y ∈ sphere G x j, (fiber G x y j).card = (sphere G x j).card * (d - 1) :=
    Finset.sum_const_nat fun y hy => card_fiber hj1 hg (mem_sphere.1 hy) hreg
  calc (d - 1) * (sphere G x j).card
      = (sphere G x j).card * (d - 1) := Nat.mul_comm _ _
    _ = ∑ y ∈ sphere G x j, (fiber G x y j).card := hsum.symm
    _ = (Finset.biUnion (sphere G x j) (fun y => fiber G x y j)).card :=
        (card_disj_bUnion fun y hy y' hy' hne => fiber_disjoint hj1 hg
          (mem_sphere.1 hy) (mem_sphere.1 hy') hne).symm
    _ ≤ (sphere G x (j + 1)).card := Finset.card_le_card hsub

/-- Sphere sizes grow geometrically up to the radius forced by the girth. -/
theorem card_sphere_ge : ∀ (j : ℕ) (x : V), 1 ≤ j →
    (∀ m, 1 ≤ m → m < j → 2 * m + 2 < G.girth) →
    ∀ {d : ℕ}, (∀ v, G.degree v = d) →
    d * (d - 1) ^ (j - 1) ≤ (sphere G x j).card := by
  intro j
  induction j with
  | zero => intro _ _; omega
  | succ j ih =>
      intro x hj1 hg d hreg
      match j, hj1 with
      | 0, _ =>
          rw [card_sphere_one x, hreg x, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
      | (j' + 1), _ =>
          have hIH : d * (d - 1) ^ (j' + 1 - 1) ≤ (sphere G x (j' + 1)).card :=
            ih x (by omega) (fun m hm1 hm2 => hg m hm1 (by omega)) hreg
          have hgrow : (d - 1) * (sphere G x (j' + 1)).card
              ≤ (sphere G x (j' + 1 + 1)).card :=
            sphere_growth (by omega) (hg (j' + 1) (by omega) (by omega)) hreg
          have hexp : j' + 1 + 1 - 1 = j' + 1 := by omega
          have hexp2 : j' + 1 - 1 = j' := by omega
          have e1 : d * (d - 1) ^ (j' + 1 + 1 - 1) = (d - 1) * (d * (d - 1) ^ (j' + 1 - 1)) := by
            rw [hexp, hexp2, Nat.pow_succ]
            ac_rfl
          rw [e1]
          exact (Nat.mul_le_mul (Nat.le_refl _) hIH).trans hgrow

/-- **The Moore bound.**  A `d`-regular graph of girth above `2r + 1` has at least
    `1 + ∑_{m < r} d (d-1)^m` vertices. -/
theorem moore_bound {x : V} {r : ℕ}
    (hg : ∀ m, 1 ≤ m → m < r → 2 * m + 2 < G.girth)
    {d : ℕ} (hreg : ∀ v, G.degree v = d) :
    1 + ∑ m ∈ Finset.range r, d * (d - 1) ^ m ≤ Fintype.card V := by
  have hsdis : ∀ m ∈ Finset.range (r + 1), ∀ m' ∈ Finset.range (r + 1), m ≠ m' →
      Disjoint (sphere G x m) (sphere G x m') := by
    intro m hm m' hm' hne
    rw [Finset.disjoint_left]
    intro y hym hy
    have e1 := mem_sphere.1 hym
    have e2 := mem_sphere.1 hy
    rw [e1] at e2
    exact hne e2
  calc 1 + ∑ m ∈ Finset.range r, d * (d - 1) ^ m
      ≤ (sphere G x 0).card + ∑ m ∈ Finset.range r, (sphere G x (m + 1)).card := by
        refine Nat.add_le_add (Finset.one_le_card.2 ⟨x, mem_sphere.2 G.dist_self⟩)
          (Finset.sum_le_sum fun m hm => ?_)
        have hmr : m < r := Finset.mem_range.1 hm
        exact card_sphere_ge (m + 1) x (by omega)
          (fun m' hm'1 hm'2 => hg m' hm'1 (by omega)) hreg
    _ = ∑ m ∈ Finset.range (r + 1), (sphere G x m).card := by
        rw [Finset.sum_range_succ']
        ac_rfl
    _ = (Finset.biUnion (Finset.range (r + 1)) (fun m => sphere G x m)).card :=
        (card_disj_bUnion hsdis).symm
    _ ≤ Fintype.card V := Finset.card_le_card (Finset.subset_univ _)


/-- **TLMC #2148 is false**: every 5-regular graph of girth at least 8
    has at least 106 vertices, not 80. -/
theorem tlm2148 (hreg : ∀ v, G.degree v = 5) (hg : 8 ≤ G.girth) :
    106 ≤ Fintype.card V := by
  have hna : ¬ G.IsAcyclic := by
    intro hacyc
    rw [hacyc.girth_eq_zero] at hg
    omega
  obtain ⟨a, w, hw, hwl⟩ := exists_girth_eq_length.mpr hna
  have hgt : ∀ m, 1 ≤ m → m < 3 → 2 * m + 2 < G.girth := by
    intro m hm1 hm2; omega
  have h := moore_bound (x := a) (r := 3) hgt hreg
  rwa [show ∑ m ∈ Finset.range 3, 5 * 4 ^ m = 105 from by decide] at h

/-- TLMC #2148 restated: the order of the (5,8)-cage is not 80. -/
theorem tlm2148_order_ne_80 (hreg : ∀ v, G.degree v = 5) (hg : 8 ≤ G.girth)
    (hcard : Fintype.card V = 80) : False := by
  have := tlm2148 hreg hg
  omega

end Moore

end TLMCBatch3
