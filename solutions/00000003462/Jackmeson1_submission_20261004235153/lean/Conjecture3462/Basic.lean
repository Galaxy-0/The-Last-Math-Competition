import Mathlib

/-!
# Conjecture 00000003462 is false

Conjecture: *doubly critical graphs are `k`-chromatic edge-critical graphs in which deleting any two
vertices lowers `χ` (Chinese text: "makes `χ` drop by one"); for six-doubly-critical graphs the edge
bound improves to `(5v-2)/3`, uniquely attained by Kostochka-Yancey extremal graphs; ...*

Classes (`k = 6`, graphs on `Fin n`, i.e. all finite simple graphs up to isomorphism):
`IsDoublyCriticalEN` (English: `χ(G - x - y) < χ(G)` for distinct `x, y`), `IsDoublyCriticalZH`
(Chinese: `χ(G - x - y) + 1 = χ(G)`), and the standard Erdős–Lovász notion `IsDoublyCriticalEL`
(connected, `χ(G - x - y) + 2 = χ(G)` for every edge `xy`).

1. `K₆` lies in the English and Erdős–Lovász classes and has `15 > 28/3` edges: the upper bound
   fails (`not_improvedBound_EN`, `not_improvedBound_EL`).
2. Every graph of the English class, hence of the Chinese class, has `|E| > (5v-2)/3 + 1`
   (`edges_gt`): non-isolated vertices have degree `≥ 5` and at most one vertex is isolated. So no
   graph of either class attains `(5v-2)/3`, even up to rounding.
3. Hence the conjecture (bound ∧ attained ∧ uniqueness ∧ girth clause) is false under both
   readings for any uniqueness predicate and girth clause, with `(5v-2)/3` read as an upper bound
   (`Conjecture`) or, like Gallai's bound, as a lower bound (`ConjectureLower`).

Main theorem: `C3462.conjecture_00000003462_false`.
-/

open SimpleGraph

namespace C3462

variable {W V : Type*}

lemma colorable_five_of_lt_six {H : SimpleGraph W} (h : H.chromaticNumber < 6) : H.Colorable 5 :=
  chromaticNumber_le_iff_colorable.mp
    ((ENat.lt_add_one_iff (ENat.natCast_ne_top 5)).mp (by norm_num; exact h))

lemma not_colorable_five {H : SimpleGraph W} (h : H.chromaticNumber = 6) : ¬ H.Colorable 5 :=
  fun hc => by have := hc.chromaticNumber_le; rw [h] at this; norm_num at this

/-! ## Definitions -/

/-- Edge-critical: deleting any edge lowers the chromatic number. -/
def IsEdgeCritical (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber < G.chromaticNumber

/-- English definition: a `k`-chromatic edge-critical graph in which deleting any two (distinct)
vertices lowers the chromatic number. `G.induce {x, y}ᶜ` is `G - x - y`. -/
def IsDoublyCriticalEN (k : ℕ) (G : SimpleGraph V) : Prop :=
  G.chromaticNumber = k ∧ IsEdgeCritical G ∧
    ∀ x y : V, x ≠ y → (G.induce ({x, y}ᶜ : Set V)).chromaticNumber < G.chromaticNumber

/-- Chinese definition ("drops by one"): a `k`-chromatic edge-critical graph in which deleting any
two (distinct) vertices lowers the chromatic number by exactly one. -/
def IsDoublyCriticalZH (k : ℕ) (G : SimpleGraph V) : Prop :=
  G.chromaticNumber = k ∧ IsEdgeCritical G ∧
    ∀ x y : V, x ≠ y → (G.induce ({x, y}ᶜ : Set V)).chromaticNumber + 1 = G.chromaticNumber

/-- The standard (Erdős–Lovász) notion, for comparison: a connected `k`-chromatic edge-critical
graph in which deleting the two ends of any edge lowers the chromatic number by two. -/
def IsDoublyCriticalEL (k : ℕ) (G : SimpleGraph V) : Prop :=
  G.Connected ∧ G.chromaticNumber = k ∧ IsEdgeCritical G ∧
    ∀ x y : V, G.Adj x y → (G.induce ({x, y}ᶜ : Set V)).chromaticNumber + 2 = G.chromaticNumber

/-- A class of finite graphs (all finite graphs up to isomorphism live on some `Fin n`). -/
abbrev GraphClass := (n : ℕ) → SimpleGraph (Fin n) → Prop

def EN6 : GraphClass := fun _ G => IsDoublyCriticalEN 6 G
def ZH6 : GraphClass := fun _ G => IsDoublyCriticalZH 6 G
def EL6 : GraphClass := fun _ G => IsDoublyCriticalEL 6 G

/-- The proposed improved bound: every graph of the class has at most `(5v-2)/3` edges. -/
def ImprovedBound (D : GraphClass) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)), D n G → (G.edgeSet.ncard : ℝ) ≤ (5 * n - 2) / 3

/-- The bound `(5v-2)/3` is attained by some graph of the class. -/
def BoundAttained (D : GraphClass) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), D n G ∧ (G.edgeSet.ncard : ℝ) = (5 * n - 2) / 3

/-- The bound is attained up to rounding (`|E|` within distance `< 1` of `(5v-2)/3`, which covers
`|E| = ⌊(5v-2)/3⌋` and `|E| = ⌈(5v-2)/3⌉`). Exact attainment implies this. -/
def BoundAttainedUpToRounding (D : GraphClass) : Prop :=
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), D n G ∧ |(G.edgeSet.ncard : ℝ) - (5 * n - 2) / 3| < 1

/-- The conjecture for class `D`: the bound holds, it is attained, it is attained only by
Kostochka–Yancey extremal graphs (predicate `KY`), and the girth-five merging clause holds. -/
def Conjecture (D : GraphClass) (KY : GraphClass) (girthClause : Prop) : Prop :=
  ImprovedBound D ∧ BoundAttained D ∧
    (∀ n (G : SimpleGraph (Fin n)), D n G → (G.edgeSet.ncard : ℝ) = (5 * n - 2) / 3 → KY n G) ∧
    girthClause

/-- Gallai's bound for critical graphs is a *lower* bound on `|E|`; this is the conjecture with
`(5v-2)/3` read as an improved lower bound. -/
def ImprovedLowerBound (D : GraphClass) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)), D n G → (5 * n - 2) / 3 ≤ (G.edgeSet.ncard : ℝ)

def ConjectureLower (D : GraphClass) (KY : GraphClass) (girthClause : Prop) : Prop :=
  ImprovedLowerBound D ∧ BoundAttained D ∧
    (∀ n (G : SimpleGraph (Fin n)), D n G → (G.edgeSet.ncard : ℝ) = (5 * n - 2) / 3 → KY n G) ∧
    girthClause

/-! ## The Chinese class is contained in the English class -/

theorem ZH_to_EN {G : SimpleGraph V} (h : IsDoublyCriticalZH 6 G) : IsDoublyCriticalEN 6 G := by
  refine ⟨h.1, h.2.1, fun x y hxy => ?_⟩
  have e := h.2.2 x y hxy
  rw [h.1] at e ⊢
  have hne : (G.induce ({x, y}ᶜ : Set V)).chromaticNumber ≠ ⊤ := by
    intro ht; rw [ht] at e; simp at e
  rw [← e]
  exact (ENat.lt_add_one_iff hne).mpr le_rfl

/-! ## `K₆` is in the English class -/

theorem top_chromaticNumber : (⊤ : SimpleGraph (Fin 6)).chromaticNumber = 6 := by
  rw [chromaticNumber_top, Fintype.card_fin]; rfl

theorem top_edgeCritical : IsEdgeCritical (⊤ : SimpleGraph (Fin 6)) := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := by simpa using he
  rw [top_chromaticNumber]
  classical
  let C : (⊤ : SimpleGraph (Fin 6)).deleteEdges {s(a, b)} |>.Coloring {v : Fin 6 // v ≠ b} :=
    Coloring.mk (fun v => if hv : v = b then ⟨a, hab⟩ else ⟨v, hv⟩) (by
      intro v w hvw
      rw [deleteEdges_adj] at hvw
      obtain ⟨hvw, hne⟩ := hvw
      have hvw' : v ≠ w := hvw
      simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
        at hne
      by_cases hv : v = b <;> by_cases hw : w = b <;> simp only [hv, hw, dite_true, dite_false,
        ne_eq, Subtype.mk.injEq] <;> grind)
  have h5 : Fintype.card {v : Fin 6 // v ≠ b} = 5 := by simp
  have := C.colorable
  rw [h5] at this
  exact lt_of_le_of_lt this.chromaticNumber_le (by norm_num)

theorem top_deleteTwo {x y : Fin 6} (hxy : x ≠ y) :
    ((⊤ : SimpleGraph (Fin 6)).induce ({x, y}ᶜ : Set (Fin 6))).chromaticNumber = 4 := by
  classical
  rw [← completeGraph_eq_top, induce_top, completeGraph_eq_top, chromaticNumber_top,
    Fintype.card_compl_set]
  simp [hxy]

/-- `K₆` satisfies the English definition; deleting any two vertices drops `χ` by two. -/
theorem top_EN : IsDoublyCriticalEN 6 (⊤ : SimpleGraph (Fin 6)) := by
  refine ⟨top_chromaticNumber, top_edgeCritical, fun x y hxy => ?_⟩
  rw [top_deleteTwo hxy, top_chromaticNumber]; norm_num

/-- `K₆` is also double-critical in the standard (Erdős–Lovász) sense. -/
theorem top_EL : IsDoublyCriticalEL 6 (⊤ : SimpleGraph (Fin 6)) := by
  refine ⟨by rw [← completeGraph_eq_top]; exact connected_top, top_chromaticNumber,
    top_edgeCritical, fun x y hxy => ?_⟩
  rw [top_deleteTwo hxy.ne, top_chromaticNumber]; rfl

theorem top_edges : (⊤ : SimpleGraph (Fin 6)).edgeSet.ncard = 15 := by
  classical
  rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two]
  rfl

theorem not_improvedBound_of_top {D : GraphClass} (hD : D 6 ⊤) : ¬ ImprovedBound D := by
  intro h
  have := h 6 ⊤ hD
  rw [top_edges] at this
  norm_num at this

theorem not_improvedBound_EN : ¬ ImprovedBound EN6 := not_improvedBound_of_top top_EN
theorem not_improvedBound_EL : ¬ ImprovedBound EL6 := not_improvedBound_of_top top_EL

/-! ## Degree bound and edge count for the whole class -/

section counting

variable [Fintype V] {G : SimpleGraph V}

/-- In a `6`-chromatic edge-critical graph, every non-isolated vertex has degree `≥ 5`. -/
theorem degree_ge_five [DecidableRel G.Adj] (hχ : G.chromaticNumber = 6) (hc : IsEdgeCritical G)
    {v u : V} (hvu : G.Adj v u) : 5 ≤ G.degree v := by
  classical
  by_contra hlt
  have hlt : G.degree v < 5 := by omega
  have h1 : (G.deleteEdges {s(v, u)}).chromaticNumber < 6 := hχ ▸ hc _ hvu
  obtain ⟨C⟩ := colorable_five_of_lt_six h1
  -- a colour not used on the neighbourhood of `v`
  obtain ⟨c, hcfree⟩ : ∃ c : Fin 5, ∀ w, G.Adj v w → C w ≠ c := by
    by_contra hne
    push Not at hne
    have hsub : (Finset.univ : Finset (Fin 5)) ⊆ (G.neighborFinset v).image C := by
      intro c _
      obtain ⟨w, hw, hwc⟩ := hne c
      exact Finset.mem_image.mpr ⟨w, (mem_neighborFinset G v w).mpr hw, hwc⟩
    have := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_univ, Fintype.card_fin, card_neighborFinset_eq_degree] at this
    omega
  apply not_colorable_five hχ
  refine ⟨Coloring.mk (fun w => if w = v then c else C w) ?_⟩
  intro a b hab
  by_cases ha : a = v <;> by_cases hb : b = v
  · subst ha; subst hb; exact (G.irrefl hab).elim
  · subst ha; simp only [if_neg hb]; exact (hcfree b hab).symm
  · subst hb; simp only [if_neg ha]; exact hcfree a hab.symm
  · simp only [if_neg ha, if_neg hb]
    apply C.valid
    rw [deleteEdges_adj]
    refine ⟨hab, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    tauto

lemma not_adj_of_degree_eq_zero [DecidableRel G.Adj] {x : V} (hx : G.degree x = 0) (w : V) :
    ¬ G.Adj x w := fun hw => by
  rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero] at hx
  exact (Finset.notMem_empty w) (hx ▸ (mem_neighborFinset G x w).mpr hw)

omit [Fintype V] in
lemma mem_compl_pair {x y z z' : V} (hx : ∀ w, ¬ G.Adj x w) (hy : ∀ w, ¬ G.Adj y w)
    (h : G.Adj z z') : z ∈ ({x, y}ᶜ : Set V) := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨by rintro rfl; exact hx z' h, by rintro rfl; exact hy z' h⟩

omit [Fintype V] in
/-- If `x` and `y` are isolated, colourings of `G - x - y` extend to `G`. -/
theorem colorable_of_induce {x y z : V} (hx : ∀ w, ¬ G.Adj x w) (hy : ∀ w, ¬ G.Adj y w)
    (hz : z ∈ ({x, y}ᶜ : Set V)) {n : ℕ} (hcol : (G.induce ({x, y}ᶜ : Set V)).Colorable n) :
    G.Colorable n := by
  classical
  obtain ⟨C⟩ := hcol
  refine ⟨Coloring.mk (fun w => if h : w ∈ ({x, y}ᶜ : Set V) then C ⟨w, h⟩ else C ⟨z, hz⟩) ?_⟩
  intro a b hab
  simp only [dif_pos (mem_compl_pair hx hy hab), dif_pos (mem_compl_pair hx hy hab.symm)]
  exact C.valid (induce_adj.mpr hab)

/-- Every graph in the English class has more than `(5v-2)/3 + 1` edges: `5v + 1 < 3|E|`. -/
theorem edges_gt (h : IsDoublyCriticalEN 6 G) :
    5 * Fintype.card V + 1 < 3 * G.edgeSet.ncard := by
  classical
  obtain ⟨hχ, hc, hdel⟩ := h
  -- `G` has an edge
  obtain ⟨z, z', hzz'⟩ : ∃ z z', G.Adj z z' := by
    by_contra hne
    push Not at hne
    apply not_colorable_five hχ
    exact ⟨Coloring.mk (fun _ => 0) (fun hab => absurd hab (hne _ _))⟩
  -- at most one isolated vertex
  have hiso : ((Finset.univ : Finset V).filter (fun v => G.degree v = 0)).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    by_contra hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have hx' := not_adj_of_degree_eq_zero hx
    have hy' := not_adj_of_degree_eq_zero hy
    have hlt := hdel x y hxy
    rw [hχ] at hlt
    exact not_colorable_five hχ (colorable_of_induce hx' hy' (mem_compl_pair hx' hy' hzz')
      (colorable_five_of_lt_six hlt))
  -- degree sum
  have hsum : ∑ _v : V, 5 ≤ ∑ v : V, (G.degree v + if G.degree v = 0 then 5 else 0) := by
    refine Finset.sum_le_sum fun v _ => ?_
    split_ifs with h0
    · omega
    · obtain ⟨w, hw⟩ : ∃ w, G.Adj v w := by
        rw [← card_neighborFinset_eq_degree] at h0
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
        exact ⟨w, (mem_neighborFinset G v w).mp hw⟩
      have := degree_ge_five hχ hc hw
      omega
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, Finset.card_univ, sum_degrees_eq_twice_card_edges] at hsum
  have hcard : 6 ≤ Fintype.card V := by
    have := G.chromaticNumber_le_card
    rw [hχ] at this
    exact_mod_cast this
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  omega

end counting

/-! ## Refutation -/

theorem edges_gt_real {n : ℕ} {G : SimpleGraph (Fin n)} (h : IsDoublyCriticalEN 6 G) :
    (5 * (n : ℝ) - 2) / 3 + 1 < G.edgeSet.ncard := by
  have := edges_gt h
  rw [Fintype.card_fin] at this
  have : (5 * n + 1 : ℝ) < 3 * G.edgeSet.ncard := by exact_mod_cast this
  linarith

theorem attained_of_exact {D : GraphClass} (h : BoundAttained D) : BoundAttainedUpToRounding D := by
  obtain ⟨n, G, hG, he⟩ := h
  exact ⟨n, G, hG, by rw [he, sub_self, abs_zero]; norm_num⟩

/-- A class contained in the English class (e.g. the English or the Chinese class). -/
def SubEN (D : GraphClass) : Prop := ∀ n (G : SimpleGraph (Fin n)), D n G → IsDoublyCriticalEN 6 G

theorem subEN_EN : SubEN EN6 := fun _ _ h => h
theorem subEN_ZH : SubEN ZH6 := fun _ _ h => ZH_to_EN h

theorem not_attainedUpToRounding {D : GraphClass} (hD : SubEN D) :
    ¬ BoundAttainedUpToRounding D := by
  rintro ⟨n, G, hG, he⟩
  have := edges_gt_real (hD n G hG)
  rw [abs_lt] at he
  linarith

/-- Under the lower-bound reading the inequality itself holds (strictly). -/
theorem improvedLowerBound {D : GraphClass} (hD : SubEN D) : ImprovedLowerBound D :=
  fun n G hG => by have := edges_gt_real (hD n G hG); linarith

theorem not_conjecture {D : GraphClass} (hD : SubEN D) (KY : GraphClass) (girthClause : Prop) :
    ¬ Conjecture D KY girthClause ∧ ¬ ConjectureLower D KY girthClause :=
  ⟨fun h => not_attainedUpToRounding hD (attained_of_exact h.2.1),
    fun h => not_attainedUpToRounding hD (attained_of_exact h.2.1)⟩

/-- **Main theorem.** Conjecture 00000003462 is false. Under the English definition (and the
standard Erdős–Lovász one) the upper bound `(5v-2)/3` fails at `K₆`. Under both the English and the
Chinese ("drops by one") definitions no graph of the class attains `(5v-2)/3`, even up to rounding,
so the conjecture fails for every Kostochka–Yancey predicate and girth clause, with `(5v-2)/3` read
as an upper or as a lower bound. -/
theorem conjecture_00000003462_false :
    IsDoublyCriticalEN 6 (⊤ : SimpleGraph (Fin 6)) ∧ IsDoublyCriticalEL 6 (⊤ : SimpleGraph (Fin 6)) ∧
    (⊤ : SimpleGraph (Fin 6)).edgeSet.ncard = 15 ∧
    ¬ ImprovedBound EN6 ∧ ¬ ImprovedBound EL6 ∧
    ¬ BoundAttainedUpToRounding EN6 ∧ ¬ BoundAttainedUpToRounding ZH6 ∧
    (∀ (KY : GraphClass) (girthClause : Prop), ¬ Conjecture EN6 KY girthClause) ∧
    (∀ (KY : GraphClass) (girthClause : Prop), ¬ Conjecture ZH6 KY girthClause) ∧
    (∀ (KY : GraphClass) (girthClause : Prop), ¬ ConjectureLower EN6 KY girthClause) ∧
    (∀ (KY : GraphClass) (girthClause : Prop), ¬ ConjectureLower ZH6 KY girthClause) :=
  ⟨top_EN, top_EL, top_edges, not_improvedBound_EN, not_improvedBound_EL,
    not_attainedUpToRounding subEN_EN, not_attainedUpToRounding subEN_ZH,
    fun KY g => (not_conjecture subEN_EN KY g).1, fun KY g => (not_conjecture subEN_ZH KY g).1,
    fun KY g => (not_conjecture subEN_EN KY g).2, fun KY g => (not_conjecture subEN_ZH KY g).2⟩

end C3462
