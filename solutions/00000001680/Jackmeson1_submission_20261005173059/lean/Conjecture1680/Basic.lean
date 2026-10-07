import Mathlib

/-!
# Conjecture 00000001680 (disproof of the upper half)

Statement: "The treewidth of random geometric graphs (unit disk, radius `r_n` at the
connectivity threshold) is `Θ(√(log n / log log n))`."

We show that the upper bound `tw = O(√(log n / log log n))` fails for *every* placement of
the points, not only with high probability.  Let `n` points lie in a box `[-L, L]²` of the
Euclidean plane, and let the radius satisfy `n r² ≥ c₀ log n` (this covers the connectivity
threshold `π n r² = log n + O(1)`, and `π n r² ~ log n`).  Cut the box into squares of side
`r / 2`.  There are `O(n / log n)` squares, so one of them holds `≥ c · log n` points.  These
points are pairwise within distance `r`, so they form a clique.  Every tree decomposition has
a bag that contains this clique (Helly property of subtrees of a tree).  Hence
`tw ≥ c · log n - 1`, which beats `C · √(log n / log log n)` for every constant `C` once `n` is
large.

Definitions (Mathlib has no treewidth):
* the unit-disk graph on points `p : Fin m → EuclideanSpace ℝ (Fin 2)`: distinct `i, j` are
  adjacent iff `dist (p i) (p j) ≤ r` (Euclidean distance);
* a tree decomposition `(T, bag)`: `T` is a finite tree, (T1) every vertex is in some bag,
  (T2) the two ends of every edge share a bag, (T3) for every vertex `v` the nodes whose bags
  contain `v` induce a connected subgraph of `T`;
* width = (maximum bag size) - 1; treewidth = minimum width over all tree decompositions.
-/

open SimpleGraph Finset

namespace C1680

/-! ## Tree decompositions and treewidth -/

/-- A tree decomposition of `G`: a finite tree `T` on a node type `ι` and a bag of vertices at
each node, satisfying (T1) vertex coverage, (T2) edge coverage and (T3) connectivity: for each
vertex `v`, the nodes whose bags contain `v` induce a connected subgraph of `T`. -/
structure TreeDecomposition {V : Type*} (G : SimpleGraph V) where
  /-- The node type of the tree. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The tree. -/
  T : SimpleGraph ι
  isTree : T.IsTree
  /-- The bag at each node. -/
  bag : ι → Finset V
  cover_vertex : ∀ v, ∃ i, v ∈ bag i
  cover_edge : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  connected : ∀ v, (T.induce {i | v ∈ bag i}).Connected

attribute [instance] TreeDecomposition.fintype

/-- The width of a tree decomposition: maximum bag size minus one. -/
def TreeDecomposition.width {V : Type*} {G : SimpleGraph V} (D : TreeDecomposition G) : ℕ :=
  (Finset.univ.sup fun i => (D.bag i).card) - 1

/-- The treewidth: the minimum width of a tree decomposition. -/
noncomputable def treewidth {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf (Set.range (TreeDecomposition.width (G := G)))

lemma connected_of_subsingleton {W : Type*} [Subsingleton W] [Nonempty W] (H : SimpleGraph W) :
    H.Connected :=
  (connected_iff H).2 ⟨fun a b => by obtain rfl := Subsingleton.elim a b; rfl, ‹_›⟩

/-- The one-bag decomposition: a single node whose bag is the whole vertex set. -/
def trivialDecomp {V : Type*} [Fintype V] (G : SimpleGraph V) : TreeDecomposition G where
  ι := Unit
  T := ⊥
  isTree := ⟨connected_of_subsingleton _, isAcyclic_bot⟩
  bag := fun _ => Finset.univ
  cover_vertex := fun v => ⟨(), Finset.mem_univ v⟩
  cover_edge := fun u v _ => ⟨(), Finset.mem_univ u, Finset.mem_univ v⟩
  connected := fun v => by
    have : Nonempty {i : Unit | v ∈ (Finset.univ : Finset V)} := ⟨⟨(), Finset.mem_univ v⟩⟩
    exact connected_of_subsingleton _

/-! ## Helly property of subtrees -/

section Helly

variable {ι : Type*} {T : SimpleGraph ι}

/-- `S` is walk-connected in `T`: any two nodes of `S` are joined by a walk inside `S`. -/
def WConn (T : SimpleGraph ι) (S : Set ι) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∃ p : T.Walk i j, ∀ k ∈ p.support, k ∈ S

/-- (T3) in walk form. -/
lemma wconn_of_connected {S : Set ι} (h : (T.induce S).Connected) : WConn T S := by
  intro i hi j hj
  obtain ⟨q⟩ := h.preconnected ⟨i, hi⟩ ⟨j, hj⟩
  have hsup : ∀ k ∈ (q.map (Embedding.induce S).toHom).support, k ∈ S := by
    intro k hk
    rw [Walk.support_map, List.mem_map] at hk
    obtain ⟨x, -, rfl⟩ := hk
    exact x.2
  exact ⟨q.map (Embedding.induce S).toHom, hsup⟩

lemma wconn_univ (hT : T.Connected) : WConn T Set.univ := fun i _ j _ =>
  ⟨(hT.preconnected i j).some, fun _ _ => trivial⟩

/-- In an acyclic graph, the unique path between two nodes of a walk-connected set stays in it. -/
lemma path_subset (hT : T.IsAcyclic) {S : Set ι} (hS : WConn T S) {i j : ι} (hi : i ∈ S)
    (hj : j ∈ S) (q : T.Path i j) : ∀ k ∈ q.1.support, k ∈ S := by
  classical
  obtain ⟨p, hp⟩ := hS i hi j hj
  have hq : q = p.toPath := (hT.subsingleton_path i j).elim _ _
  intro k hk
  rw [hq] at hk
  exact hp k (p.support_bypass_subset_support hk)

lemma wconn_inter (hT : T.IsAcyclic) {S S' : Set ι} (hS : WConn T S) (hS' : WConn T S') :
    WConn T (S ∩ S') := by
  classical
  intro i hi j hj
  obtain ⟨p, -⟩ := hS i hi.1 j hj.1
  exact ⟨p.toPath.1, fun k hk =>
    ⟨path_subset hT hS hi.1 hj.1 _ k hk, path_subset hT hS' hi.2 hj.2 _ k hk⟩⟩

/-- For an edge `xz` and a node `c` of a tree, the `c`-`x` path passes through `z` or the
`c`-`z` path passes through `x`. -/
lemma edge_side (hT : T.IsAcyclic) {c x z : ι} (hxz : T.Adj x z) (P : T.Path c x)
    (Q : T.Path c z) : z ∈ P.1.support ∨ x ∈ Q.1.support := by
  by_cases hz : z ∈ P.1.support
  · exact Or.inl hz
  · right
    have hQ : Q = ⟨P.1.concat hxz, P.2.concat hz hxz⟩ := (hT.subsingleton_path c z).elim _ _
    rw [hQ]
    simp [Walk.support_concat]

/-- A walk from `X` to `Z` inside `X ∪ Z` has a node of `X` equal or adjacent to a node of `Z`. -/
lemma transition {X Z : Set ι} : ∀ {a b : ι} (w : T.Walk a b), (∀ k ∈ w.support, k ∈ X ∪ Z) →
    a ∈ X → b ∈ Z → ∃ x ∈ w.support, ∃ z ∈ w.support, x ∈ X ∧ z ∈ Z ∧ (x = z ∨ T.Adj x z)
  | _, _, .nil, _, ha, hb => ⟨_, Walk.start_mem_support _, _, Walk.start_mem_support _, ha, hb,
      Or.inl rfl⟩
  | a, _, .cons (v := a') h p, hw, ha, hb => by
    by_cases ha' : a' ∈ Z
    · exact ⟨a, Walk.start_mem_support _, a', by simp, ha, ha', Or.inr h⟩
    · have hX : a' ∈ X := by
        rcases hw a' (by simp) with h' | h'
        · exact h'
        · exact absurd h' ha'
      obtain ⟨x, hx, z, hz, h1, h2, h3⟩ :=
        transition p (fun k hk => hw k (by simp [hk])) hX hb
      exact ⟨x, by simp [hx], z, by simp [hz], h1, h2, h3⟩

/-- Helly property for three subtrees of a tree. -/
lemma helly_three (hT : T.IsAcyclic) {X Y Z : Set ι} (hX : WConn T X) (hY : WConn T Y)
    (hZ : WConn T Z) {a b c : ι} (ha : a ∈ X ∩ Y) (hb : b ∈ Y ∩ Z) (hc : c ∈ Z ∩ X) :
    ∃ k, k ∈ X ∧ k ∈ Y ∧ k ∈ Z := by
  classical
  obtain ⟨q, hq⟩ := hZ b hb.2 c hc.1
  obtain ⟨r, hr⟩ := hX c hc.2 a ha.1
  set P := (q.append r).toPath with hPdef
  have hPXZ : ∀ k ∈ P.1.support, k ∈ Z ∪ X := by
    intro k hk
    have hk' := (q.append r).support_bypass_subset_support hk
    rcases (Walk.mem_support_append_iff q r).1 hk' with h | h
    · exact Or.inl (hq k h)
    · exact Or.inr (hr k h)
  have hPY := path_subset hT hY hb.1 ha.2 P
  obtain ⟨x, hx, z, hz, hxZ, hzX, hxz⟩ := transition P.1 hPXZ hb.2 ha.1
  rcases hxz with rfl | hadj
  · exact ⟨x, hzX, hPY x hx, hxZ⟩
  · obtain ⟨Pc, -⟩ := hZ c hc.1 x hxZ
    obtain ⟨Qc, -⟩ := hX c hc.2 z hzX
    rcases edge_side hT hadj Pc.toPath Qc.toPath with h | h
    · exact ⟨z, hzX, hPY z hz, path_subset hT hZ hc.1 hxZ _ z h⟩
    · exact ⟨x, path_subset hT hX hc.2 hzX _ x h, hPY x hx, hxZ⟩

/-- Helly property for finitely many pairwise intersecting subtrees (relative to a subtree `R`). -/
lemma helly {V : Type*} [DecidableEq V] (hT : T.IsAcyclic) (S : V → Set ι) (K : Finset V)
    (hS : ∀ v ∈ K, WConn T (S v)) : ∀ R : Set ι, WConn T R → R.Nonempty →
    (∀ u ∈ K, ∀ w ∈ K, (S u ∩ S w ∩ R).Nonempty) → ∃ i ∈ R, ∀ v ∈ K, i ∈ S v := by
  induction K using Finset.induction_on with
  | empty => exact fun R _ hR _ => ⟨hR.some, hR.some_mem, by simp⟩
  | insert a K ha ih =>
    intro R hR hRne hpair
    have hSK : ∀ v ∈ K, WConn T (S v) := fun v hv => hS v (Finset.mem_insert_of_mem hv)
    have hSa : WConn T (S a) := hS a (Finset.mem_insert_self a K)
    have hpair' : ∀ u ∈ K, ∀ w ∈ K, (S u ∩ S w ∩ (S a ∩ R)).Nonempty := by
      intro u hu w hw
      have hu' : u ∈ insert a K := Finset.mem_insert_of_mem hu
      have hw' : w ∈ insert a K := Finset.mem_insert_of_mem hw
      have ha' : a ∈ insert a K := Finset.mem_insert_self a K
      obtain ⟨i1, ⟨h1u, h1w⟩, h1R⟩ := hpair u hu' w hw'
      obtain ⟨i2, ⟨h2w, h2a⟩, h2R⟩ := hpair w hw' a ha'
      obtain ⟨i3, ⟨h3a, h3u⟩, h3R⟩ := hpair a ha' u hu'
      obtain ⟨k, ⟨hku, hkR⟩, ⟨hkw, -⟩, ⟨hka, -⟩⟩ :=
        helly_three hT (wconn_inter hT (hSK u hu) hR) (wconn_inter hT (hSK w hw) hR)
          (wconn_inter hT hSa hR) (a := i1) (b := i2) (c := i3)
          ⟨⟨h1u, h1R⟩, ⟨h1w, h1R⟩⟩ ⟨⟨h2w, h2R⟩, ⟨h2a, h2R⟩⟩ ⟨⟨h3a, h3R⟩, ⟨h3u, h3R⟩⟩
      exact ⟨k, ⟨hku, hkw⟩, hka, hkR⟩
    obtain ⟨i0, ⟨-, h0a⟩, h0R⟩ := hpair a (Finset.mem_insert_self a K) a
      (Finset.mem_insert_self a K)
    obtain ⟨i, ⟨hia, hiR⟩, hiK⟩ :=
      ih hSK (S a ∩ R) (wconn_inter hT hSa hR) ⟨i0, h0a, h0R⟩ hpair'
    refine ⟨i, hiR, fun v hv => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact hia
    · exact hiK v hv

end Helly

/-! ## A clique lies in one bag, so `tw ≥ ω - 1` -/

/-- Every clique of `G` is contained in some bag of every tree decomposition. -/
lemma clique_subset_bag {V : Type*} {G : SimpleGraph V} (D : TreeDecomposition G) (K : Finset V)
    (hK : G.IsClique (K : Set V)) : ∃ i, K ⊆ D.bag i := by
  classical
  have : Nonempty D.ι := D.isTree.1.nonempty
  obtain ⟨i, -, hi⟩ := helly D.isTree.2 (fun v => {i | v ∈ D.bag i}) K
    (fun v _ => wconn_of_connected (D.connected v)) Set.univ (wconn_univ D.isTree.1)
    Set.univ_nonempty (by
      intro u hu w hw
      by_cases huw : u = w
      · subst huw
        obtain ⟨i, hi⟩ := D.cover_vertex u
        exact ⟨i, ⟨hi, hi⟩, trivial⟩
      · obtain ⟨i, hi⟩ := D.cover_edge u w (hK hu hw huw)
        exact ⟨i, hi, trivial⟩)
  exact ⟨i, fun v hv => hi v hv⟩

lemma card_le_width_add_one {V : Type*} {G : SimpleGraph V} (D : TreeDecomposition G)
    (K : Finset V) (hK : G.IsClique (K : Set V)) : K.card ≤ D.width + 1 := by
  obtain ⟨i, hi⟩ := clique_subset_bag D K hK
  have h1 := Finset.card_le_card hi
  have h2 : (D.bag i).card ≤ Finset.univ.sup fun i => (D.bag i).card :=
    Finset.le_sup (f := fun i => (D.bag i).card) (Finset.mem_univ i)
  unfold TreeDecomposition.width
  omega

/-- `ω(G) ≤ tw(G) + 1`. -/
theorem card_clique_le_treewidth_add_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    (K : Finset V) (hK : G.IsClique (K : Set V)) : K.card ≤ treewidth G + 1 := by
  obtain ⟨D, hD⟩ : treewidth G ∈ Set.range (TreeDecomposition.width (G := G)) :=
    Nat.sInf_mem ⟨_, trivialDecomp G, rfl⟩
  rw [← hD]
  exact card_le_width_add_one D K hK

/-! ## The unit-disk graph and the grid pigeonhole -/

/-- The Euclidean plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The unit-disk (random geometric) graph on points `p` with radius `r`: distinct `i, j` are
adjacent iff `dist (p i) (p j) ≤ r` (Euclidean distance). -/
def unitDiskGraph {m : ℕ} (p : Fin m → E2) (r : ℝ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun i j => dist (p i) (p j) ≤ r

/-- Two numbers with the same floor (of nonnegative values) differ by less than one. -/
lemma abs_sub_lt_of_floor_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ⌊a⌋₊ = ⌊b⌋₊) :
    |a - b| < 1 := by
  have h1 := Nat.lt_floor_add_one a
  have h2 := Nat.lt_floor_add_one b
  have h3 := Nat.floor_le ha
  have h4 := Nat.floor_le hb
  rw [h] at h1 h3
  rw [abs_lt]; constructor <;> linarith

/-- Deterministic bound: `m` points in `[-L, L]²`, radius `r > 0`, and any supergraph `G` of
the unit-disk graph satisfy `m ≤ (tw G + 1) · (32 L² / r² + 2)`. -/
theorem points_le_treewidth {m : ℕ} (p : Fin m → E2) (L r : ℝ) (hL : 0 < L) (hr : 0 < r)
    (hbox : ∀ i k, |p i k| ≤ L) (G : SimpleGraph (Fin m)) (hG : unitDiskGraph p r ≤ G) :
    (m : ℝ) ≤ (treewidth G + 1) * (32 * L ^ 2 / r ^ 2 + 2) := by
  classical
  set s := r / 2 with hs
  have hs0 : 0 < s := by positivity
  set M := ⌊2 * L / s⌋₊ with hM
  let cell : E2 → ℕ × ℕ := fun x => (⌊(x 0 + L) / s⌋₊, ⌊(x 1 + L) / s⌋₊)
  have hnn : ∀ i k, 0 ≤ (p i k + L) / s := fun i k => by
    have := (abs_le.1 (hbox i k)).1; exact div_nonneg (by linarith) hs0.le
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      cell (p i) ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1) := by
    intro i _
    have hk : ∀ k, ⌊(p i k + L) / s⌋₊ < M + 1 := fun k => by
      have : ⌊(p i k + L) / s⌋₊ ≤ M := Nat.floor_le_floor (by
        have := (abs_le.1 (hbox i k)).2
        exact div_le_div_of_nonneg_right (by linarith) hs0.le)
      omega
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨hk 0, hk 1⟩
  obtain ⟨y, -, hy⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps
    ⟨(0, 0), by simp⟩ (b := (m : ℝ) / ((M + 1) * (M + 1) : ℕ)) (by
      rw [nsmul_eq_mul, Finset.card_product, Finset.card_range, Finset.card_univ,
        Fintype.card_fin, mul_div_cancel₀]
      positivity)
  set K := {x ∈ (Finset.univ : Finset (Fin m)) | cell (p x) = y}
  have hclique : G.IsClique (K : Set (Fin m)) := by
    intro i hi j hj hij
    apply hG
    simp only [K, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    rw [← hj] at hi
    simp only [cell, Prod.mk.injEq] at hi
    have hd : ∀ k : Fin 2, |p i k - p j k| < s := fun k => by
      have h := abs_sub_lt_of_floor_eq (hnn i k) (hnn j k) (by fin_cases k <;> simp [hi.1, hi.2])
      rw [← sub_div, abs_div, abs_of_pos hs0, div_lt_one hs0] at h
      have e : p i k + L - (p j k + L) = p i k - p j k := by ring
      rwa [e] at h
    refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨hij, Or.inl ?_⟩
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
    calc √(|p i 0 - p j 0| ^ 2 + |p i 1 - p j 1| ^ 2) ≤ √(r ^ 2) := by
          apply Real.sqrt_le_sqrt
          have h0 := hd 0; have h1 := hd 1
          have a0 := abs_nonneg (p i 0 - p j 0); have a1 := abs_nonneg (p i 1 - p j 1)
          nlinarith
      _ = r := Real.sqrt_sq hr.le
  have hK := card_clique_le_treewidth_add_one G K hclique
  have hMle : (M : ℝ) ≤ 4 * L / r := by
    have h1 : (M : ℝ) ≤ 2 * L / s := Nat.floor_le (show 0 ≤ 2 * L / s by positivity)
    have e : 2 * L / s = 4 * L / r := by rw [hs]; field_simp; ring
    linarith
  have hcells : ((M : ℝ) + 1) * (M + 1) ≤ 32 * L ^ 2 / r ^ 2 + 2 := by
    have e : 32 * L ^ 2 / r ^ 2 = 2 * (4 * L / r) ^ 2 := by field_simp; ring
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith [sq_nonneg ((M : ℝ) - 1)]
  have hpos : (0 : ℝ) < ((M : ℝ) + 1) * (M + 1) := by positivity
  push_cast at hy
  rw [div_le_iff₀ hpos] at hy
  have hK' : (K.card : ℝ) ≤ treewidth G + 1 := by exact_mod_cast hK
  have htw : (0 : ℝ) ≤ treewidth G + 1 := by positivity
  calc (m : ℝ) ≤ K.card * (((M : ℝ) + 1) * (M + 1)) := hy
    _ ≤ (treewidth G + 1) * (((M : ℝ) + 1) * (M + 1)) := by gcongr
    _ ≤ (treewidth G + 1) * (32 * L ^ 2 / r ^ 2 + 2) := by gcongr

/-- At or above the connectivity scale (`n r² ≥ c₀ log n`), with `m ≥ n / 2` points:
`log n ≤ A · (tw + 1)` for `A = 64 L² / c₀ + 4`. -/
theorem log_le_treewidth {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ 2 * m) (p : Fin m → E2)
    (L c₀ r : ℝ) (hL : 0 < L) (hc : 0 < c₀) (hr : 0 < r) (hbox : ∀ i k, |p i k| ≤ L)
    (hrad : c₀ * Real.log n ≤ n * r ^ 2) (G : SimpleGraph (Fin m)) (hG : unitDiskGraph p r ≤ G) :
    Real.log n ≤ (64 * L ^ 2 / c₀ + 4) * (treewidth G + 1) := by
  have h := points_le_treewidth p L r hL hr hbox G hG
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlogn : Real.log n ≤ n := by linarith [Real.log_le_sub_one_of_pos hn0]
  have hnm' : (n : ℝ) ≤ 2 * m := by exact_mod_cast hnm
  have htw : (0 : ℝ) ≤ treewidth G + 1 := by positivity
  have hq : Real.log n / r ^ 2 ≤ n / c₀ := by
    rw [div_le_div_iff₀ (by positivity) hc]; linarith
  -- `n log n ≤ 2 m log n ≤ 2 (tw+1) (32 L² log n / r² + 2 log n) ≤ 2 (tw+1) (32 L² n / c₀ + 2 n)`
  have key : (n : ℝ) * Real.log n ≤ n * ((64 * L ^ 2 / c₀ + 4) * (treewidth G + 1)) := by
    have e1 : 32 * L ^ 2 / r ^ 2 * Real.log n = 32 * L ^ 2 * (Real.log n / r ^ 2) := by ring
    have e2 : 32 * L ^ 2 * (n / c₀) = n * (32 * L ^ 2 / c₀) := by ring
    have h3 : 32 * L ^ 2 / r ^ 2 * Real.log n ≤ n * (32 * L ^ 2 / c₀) := by
      rw [e1, ← e2]; gcongr
    have h4 : (m : ℝ) * Real.log n ≤
        (treewidth G + 1) * (32 * L ^ 2 / r ^ 2 * Real.log n + 2 * Real.log n) := by
      nlinarith
    have s1 : (n : ℝ) * Real.log n ≤ 2 * (m * Real.log n) := by
      nlinarith [mul_le_mul_of_nonneg_right hnm' hlog0]
    have s3 : (treewidth G + 1) * (32 * L ^ 2 / r ^ 2 * Real.log n + 2 * Real.log n) ≤
        (treewidth G + 1) * (n * (32 * L ^ 2 / c₀) + 2 * n) :=
      mul_le_mul_of_nonneg_left (add_le_add h3 (by linarith)) htw
    have e3 : 2 * ((treewidth G + 1) * (n * (32 * L ^ 2 / c₀) + 2 * n)) =
        (n : ℝ) * ((64 * L ^ 2 / c₀ + 4) * (treewidth G + 1)) := by ring
    linarith
  exact le_of_mul_le_mul_left key hn0

/-! ## Main theorem -/

/-- **Disproof of the upper bound.**  For every box `[-L, L]²`, every `c₀ > 0` and every
constant `C`, there is `N` such that for every `n ≥ N`, every `m ≥ n / 2`, every placement of
`m` points in the box and every radius `r > 0` with `n r² ≥ c₀ log n`, every supergraph `G` of
the unit-disk graph has `tw(G) > C · √(log n / log log n)`. -/
theorem treewidth_not_upper_bound_supergraph (L c₀ C : ℝ) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ, n ≤ 2 * m → ∀ (p : Fin m → E2) (r : ℝ),
      (∀ i k, |p i k| ≤ L) → 0 < r → c₀ * Real.log n ≤ n * r ^ 2 →
      ∀ G : SimpleGraph (Fin m), unitDiskGraph p r ≤ G →
      C * √(Real.log n / Real.log (Real.log n)) < treewidth G := by
  set A := 64 * L ^ 2 / c₀ + 4 with hA
  have hA0 : 0 < A := by positivity
  set X := A * |C| + A + 1 with hX
  have hX1 : 1 ≤ X := by have := abs_nonneg C; nlinarith
  refine ⟨⌈Real.exp (max (X ^ 2) (Real.exp 1))⌉₊ + 1, fun n hn m hnm p r hbox hr hrad G hG => ?_⟩
  have hn' : Real.exp (max (X ^ 2) (Real.exp 1)) ≤ n := by
    have := Nat.le_ceil (Real.exp (max (X ^ 2) (Real.exp 1)))
    have h2 : ((⌈Real.exp (max (X ^ 2) (Real.exp 1))⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2; linarith
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn'
  have hn1 : 1 ≤ n := by exact_mod_cast hn0
  set ℓ := Real.log n with hℓ
  have hℓm : max (X ^ 2) (Real.exp 1) ≤ ℓ := (Real.le_log_iff_exp_le hn0).2 hn'
  have hℓX : X ^ 2 ≤ ℓ := le_trans (le_max_left _ _) hℓm
  have hℓe : Real.exp 1 ≤ ℓ := le_trans (le_max_right _ _) hℓm
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.exp_pos 1) hℓe
  have hll : 1 ≤ Real.log ℓ := (Real.le_log_iff_exp_le hℓ0).2 hℓe
  have hbound := log_le_treewidth hn1 hnm p L c₀ r hL hc hr hbox hrad G hG
  rw [← hℓ, ← hA] at hbound
  set x := √ℓ with hx
  have hx2 : x ^ 2 = ℓ := Real.sq_sqrt hℓ0.le
  have hxX : X ≤ x := by
    rw [hx]; exact Real.le_sqrt_of_sq_le hℓX
  have hsq : √(ℓ / Real.log ℓ) ≤ x :=
    Real.sqrt_le_sqrt (div_le_self hℓ0.le hll)
  have hC : C * √(ℓ / Real.log ℓ) ≤ |C| * x := by
    calc C * √(ℓ / Real.log ℓ) ≤ |C| * √(ℓ / Real.log ℓ) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
      _ ≤ |C| * x := mul_le_mul_of_nonneg_left hsq (abs_nonneg C)
  have hCx : A * (|C| * x) + A < x ^ 2 := by
    have := abs_nonneg C
    nlinarith
  have : A * (|C| * x) < A * (treewidth G : ℝ) := by nlinarith
  have := lt_of_mul_lt_mul_left this hA0.le
  linarith

/-- The statement for the unit-disk graph itself. -/
theorem treewidth_not_upper_bound (L c₀ C : ℝ) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ, n ≤ 2 * m → ∀ (p : Fin m → E2) (r : ℝ),
      (∀ i k, |p i k| ≤ L) → 0 < r → c₀ * Real.log n ≤ n * r ^ 2 →
      C * √(Real.log n / Real.log (Real.log n)) < treewidth (unitDiskGraph p r) := by
  obtain ⟨N, hN⟩ := treewidth_not_upper_bound_supergraph L c₀ C hL hc
  exact ⟨N, fun n hn m hnm p r hbox hr hrad => hN n hn m hnm p r hbox hr hrad _ le_rfl⟩

/-- **Probability zero.**  For `n ≥ N` points (binomial model), every measure `μ` on placements
that is carried by the box `[-L, L]²` gives the event `tw ≤ C · √(log n / log log n)`
measure zero. -/
theorem prob_upper_bound_eq_zero (L c₀ C : ℝ) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (r : ℝ), 0 < r → c₀ * Real.log n ≤ n * r ^ 2 →
      ∀ μ : MeasureTheory.Measure (Fin n → E2), μ {p | ∀ i k, |p i k| ≤ L}ᶜ = 0 →
      μ {p | (treewidth (unitDiskGraph p r) : ℝ) ≤
        C * √(Real.log n / Real.log (Real.log n))} = 0 := by
  obtain ⟨N, hN⟩ := treewidth_not_upper_bound L c₀ C hL hc
  refine ⟨N, fun n hn r hr hrad μ hμ => MeasureTheory.measure_mono_null ?_ hμ⟩
  intro p hp hbox
  exact absurd hp (not_le.2 (hN n hn n (by omega) p r hbox hr hrad))

end C1680
