/-!
# Conjecture 00000003952: twin-width at most 1 is not the same as distance-hereditary

The conjecture contains the clause

  "The graphs of twin-width at most 1 are exactly the distance-hereditary graphs."

We refute this clause in both directions:

* the **house** `H` (vertices `0,…,4`, edges `02,03,04,13,14,24`; it is the complement of
  the path `0-1-2-3-4`) has twin-width at most 1 (indeed exactly 1) but is **not**
  distance-hereditary: `d_H(2,3) = 2` (via `2-0-3`), while in the connected induced
  subgraph `H - 0 = H[{1,2,3,4}]` (the path `2-4-1-3`) the distance is 3;
* the **net** `N` (triangle `0,1,2` with pendant vertices `3,4,5` attached to `0,1,2`)
  is distance-hereditary but has twin-width exactly 2 (every first contraction already
  creates a vertex of red degree 2).

Everything is defined from scratch in core Lean 4:

* graphs on `{0,…,n-1}` given by an edge list;
* trigraphs (red/black graphs), the contraction of two vertices (standard rule: the
  merged vertex is black-adjacent to `w` iff both parts were black-adjacent to `w`,
  non-adjacent iff both were non-adjacent, red otherwise -- in particular red edges stay red),
  contraction sequences, the width of a sequence (maximum red degree over all trigraphs
  along it) and `TwwLe G d` (twin-width at most `d`, i.e. some contraction sequence has
  width at most `d`);
* walks in induced subgraphs (`Reach`), connected induced subgraphs and the
  distance-hereditary property (every connected induced subgraph is isometric).
-/

namespace TwinWidth

/-! ## Graphs -/

/-- A graph on the vertex set `{0, …, n-1}`, given by a list of edges. -/
structure Graph where
  n : Nat
  edges : List (Nat × Nat)

/-- Adjacency (symmetric by construction). -/
def Graph.adj (G : Graph) (u v : Nat) : Bool :=
  G.edges.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

/-- Well-formed simple graph: edges join two distinct vertices of `{0, …, n-1}`. -/
def Graph.WF (G : Graph) : Prop := ∀ e ∈ G.edges, e.1 < G.n ∧ e.2 < G.n ∧ e.1 ≠ e.2

instance (G : Graph) : Decidable G.WF := by unfold Graph.WF; infer_instance

theorem Graph.adj_lt {G : Graph} (hG : G.WF) {u v : Nat} (h : G.adj u v = true) :
    v < G.n := by
  unfold Graph.adj at h
  rw [List.any_eq_true] at h
  obtain ⟨e, he, h⟩ := h
  have := hG e he
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
  · rw [← h2]; exact this.2.1
  · rw [← h1]; exact this.1

/-! ## Trigraphs, contractions and twin-width -/

/-- Colour of a pair of vertices in a trigraph. -/
inductive Col
  | none
  | black
  | red
  deriving DecidableEq, Repr

/-- A trigraph (red/black graph): a list of vertices and a list of coloured edges
`(a, b, c)` with `c ∈ {black, red}` (each unordered pair listed at most once). -/
structure Trigraph where
  verts : List Nat
  edges : List (Nat × Nat × Col)

/-- The colour of the pair `{a, b}`. -/
def Trigraph.col (T : Trigraph) (a b : Nat) : Col :=
  match T.edges.find? (fun e => (e.1 == a && e.2.1 == b) || (e.1 == b && e.2.1 == a)) with
  | some e => e.2.2
  | none => .none

/-- Colour of the edge from a merged vertex to `w`, given the colours from the two parts:
black iff both black, absent iff both absent, red otherwise. -/
def mergeCol : Col → Col → Col
  | .black, .black => .black
  | .none, .none => .none
  | _, _ => .red

/-- Contract the vertices `u` and `v` of `T` into one vertex, which keeps the name `u`.
Edges not touching `u, v` are unchanged; the edge from the new vertex to any other `w`
gets colour `mergeCol (col u w) (col v w)`. -/
def Trigraph.contract (T : Trigraph) (u v : Nat) : Trigraph :=
  { verts := T.verts.filter (· != v)
    edges := T.edges.filter (fun e => e.1 != u && e.1 != v && e.2.1 != u && e.2.1 != v) ++
      (T.verts.filter (fun w => w != u && w != v)).filterMap fun w =>
        match mergeCol (T.col u w) (T.col v w) with
        | .none => Option.none
        | c => some (u, w, c) }

/-- Red degree of `x`. -/
def Trigraph.redDeg (T : Trigraph) (x : Nat) : Nat :=
  (T.verts.filter fun w => w != x && T.col x w == .red).length

/-- Maximum red degree of a trigraph. -/
def Trigraph.maxRedDeg (T : Trigraph) : Nat := (T.verts.map T.redDeg).foldr max 0

/-- The trigraph of a graph: all edges black, no red edges. -/
def Graph.toTrigraph (G : Graph) : Trigraph :=
  { verts := List.range G.n
    edges := (List.range G.n).flatMap fun a => (List.range G.n).filterMap fun b =>
      if a < b && G.adj a b then some (a, b, Col.black) else Option.none }

/-- A contraction sequence: every step contracts two distinct current vertices, and at the
end at most one vertex is left. -/
def IsContractionSeq : Trigraph → List (Nat × Nat) → Bool
  | T, [] => T.verts.length ≤ 1
  | T, (u, v) :: s => T.verts.contains u && T.verts.contains v && u != v &&
      IsContractionSeq (T.contract u v) s

/-- All trigraphs along a contraction sequence (including the initial one). -/
def trigraphsAlong : Trigraph → List (Nat × Nat) → List Trigraph
  | T, [] => [T]
  | T, (u, v) :: s => T :: trigraphsAlong (T.contract u v) s

/-- Width of a contraction sequence: the maximum red degree of all its trigraphs. -/
def seqWidth (T : Trigraph) (s : List (Nat × Nat)) : Nat :=
  ((trigraphsAlong T s).map Trigraph.maxRedDeg).foldr max 0

/-- Twin-width at most `d`: some contraction sequence of `G` has width at most `d`
(twin-width = minimum width over all contraction sequences). -/
def TwwLe (G : Graph) (d : Nat) : Prop :=
  ∃ s, IsContractionSeq G.toTrigraph s = true ∧ seqWidth G.toTrigraph s ≤ d

/-- Twin-width exactly `d`. -/
def TwwEq (G : Graph) (d : Nat) : Prop := TwwLe G d ∧ ∀ d', d' < d → ¬ TwwLe G d'

theorem seqWidth_cons (T : Trigraph) (u v : Nat) (s : List (Nat × Nat)) :
    seqWidth T ((u, v) :: s) = max T.maxRedDeg (seqWidth (T.contract u v) s) := rfl

theorem maxRedDeg_le_seqWidth (T : Trigraph) (s : List (Nat × Nat)) :
    T.maxRedDeg ≤ seqWidth T s := by
  cases s with
  | nil => simp [seqWidth, trigraphsAlong]
  | cons p s => obtain ⟨u, v⟩ := p; rw [seqWidth_cons]; exact Nat.le_max_left _ _

/-- Lower bound: if every first contraction of `G` produces a trigraph with a vertex of
red degree greater than `d` (and `G` has at least two vertices), then `tww G > d`. -/
theorem not_twwLe_of_first (G : Graph) (d : Nat) (hn : 2 ≤ G.n)
    (h : ∀ u, u < G.n → ∀ v, v < G.n → u ≠ v → d < (G.toTrigraph.contract u v).maxRedDeg) :
    ¬ TwwLe G d := by
  rintro ⟨s, hs, hw⟩
  cases s with
  | nil =>
    simp [IsContractionSeq, Graph.toTrigraph, List.length_range] at hs
    omega
  | cons p s =>
    obtain ⟨u, v⟩ := p
    simp only [IsContractionSeq, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
    obtain ⟨⟨⟨hu, hv⟩, huv⟩, -⟩ := hs
    rw [List.contains_iff_mem] at hu hv
    simp only [Graph.toTrigraph, List.mem_range] at hu hv
    have h1 := h u hu v hv huv
    have h2 := maxRedDeg_le_seqWidth (G.toTrigraph.contract u v) s
    rw [seqWidth_cons] at hw
    have h3 := Nat.le_max_right (G.toTrigraph.maxRedDeg)
      (seqWidth (G.toTrigraph.contract u v) s)
    omega

/-! ## Walks in induced subgraphs, distance-hereditary graphs -/

/-- `Reach G m k x y`: there is a walk `x = v₀, v₁, …, v_j = y` with `j ≤ k`, consecutive
vertices adjacent in `G`, and `v₁, …, v_j` in the vertex set encoded by the bit mask `m`.
For `x` in `m` this says `dist_{G[m]}(x, y) ≤ k`. -/
inductive Reach (G : Graph) (m : Nat) : Nat → Nat → Nat → Prop
  | refl (k x : Nat) : Reach G m k x x
  | step {k x z y : Nat} : Reach G m k x z → G.adj z y = true → m.testBit y = true →
      Reach G m (k + 1) x y

/-- The mask of the full vertex set `{0, …, n-1}`. -/
def full (G : Graph) : Nat := 2 ^ G.n - 1

/-- `G[m]` is connected (as an induced subgraph on the vertex set `m ⊆ {0,…,n-1}`). -/
def ConnectedOn (G : Graph) (m : Nat) : Prop :=
  ∀ x y, m.testBit x = true → m.testBit y = true → ∃ k, Reach G m k x y

/-- Distance-hereditary: every connected induced subgraph `G[m]` is isometric, i.e.
`dist_{G[m]}(x, y) ≤ k` whenever `dist_G(x, y) ≤ k`, for `x, y ∈ m`. -/
def DH (G : Graph) : Prop :=
  ∀ m, m < 2 ^ G.n → ConnectedOn G m → ∀ x y, m.testBit x = true → m.testBit y = true →
    ∀ k, Reach G (full G) k x y → Reach G m k x y

/-! ### Computable balls -/

/-- One BFS step inside `G[m]`. -/
def ballStep (G : Graph) (m : Nat) (b : List Nat) : List Nat :=
  (List.range G.n).filter fun v => b.contains v || (m.testBit v && b.any fun z => G.adj z v)

/-- The ball of radius `k` around `x` in `G[m]`. -/
def ball (G : Graph) (m x : Nat) : Nat → List Nat
  | 0 => (List.range G.n).filter (· == x)
  | k + 1 => ballStep G m (ball G m x k)

theorem mem_ballStep {G : Graph} {m : Nat} {b : List Nat} {v : Nat} :
    v ∈ ballStep G m b ↔ v < G.n ∧ (v ∈ b ∨ (m.testBit v = true ∧ ∃ z ∈ b, G.adj z v = true)) := by
  simp [ballStep, List.mem_filter, List.mem_range, List.any_eq_true, List.contains_iff_mem]

theorem ball_lt {G : Graph} {m x : Nat} : ∀ {k y}, y ∈ ball G m x k → y < G.n
  | 0, y, h => by simp [ball, List.mem_filter, List.mem_range] at h; exact h.1
  | k + 1, y, h => (mem_ballStep.1 h).1

theorem ball_succ {G : Graph} {m x k y : Nat} (h : y ∈ ball G m x k) : y ∈ ball G m x (k + 1) :=
  mem_ballStep.2 ⟨ball_lt h, Or.inl h⟩

theorem ball_mono {G : Graph} {m x k y : Nat} (h : y ∈ ball G m x k) :
    ∀ j, y ∈ ball G m x (k + j)
  | 0 => h
  | j + 1 => ball_succ (ball_mono h j)

theorem ball_stable {G : Graph} {m x K : Nat} (h : ball G m x (K + 1) = ball G m x K) :
    ∀ j, ball G m x (K + j) = ball G m x K
  | 0 => rfl
  | j + 1 => by
    show ballStep G m (ball G m x (K + j)) = ball G m x K
    rw [ball_stable h j]; exact h

/-- Monotonicity of `Reach` in the length bound. -/
theorem Reach.succ {G : Graph} {m k x y : Nat} (h : Reach G m k x y) : Reach G m (k + 1) x y := by
  induction h with
  | refl k x => exact Reach.refl _ _
  | step _ h2 h3 ih => exact Reach.step ih h2 h3

theorem reach_iff_ball {G : Graph} (hG : G.WF) {m x : Nat} (hx : x < G.n) :
    ∀ k y, Reach G m k x y ↔ y ∈ ball G m x k := by
  intro k
  induction k with
  | zero =>
    intro y
    simp only [ball, List.mem_filter, List.mem_range, beq_iff_eq]
    constructor
    · intro h; cases h; exact ⟨hx, rfl⟩
    · rintro ⟨-, rfl⟩; exact Reach.refl 0 y
  | succ k ih =>
    intro y
    rw [ball, mem_ballStep]
    constructor
    · intro h
      cases h with
      | refl => exact ⟨hx, Or.inl ((ih x).1 (Reach.refl k x))⟩
      | step h1 h2 h3 => exact ⟨Graph.adj_lt hG h2, Or.inr ⟨h3, _, (ih _).1 h1, h2⟩⟩
    · rintro ⟨-, h | ⟨h3, z, hz, h2⟩⟩
      · exact Reach.succ ((ih y).2 h)
      · exact Reach.step ((ih z).2 hz) h2 h3

/-! ### A Boolean certificate for being distance-hereditary -/

/-- `G[m]` connected, checked with balls of radius `n`. -/
def connB (G : Graph) (m : Nat) : Bool :=
  (List.range G.n).all fun x => (List.range G.n).all fun y =>
    !(m.testBit x && m.testBit y) || (ball G m x G.n).contains y

/-- Finite check: for every mask `m < 2^n` and every `x < n`, balls are stable at radius `n`,
and if `G[m]` is connected then for `x, y ∈ m` and `k ≤ n`, `y` in the `k`-ball of `G` implies
`y` in the `k`-ball of `G[m]`. -/
def dhCheck (G : Graph) : Bool :=
  (List.range (2 ^ G.n)).all fun m => (List.range G.n).all fun x =>
    (ball G m x (G.n + 1) == ball G m x G.n) &&
    (!(m.testBit x && connB G m) ||
      (List.range (G.n + 1)).all fun k => (List.range G.n).all fun y =>
        !m.testBit y || !(ball G (full G) x k).contains y || (ball G m x k).contains y)

theorem lt_of_testBit {m n x : Nat} (hm : m < 2 ^ n) (h : m.testBit x = true) : x < n := by
  apply Nat.lt_of_not_le
  intro hx
  have : m < 2 ^ x := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hx)
  rw [Nat.testBit_lt_two_pow this] at h
  exact Bool.false_ne_true h

theorem full_lt (G : Graph) : full G < 2 ^ G.n := by
  unfold full
  have : 0 < 2 ^ G.n := Nat.pow_pos (by decide)
  omega

/-- Soundness of `dhCheck`. -/
theorem dh_of_check (G : Graph) (hG : G.WF) (hc : dhCheck G = true) : DH G := by
  intro m hm hconn x y hx hy k hr
  have hxn : x < G.n := lt_of_testBit hm hx
  unfold dhCheck at hc
  rw [List.all_eq_true] at hc
  -- stability of all balls at radius `n`
  have stab : ∀ m', m' < 2 ^ G.n → ∀ x', x' < G.n → ∀ j,
      ball G m' x' (G.n + j) = ball G m' x' G.n := by
    intro m' hm' x' hx' j
    have := hc m' (List.mem_range.2 hm')
    rw [List.all_eq_true] at this
    have := this x' (List.mem_range.2 hx')
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ball_stable this.1 j
  -- membership in a ball of any radius reduces to radius `min k n`
  have toN : ∀ m', m' < 2 ^ G.n → ∀ x', x' < G.n → ∀ k y', y' ∈ ball G m' x' k →
      y' ∈ ball G m' x' G.n := by
    intro m' hm' x' hx' k y' h
    by_cases hk : k ≤ G.n
    · have := ball_mono h (G.n - k)
      rwa [Nat.add_sub_cancel' hk] at this
    · have e := stab m' hm' x' hx' (k - G.n)
      rw [Nat.add_sub_cancel' (by omega)] at e
      rwa [e] at h
  have hcm := hc m (List.mem_range.2 hm)
  rw [List.all_eq_true] at hcm
  have hcx := hcm x (List.mem_range.2 hxn)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    List.all_eq_true, List.mem_range] at hcx
  have hcb : connB G m = true := by
    unfold connB
    rw [List.all_eq_true]
    intro a ha
    rw [List.all_eq_true]
    intro b _
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
    by_cases ha' : m.testBit a = true
    · by_cases hb' : m.testBit b = true
      · right
        obtain ⟨j, hj⟩ := hconn a b ha' hb'
        have ha2 := List.mem_range.1 ha
        rw [List.contains_iff_mem]
        exact toN m hm a ha2 j b ((reach_iff_ball hG ha2 j b).1 hj)
      · left; right; simpa using hb'
    · left; left; simpa using ha'
  have hmain := hcx.2
  rcases hmain with (h | h) | h
  · rw [hx] at h; exact absurd h (by decide)
  · rw [hcb] at h; exact absurd h (by decide)
  · rw [reach_iff_ball hG hxn] at hr ⊢
    have hyn : y < G.n := ball_lt hr
    -- reduce `k` to `k' = min k n`
    by_cases hk : k ≤ G.n
    · have := h k (by omega) y hyn
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at this
      rcases this with (h1 | h1) | h1
      · rw [hy] at h1; exact absurd h1 (by decide)
      · exact absurd hr (by simpa using h1)
      · exact h1
    · have hf := stab (full G) (full_lt G) x hxn (k - G.n)
      have hm' := stab m hm x hxn (k - G.n)
      rw [Nat.add_sub_cancel' (by omega)] at hf hm'
      rw [hf] at hr
      rw [hm']
      have := h G.n (by omega) y hyn
      simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at this
      rcases this with (h1 | h1) | h1
      · rw [hy] at h1; exact absurd h1 (by decide)
      · exact absurd hr (by simpa using h1)
      · exact h1

/-! ## The counterexamples -/

/-- The house: complement of the path `0-1-2-3-4`; square `0-3-1-4-0` with roof `2` on `04`. -/
def house : Graph := ⟨5, [(0,2), (0,3), (0,4), (1,3), (1,4), (2,4)]⟩

/-- The net: triangle `0,1,2` with pendant vertices `3,4,5` attached to `0,1,2`. -/
def net : Graph := ⟨6, [(0,1), (1,2), (0,2), (0,3), (1,4), (2,5)]⟩

/-- The path `0-1-2-3-4` (used only as a sanity check). -/
def P5 : Graph := ⟨5, [(0,1), (1,2), (2,3), (3,4)]⟩

theorem house_wf : house.WF := by decide
theorem net_wf : net.WF := by decide
theorem P5_wf : P5.WF := by decide

/-- The contraction sequence for the house: `{3,4}`, then `2`, `1`, `0` are merged into it. -/
def houseSeq : List (Nat × Nat) := [(3,4), (3,2), (3,1), (3,0)]

theorem house_seq_valid : IsContractionSeq house.toTrigraph houseSeq = true := by decide

/-- The red degrees along the sequence are `0, 1, 1, 1, 0`. -/
theorem house_seq_widths :
    (trigraphsAlong house.toTrigraph houseSeq).map Trigraph.maxRedDeg = [0, 1, 1, 1, 0] := by
  decide

theorem house_twwLe_one : TwwLe house 1 := ⟨houseSeq, house_seq_valid, by decide⟩

/-- The house has no twins: every first contraction creates a red edge. -/
theorem house_not_twwLe_zero : ¬ TwwLe house 0 := by
  apply not_twwLe_of_first house 0 (by decide)
  have : ∀ u, u < 5 → ∀ v, v < 5 → u ≠ v → 0 < (house.toTrigraph.contract u v).maxRedDeg := by
    decide
  exact this

theorem house_tww_eq_one : TwwEq house 1 := by
  refine ⟨house_twwLe_one, fun d hd => ?_⟩
  have : d = 0 := by omega
  subst this; exact house_not_twwLe_zero

/-- The vertex set `{1,2,3,4}` as a bit mask. -/
def houseMinus0 : Nat := 0b11110

theorem houseMinus0_connected : ConnectedOn house houseMinus0 := by
  intro x y hx hy
  refine ⟨3, ?_⟩
  have hxn : x < 5 := lt_of_testBit (n := 5) (by decide) hx
  have hyn : y < 5 := lt_of_testBit (n := 5) (by decide) hy
  rw [reach_iff_ball house_wf hxn]
  have : ∀ x, x < 5 → ∀ y, y < 5 → houseMinus0.testBit x = true →
      houseMinus0.testBit y = true → (ball house houseMinus0 x 3).contains y = true := by
    decide
  exact List.contains_iff_mem.1 (this x hxn y hyn hx hy)

/-- `d_H(2,3) ≤ 2` via the walk `2-0-3`. -/
theorem house_reach_2_3 : Reach house (full house) 2 2 3 :=
  Reach.step (Reach.step (Reach.refl 0 2) (z := 2) (y := 0) (by decide) (by decide))
    (by decide) (by decide)

/-- In `H - 0` the distance from 2 to 3 is more than 2. -/
theorem house_minus0_not_reach : ¬ Reach house houseMinus0 2 2 3 := by
  rw [reach_iff_ball house_wf (by decide)]
  decide

theorem house_not_DH : ¬ DH house := by
  intro h
  exact house_minus0_not_reach
    (h houseMinus0 (by decide) houseMinus0_connected 2 3 (by decide) (by decide) 2 house_reach_2_3)

set_option maxRecDepth 100000 in
theorem net_check : dhCheck net = true := by decide +kernel

theorem net_DH : DH net := dh_of_check net net_wf net_check

/-- Every first contraction of the net creates a vertex of red degree at least 2. -/
theorem net_first_contraction :
    ∀ u, u < 6 → ∀ v, v < 6 → u ≠ v → 1 < (net.toTrigraph.contract u v).maxRedDeg := by
  decide

theorem net_not_twwLe_one : ¬ TwwLe net 1 :=
  not_twwLe_of_first net 1 (by decide) net_first_contraction

/-- A width-2 sequence for the net: contract `3` into `0`, `4` into `1`, `5` into `2`,
then the triangle. -/
theorem net_twwLe_two : TwwLe net 2 :=
  ⟨[(0,3), (1,4), (2,5), (0,1), (0,2)], by decide, by decide⟩

theorem net_tww_eq_two : TwwEq net 2 := by
  refine ⟨net_twwLe_two, fun d hd h => net_not_twwLe_one ?_⟩
  obtain ⟨s, hs, hw⟩ := h
  exact ⟨s, hs, by omega⟩

/-! ## Sanity checks (non-vacuity) -/

/-- The path `P5` has twin-width at most 1 and is distance-hereditary, so neither predicate
is trivially false, and the agreement claimed by the conjecture does hold for `P5`. -/
theorem P5_twwLe_one : TwwLe P5 1 := ⟨[(3,4), (3,2), (3,1), (3,0)], by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem P5_check : dhCheck P5 = true := by decide +kernel

theorem P5_DH : DH P5 := dh_of_check P5 P5_wf P5_check

/-! ## The conjecture -/

/-- The first clause of conjecture 00000003952: the (simple) graphs of twin-width at most 1
are exactly the distance-hereditary graphs. -/
def Clause : Prop := ∀ G : Graph, G.WF → (TwwLe G 1 ↔ DH G)

/-- Inclusion "twin-width ≤ 1 ⟹ distance-hereditary". -/
def ClauseTwwToDH : Prop := ∀ G : Graph, G.WF → TwwLe G 1 → DH G

/-- Inclusion "distance-hereditary ⟹ twin-width ≤ 1". -/
def ClauseDHToTww : Prop := ∀ G : Graph, G.WF → DH G → TwwLe G 1

theorem twwToDH_false : ¬ ClauseTwwToDH := fun h =>
  house_not_DH (h house house_wf house_twwLe_one)

theorem DHToTww_false : ¬ ClauseDHToTww := fun h =>
  net_not_twwLe_one (h net net_wf net_DH)

theorem conjecture_00000003952_false : ¬ Clause := fun h =>
  twwToDH_false fun G hG hT => (h G hG).1 hT

/-- The conjecture is a conjunction of this clause with complexity statements; whatever
those are, the conjunction is false. -/
theorem conjecture_00000003952_conjunction_false (Rest : Prop) : ¬ (Clause ∧ Rest) :=
  fun h => conjecture_00000003952_false h.1

end TwinWidth

#print axioms TwinWidth.house_twwLe_one
#print axioms TwinWidth.house_tww_eq_one
#print axioms TwinWidth.house_not_DH
#print axioms TwinWidth.net_DH
#print axioms TwinWidth.net_tww_eq_two
#print axioms TwinWidth.P5_DH
#print axioms TwinWidth.twwToDH_false
#print axioms TwinWidth.DHToTww_false
#print axioms TwinWidth.conjecture_00000003952_false
#print axioms TwinWidth.conjecture_00000003952_conjunction_false
