/-!
# Conjecture 00000003481 (Thue numbers of trees): the logarithmic upper bound is false

The conjecture (paraphrased): *the Thue number of the binary tree is four and the Thue number
of general trees is unbounded; the Thue-number upper bound for trees is twice the logarithm of
the maximum degree, `π(T) ≤ 2 log Δ(T)`, attained asymptotically by subtree families of the
complete binary tree.*

This file refutes the clause **"`π(T) ≤ 2 log Δ(T)` for trees"** for **every logarithm base
`b > 1`** (base 2, `e`, 10, ...):

* the single edge `K₂` is a tree with `Δ = 1` and Thue number `2`, but `2 log_b 1 = 0`;
* the path `P₄` is a tree with `Δ = 2` and Thue number `3`, but `2 log_b 2 < 3` for every
  `b > 4^{1/3} ≈ 1.587` (so for `b = 2, e, 10`).

It also refutes the clause **"the Thue number of general trees is unbounded"** (section 7),
modulo one explicit hypothesis, Thue's theorem (1906) that square-free words of every length
exist over 3 letters (`ThueHyp`, or `ThueHypList` in list form): `tree_colorable_four` proves
that every tree has a Thue 4-colouring (Brešar, Grytczuk, Klavžar, Niwczyk, Peterin 2007), via
the Kündgen–Pelsmajer word, the folding lemma and the "down, then up" shape of paths in trees;
`conjecture_C2_false : ThueHyp → ¬ (∀ k, ∃ G, IsTree G ∧ ¬ Colorable G k)`.

Everything is defined from scratch in core Lean 4:

* `Graph`: a finite graph on `{0, …, n-1}` with a Boolean adjacency function;
  `IsTree`: simple, and any two vertices are joined by exactly one path;
* `IsPath`: a nonempty list of pairwise distinct vertices, consecutive ones adjacent
  (paths of **all** lengths, between **any** two vertices; not only root-to-leaf paths);
* `HasSquare s`: `s = a ++ x ++ x ++ b` with `x ≠ []` (a square factor `xx`);
* `Nonrepetitive G c`: no path has a colour sequence with a square factor (a Thue colouring);
* `Colorable G k`: a Thue colouring with colours in `{0, …, k-1}`;
* `IsThueNumber G k`: `k` is the least such number (it is unique, `thueNumber_unique`);
* `maxDeg G`: the maximum degree.

The real-valued bound `k ≤ 2 log_b Δ` (with `b > 1`, `Δ ≥ 1`) is equivalent to `b^k ≤ Δ²`;
for a rational base `b = p/q` this is `p^k ≤ Δ² q^k` (`LogBound`). Since a larger base gives a
stronger claim (`claim_mono`), refuting every rational base `p/q > 1` refutes every real base
`b > 1` as well (each real `b > 1` lies above some rational `p/q > 1`).
-/

namespace Thue3481

/-! ## 1. Graphs, paths, squares, Thue colourings -/

/-- A finite graph on the vertex set `{0, …, n-1}`, with a Boolean adjacency function. -/
structure Graph where
  n : Nat
  adj : Nat → Nat → Bool

/-- Consecutive vertices of the list are adjacent. -/
def adjChain (G : Graph) : List Nat → Bool
  | a :: b :: t => G.adj a b && adjChain G (b :: t)
  | _ => true

/-- A path of `G`: a nonempty sequence of pairwise distinct vertices of `G`, consecutive ones
adjacent. (A single vertex is a path with one vertex.) -/
def IsPath (G : Graph) (p : List Nat) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ (∀ v ∈ p, v < G.n) ∧ adjChain G p = true

/-- The word `s` contains a square factor `xx` with `x` nonempty. -/
def HasSquare (s : List Nat) : Prop :=
  ∃ a x b : List Nat, x ≠ [] ∧ s = a ++ x ++ x ++ b

/-- A Thue (nonrepetitive) colouring: the colour sequence of every path is square-free. -/
def Nonrepetitive (G : Graph) (c : Nat → Nat) : Prop :=
  ∀ p, IsPath G p → ¬ HasSquare (p.map c)

/-- `G` has a Thue colouring with colours `0, …, k-1`. -/
def Colorable (G : Graph) (k : Nat) : Prop :=
  ∃ c : Nat → Nat, (∀ v, v < G.n → c v < k) ∧ Nonrepetitive G c

/-- `k` is the Thue number `π(G)`: the least number of colours of a Thue colouring. -/
def IsThueNumber (G : Graph) (k : Nat) : Prop :=
  Colorable G k ∧ ∀ j, j < k → ¬ Colorable G j

theorem colorable_mono {G : Graph} {j k : Nat} (h : Colorable G j) (hjk : j ≤ k) :
    Colorable G k := by
  obtain ⟨c, hc, hn⟩ := h
  exact ⟨c, fun v hv => Nat.lt_of_lt_of_le (hc v hv) hjk, hn⟩

/-- The Thue number is well defined (unique). -/
theorem thueNumber_unique {G : Graph} {k k' : Nat} (h : IsThueNumber G k)
    (h' : IsThueNumber G k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hl | he | hg
  · exact absurd h.1 (h'.2 k hl)
  · exact he
  · exact absurd h'.1 (h.2 k' hg)

/-- To determine `π(G) = k` it suffices to give a `k`-colouring and exclude `k-1` colours. -/
theorem isThueNumber_of {G : Graph} {k : Nat} (hk : Colorable G k)
    (hlow : ¬ Colorable G (k - 1)) : IsThueNumber G k := by
  refine ⟨hk, fun j hj hc => hlow (colorable_mono hc (by omega))⟩

/-! ## 2. Trees and maximum degree -/

/-- Symmetric, loopless, and edges only between vertices of `G`. -/
def IsSimple (G : Graph) : Prop :=
  (∀ u v, G.adj u v = G.adj v u) ∧ (∀ u, G.adj u u = false) ∧
    (∀ u v, G.adj u v = true → u < G.n ∧ v < G.n)

/-- `p` is a path from `u` to `v`. -/
def PathFT (G : Graph) (p : List Nat) (u v : Nat) : Prop :=
  IsPath G p ∧ p.head? = some u ∧ p.getLast? = some v

/-- Any two vertices are joined by a path. -/
def Connected (G : Graph) : Prop :=
  ∀ u v, u < G.n → v < G.n → ∃ p, PathFT G p u v

/-- Any two vertices are joined by exactly one path. -/
def UniquePaths (G : Graph) : Prop :=
  ∀ u v, u < G.n → v < G.n → ∃ p, PathFT G p u v ∧ ∀ q, PathFT G q u v → q = p

/-- The edges `{u, v}` (listed once, as `(u, v)` with `u < v`). -/
def edgeList (G : Graph) : List (Nat × Nat) :=
  (List.range G.n).flatMap fun u =>
    ((List.range G.n).filter fun v => u < v && G.adj u v).map fun v => (u, v)

/-- A tree (textbook definition): a nonempty simple graph in which any two vertices are joined
by exactly one path. (For `K₂` and `P₄` we also check the equivalent "connected with `n - 1`
edges", see `K2_P4_connected_edges`.) -/
def IsTree (G : Graph) : Prop :=
  1 ≤ G.n ∧ IsSimple G ∧ UniquePaths G

def degree (G : Graph) (v : Nat) : Nat := ((List.range G.n).filter (G.adj v)).length

/-- The maximum degree `Δ(G)`. -/
def maxDeg (G : Graph) : Nat := ((List.range G.n).map (degree G)).foldl max 0

/-! ## 3. The clause of the conjecture -/

/-- `k ≤ 2·log_{p/q} Δ`, i.e. `(p/q)^k ≤ Δ²`, i.e. `p^k ≤ Δ²·q^k` (for `p > q ≥ 1`, `Δ ≥ 1`). -/
def LogBound (p q Δ k : Nat) : Prop := p ^ k ≤ Δ ^ 2 * q ^ k

/-- The clause "`π(T) ≤ 2 log_b Δ(T)` for every tree `T`", for the base `b = p/q`. -/
def Claim (p q : Nat) : Prop :=
  ∀ G k, IsTree G → 1 ≤ maxDeg G → IsThueNumber G k → LogBound p q (maxDeg G) k

/-- The same clause restricted to trees with `Δ ≥ 2` (excluding the single edge). -/
def ClaimDeg2 (p q : Nat) : Prop :=
  ∀ G k, IsTree G → 2 ≤ maxDeg G → IsThueNumber G k → LogBound p q (maxDeg G) k

/-- Colouring form (no minimum needed): "every tree has a Thue colouring with at most
`2 log_b Δ` colours". -/
def ClaimCol (p q : Nat) : Prop :=
  ∀ G, IsTree G → 1 ≤ maxDeg G → ∃ k, LogBound p q (maxDeg G) k ∧ Colorable G k

/-- A larger base gives a stronger claim: if `p'/q' ≤ p/q` then `Claim p q → Claim p' q'`.
Hence refuting all rational bases `> 1` refutes all real bases `> 1`. -/
theorem logBound_mono {p q p' q' Δ k : Nat} (hq : 0 < q) (hle : p' * q ≤ p * q')
    (h : LogBound p q Δ k) : LogBound p' q' Δ k := by
  unfold LogBound at *
  have h1 : (p' * q) ^ k ≤ (p * q') ^ k := Nat.pow_le_pow_left hle k
  rw [Nat.mul_pow, Nat.mul_pow] at h1
  have h2 : p ^ k * q' ^ k ≤ Δ ^ 2 * q ^ k * q' ^ k := Nat.mul_le_mul_right _ h
  have h3 : q ^ k * p' ^ k ≤ q ^ k * (Δ ^ 2 * q' ^ k) := by
    have e1 : q ^ k * p' ^ k = p' ^ k * q ^ k := Nat.mul_comm _ _
    have e2 : q ^ k * (Δ ^ 2 * q' ^ k) = Δ ^ 2 * q ^ k * q' ^ k := by
      rw [Nat.mul_comm (Δ ^ 2) (q ^ k), Nat.mul_assoc]
    rw [e1, e2]; exact Nat.le_trans h1 h2
  exact Nat.le_of_mul_le_mul_left h3 (Nat.pow_pos hq)

theorem claim_mono {p q p' q' : Nat} (hq : 0 < q) (hle : p' * q ≤ p * q') :
    Claim p q → Claim p' q' :=
  fun h G k hT hD hk => logBound_mono hq hle (h G k hT hD hk)

/-! ## 4. Deciding nonrepetitiveness on a finite graph -/

/-- Pigeonhole: a duplicate-free list of numbers `< n` has length `≤ n`. -/
theorem nodup_length_le : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ v ∈ l, v < n) →
    l.length ≤ n := by
  intro n
  induction n with
  | zero =>
    intro l _ hl
    cases l with
    | nil => exact Nat.le_refl _
    | cons a t => exact absurd (hl a (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | succ n ih =>
    intro l hnd hl
    by_cases hm : n ∈ l
    · have hlen := List.length_erase_of_mem hm
      have hnd' : (l.erase n).Nodup := List.Nodup.erase n hnd
      have hl' : ∀ v ∈ l.erase n, v < n := by
        intro v hv
        have := (List.Nodup.mem_erase_iff hnd).mp hv
        have := hl v this.2
        omega
      have := ih (l.erase n) hnd' hl'
      omega
    · have hl' : ∀ v ∈ l, v < n := by
        intro v hv
        have := hl v hv
        have : v ≠ n := fun e => hm (e ▸ hv)
        omega
      exact Nat.le_succ_of_le (ih l hnd hl')

/-- All lists of length `L` with entries `< n`. -/
def allLists (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | L + 1 => (allLists n L).flatMap fun l => (List.range n).map fun v => v :: l

theorem mem_allLists (n : Nat) : ∀ (L : Nat) (l : List Nat), l.length = L →
    (∀ v ∈ l, v < n) → l ∈ allLists n L := by
  intro L
  induction L with
  | zero =>
    intro l hlen _
    cases l with
    | nil => simp [allLists]
    | cons a t => simp at hlen
  | succ L ih =>
    intro l hlen hl
    cases l with
    | nil => simp at hlen
    | cons a t =>
      simp only [allLists, List.mem_flatMap, List.mem_map, List.mem_range]
      refine ⟨t, ih t (by simp at hlen; exact hlen) (fun v hv => hl v (List.mem_cons_of_mem _ hv)),
        a, hl a (List.mem_cons_self ..), rfl⟩

/-- All candidate vertex sequences of length `≤ n`. -/
def candidates (G : Graph) : List (List Nat) :=
  (List.range (G.n + 1)).flatMap (allLists G.n)

theorem path_mem_candidates {G : Graph} {p : List Nat} (hp : IsPath G p) :
    p ∈ candidates G := by
  obtain ⟨_, hnd, hin, _⟩ := hp
  have hlen := nodup_length_le G.n p hnd hin
  simp only [candidates, List.mem_flatMap, List.mem_range]
  exact ⟨p.length, by omega, mem_allLists G.n p.length p rfl hin⟩

/-- Boolean path test. -/
def pathB (G : Graph) (p : List Nat) : Bool :=
  !p.isEmpty && decide p.Nodup && p.all (fun v => decide (v < G.n)) && adjChain G p

theorem pathB_of_isPath {G : Graph} {p : List Nat} (hp : IsPath G p) : pathB G p = true := by
  obtain ⟨hne, hnd, hin, hch⟩ := hp
  have h1 : p.isEmpty = false := by
    cases p with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  have h3 : p.all (fun v => decide (v < G.n)) = true :=
    List.all_eq_true.mpr fun v hv => decide_eq_true (hin v hv)
  simp only [pathB, h1, h3, hch, decide_eq_true hnd, Bool.not_false, Bool.and_self]

theorem isPath_of_pathB {G : Graph} {p : List Nat} (h : pathB G p = true) : IsPath G p := by
  simp only [pathB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, h2, fun v hv => ?_, h4⟩
  · intro e; subst e; simp at h1
  · have := List.all_eq_true.mp h3 v hv
    simpa using this

/-- Boolean square test: some factor `s[i, i+k) = s[i+k, i+2k)` with `k ≥ 1`. -/
def hasSquareB (s : List Nat) : Bool :=
  (List.range s.length).any fun i => (List.range (s.length + 1)).any fun k =>
    decide (0 < k) && decide (i + 2 * k ≤ s.length) &&
      ((s.drop i).take k == (s.drop (i + k)).take k)

theorem hasSquareB_of_hasSquare {s : List Nat} (h : HasSquare s) : hasSquareB s = true := by
  obtain ⟨a, x, b, hx, rfl⟩ := h
  have hxpos : 0 < x.length := List.length_pos_iff.mpr hx
  have hlen : (a ++ x ++ x ++ b).length = a.length + x.length + x.length + b.length := by
    simp [List.length_append]; omega
  simp only [hasSquareB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  refine ⟨a.length, by omega, x.length, by omega, ⟨hxpos, by omega⟩, ?_⟩
  have e1 : (a ++ x ++ x ++ b).drop a.length = x ++ (x ++ b) := by
    rw [List.append_assoc, List.append_assoc, List.drop_left]
  have e2 : (a ++ x ++ x ++ b).drop (a.length + x.length) = x ++ b := by
    rw [← List.drop_drop, e1, List.drop_left]
  rw [e1, e2, List.take_left, List.take_left]

/-- Boolean check that the colouring `c` is nonrepetitive on all paths of `G`. -/
def nonrepB (G : Graph) (c : Nat → Nat) : Bool :=
  (candidates G).all fun p => !(pathB G p) || !(hasSquareB (p.map c))

theorem nonrepetitive_of_nonrepB {G : Graph} {c : Nat → Nat} (h : nonrepB G c = true) :
    Nonrepetitive G c := by
  intro p hp hsq
  have hm := path_mem_candidates hp
  have := List.all_eq_true.mp h p hm
  rw [pathB_of_isPath hp, hasSquareB_of_hasSquare hsq] at this
  exact absurd this (by decide)

/-! ## 5. The two counterexamples: `K₂` and `P₄` -/

/-- The single edge `K₂` (vertices 0, 1). -/
def K2 : Graph := ⟨2, fun u v => (u == 0 && v == 1) || (u == 1 && v == 0)⟩

/-- The path `P₄`: 0 - 1 - 2 - 3. -/
def P4 : Graph := ⟨4, fun u v => (u + 1 == v || v + 1 == u) && decide (u < 4) && decide (v < 4)⟩

/-- An explicit path from `u` to `v` along `0 - 1 - … - (n-1)`. -/
def seg (u v : Nat) : List Nat :=
  if u ≤ v then List.range' u (v - u + 1) else (List.range' v (u - v + 1)).reverse

/-- Boolean test for "`p` is a path from `u` to `v`". -/
def pathFTB (G : Graph) (p : List Nat) (u v : Nat) : Bool :=
  pathB G p && p.head? == some u && p.getLast? == some v

theorem pathFT_of_pathFTB {G : Graph} {p : List Nat} {u v : Nat} (h : pathFTB G p u v = true) :
    PathFT G p u v := by
  simp only [pathFTB, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨isPath_of_pathB h.1.1, h.1.2, h.2⟩

theorem pathFTB_of_pathFT {G : Graph} {p : List Nat} {u v : Nat} (h : PathFT G p u v) :
    pathFTB G p u v = true := by
  simp only [pathFTB, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨pathB_of_isPath h.1, h.2.1⟩, h.2.2⟩

/-- Unique paths, checked over all candidate vertex sequences (complete by
`path_mem_candidates`). -/
theorem uniquePaths_of_check {G : Graph}
    (h : ∀ u, u < G.n → ∀ v, v < G.n → (pathFTB G (seg u v) u v &&
      (candidates G).all (fun q => !(pathFTB G q u v) || q == seg u v)) = true) :
    UniquePaths G := by
  intro u v hu hv
  have h' := h u hu v hv
  simp only [Bool.and_eq_true] at h'
  refine ⟨seg u v, pathFT_of_pathFTB h'.1, fun q hq => ?_⟩
  have := List.all_eq_true.mp h'.2 q (path_mem_candidates hq.1)
  rw [pathFTB_of_pathFT hq] at this
  simpa using this

theorem connected_of_check {G : Graph}
    (h : ∀ u, u < G.n → ∀ v, v < G.n → pathFTB G (seg u v) u v = true) : Connected G :=
  fun u v hu hv => ⟨seg u v, pathFT_of_pathFTB (h u hu v hv)⟩

theorem K2_tree : IsTree K2 := by
  refine ⟨by decide, ⟨?_, ?_, ?_⟩, uniquePaths_of_check (by decide +kernel)⟩
  · intro u v
    show ((u == 0 && v == 1) || (u == 1 && v == 0)) = ((v == 0 && u == 1) || (v == 1 && u == 0))
    rw [Bool.or_comm, Bool.and_comm (v == 1), Bool.and_comm (v == 0)]
  · intro u; simp only [K2]; cases h1 : (u == 0) <;> cases h2 : (u == 1) <;> simp_all
  · intro u v h
    simp only [K2, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    show u < 2 ∧ v < 2
    omega

theorem P4_tree : IsTree P4 := by
  refine ⟨by decide, ⟨?_, ?_, ?_⟩, uniquePaths_of_check (by decide +kernel)⟩
  · intro u v
    simp only [P4]
    cases h1 : (u + 1 == v) <;> cases h2 : (v + 1 == u) <;> simp_all [Bool.and_comm]
  · intro u; simp [P4]
  · intro u v h
    simp only [P4, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.2, h.2⟩

/-- `K₂` and `P₄` are also trees in the other usual sense: connected with `n - 1` edges. -/
theorem K2_P4_connected_edges :
    (Connected K2 ∧ (edgeList K2).length = K2.n - 1) ∧
    (Connected P4 ∧ (edgeList P4).length = P4.n - 1) :=
  ⟨⟨connected_of_check (by decide), by decide⟩, ⟨connected_of_check (by decide), by decide⟩⟩

theorem K2_maxDeg : maxDeg K2 = 1 := by decide
theorem P4_maxDeg : maxDeg P4 = 2 := by decide

/-- A Thue 2-colouring of `K₂`. -/
def colK2 (v : Nat) : Nat := v % 2

/-- A Thue 3-colouring of `P₄`: colours `0 1 2 0`. -/
def colP4 (v : Nat) : Nat := [0, 1, 2, 0].getD v 0

theorem K2_colorable : Colorable K2 2 :=
  ⟨colK2, fun v _ => Nat.mod_lt v (by decide), nonrepetitive_of_nonrepB (by decide)⟩

theorem P4_colorable : Colorable P4 3 :=
  ⟨colP4, fun v hv => by
    have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by simp [P4] at hv; omega
    rcases this with rfl | rfl | rfl | rfl <;> decide,
   nonrepetitive_of_nonrepB (by decide +kernel)⟩

/-- The colour sequence of a path `[u, v]` with equal colours is a square. -/
theorem square2 {c : Nat → Nat} {u v : Nat} (h : c u = c v) : HasSquare ([u, v].map c) :=
  ⟨[], [c u], [], by simp, by simp [h]⟩

theorem K2_not_colorable_1 : ¬ Colorable K2 1 := by
  rintro ⟨c, hc, hn⟩
  have h0 := hc 0 (by decide)
  have h1 := hc 1 (by decide)
  exact hn [0, 1] (isPath_of_pathB (by decide)) (square2 (by omega))

/-- `P₄` has no Thue 2-colouring: `aa` or `abab` is unavoidable. -/
theorem P4_not_colorable_2 : ¬ Colorable P4 2 := by
  rintro ⟨c, hc, hn⟩
  have h0 := hc 0 (by decide)
  have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide)
  have h3 := hc 3 (by decide)
  by_cases e01 : c 0 = c 1
  · exact hn [0, 1] (isPath_of_pathB (by decide)) (square2 e01)
  by_cases e12 : c 1 = c 2
  · exact hn [1, 2] (isPath_of_pathB (by decide)) (square2 e12)
  by_cases e23 : c 2 = c 3
  · exact hn [2, 3] (isPath_of_pathB (by decide)) (square2 e23)
  have e02 : c 2 = c 0 := by omega
  have e13 : c 3 = c 1 := by omega
  exact hn [0, 1, 2, 3] (isPath_of_pathB (by decide))
    ⟨[], [c 0, c 1], [], by simp, by simp [e02, e13]⟩

/-- `π(K₂) = 2`. -/
theorem thue_K2 : IsThueNumber K2 2 := isThueNumber_of K2_colorable K2_not_colorable_1

/-- `π(P₄) = 3`. -/
theorem thue_P4 : IsThueNumber P4 3 := isThueNumber_of P4_colorable P4_not_colorable_2

/-! ## 6. Main theorems -/

/-- **Main theorem.** For every rational base `p/q > 1`, the clause
"`π(T) ≤ 2 log_{p/q} Δ(T)` for every tree `T`" is false; the witness is `K₂`
(`Δ = 1`, `π = 2`, `2 log 1 = 0`). By `claim_mono` this covers every real base `b > 1`. -/
theorem conjecture_00000003481_false (p q : Nat) (hpq : q < p) : ¬ Claim p q := by
  intro h
  have hb := h K2 2 K2_tree (by rw [K2_maxDeg]; decide) thue_K2
  unfold LogBound at hb
  rw [K2_maxDeg, Nat.one_pow, Nat.one_mul] at hb
  exact absurd hb (Nat.not_le_of_lt (Nat.pow_lt_pow_left hpq (by decide)))

/-- The colouring form of the clause is false too (no minimum is used). -/
theorem claimCol_false (p q : Nat) (hpq : q < p) : ¬ ClaimCol p q := by
  intro h
  obtain ⟨k, hb, hk⟩ := h K2 K2_tree (by rw [K2_maxDeg]; decide)
  unfold LogBound at hb
  rw [K2_maxDeg, Nat.one_pow, Nat.one_mul] at hb
  have hk2 : 2 ≤ k := by
    apply Nat.not_lt.mp
    intro hlt
    exact K2_not_colorable_1 (colorable_mono hk (by omega))
  have : q ^ k < p ^ k := Nat.pow_lt_pow_left hpq (by omega)
  omega

/-- Second witness, avoiding the degenerate `Δ = 1`: the path `P₄` (`Δ = 2`, `π = 3`) refutes
the clause for every rational base `p/q` with `(p/q)³ > 4`, e.g. bases 2 and 10. -/
theorem claimDeg2_false (p q : Nat) (h : 4 * q ^ 3 < p ^ 3) : ¬ ClaimDeg2 p q := by
  intro hc
  have hb := hc P4 3 P4_tree (by rw [P4_maxDeg]; decide) thue_P4
  unfold LogBound at hb
  rw [P4_maxDeg] at hb
  omega

theorem base2_false : ¬ Claim 2 1 := conjecture_00000003481_false 2 1 (by decide)
theorem base10_false : ¬ Claim 10 1 := conjecture_00000003481_false 10 1 (by decide)
/-- Natural logarithm: `e > 27/10`, and a larger base gives a stronger claim (the real-base
analogue of `claim_mono`, see the report), so the claim for base `e` would imply the claim for
base `27/10`, which is false. -/
theorem base_e_lower_false : ¬ Claim 27 10 := conjecture_00000003481_false 27 10 (by decide)
theorem base2_deg2_false : ¬ ClaimDeg2 2 1 := claimDeg2_false 2 1 (by decide)
theorem base_e_deg2_false : ¬ ClaimDeg2 27 10 := claimDeg2_false 27 10 (by decide)

/-- Non-vacuity: the hypotheses of the claim are satisfiable (by `K₂` and `P₄`), and the
nonrepetitiveness predicate is not trivial (some colourings fail it). -/
theorem nonvacuous :
    (IsTree K2 ∧ maxDeg K2 = 1 ∧ IsThueNumber K2 2) ∧
    (IsTree P4 ∧ maxDeg P4 = 2 ∧ IsThueNumber P4 3) ∧
    ¬ Nonrepetitive P4 (fun v => v % 2) :=
  ⟨⟨K2_tree, K2_maxDeg, thue_K2⟩, ⟨P4_tree, P4_maxDeg, thue_P4⟩,
   fun h => h [0, 1, 2, 3] (isPath_of_pathB (by decide))
     ⟨[], [0, 1], [], by simp, by decide⟩⟩

/-! ## 7. Clause (C2): every tree has a Thue 4-colouring, assuming Thue's theorem

We prove `π(T) ≤ 4` for every tree `T` (Brešar–Grytczuk–Klavžar–Niwczyk–Peterin 2007) from one
explicit hypothesis, `ThueHyp`: Thue's theorem (1906) that there are square-free words of every
length over a 3-letter alphabet. The proof:

* `kp`: the Kündgen–Pelsmajer word `u = w₀ w₁ 3 w₂ w₃ 3 ⋯` (a letter `3` inserted after every
  second letter of `w`) is square-free (`kp_sqfree`), and any 3 consecutive letters of it are
  distinct (`kp_ne1`, `kp_ne2`);
* `fold_sqfree`: for such a word `u`, every "folded" word `t ↦ u (m + |t - a|)` is square-free;
* `valley`: along any path of a graph with a *layering with unique parents* (`Layering`), the
  depth is `m + |t - a|`; `tree_layering`: every tree has such a layering (depth = length of the
  unique path from vertex `0`, minus 1);
* `tree_colorable_four`: colour `v` by `u (depth v)`.
-/

/-- Index form of square-freeness of the word `w₀ w₁ ⋯ w_{L-1}`: no factor `xx`. -/
def SqFreeUpTo (w : Nat → Nat) (L : Nat) : Prop :=
  ∀ i k, 0 < k → i + 2 * k ≤ L → ∃ j, j < k ∧ w (i + j) ≠ w (i + j + k)

/-- **Thue's theorem** (Thue 1906), finite form, used as an explicit hypothesis: for every `L`
there is a square-free word of length `L` over the alphabet `{0, 1, 2}`. -/
def ThueHyp : Prop := ∀ L, ∃ w : Nat → Nat, (∀ i, w i < 3) ∧ SqFreeUpTo w L

/-! ### 7.1 Lists: index form of squares -/

theorem getD_append_lt : ∀ (l l' : List Nat) (n : Nat), n < l.length →
    (l ++ l').getD n 0 = l.getD n 0
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: l, l', n + 1, h => by
    simp only [List.cons_append, List.getD_cons_succ]
    exact getD_append_lt l l' n (by simp at h; omega)

theorem getD_append_ge : ∀ (l l' : List Nat) (n : Nat), (l ++ l').getD (l.length + n) 0 = l'.getD n 0
  | [], l', n => by simp
  | _ :: l, l', n => by
    simp only [List.cons_append, List.length_cons]
    rw [show l.length + 1 + n = (l.length + n) + 1 by omega, List.getD_cons_succ]
    exact getD_append_ge l l' n

theorem getD_map_lt : ∀ (p : List Nat) (c : Nat → Nat) (t : Nat), t < p.length →
    (p.map c).getD t 0 = c (p.getD t 0)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: p, c, t + 1, h => by
    simp only [List.map_cons, List.getD_cons_succ]
    exact getD_map_lt p c t (by simp at h; omega)

theorem getD_mem : ∀ (p : List Nat) (t : Nat), t < p.length → p.getD t 0 ∈ p
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.mem_cons_self ..
  | _ :: p, t + 1, h => by
    rw [List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (getD_mem p t (by simp at h; omega))

/-- A square factor `xx` at position `i`, `|x| = k`. -/
theorem sq_index {s : List Nat} (h : HasSquare s) : ∃ i k, 0 < k ∧ i + 2 * k ≤ s.length ∧
    ∀ j, j < k → s.getD (i + j) 0 = s.getD (i + j + k) 0 := by
  obtain ⟨a, x, b, hx, rfl⟩ := h
  refine ⟨a.length, x.length, List.length_pos_iff.mpr hx, by simp; omega, fun j hj => ?_⟩
  rw [List.append_assoc, List.append_assoc, getD_append_ge, getD_append_lt _ _ _ hj,
    show a.length + j + x.length = a.length + (x.length + j) by omega, getD_append_ge,
    getD_append_ge, getD_append_lt _ _ _ hj]

/-! ### 7.2 The Kündgen–Pelsmajer word -/

/-- `u = w₀ w₁ 3 w₂ w₃ 3 w₄ w₅ 3 ⋯`. -/
def kp (w : Nat → Nat) (i : Nat) : Nat := if i % 3 = 2 then 3 else w (2 * (i / 3) + i % 3)

theorem kp_of_ne {w : Nat → Nat} {i : Nat} (h : i % 3 ≠ 2) : kp w i = w (2 * (i / 3) + i % 3) :=
  if_neg h

theorem kp_of_eq {w : Nat → Nat} {i : Nat} (h : i % 3 = 2) : kp w i = 3 := if_pos h

theorem kp_lt {w : Nat → Nat} (hw : ∀ i, w i < 3) (i : Nat) : kp w i < 4 := by
  unfold kp
  split
  · decide
  · have := hw (2 * (i / 3) + i % 3); omega

/-- The letter of `u` at position `3⌊m/2⌋ + (m mod 2)` is `w m`. -/
theorem kp_psi {w : Nat → Nat} (m : Nat) : kp w (3 * (m / 2) + m % 2) = w m := by
  rw [kp_of_ne (by omega)]
  congr 1
  omega

theorem sq_ne1 {w : Nat → Nat} {N : Nat} (hsq : SqFreeUpTo w N) {j : Nat} (hj : j + 2 ≤ N) :
    w j ≠ w (j + 1) := by
  obtain ⟨j', hj', hne⟩ := hsq j 1 (by decide) (by omega)
  have : j' = 0 := by omega
  subst this
  simpa using hne

theorem kp_ne1 {w : Nat → Nat} {N M : Nat} (hw : ∀ i, w i < 3) (hsq : SqFreeUpTo w N)
    (i : Nat) (hi : i + 1 < M) (hMN : M + 2 ≤ N) : kp w i ≠ kp w (i + 1) := by
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
  · rw [kp_of_ne (by omega), kp_of_ne (by omega),
      show 2 * ((i + 1) / 3) + (i + 1) % 3 = 2 * (i / 3) + i % 3 + 1 by omega]
    exact sq_ne1 hsq (by omega)
  · rw [kp_of_ne (by omega), kp_of_eq (by omega)]
    have := hw (2 * (i / 3) + i % 3); omega
  · rw [kp_of_eq h, kp_of_ne (by omega)]
    have := hw (2 * ((i + 1) / 3) + (i + 1) % 3); omega

theorem kp_ne2 {w : Nat → Nat} {N M : Nat} (hw : ∀ i, w i < 3) (hsq : SqFreeUpTo w N)
    (i : Nat) (hi : i + 2 < M) (hMN : M + 2 ≤ N) : kp w i ≠ kp w (i + 2) := by
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h | h | h
  · rw [kp_of_ne (by omega), kp_of_eq (by omega)]
    have := hw (2 * (i / 3) + i % 3); omega
  · rw [kp_of_ne (by omega), kp_of_ne (by omega),
      show 2 * ((i + 2) / 3) + (i + 2) % 3 = 2 * (i / 3) + i % 3 + 1 by omega]
    exact sq_ne1 hsq (by omega)
  · rw [kp_of_eq h, kp_of_ne (by omega)]
    have := hw (2 * ((i + 2) / 3) + (i + 2) % 3); omega

/-- The Kündgen–Pelsmajer word is square-free (deleting the letters `3` from a square of `u`
gives a square of `w`). -/
theorem kp_sqfree {w : Nat → Nat} {N M : Nat} (hw : ∀ i, w i < 3) (hsq : SqFreeUpTo w N)
    (hMN : M + 2 ≤ N) : SqFreeUpTo (kp w) M := by
  intro i k hk hik
  refine Classical.byContradiction fun hcon => ?_
  have H : ∀ j, j < k → kp w (i + j) = kp w (i + j + k) := fun j hj =>
    Classical.byContradiction fun hne => hcon ⟨j, hj, hne⟩
  by_cases k1 : k = 1
  · subst k1
    exact kp_ne1 hw hsq i (by omega) hMN (by simpa using H 0 (by decide))
  by_cases k2 : k = 2
  · subst k2
    exact kp_ne2 hw hsq i (by omega) hMN (by simpa using H 0 (by decide))
  by_cases k3 : k % 3 = 0
  · -- `k = 3t`: the letters of `w` in the window form a square of length `4t` in `w`
    obtain ⟨t, rfl⟩ : ∃ t, k = 3 * t := ⟨k / 3, by omega⟩
    obtain ⟨s, hs⟩ : ∃ s, s = (2 * i + 2) / 3 := ⟨_, rfl⟩
    obtain ⟨j, hj, hne⟩ := hsq s (2 * t) (by omega) (by omega)
    apply hne
    have hp := H (3 * ((s + j) / 2) + (s + j) % 2 - i) (by omega)
    rw [show i + (3 * ((s + j) / 2) + (s + j) % 2 - i) = 3 * ((s + j) / 2) + (s + j) % 2 by omega,
      show 3 * ((s + j) / 2) + (s + j) % 2 + 3 * t
        = 3 * ((s + j + 2 * t) / 2) + (s + j + 2 * t) % 2 by omega,
      kp_psi, kp_psi] at hp
    exact hp
  · -- `3 ∤ k`, `k ≥ 3`: a letter `3` of the first half faces a letter of `w`
    have hp := H ((5 - i % 3) % 3) (by omega)
    rw [kp_of_eq (by omega), kp_of_ne (by omega)] at hp
    have := hw (2 * ((i + (5 - i % 3) % 3 + k) / 3) + (i + (5 - i % 3) % 3 + k) % 3)
    omega

/-! ### 7.3 The folding lemma -/

/-- **Folding lemma.** If `u` is square-free and any 3 consecutive letters are distinct, then
for all `m, a`, the word `t ↦ u (m + |t - a|)` (read down to `u m`, then up) is square-free. -/
theorem fold_sqfree (u : Nat → Nat) (L : Nat) (hsq : SqFreeUpTo u L)
    (hd1 : ∀ i, i + 1 < L → u i ≠ u (i + 1)) (hd2 : ∀ i, i + 2 < L → u i ≠ u (i + 2))
    (ℓ m a : Nat) (hb : ∀ t, t < ℓ → m + (a - t) + (t - a) < L) :
    SqFreeUpTo (fun t => u (m + (a - t) + (t - a))) ℓ := by
  intro i k hk hik
  refine Classical.byContradiction fun hcon => ?_
  have H : ∀ j, j < k → ∀ x y, x = m + (a - (i + j)) + (i + j - a) →
      y = m + (a - (i + j + k)) + (i + j + k - a) → u x = u y := by
    intro j hj x y hx hy
    subst hx hy
    exact Classical.byContradiction fun hne => hcon ⟨j, hj, hne⟩
  by_cases c1 : a ≤ i
  · -- the square lies in the increasing part: a square of `u`
    have := hb (i + 2 * k - 1) (by omega)
    obtain ⟨j, hj, hne⟩ := hsq (m + (i - a)) k hk (by omega)
    exact hne (H j hj _ _ (by omega) (by omega))
  by_cases c2 : i + 2 * k - 1 ≤ a
  · -- the square lies in the decreasing part: a reversed square of `u`
    have := hb i (by omega)
    obtain ⟨j, hj, hne⟩ := hsq (m + a - (i + 2 * k - 1)) k hk (by omega)
    exact hne (H (k - 1 - j) (by omega) _ _ (by omega) (by omega)).symm
  -- now `i < a < i + 2k - 1`
  by_cases c3 : a + 2 ≤ i + k
  · -- the turning point and both its neighbours lie in the first half: `u_{m+k-1} = u_{m+k+1}`
    have := hb (a + 1 + k) (by omega)
    have h1 := H (a - 1 - i) (by omega) (m + 1) (m + k - 1) (by omega) (by omega)
    have h2 := H (a + 1 - i) (by omega) (m + 1) (m + k - 1 + 2) (by omega) (by omega)
    exact hd2 (m + k - 1) (by omega) (h1.symm.trans h2)
  by_cases c4 : a + 1 = i + k
  · -- turning point at the end of the first half: `u_{m+j} = u_{m+k-j}` (a palindrome)
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with he | ho
    · have := hb (i + k / 2 + k) (by omega)
      have h := H (k / 2) (by omega) (m + k / 2 - 1) (m + k / 2 - 1 + 2) (by omega) (by omega)
      exact hd2 _ (by omega) h
    · have := hb (i + (k - 1) / 2 + k) (by omega)
      have h := H ((k - 1) / 2) (by omega) (m + (k - 1) / 2) (m + (k - 1) / 2 + 1)
        (by omega) (by omega)
      exact hd1 _ (by omega) h
  by_cases c5 : a = i + k
  · -- turning point at the start of the second half
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with he | ho
    · have := hb i (by omega)
      have h := H (k / 2 - 1) (by omega) (m + k / 2 - 1 + 2) (m + k / 2 - 1) (by omega) (by omega)
      exact hd2 _ (by omega) h.symm
    · have := hb i (by omega)
      have h := H ((k - 1) / 2) (by omega) (m + (k - 1) / 2 + 1) (m + (k - 1) / 2)
        (by omega) (by omega)
      exact hd1 _ (by omega) h.symm
  · -- the turning point and both its neighbours lie in the second half
    have := hb (a - 1 - k) (by omega)
    have h1 := H (a - 1 - k - i) (by omega) (m + k - 1 + 2) (m + 1) (by omega) (by omega)
    have h2 := H (a + 1 - k - i) (by omega) (m + k - 1) (m + 1) (by omega) (by omega)
    exact hd2 (m + k - 1) (by omega) (h2.trans h1.symm)

/-! ### 7.4 Paths in trees go down, then up -/

/-- A layering with unique parents: adjacent vertices have depths differing by one, and every
vertex has at most one neighbour of smaller depth. -/
structure Layering (G : Graph) (d : Nat → Nat) : Prop where
  step : ∀ u v, G.adj u v = true → d v = d u + 1 ∨ d u = d v + 1
  parent : ∀ v w₁ w₂, G.adj v w₁ = true → G.adj v w₂ = true → d w₁ < d v → d w₂ < d v → w₁ = w₂

/-- Along a path, the depth is `m + |t - a|`: it decreases to the top vertex, then increases. -/
theorem valley {G : Graph} {d : Nat → Nat} (hsym : ∀ u v, G.adj u v = G.adj v u)
    (hL : Layering G d) : ∀ p : List Nat, p ≠ [] → p.Nodup → adjChain G p = true →
    ∃ a m, a < p.length ∧ ∀ t, t < p.length → d (p.getD t 0) = m + (a - t) + (t - a)
  | [], h, _, _ => absurd rfl h
  | [x], _, _, _ => ⟨0, d x, by simp, fun t ht => by
      have : t = 0 := by simp at ht; omega
      subst this; simp⟩
  | x :: y :: r, _, hnd, hch => by
    simp only [adjChain, Bool.and_eq_true] at hch
    have hxn : x ∉ y :: r := (List.nodup_cons.mp hnd).1
    obtain ⟨a, m, ha, hd⟩ := valley hsym hL (y :: r) (by simp) (List.nodup_cons.mp hnd).2 hch.2
    have hy : d y = m + a := by have := hd 0 (by simp); simpa using this
    rcases hL.step x y hch.1 with h | h
    · -- `y` is above `x`: the rest must be increasing (`a = 0`), else `y` has two parents
      have ha0 : a = 0 := by
        refine Classical.byContradiction fun ha0 => ?_
        cases r with
        | nil => simp at ha; omega
        | cons z r' =>
          have hz : d z = m + (a - 1) := by have := hd 1 (by simp); simp at this; omega
          have hyz : G.adj y z = true := by
            have := hch.2; simp only [adjChain, Bool.and_eq_true] at this; exact this.1
          have hxz := hL.parent y x z (by rw [hsym]; exact hch.1) hyz (by omega) (by omega)
          subst hxz
          exact hxn (by simp)
      subst ha0
      refine ⟨0, d x, by simp, fun t ht => ?_⟩
      cases t with
      | zero => simp
      | succ t =>
        rw [List.getD_cons_succ, hd t (by simp at ht ⊢; omega)]
        omega
    · refine ⟨a + 1, m, by simp at ha ⊢; omega, fun t ht => ?_⟩
      cases t with
      | zero => simp; omega
      | succ t =>
        rw [List.getD_cons_succ, hd t (by simp at ht ⊢; omega)]
        omega

theorem nodup_app {l₁ l₂ : List Nat} :
    (l₁ ++ l₂).Nodup ↔ l₁.Nodup ∧ l₂.Nodup ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b :=
  List.pairwise_append

theorem adjChain_snoc (G : Graph) {u v : Nat} : ∀ l : List Nat, adjChain G l = true →
    l.getLast? = some u → G.adj u v = true → adjChain G (l ++ [v]) = true
  | [], _, h, _ => by simp at h
  | [x], _, h, hadj => by
    simp at h; subst h; simp [adjChain, hadj]
  | x :: y :: r, hc, h, hadj => by
    simp only [adjChain, Bool.and_eq_true] at hc
    rw [List.getLast?_cons_cons] at h
    have := adjChain_snoc G (y :: r) hc.2 h hadj
    simp only [List.cons_append, adjChain, Bool.and_eq_true] at this ⊢
    exact ⟨hc.1, this⟩

theorem adjChain_prefix (G : Graph) : ∀ (l₁ l₂ : List Nat), adjChain G (l₁ ++ l₂) = true →
    adjChain G l₁ = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x :: y :: r, l₂, h => by
    simp only [List.cons_append, adjChain, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, adjChain_prefix G (y :: r) l₂ h.2⟩

theorem pathFT_snoc {G : Graph} {p : List Nat} {r u v : Nat} (hp : PathFT G p r u)
    (hv : v ∉ p) (hvn : v < G.n) (hadj : G.adj u v = true) : PathFT G (p ++ [v]) r v := by
  obtain ⟨⟨hne, hnd, hin, hch⟩, hh, hl⟩ := hp
  refine ⟨⟨by simp, ?_, ?_, adjChain_snoc G p hch hl hadj⟩, ?_, List.getLast?_concat⟩
  · refine nodup_app.mpr ⟨hnd, by simp, fun a ha b hb => ?_⟩
    simp at hb; subst hb; exact fun e => hv (e ▸ ha)
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hin x h
    · simp at h; subst h; exact hvn
  · rw [List.head?_append, hh]; rfl

theorem pathFT_prefix {G : Graph} {A B : List Nat} {r w v : Nat}
    (hp : PathFT G (A ++ v :: B) r w) : PathFT G (A ++ [v]) r v := by
  obtain ⟨⟨_, hnd, hin, hch⟩, hh, _⟩ := hp
  have hsub : (A ++ [v]).Sublist (A ++ v :: B) :=
    List.Sublist.append_left (List.singleton_sublist.mpr (List.mem_cons_self ..)) A
  refine ⟨⟨by simp, hnd.sublist hsub, fun x hx => hin x (hsub.subset hx), ?_⟩, ?_,
    List.getLast?_concat⟩
  · have e : A ++ v :: B = (A ++ [v]) ++ B := by simp
    rw [e] at hch
    exact adjChain_prefix G _ _ hch
  · cases A with
    | nil => simpa using hh
    | cons a A => simpa using hh

/-- The unique path from the root `0` to `v` (for `v < n`). -/
noncomputable def rootPath (G : Graph) (hT : IsTree G) (v : Nat) : List Nat :=
  if hv : v < G.n then Classical.choose (hT.2.2 0 v (by have := hT.1; omega) hv) else []

theorem rootPath_spec {G : Graph} (hT : IsTree G) {v : Nat} (hv : v < G.n) :
    PathFT G (rootPath G hT v) 0 v ∧ ∀ q, PathFT G q 0 v → q = rootPath G hT v := by
  unfold rootPath
  rw [dif_pos hv]
  exact Classical.choose_spec (hT.2.2 0 v (by have := hT.1; omega) hv)

/-- For an edge `uv` of a tree, one root path extends the other by one vertex. -/
theorem rootPath_step {G : Graph} (hT : IsTree G) {u v : Nat} (hadj : G.adj u v = true) :
    rootPath G hT v = rootPath G hT u ++ [v] ∨ rootPath G hT u = rootPath G hT v ++ [u] := by
  have ⟨_, ⟨hsym, hloop, hrange⟩, _⟩ := hT
  have ⟨hu, hv⟩ := hrange u v hadj
  have hvu : G.adj v u = true := by rw [hsym]; exact hadj
  have huv : u ≠ v := fun e => by subst e; rw [hloop] at hadj; exact absurd hadj (by decide)
  obtain ⟨sU, uU⟩ := rootPath_spec hT hu
  obtain ⟨sV, uV⟩ := rootPath_spec hT hv
  by_cases h1 : v ∈ rootPath G hT u
  · by_cases h2 : u ∈ rootPath G hT v
    · exfalso
      obtain ⟨A, B, hAB⟩ := List.append_of_mem h1
      rw [hAB] at sU
      have hPv := uV _ (pathFT_prefix sU)
      rw [← hPv] at h2
      rcases List.mem_append.mp h2 with h | h
      · obtain ⟨A₁, A₂, hA⟩ := List.append_of_mem h
        rw [hA, show A₁ ++ u :: A₂ ++ v :: B = A₁ ++ u :: (A₂ ++ v :: B) by simp] at sU
        have := congrArg List.length
          ((uU _ (pathFT_prefix sU)).trans (hAB.trans (by rw [hA])))
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega
      · exact huv (List.mem_singleton.mp h)
    · exact Or.inr (uU _ (pathFT_snoc sV h2 hu hvu)).symm
  · exact Or.inl (uV _ (pathFT_snoc sU h1 hv hadj)).symm

/-- Every tree has a layering with unique parents: depth = distance from the root `0`. -/
theorem tree_layering {G : Graph} (hT : IsTree G) :
    Layering G (fun v => (rootPath G hT v).length - 1) := by
  have hrange := hT.2.1.2.2
  have hsym := hT.2.1.1
  have hpos : ∀ v, v < G.n → 0 < (rootPath G hT v).length := fun v hv =>
    List.length_pos_iff.mpr (rootPath_spec hT hv).1.1.1
  refine ⟨fun u v hadj => ?_, fun v w₁ w₂ h₁ h₂ hd₁ hd₂ => ?_⟩
  · have ⟨hu, hv⟩ := hrange u v hadj
    have := hpos u hu
    have := hpos v hv
    rcases rootPath_step hT hadj with h | h
    · left; rw [h]; simp; omega
    · right; rw [h]; simp; omega
  · have ⟨hv, hw₁⟩ := hrange v w₁ h₁
    have ⟨_, hw₂⟩ := hrange v w₂ h₂
    have key : ∀ w, w < G.n → G.adj v w = true →
        (rootPath G hT w).length - 1 < (rootPath G hT v).length - 1 →
        rootPath G hT v = rootPath G hT w ++ [v] := by
      intro w hw hvw hlt
      have hwv : G.adj w v = true := by rw [hsym]; exact hvw
      rcases rootPath_step hT hwv with h | h
      · exact h
      · rw [h] at hlt; simp at hlt; omega
    have e := (key w₁ hw₁ h₁ hd₁).symm.trans (key w₂ hw₂ h₂ hd₂)
    have e' := List.append_cancel_right e
    have l₁ := (rootPath_spec hT hw₁).1.2.2
    have l₂ := (rootPath_spec hT hw₂).1.2.2
    rw [e', l₂] at l₁
    exact Option.some.inj l₁.symm

/-! ### 7.5 Every tree is Thue 4-colourable; (C2) is false -/

theorem bound_exists (f : Nat → Nat) : ∀ n, ∃ D, ∀ v, v < n → f v ≤ D
  | 0 => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨D, hD⟩ := bound_exists f n
    exact ⟨max D (f n), fun v hv => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | h
      · exact Nat.le_trans (hD v h) (Nat.le_max_left _ _)
      · subst h; exact Nat.le_max_right _ _⟩

/-- **Theorem (Brešar et al. 2007), modulo Thue's theorem.** Every tree has a Thue
colouring with 4 colours: colour `v` by `u (depth v)`, `u` the Kündgen–Pelsmajer word. -/
theorem tree_colorable_four (hThue : ThueHyp) (G : Graph) (hT : IsTree G) : Colorable G 4 := by
  have hsym := hT.2.1.1
  have hL := tree_layering hT
  obtain ⟨D, hD⟩ := bound_exists (fun v => (rootPath G hT v).length - 1) G.n
  obtain ⟨w, hw3, hwsq⟩ := hThue (D + 3)
  have husq : SqFreeUpTo (kp w) (D + 1) := kp_sqfree hw3 hwsq (by omega)
  refine ⟨fun v => kp w ((rootPath G hT v).length - 1), fun v _ => kp_lt hw3 _, ?_⟩
  intro p hp hsq
  obtain ⟨hne, hnd, hin, hch⟩ := hp
  obtain ⟨a, m, _, hval⟩ := valley hsym hL p hne hnd hch
  obtain ⟨i, k, hk, hik, heq⟩ := sq_index hsq
  rw [List.length_map] at hik
  have hfold := fold_sqfree (kp w) (D + 1) husq
    (fun i hi => kp_ne1 hw3 hwsq i hi (by omega)) (fun i hi => kp_ne2 hw3 hwsq i hi (by omega))
    p.length m a (fun t ht => by
      rw [← hval t ht]
      have := hD _ (hin _ (getD_mem p t ht))
      simp only at this
      omega)
  obtain ⟨j, hj, hne'⟩ := hfold i k hk hik
  apply hne'
  have h := heq j hj
  rw [getD_map_lt p _ _ (by omega), getD_map_lt p _ _ (by omega)] at h
  simp only at h ⊢
  rw [← hval _ (by omega), ← hval _ (by omega)]
  exact h

/-- Hence `π(T) ≤ 4` for every tree. -/
theorem thueNumber_le_four (hThue : ThueHyp) {G : Graph} {k : Nat} (hT : IsTree G)
    (h : IsThueNumber G k) : k ≤ 4 :=
  Nat.not_lt.mp fun hlt => h.2 4 hlt (tree_colorable_four hThue G hT)

/-- **Clause (C2) is false** (given Thue's theorem): the Thue number of trees is bounded. -/
theorem conjecture_C2_false (hThue : ThueHyp) : ¬ (∀ k, ∃ G, IsTree G ∧ ¬ Colorable G k) :=
  fun h => by
    obtain ⟨G, hT, hn⟩ := h 4
    exact hn (tree_colorable_four hThue G hT)

/-- The same, phrased with the Thue number: no tree has `π(T) > 4`. -/
theorem conjecture_C2_false' (hThue : ThueHyp) :
    ¬ (∀ k, ∃ G π, IsTree G ∧ IsThueNumber G π ∧ k < π) :=
  fun h => by
    obtain ⟨G, π, hT, hπ, hlt⟩ := h 4
    have := thueNumber_le_four hThue hT hπ
    omega

/-! ### 7.6 The hypothesis in list form -/

/-- An index square of a list gives a square factor `xx` in the sense of `HasSquare`. -/
theorem hasSquare_of_index (w : List Nat) (i k : Nat) (hk : 0 < k) (hik : i + 2 * k ≤ w.length)
    (h : ∀ j, j < k → w.getD (i + j) 0 = w.getD (i + j + k) 0) : HasSquare w := by
  have e1 : (w.drop (i + k)).take k = (w.drop i).take k := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
    split
    · have hj := h j ‹_›
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at hj
      rw [show i + k + j = i + j + k by omega]
      rw [List.getElem?_eq_getElem (show i + j < w.length by omega),
        List.getElem?_eq_getElem (show i + j + k < w.length by omega)] at hj ⊢
      simp only [Option.getD_some] at hj
      rw [hj]
    · rfl
  refine ⟨w.take i, (w.drop i).take k, w.drop (i + 2 * k), ?_, ?_⟩
  · intro e
    have := congrArg List.length e
    simp only [List.length_take, List.length_drop, List.length_nil] at this
    omega
  · have e2 : w = w.take i ++ ((w.drop i).take k ++ ((w.drop (i + k)).take k ++
        w.drop (i + 2 * k))) := by
      conv => lhs; rw [← List.take_append_drop i w, ← List.take_append_drop k (w.drop i),
        List.drop_drop, ← List.take_append_drop k (w.drop (i + k)), List.drop_drop]
      rw [show i + k + k = i + 2 * k by omega]
    rw [e1] at e2
    rw [List.append_assoc, List.append_assoc]
    exact e2

/-- Thue's theorem in list form: square-free words (no factor `xx` in the sense of
`HasSquare`) of every length over `{0, 1, 2}`. -/
def ThueHypList : Prop := ∀ n, ∃ w : List Nat, w.length = n ∧ (∀ x ∈ w, x < 3) ∧ ¬ HasSquare w

/-- The list form implies the index form used above. -/
theorem thueHyp_of_list (h : ThueHypList) : ThueHyp := by
  intro L
  obtain ⟨w, hlen, h3, hsq⟩ := h L
  refine ⟨fun i => w.getD i 0, fun i => ?_, fun i k hk hik => ?_⟩
  · show w.getD i 0 < 3
    rw [List.getD_eq_getElem?_getD]
    by_cases hi : i < w.length
    · rw [List.getElem?_eq_getElem hi]
      exact h3 _ (List.getElem_mem hi)
    · rw [List.getElem?_eq_none (by omega)]; decide
  · refine Classical.byContradiction fun hcon => hsq (hasSquare_of_index w i k hk (by omega) ?_)
    intro j hj
    exact Classical.byContradiction fun hne => hcon ⟨j, hj, hne⟩

theorem conjecture_C2_false_list (h : ThueHypList) : ¬ (∀ k, ∃ G, IsTree G ∧ ¬ Colorable G k) :=
  conjecture_C2_false (thueHyp_of_list h)

/-! ### 7.7 Sanity check of the hypothesis for a small length -/

/-- A square-free ternary word of length 40 (`w` of `verify.py`, letters shifted to `0,1,2`). -/
def thueWord40 : List Nat :=
  [0,1,0,2,0,1,2,0,2,1,0,1,2,0,1,0,2,0,1,2,0,2,1,0,2,0,1,0,2,1,0,1,2,0,1,0,2,0,1,2]

def sqCheck (w : Nat → Nat) (L : Nat) : Bool :=
  (List.range L).all fun i => (List.range (L + 1)).all fun k =>
    !(decide (0 < k) && decide (i + 2 * k ≤ L)) ||
      (List.range k).any fun j => w (i + j) != w (i + j + k)

theorem sqFree_of_check {w : Nat → Nat} {L : Nat} (h : sqCheck w L = true) : SqFreeUpTo w L := by
  intro i k hk hik
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 k (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h2
  rcases h2 with (h3 | h3) | ⟨j, hj, hne⟩
  · omega
  · omega
  · exact ⟨j, hj, hne⟩

/-- `ThueHyp` holds for `L = 40` (a sanity check; the general case is Thue's theorem). -/
theorem thueHyp_40 : ∃ w : Nat → Nat, (∀ i, w i < 3) ∧ SqFreeUpTo w 40 :=
  ⟨fun i => thueWord40.getD i 0 % 3, fun i => Nat.mod_lt _ (by decide),
    sqFree_of_check (by decide +kernel)⟩

end Thue3481

#print axioms Thue3481.conjecture_00000003481_false
#print axioms Thue3481.claimCol_false
#print axioms Thue3481.claimDeg2_false
#print axioms Thue3481.claim_mono
#print axioms Thue3481.nonvacuous
#print axioms Thue3481.tree_colorable_four
#print axioms Thue3481.conjecture_C2_false
#print axioms Thue3481.conjecture_C2_false'
#print axioms Thue3481.thueHyp_40
#print axioms Thue3481.conjecture_C2_false_list
