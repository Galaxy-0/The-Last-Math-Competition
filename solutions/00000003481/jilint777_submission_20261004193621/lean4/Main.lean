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

The other false clause ("the Thue number of general trees is unbounded") contradicts the theorem
`π(T) ≤ 4` for every tree (Brešar, Grytczuk, Klavžar, Niwczyk, Peterin 2007); that part is proved
in the report (it needs Thue's infinite square-free word) and is **not** formalised here.

Everything is defined from scratch in core Lean 4:

* `Graph`: a finite graph on `{0, …, n-1}` with a Boolean adjacency function;
  `IsTree`: simple, connected, with `n - 1` edges;
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

/-- Any two vertices are joined by a path. -/
def Connected (G : Graph) : Prop :=
  ∀ u v, u < G.n → v < G.n → ∃ p, IsPath G p ∧ p.head? = some u ∧ p.getLast? = some v

/-- The edges `{u, v}` (listed once, as `(u, v)` with `u < v`). -/
def edgeList (G : Graph) : List (Nat × Nat) :=
  (List.range G.n).flatMap fun u =>
    ((List.range G.n).filter fun v => u < v && G.adj u v).map fun v => (u, v)

/-- A tree: a nonempty connected simple graph with `n - 1` edges. -/
def IsTree (G : Graph) : Prop :=
  1 ≤ G.n ∧ IsSimple G ∧ Connected G ∧ (edgeList G).length = G.n - 1

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

theorem connected_of_check {G : Graph}
    (h : ∀ u, u < G.n → ∀ v, v < G.n →
      (pathB G (seg u v) && (seg u v).head? == some u && (seg u v).getLast? == some v) = true) :
    Connected G := by
  intro u v hu hv
  have := h u hu v hv
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨seg u v, isPath_of_pathB this.1.1, this.1.2, this.2⟩

theorem K2_tree : IsTree K2 := by
  refine ⟨by decide, ⟨?_, ?_, ?_⟩, connected_of_check (by decide), by decide⟩
  · intro u v
    show ((u == 0 && v == 1) || (u == 1 && v == 0)) = ((v == 0 && u == 1) || (v == 1 && u == 0))
    rw [Bool.or_comm, Bool.and_comm (v == 1), Bool.and_comm (v == 0)]
  · intro u; simp only [K2]; cases h1 : (u == 0) <;> cases h2 : (u == 1) <;> simp_all
  · intro u v h
    simp only [K2, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    show u < 2 ∧ v < 2
    omega

theorem P4_tree : IsTree P4 := by
  refine ⟨by decide, ⟨?_, ?_, ?_⟩, connected_of_check (by decide), by decide⟩
  · intro u v
    simp only [P4]
    cases h1 : (u + 1 == v) <;> cases h2 : (v + 1 == u) <;> simp_all [Bool.and_comm]
  · intro u; simp [P4]
  · intro u v h
    simp only [P4, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.2, h.2⟩

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

end Thue3481

#print axioms Thue3481.conjecture_00000003481_false
#print axioms Thue3481.claimCol_false
#print axioms Thue3481.claimDeg2_false
#print axioms Thue3481.claim_mono
#print axioms Thue3481.nonvacuous
