import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Rat.Cast.Order
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Subdividing an edge of the complete graph `K₉` increases the Wiener index, although the
betweenness of that edge is below a quarter of the number of vertices. -/
namespace Conjecture3476

open SimpleGraph

/-! ### Subdivision, Wiener index, betweenness -/

/-- Adjacency after subdividing the edge `ab`. The new vertex is `none`; it is joined to `a`
and `b`, and the edge `ab` itself is removed. -/
def SubAdj {V : Type} (G : SimpleGraph V) (a b : V) : Option V → Option V → Prop
  | some u, some v => G.Adj u v ∧ ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a))
  | none, some v => v = a ∨ v = b
  | some u, none => u = a ∨ u = b
  | none, none => False

/-- The graph obtained from `G` by subdividing the edge `ab` once. -/
def subdivide {V : Type} (G : SimpleGraph V) (a b : V) : SimpleGraph (Option V) where
  Adj := SubAdj G a b
  symm := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => exact h
      | some v => exact h
    | some u =>
      cases y with
      | none => exact h
      | some v =>
        refine ⟨h.1.symm, fun h' => h.2 ?_⟩
        rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr ⟨h2, h1⟩
        · exact Or.inl ⟨h2, h1⟩
  loopless := by
    intro x h
    cases x with
    | none => exact h
    | some u => exact G.loopless u h.1

/-- The sum of distances over ordered pairs of vertices: twice the Wiener index. -/
noncomputable def wienerTwice {W : Type} [Fintype W] (G : SimpleGraph W) : ℕ :=
  ∑ u : W, ∑ v : W, G.dist u v

/-- The Wiener index: the sum of distances over unordered pairs of vertices. -/
noncomputable def wiener {W : Type} [Fintype W] (G : SimpleGraph W) : ℚ :=
  (wienerTwice G : ℚ) / 2

/-- The number of shortest walks from `s` to `t`. -/
noncomputable def sigma {W : Type} (G : SimpleGraph W) (s t : W) : ℕ :=
  Nat.card {p : G.Walk s t // p.length = G.dist s t}

/-- The number of shortest walks from `s` to `t` that traverse the edge `e`. -/
noncomputable def sigmaThrough {W : Type} (G : SimpleGraph W) (e : Sym2 W) (s t : W) : ℕ :=
  Nat.card {p : G.Walk s t // p.length = G.dist s t ∧ e ∈ p.edges}

/-- Edge betweenness summed over ordered pairs `s ≠ t`. -/
noncomputable def betweennessOrdered {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (e : Sym2 W) : ℚ :=
  ∑ s : W, ∑ t : W, if s = t then 0 else (sigmaThrough G e s t : ℚ) / (sigma G s t : ℚ)

/-- Edge betweenness: the sum over unordered pairs `{s, t}` of the fraction of shortest
`s`–`t` paths through `e`. -/
noncomputable def betweenness {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (e : Sym2 W) : ℚ :=
  betweennessOrdered G e / 2

/-! ### A connected graph has distance at least one between distinct vertices -/

theorem wienerTwice_ge {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (hG : G.Connected) : Fintype.card W * (Fintype.card W - 1) ≤ wienerTwice G := by
  have hinner : ∀ u : W, ∑ v : W, (if u ≠ v then 1 else 0) = Fintype.card W - 1 := by
    intro u
    rw [← Finset.card_filter, Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ u),
      Finset.card_univ]
  calc Fintype.card W * (Fintype.card W - 1)
      = ∑ u : W, ∑ v : W, (if u ≠ v then 1 else 0) := by
        rw [Finset.sum_congr rfl fun u _ => hinner u, Finset.sum_const, Finset.card_univ,
          smul_eq_mul]
    _ ≤ wienerTwice G := by
        unfold wienerTwice
        refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
        split_ifs with h
        · exact hG.pos_dist_of_ne h
        · exact Nat.zero_le _

/-! ### Shortest walks in a complete graph -/

theorem walk_length_one {W : Type} {G : SimpleGraph W} {s t : W} (p : G.Walk s t)
    (hp : p.length = 1) : ∃ h : G.Adj s t, p = Walk.cons h Walk.nil := by
  cases p with
  | nil => simp at hp
  | cons h q =>
    cases q with
    | nil => exact ⟨h, rfl⟩
    | cons h' q' =>
      rw [Walk.length_cons, Walk.length_cons] at hp
      omega

theorem sigma_top {W : Type} {s t : W} (hst : s ≠ t) :
    sigma (⊤ : SimpleGraph W) s t = 1 := by
  unfold sigma
  rw [dist_top_of_ne hst]
  have hadj : (⊤ : SimpleGraph W).Adj s t := hst
  haveI : Unique {p : (⊤ : SimpleGraph W).Walk s t // p.length = 1} :=
    { default := ⟨Walk.cons hadj Walk.nil, rfl⟩
      uniq := fun ⟨p, hp⟩ => by
        obtain ⟨h, rfl⟩ := walk_length_one p hp
        rfl }
  exact Nat.card_unique

theorem sigmaThrough_top {W : Type} [DecidableEq W] {s t : W} (hst : s ≠ t) (e : Sym2 W) :
    sigmaThrough (⊤ : SimpleGraph W) e s t = if s(s, t) = e then 1 else 0 := by
  unfold sigmaThrough
  rw [dist_top_of_ne hst]
  have hadj : (⊤ : SimpleGraph W).Adj s t := hst
  split_ifs with he
  · haveI : Unique {p : (⊤ : SimpleGraph W).Walk s t // p.length = 1 ∧ e ∈ p.edges} :=
      { default := ⟨Walk.cons hadj Walk.nil, rfl, by
          rw [Walk.edges_cons, Walk.edges_nil, List.mem_singleton]
          exact he.symm⟩
        uniq := fun ⟨p, hp, _⟩ => by
          obtain ⟨h, rfl⟩ := walk_length_one p hp
          rfl }
    exact Nat.card_unique
  · haveI : IsEmpty {p : (⊤ : SimpleGraph W).Walk s t // p.length = 1 ∧ e ∈ p.edges} :=
      ⟨fun ⟨p, hp, hmem⟩ => by
        obtain ⟨h, rfl⟩ := walk_length_one p hp
        rw [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at hmem
        exact he hmem.symm⟩
    exact Nat.card_of_isEmpty

/-! ### The complete graph on nine vertices -/

abbrev K9 : SimpleGraph (Fin 9) := ⊤

theorem K9_connected : K9.Connected := top_connected

theorem K9_adj : K9.Adj 0 1 := by decide

theorem wienerTwice_K9 : wienerTwice K9 = 72 := by
  unfold wienerTwice
  simp_rw [dist_top]
  decide

/-- In `K₉`, exactly the two ordered pairs `(0, 1)` and `(1, 0)` contribute to the betweenness
of the edge `01`, each with the value one. -/
theorem betweennessOrdered_K9 : betweennessOrdered K9 s(0, 1) = 2 := by
  unfold betweennessOrdered
  have key : ∀ s t : Fin 9,
      (if s = t then (0 : ℚ) else (sigmaThrough K9 s(0, 1) s t : ℚ) / (sigma K9 s t : ℚ))
        = ((if s ≠ t ∧ s(s, t) = s(0, 1) then 1 else 0 : ℕ) : ℚ) := by
    intro s t
    by_cases hst : s = t
    · simp [hst]
    · rw [if_neg hst, sigma_top hst, sigmaThrough_top hst]
      by_cases he : s(s, t) = s(0, 1)
      · simp [hst, he]
      · simp [hst, he]
  simp_rw [key]
  have hcount : (∑ s : Fin 9, ∑ t : Fin 9,
      (if s ≠ t ∧ s(s, t) = s(0, 1) then 1 else 0 : ℕ)) = 2 := by decide
  have hcast : (∑ s : Fin 9, ∑ t : Fin 9,
      ((if s ≠ t ∧ s(s, t) = s(0, 1) then 1 else 0 : ℕ) : ℚ))
      = ((∑ s : Fin 9, ∑ t : Fin 9,
        (if s ≠ t ∧ s(s, t) = s(0, 1) then 1 else 0 : ℕ) : ℕ) : ℚ) := by
    norm_cast
  rw [hcast, hcount]
  norm_num

theorem betweenness_K9 : betweenness K9 s(0, 1) = 1 := by
  unfold betweenness
  rw [betweennessOrdered_K9]
  norm_num

/-! ### The subdivided graph -/

theorem subdivide_K9_connected : (subdivide K9 0 1).Connected := by
  have hub : ∀ x : Option (Fin 9), (subdivide K9 0 1).Reachable (some 2) x := by
    intro x
    cases x with
    | none =>
      have h1 : (subdivide K9 0 1).Adj (some 2) (some 0) := by
        change K9.Adj 2 0 ∧ ¬ (((2 : Fin 9) = 0 ∧ (0 : Fin 9) = 1) ∨ ((2 : Fin 9) = 1 ∧ (0 : Fin 9) = 0))
        decide
      have h2 : (subdivide K9 0 1).Adj (some 0) none := Or.inl rfl
      exact h1.reachable.trans h2.reachable
    | some v =>
      by_cases hv : v = 2
      · subst hv
        exact Reachable.refl _
      · have h1 : (subdivide K9 0 1).Adj (some 2) (some v) := by
          refine ⟨fun h => hv h.symm, ?_⟩
          rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact absurd h (by decide)
          · exact absurd h (by decide)
        exact h1.reachable
  exact { preconnected := fun u v => (hub u).symm.trans (hub v), nonempty := ⟨none⟩ }

theorem wienerTwice_subdivide_K9 : 90 ≤ wienerTwice (subdivide K9 0 1) := by
  have h := wienerTwice_ge (subdivide K9 0 1) subdivide_K9_connected
  simpa using h

/-- Subdividing the edge `01` of `K₉` strictly increases the Wiener index. -/
theorem wiener_increases : wiener K9 < wiener (subdivide K9 0 1) := by
  unfold wiener
  rw [wienerTwice_K9]
  have h : ((90 : ℕ) : ℚ) ≤ (wienerTwice (subdivide K9 0 1) : ℚ) :=
    Nat.cast_le.mpr wienerTwice_subdivide_K9
  push_cast at h ⊢
  linarith

/-! ### The conjectured criterion and its negation -/

/-- The criterion: for every finite connected graph and every edge, subdividing the edge
decreases the Wiener index if and only if the betweenness of the edge is below a quarter of
the number of vertices. -/
def ClaimedCriterion : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.Connected →
    ∀ a b : V, G.Adj a b →
      (wiener (subdivide G a b) < wiener G ↔
        betweenness G s(a, b) < (Fintype.card V : ℚ) / 4)

/-- The same criterion with betweenness summed over ordered pairs. -/
def ClaimedCriterionOrdered : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.Connected →
    ∀ a b : V, G.Adj a b →
      (wiener (subdivide G a b) < wiener G ↔
        betweennessOrdered G s(a, b) < (Fintype.card V : ℚ) / 4)

theorem conjecture_false : ¬ ClaimedCriterion := by
  intro h
  have hb : betweenness K9 s(0, 1) < (Fintype.card (Fin 9) : ℚ) / 4 := by
    rw [betweenness_K9, Fintype.card_fin]
    norm_num
  have hw := (h (Fin 9) K9 K9_connected 0 1 K9_adj).mpr hb
  exact absurd hw (not_lt.mpr wiener_increases.le)

theorem conjecture_false_ordered : ¬ ClaimedCriterionOrdered := by
  intro h
  have hb : betweennessOrdered K9 s(0, 1) < (Fintype.card (Fin 9) : ℚ) / 4 := by
    rw [betweennessOrdered_K9, Fintype.card_fin]
    norm_num
  have hw := (h (Fin 9) K9 K9_connected 0 1 K9_adj).mpr hb
  exact absurd hw (not_lt.mpr wiener_increases.le)

#print axioms wienerTwice_ge
#print axioms sigma_top
#print axioms sigmaThrough_top
#print axioms wienerTwice_K9
#print axioms betweennessOrdered_K9
#print axioms betweenness_K9
#print axioms subdivide_K9_connected
#print axioms wiener_increases
#print axioms conjecture_false
#print axioms conjecture_false_ordered

end Conjecture3476
