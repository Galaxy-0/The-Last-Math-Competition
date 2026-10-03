import Mathlib

/-!
# Conjecture 00000001666 is false

In the *domination game* on a graph `G`, Dominator and Staller alternately choose
vertices, Dominator first. Each chosen vertex must dominate (be or be adjacent to) at
least one vertex not dominated so far, and the game ends when every vertex is
dominated. Dominator tries to finish in as few moves as possible, Staller in as many as
possible; the *game domination number* `γ_g(G)` is the number of moves under optimal
play.

Conjecture 00000001666 asserts that `γ_g(C_n) = ⌈n/5⌉ + O(1)` for the cycle `C_n`. In
fact `γ_g(C_n) ≥ n/3`, whatever the players do: a vertex of `C_n` dominates at most
three vertices, so each move removes at most three undominated vertices, and all
`n` vertices must be dominated. Since `n/3 - n/5` is unbounded, no constant works.
(The true value of `γ_g(C_n)` is about `n/2`; it was determined exactly by Košmrlj.)
-/

namespace Submission00000001666

open Finset

section Game

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The closed neighbourhood `N[v] = {v} ∪ N(v)`. -/
def closedNbhd (v : V) : Finset V := insert v (univ.filter (G.Adj v))

/-- The vertices dominated by a set `S` of chosen vertices. -/
def dominated (S : Finset V) : Finset V := S.biUnion (closedNbhd G)

/-- The legal moves after `S` has been chosen: vertices that dominate a vertex not yet
dominated. There are none exactly when every vertex is dominated. -/
def legalMoves (S : Finset V) : Finset V :=
  univ.filter fun v => ¬ closedNbhd G v ⊆ dominated G S

/-- The value of the domination game from position `S` (the vertices chosen so far),
with `dom = true` when Dominator is to move: `0` once no legal move remains;
otherwise `1` plus the minimum (Dominator) or maximum (Staller) of the values after
the legal moves. The argument `fuel` bounds the number of remaining moves; each move
dominates a new vertex, so `fuel = |V|` is never exhausted. -/
def gameValue : ℕ → Bool → Finset V → ℕ
  | 0, _, _ => 0
  | fuel + 1, dom, S =>
    if h : (legalMoves G S).Nonempty then
      if dom then
        1 + ((legalMoves G S).image fun v => gameValue fuel false (insert v S)).min'
          (h.image _)
      else
        1 + ((legalMoves G S).image fun v => gameValue fuel true (insert v S)).max'
          (h.image _)
    else 0

/-- The game domination number `γ_g(G)`: the value of the game from the empty position
with Dominator to move. -/
def gameDominationNumber : ℕ := gameValue G (Fintype.card V) true ∅

theorem dominated_insert (v : V) (S : Finset V) :
    dominated G (insert v S) = closedNbhd G v ∪ dominated G S := by
  simp [dominated, biUnion_insert]

/-- A legal move strictly decreases the number of undominated vertices. -/
theorem card_undominated_insert_lt {v : V} {S : Finset V} (hv : v ∈ legalMoves G S) :
    (univ \ dominated G (insert v S)).card < (univ \ dominated G S).card := by
  rw [legalMoves, mem_filter, not_subset] at hv
  obtain ⟨-, u, hu, hus⟩ := hv
  apply card_lt_card
  rw [ssubset_iff_of_subset]
  · refine ⟨u, by simp [hus], ?_⟩
    simp [dominated_insert, hu]
  · intro w hw
    simp only [mem_sdiff, mem_univ, true_and, dominated_insert, mem_union, not_or] at hw ⊢
    exact hw.2

/-- A move removes at most `|N[v]|` undominated vertices. -/
theorem card_undominated_le {v : V} {S : Finset V} :
    (univ \ dominated G S).card ≤
      (univ \ dominated G (insert v S)).card + (closedNbhd G v).card := by
  rw [add_comm]
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro w hw
  simp only [mem_sdiff, mem_univ, true_and, mem_union, dominated_insert, not_or] at hw ⊢
  by_cases h : w ∈ closedNbhd G v
  · exact Or.inl h
  · exact Or.inr ⟨h, hw⟩

/-- When no legal move remains, every vertex is dominated. -/
theorem card_undominated_eq_zero {S : Finset V} (h : ¬ (legalMoves G S).Nonempty) :
    (univ \ dominated G S).card = 0 := by
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro u hu
  apply h
  refine ⟨u, ?_⟩
  rw [legalMoves, mem_filter, not_subset]
  exact ⟨mem_univ _, u, mem_insert_self _ _, (mem_sdiff.1 hu).2⟩

/-- If every closed neighbourhood has at most `m` vertices, then whatever the players do,
the game lasts at least `(number of undominated vertices) / m` more moves. -/
theorem card_undominated_le_mul (m : ℕ) (hm : ∀ v, (closedNbhd G v).card ≤ m) :
    ∀ (fuel : ℕ) (dom : Bool) (S : Finset V), (univ \ dominated G S).card ≤ fuel →
      (univ \ dominated G S).card ≤ m * gameValue G fuel dom S := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; omega
  | succ fuel ih =>
    intro dom S hS
    -- after any legal move `v`, the bound holds by induction
    have hstep : ∀ v ∈ legalMoves G S, ∀ d,
        (univ \ dominated G S).card ≤ m * gameValue G fuel d (insert v S) + m := by
      intro v hv d
      have hlt := card_undominated_insert_lt G hv
      have h1 := ih d (insert v S) (by omega)
      have h2 := card_undominated_le G (v := v) (S := S)
      have h3 := hm v
      omega
    rw [gameValue]
    split_ifs with h hd
    · obtain ⟨v, hv, hmin⟩ := mem_image.1
        (min'_mem ((legalMoves G S).image fun v => gameValue G fuel false (insert v S))
          (h.image _))
      have := hstep v hv false
      rw [hmin] at this
      rw [mul_add, mul_one]
      omega
    · obtain ⟨v, hv⟩ := id h
      have hle : gameValue G fuel true (insert v S) ≤
          ((legalMoves G S).image fun v => gameValue G fuel true (insert v S)).max'
            (h.image _) :=
        le_max' _ _ (mem_image_of_mem (fun v => gameValue G fuel true (insert v S)) hv)
      have := hstep v hv true
      have := Nat.mul_le_mul_left m hle
      rw [mul_add, mul_one]
      omega
    · rw [card_undominated_eq_zero G h]
      exact Nat.zero_le _

/-- `γ_g(G) ≥ |V| / m` when every closed neighbourhood has at most `m` vertices. -/
theorem card_le_mul_gameDominationNumber (m : ℕ) (hm : ∀ v, (closedNbhd G v).card ≤ m) :
    Fintype.card V ≤ m * gameDominationNumber G := by
  have h := card_undominated_le_mul G m hm (Fintype.card V) true ∅ (by
    simp [dominated])
  simpa [dominated, gameDominationNumber] using h

end Game

/-! ## Cycles -/

open SimpleGraph

/-- A vertex of the cycle `C_n` dominates at most three vertices. -/
theorem card_closedNbhd_cycleGraph (n : ℕ) (v : Fin n) :
    (closedNbhd (cycleGraph n) v).card ≤ 3 := by
  refine (card_insert_le _ _).trans ?_
  have : (univ.filter ((cycleGraph n).Adj v)).card ≤ 2 := by
    match n, v with
    | 0, v => exact v.elim0
    | 1, v => simp [cycleGraph_one_adj]
    | k + 2, v =>
      rw [← neighborFinset_eq_filter, cycleGraph_neighborFinset]
      exact card_le_two
  omega

/-- `γ_g(C_n) ≥ n / 3`. -/
theorem le_three_mul_gameDominationNumber (n : ℕ) :
    n ≤ 3 * gameDominationNumber (cycleGraph n) := by
  simpa using card_le_mul_gameDominationNumber (cycleGraph n) 3
    (card_closedNbhd_cycleGraph n)

/-- Conjecture 00000001666: `γ_g(C_n) = ⌈n/5⌉ + O(1)`, i.e. there is a constant `C` with
`|γ_g(C_n) - ⌈n/5⌉| ≤ C` for all `n ≥ 3` (`⌈n/5⌉ = (n + 4) / 5`). -/
def ConjectureHolds : Prop :=
  ∃ C : ℕ, ∀ n, 3 ≤ n →
    gameDominationNumber (cycleGraph n) ≤ (n + 4) / 5 + C ∧
      (n + 4) / 5 ≤ gameDominationNumber (cycleGraph n) + C

/-- Conjecture 00000001666 is false: `γ_g(C_n) ≥ n/3` exceeds `⌈n/5⌉ + C` for
`n = 15C + 15`. -/
theorem conjecture_00000001666_false : ¬ ConjectureHolds := by
  rintro ⟨C, hC⟩
  have h1 := (hC (15 * C + 15) (by omega)).1
  have h2 := le_three_mul_gameDominationNumber (15 * C + 15)
  omega

end Submission00000001666

#print axioms Submission00000001666.conjecture_00000001666_false
