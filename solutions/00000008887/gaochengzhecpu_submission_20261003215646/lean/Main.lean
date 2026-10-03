import Std

namespace Conjecture8887
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
instance productForall {m n} (P : Fin m × Fin n → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  decidable_of_iff (∀ a b, P (a,b)) (by
    constructor
    · intro h x; exact h x.1 x.2
    · intro h a b; exact h (a,b))

/-- A finite normal-play partisan game, with ALL states enumerated and a
    strictly decreasing height, so play always ends. false=Left, true=Right. -/
structure Game (S : Type) where
  states : List S
  complete : ∀ s, s ∈ states
  move : Bool → S → S → Bool
  height : S → Nat
  decreases : ∀ p s t, move p s t = true → height t < height s

def wins {S : Type} (G : Game S) (p : Bool) (s : S) : Bool :=
  G.states.any (fun t => if _h : G.move p s t = true then !(wins G (!p) t) else false)
termination_by G.height s
decreasing_by exact G.decreases p s t _h

def winsFuel {S : Type} (G : Game S) : Nat → Bool → S → Bool
  | 0, _, _ => false
  | k+1, p, s => G.states.any (fun t =>
      if G.move p s t = true then !(winsFuel G k (!p) t) else false)

theorem wins_eq_fuel {S : Type} (G : Game S) (k : Nat) (p : Bool) (s : S)
    (hk : G.height s < k) : wins G p s = winsFuel G k p s := by
  induction k generalizing p s with
  | zero => omega
  | succ k ih =>
    rw [wins, winsFuel]
    apply congrArg (List.any G.states)
    funext t
    by_cases hm : G.move p s t = true
    · simp only [dif_pos hm, if_pos hm]
      have hd := G.decreases p s t hm
      rw [ih (!p) t (by omega)]
    · simp only [dif_neg hm, if_neg hm]

/-- Standard negation interchanges Left and Right options at every state. -/
def negative {S} (G : Game S) : Game S where
  states := G.states
  complete := G.complete
  move p := G.move (!p)
  height := G.height
  decreases p := G.decreases (!p)

def sumGame {S T : Type} [BEq S] [LawfulBEq S] [BEq T] [LawfulBEq T]
    (G : Game S) (H : Game T) : Game (S × T) where
  states := G.states.flatMap (fun s => H.states.map (fun t => (s,t)))
  complete st := by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨st.1, G.complete st.1, st.2, H.complete st.2, rfl⟩
  move p s t := (G.move p s.1 t.1 && (s.2 == t.2)) ||
    ((s.1 == t.1) && H.move p s.2 t.2)
  height s := G.height s.1 + H.height s.2
  decreases p s t hm := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
    rcases hm with ⟨hg, he⟩ | ⟨he, hh⟩
    · have h := G.decreases p s.1 t.1 hg
      rw [he]
      omega
    · have h := H.decreases p s.2 t.2 hh
      rw [he]
      omega

def zeroGame : Game Unit where
  states := [()]
  complete s := by cases s; simp
  move _ _ _ := false
  height _ := 0
  decreases _ _ _ h := by contradiction

/-- Equality of short-game values is indistinguishability under disjunctive
    addition of every finite normal-play context, for either starting player. -/
def EqualValue {S T : Type} [BEq S] [LawfulBEq S] [BEq T] [LawfulBEq T]
    (G : Game S) (s : S) (H : Game T) (t : T) : Prop :=
  ∀ (U : Type) [BEq U] [LawfulBEq U] (K : Game U) (u : U) (p : Bool),
    wins (sumGame G K) p (s,u) = wins (sumGame H K) p (t,u)

abbrev Vertex := Fin 2
abbrev Color := Fin 3
abbrev Board := Color × Color
def boards : List Board := (List.finRange 3).flatMap (fun a => (List.finRange 3).map (fun b => (a,b)))
def cell (b : Board) (v : Vertex) : Color := if v=0 then b.1 else b.2
def playerColor (p : Bool) : Color := if p then 2 else 1
def place (b : Board) (p : Bool) (v : Vertex) : Board :=
  if v=0 then (playerColor p,b.2) else (b.1,playerColor p)
def adjacent (u v : Vertex) : Bool := u != v
def emptyCount (b : Board) : Nat := ((List.finRange 2).filter (fun v => cell b v == 0)).length

theorem every_board_present : ∀ b : Board, b ∈ boards := by decide
theorem every_coloring_represented (f : Vertex → Color) : cell (f 0,f 1) = f := by
  funext v
  have all : ∀ v : Vertex, v=0 ∨ v=1 := by decide
  have h := all v
  rcases h with rfl | rfl <;> rfl

/-- Snort disallows adjacent opposite colors; Col disallows adjacent equal
    colors. Already occupied vertices cannot be chosen in either game. -/
def legal (snort : Bool) (p : Bool) (b : Board) (v : Vertex) : Bool :=
  (cell b v == 0) && (List.finRange 2).all (fun w =>
    !adjacent v w || (cell b w != playerColor (if snort then !p else p)))
def boardMove (snort : Bool) (p : Bool) (b c : Board) : Bool :=
  (List.finRange 2).any (fun v => legal snort p b v && (place b p v == c))
theorem every_move_is_a_legal_placement : ∀ snort p b c,
    boardMove snort p b c = true ↔
    (legal snort p b 0 = true ∧ place b p 0 = c) ∨
    (legal snort p b 1 = true ∧ place b p 1 = c) := by decide
theorem all_moves_decrease : ∀ snort p b c,
    boardMove snort p b c = true → emptyCount c < emptyCount b := by decide
def boardGame (snort : Bool) : Game Board where
  states := boards
  complete := every_board_present
  move := boardMove snort
  height := emptyCount
  decreases := all_moves_decrease snort
def emptyBoard : Board := (0,0)

theorem snort_first_player_wins :
    wins (boardGame true) false emptyBoard = true ∧
    wins (boardGame true) true emptyBoard = true := by
  constructor <;> rw [wins_eq_fuel _ 3 _ _ (by decide)] <;> decide
theorem col_first_player_loses :
    wins (boardGame false) false emptyBoard = false ∧
    wins (boardGame false) true emptyBoard = false := by
  constructor <;> rw [wins_eq_fuel _ 3 _ _ (by decide)] <;> decide
theorem zero_context_separates :
    wins (sumGame (boardGame true) zeroGame) false (emptyBoard,()) = true ∧
    wins (sumGame (negative (boardGame false)) zeroGame) false (emptyBoard,()) = false := by
  constructor <;> rw [wins_eq_fuel _ 3 _ _ (by decide)] <;> decide

def swapVertices (v : Vertex) : Vertex := if v=0 then 1 else 0
theorem symmetric_graph :
    (∀ v, adjacent v v = false) ∧
    (∀ u v, adjacent u v = adjacent v u) ∧
    (∀ v, swapVertices (swapVertices v)=v) ∧
    (∀ u v, adjacent (swapVertices u) (swapVertices v)=adjacent u v) ∧
    swapVertices 0 ≠ 0 := by decide

theorem conjecture8887_counterexample :
    ¬ EqualValue (boardGame true) emptyBoard (negative (boardGame false)) emptyBoard := by
  intro h
  have hf := h Unit zeroGame () false
  rw [zero_context_separates.1, zero_context_separates.2] at hf
  contradiction

end Conjecture8887
#print axioms Conjecture8887.conjecture8887_counterexample
#print axioms Conjecture8887.every_coloring_represented
