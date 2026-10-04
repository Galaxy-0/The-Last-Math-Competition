import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Normal-play undirected vertex geography

`S` consists of the current vertex and all unvisited available vertices.
The current vertex has already been visited: a move along an edge from `v`
to `w` deletes `v` from `S`, and requires `w` to belong to `S.erase v`.
Thus a vertex cannot be revisited. Players alternate moving one token;
the player with no legal move loses. These conventions are made explicit
because the short conjecture statement does not spell them out.

The definition of `Wins` depends only on legal moves and normal play,
independently of matchings. Its recursion terminates because each legal
move strictly decreases the number of available vertices.
-/

namespace Conjecture1227

variable {V : Type*} [DecidableEq V]

/-- A legal move deletes the current vertex and enters an adjacent one. -/
def LegalMove (G : SimpleGraph V) (S : Finset V) (v w : V) : Prop :=
  v ∈ S ∧ w ∈ S.erase v ∧ G.Adj v w

/-- The player whose turn it is can force a win under normal play. -/
noncomputable def Wins (G : SimpleGraph V) (S : Finset V) (v : V) : Prop :=
  if _hv : v ∈ S then
    ∃ w ∈ S.erase v, G.Adj v w ∧ ¬ Wins G (S.erase v) w
  else False
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem _hv

/-- At every valid position, winning means having a move to a losing position. -/
theorem wins_recurrence (G : SimpleGraph V) (S : Finset V) (v : V)
    (hv : v ∈ S) :
    Wins G S v ↔ ∃ w ∈ S.erase v, G.Adj v w ∧ ¬ Wins G (S.erase v) w := by
  rw [Wins]
  simp only [dif_pos hv]

/-- A position with no legal move is losing. -/
theorem not_wins_of_no_move (G : SimpleGraph V) (S : Finset V) (v : V)
    (hv : v ∈ S) (h : ∀ w, ¬ LegalMove G S v w) : ¬ Wins G S v := by
  rw [wins_recurrence G S v hv]
  rintro ⟨w, hw, ha, _⟩
  exact h w ⟨hv, hw, ha⟩

/-- The finite normal-play recurrence uniquely specifies the outcome. -/
theorem wins_iff_of_recurrence (G : SimpleGraph V) (P : Finset V → V → Prop)
    (hP : ∀ S v, v ∈ S →
      (P S v ↔ ∃ w ∈ S.erase v, G.Adj v w ∧ ¬ P (S.erase v) w)) :
    ∀ S v, v ∈ S → (Wins G S v ↔ P S v) := by
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih v hv
  rw [wins_recurrence G S v hv, hP S v hv]
  apply exists_congr
  intro w
  apply and_congr_right
  intro hw
  rw [ih (S.erase v) (Finset.erase_ssubset hv) w hw]

/-- Initially every vertex is available, with the token already at `start`. -/
noncomputable def FirstPlayerWins [Fintype V] (G : SimpleGraph V) (start : V) : Prop :=
  Wins G Finset.univ start

end Conjecture1227
