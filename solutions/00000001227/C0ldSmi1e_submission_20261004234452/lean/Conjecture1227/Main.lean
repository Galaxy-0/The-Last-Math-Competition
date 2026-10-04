import Conjecture1227.Matching
import Conjecture1227.Game

/-!
# The maximum-matching criterion for undirected vertex geography

The theorem applies to every finite simple undirected graph and every
start vertex, including isolated vertices and disconnected graphs.
"Belongs to a matching" means endpoint saturation, and "maximum" means
maximum edge cardinality. No perfect matching is assumed to exist.

This is the known maximum-matching characterization of undirected vertex
geography. The historical extension language in the source statement is
not asserted as a new mathematical result here.
-/

namespace Conjecture1227

variable {V : Type*} [DecidableEq V]

/-- The criterion holds at every residual position, not only initial positions. -/
theorem wins_iff_essential (G : SimpleGraph V) (S : Finset V) (v : V)
    (hv : v ∈ S) : Wins G S v ↔ Essential G S v :=
  wins_iff_of_recurrence G (Essential G) (essential_recurrence G) S v hv

/-- Conjecture 00000001227: all maximum matchings must saturate the start. -/
theorem first_player_wins_iff_every_maximum_matching_saturates
    [Fintype V] (G : SimpleGraph V) (start : V) :
    FirstPlayerWins G start ↔
      ∀ M : Finset (Sym2 V), MaximumMatching G Finset.univ M → Saturates M start :=
  wins_iff_essential G Finset.univ start (Finset.mem_univ start)

/-- An isolated start loses, including in disconnected graphs. -/
theorem isolated_start_loses [Fintype V] (G : SimpleGraph V) (start : V)
    (h : ∀ w, ¬ G.Adj start w) : ¬ FirstPlayerWins G start := by
  apply not_wins_of_no_move G Finset.univ start (Finset.mem_univ start)
  intro w hw
  exact h w hw.2.2

end Conjecture1227
