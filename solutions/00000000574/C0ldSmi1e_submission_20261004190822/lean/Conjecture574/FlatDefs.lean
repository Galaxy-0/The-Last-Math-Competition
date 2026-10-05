import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace Conjecture574

/-- The finite sets indexing the flats of the rank-three uniform matroid on four points.
The correspondence with actual matroid flats is proved in the matroid module. -/
abbrev Flat := {F : Finset (Fin 4) // F.card < 3 ∨ F = Finset.univ}

def flatRank (F : Flat) : ℕ := min 3 F.val.card

theorem flatRank_strictMono : StrictMono flatRank := by decide

theorem flat_card : Fintype.card Flat = 12 := by decide

end Conjecture574
