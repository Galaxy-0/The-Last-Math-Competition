import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Conjecture 00000000024 is false. This file constructs a proper four-coloring
of the graph on ALL real numbers whose adjacent points have prime distance.
It also supplies the same four-color bound for every restricted prime set.
-/

namespace TLMC24

def primeGraph (S : Set ℕ) : SimpleGraph ℝ where
  Adj x y := ∃ p : ℕ, p.Prime ∧ p ∈ S ∧ (y = x + p ∨ x = y + p)
  symm := by
    constructor
    intro x y h
    rcases h with ⟨p, hp, hS, hxy⟩
    exact ⟨p, hp, hS, hxy.symm⟩
  loopless := by
    constructor
    intro x h
    rcases h with ⟨p, hp, _, hxy⟩
    have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    rcases hxy with hxy | hxy <;> linarith

noncomputable def color (x : ℝ) : Fin 4 :=
  ⟨(Int.floor x % 4).toNat, by omega⟩

theorem prime_mod_four_ne_zero {p : ℕ} (hp : p.Prime) : p % 4 ≠ 0 := by
  intro h
  have hd : 4 ∣ p := Nat.dvd_of_mod_eq_zero h
  rcases hp.eq_one_or_self_of_dvd 4 hd with h4 | h4
  · omega
  · have : p = 4 := h4.symm
    subst p
    exact (by decide : ¬ Nat.Prime 4) hp

theorem shifted_colors_differ (x : ℝ) {p : ℕ} (hp : p.Prime) :
    color x ≠ color (x + p) := by
  intro heq
  have hv := congrArg Fin.val heq
  have hf := Int.floor_add_natCast x p
  have hm := prime_mod_four_ne_zero hp
  dsimp [color] at hv
  omega

noncomputable def fourColoring (S : Set ℕ) : (primeGraph S).Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk color (by
    intro x y h
    rcases h with ⟨p, hp, _, hxy⟩
    rcases hxy with hy | hx
    · subst y
      exact shifted_colors_differ x hp
    · subst x
      exact (shifted_colors_differ y hp).symm)

theorem all_real_prime_distances_four_colorable :
    Nonempty ((primeGraph Set.univ).Coloring (Fin 4)) :=
  ⟨fourColoring Set.univ⟩

theorem every_restricted_prime_set_four_colorable (S : Set ℕ) :
    Nonempty ((primeGraph S).Coloring (Fin 4)) :=
  ⟨fourColoring S⟩

theorem chromatic_number_le_four (S : Set ℕ) : (primeGraph S).chromaticNumber ≤ 4 := by
  exact (show (primeGraph S).Colorable 4 from ⟨fourColoring S⟩).chromaticNumber_le

theorem full_chromatic_number_is_finite : (primeGraph Set.univ).chromaticNumber ≠ ⊤ := by
  exact SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr
    ⟨4, ⟨fourColoring Set.univ⟩⟩

-- These are genuine real-line graph colorings, not just residue computations.
#print axioms all_real_prime_distances_four_colorable
#print axioms every_restricted_prime_set_four_colorable
#print axioms full_chromatic_number_is_finite

end TLMC24
