import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finite.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The cycle graph `C_L` (`L ≥ 3`) has maximum degree `2`, and its measure of cycles of length
`L` is at least `1 / L`, which exceeds the conjectured bound `(d - 1) ^ L / (2 L) = 1 / (2 L)`
for `d = 2`. -/
namespace Conjecture4413

open SimpleGraph

/-- A rooted, oriented cycle of length `L` in `G`: an injective graph homomorphism from
Mathlib's cycle graph `C_L` to `G`. For `L ≥ 3` every cycle of length `L` in `G` (as a
subgraph) is the image of exactly `2 L` of them, one for each choice of a starting vertex and
a direction. -/
abbrev CycleCopy {V : Type} (G : SimpleGraph V) (L : ℕ) : Type :=
  {φ : cycleGraph L →g G // Function.Injective φ}

instance {V : Type} [Finite V] (G : SimpleGraph V) (L : ℕ) : Finite (CycleCopy G L) :=
  Finite.of_injective (fun φ : CycleCopy G L => (φ.1 : Fin L → V))
    fun _ _ h => Subtype.ext (DFunLike.coe_injective h)

/-- The measure of cycles of length `L` of a finite graph with the uniform probability measure
on its vertices: the number of cycles of length `L` divided by the number of vertices. -/
noncomputable def cycleMeasure {V : Type} [Fintype V] (G : SimpleGraph V) (L : ℕ) : ℚ :=
  (Nat.card (CycleCopy G L) : ℚ) / (2 * L) / Fintype.card V

/-- The conjectured upper bound `(d - 1) ^ L / (2 L)`. -/
def claimedBound (d L : ℕ) : ℚ := ((d : ℚ) - 1) ^ L / (2 * L)

/-! ### Rotations and reflections of the cycle graph -/

/-- The rotation `i ↦ i + k`. -/
def rotation (l : ℕ) (k : Fin (l + 3)) : CycleCopy (cycleGraph (l + 3)) (l + 3) :=
  ⟨⟨fun i => i + k, fun {a b} h => by
      rw [cycleGraph_adj] at h ⊢
      rwa [add_sub_add_right_eq_sub, add_sub_add_right_eq_sub]⟩,
    fun _ _ h => add_right_cancel h⟩

/-- The reflection `i ↦ k - i`. -/
def reflection (l : ℕ) (k : Fin (l + 3)) : CycleCopy (cycleGraph (l + 3)) (l + 3) :=
  ⟨⟨fun i => k - i, fun {a b} h => by
      rw [cycleGraph_adj] at h ⊢
      rw [sub_sub_sub_cancel_left, sub_sub_sub_cancel_left]
      exact h.symm⟩,
    fun _ _ h => sub_right_injective h⟩

theorem two_ne_zero_fin (l : ℕ) : (1 : Fin (l + 3)) + 1 ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_add, Fin.val_one, Fin.val_zero, Nat.reduceAdd] at this
  rw [Nat.mod_eq_of_lt (by omega : 2 < l + 3)] at this
  omega

theorem rotation_ne_reflection (l : ℕ) (k k' : Fin (l + 3)) :
    rotation l k ≠ reflection l k' := by
  intro h
  have hfun : ∀ i : Fin (l + 3), i + k = k' - i := fun i =>
    congrFun (congrArg (fun φ : CycleCopy (cycleGraph (l + 3)) (l + 3) =>
      (φ.1 : Fin (l + 3) → Fin (l + 3))) h) i
  have h0 : k = k' := by simpa using hfun 0
  have h1 := hfun 1
  rw [← h0] at h1
  apply two_ne_zero_fin l
  have : (1 : Fin (l + 3)) + 1 + k = k := by
    rw [add_assoc, h1, add_sub_cancel]
  simpa using this

/-- The cycle graph `C_L` has at least `2 L` rooted oriented cycles of length `L`. -/
theorem two_mul_le_card (l : ℕ) :
    2 * (l + 3) ≤ Nat.card (CycleCopy (cycleGraph (l + 3)) (l + 3)) := by
  let F : Fin (l + 3) × Bool → CycleCopy (cycleGraph (l + 3)) (l + 3) := fun p =>
    if p.2 then reflection l p.1 else rotation l p.1
  have hval : ∀ k i, ((rotation l k).1 : Fin (l + 3) → Fin (l + 3)) i = i + k := fun _ _ => rfl
  have hval' : ∀ k i, ((reflection l k).1 : Fin (l + 3) → Fin (l + 3)) i = k - i :=
    fun _ _ => rfl
  have hF : Function.Injective F := by
    rintro ⟨k, b⟩ ⟨k', b'⟩ h
    cases b <;> cases b'
    · have h0 := congrFun (congrArg (fun φ : CycleCopy (cycleGraph (l + 3)) (l + 3) =>
        (φ.1 : Fin (l + 3) → Fin (l + 3))) h) 0
      simp only [F, Bool.false_eq_true, if_false, hval] at h0
      rw [zero_add, zero_add] at h0
      rw [h0]
    · exact absurd h (rotation_ne_reflection l k k')
    · exact absurd h.symm (rotation_ne_reflection l k' k)
    · have h0 := congrFun (congrArg (fun φ : CycleCopy (cycleGraph (l + 3)) (l + 3) =>
        (φ.1 : Fin (l + 3) → Fin (l + 3))) h) 0
      simp only [F, if_true, hval'] at h0
      rw [sub_zero, sub_zero] at h0
      rw [h0]
  have hcard := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin (l + 3)), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hcard
  omega

/-! ### The cycle graph violates the conjectured bound -/

/-- The cycle measure of `C_L` at length `L` is at least `1 / L`. -/
theorem one_div_le_cycleMeasure (l : ℕ) :
    (1 : ℚ) / ((l : ℚ) + 3) ≤ cycleMeasure (cycleGraph (l + 3)) (l + 3) := by
  have hN : ((2 * (l + 3) : ℕ) : ℚ) ≤
      (Nat.card (CycleCopy (cycleGraph (l + 3)) (l + 3)) : ℚ) := by
    exact_mod_cast two_mul_le_card l
  have hL : (0 : ℚ) < (l : ℚ) + 3 := by positivity
  unfold cycleMeasure
  rw [Fintype.card_fin]
  push_cast at hN ⊢
  rw [div_le_div_iff_of_pos_right hL, le_div_iff₀ (by positivity)]
  linarith

theorem claimedBound_two (l : ℕ) : claimedBound 2 (l + 3) = 1 / (2 * ((l : ℚ) + 3)) := by
  unfold claimedBound
  push_cast
  norm_num

/-- For every `L ≥ 3` the cycle graph `C_L`, of maximum degree `2`, has cycle measure larger
than the conjectured bound for `d = 2`. -/
theorem cycle_violates (l : ℕ) :
    claimedBound 2 (l + 3) < cycleMeasure (cycleGraph (l + 3)) (l + 3) := by
  have hL : (0 : ℚ) < (l : ℚ) + 3 := by positivity
  calc claimedBound 2 (l + 3) = 1 / (2 * ((l : ℚ) + 3)) := claimedBound_two l
    _ < 1 / ((l : ℚ) + 3) := one_div_lt_one_div_of_lt hL (by linarith)
    _ ≤ cycleMeasure (cycleGraph (l + 3)) (l + 3) := one_div_le_cycleMeasure l

/-! ### The conjectured bound and its negation -/

/-- The upper bound of the conjecture, for finite graphs: if every vertex has degree at most
`d`, then the measure of cycles of length `L ≥ 3` is at most `(d - 1) ^ L / (2 L)`. -/
def ClaimedUpperBound : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d L : ℕ),
    3 ≤ L → (∀ v, G.degree v ≤ d) → cycleMeasure G L ≤ claimedBound d L

theorem conjecture_false : ¬ ClaimedUpperBound := fun h => by
  have h1 := h (Fin 3) (cycleGraph 3) 2 3 le_rfl fun v =>
    (cycleGraph_degree_three_le (n := 0) (v := v)).le
  exact absurd h1 (not_le.mpr (cycle_violates 0))

/-- The bound fails for `d = 2` at every length `L ≥ 3`. -/
theorem conjecture_false_every_length (l : ℕ) :
    ∃ (G : SimpleGraph (Fin (l + 3))) (_ : DecidableRel G.Adj),
      (∀ v, G.degree v ≤ 2) ∧ claimedBound 2 (l + 3) < cycleMeasure G (l + 3) :=
  ⟨cycleGraph (l + 3), inferInstance, fun _ => cycleGraph_degree_three_le.le, cycle_violates l⟩

#print axioms two_mul_le_card
#print axioms one_div_le_cycleMeasure
#print axioms cycle_violates
#print axioms conjecture_false
#print axioms conjecture_false_every_length

end Conjecture4413
