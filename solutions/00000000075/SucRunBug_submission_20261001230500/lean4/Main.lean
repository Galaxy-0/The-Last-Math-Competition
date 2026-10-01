import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
For every odd prime p and every c, the image of x ↦ x²+c on ZMod p has
(p+1)/2 elements. In particular the normalized image size is at least 1/2,
so it cannot tend to the conjectured smaller constant 1-sqrt(pi/8).
-/

namespace TLMC75

open Finset Filter
open scoped Topology

def squares (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.image (fun x : ZMod p => x ^ 2)

def imageSet (p : ℕ) [Fact p.Prime] (c : ZMod p) : Finset (ZMod p) :=
  Finset.univ.image (fun x : ZMod p => x ^ 2 + c)

theorem two_ne_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  rcases Nat.prime_two.eq_one_or_self_of_dvd p hd with h1 | h2
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp h2

theorem zero_mem_squares (p : ℕ) [Fact p.Prime] : (0 : ZMod p) ∈ squares p := by
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp⟩

theorem nonzero_square_fiber_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (y : ZMod p) (hy : y ∈ squares p) (hne : y ≠ 0) :
    (Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card = 2 := by
  rcases Finset.mem_image.mp hy with ⟨b, _, hb⟩
  have hb0 : b ≠ 0 := by intro h; subst b; simp at hb; exact hne hb.symm
  have hbneg : b ≠ -b := by
    intro h
    have hsum : b + b = 0 := eq_neg_iff_add_eq_zero.mp h
    have hmul : (2 : ZMod p) * b = 0 := by simpa only [two_mul] using hsum
    exact hb0 ((mul_eq_zero.mp hmul).resolve_left (two_ne_zero p hp))
  have hset : Finset.univ.filter (fun x : ZMod p => x ^ 2 = y) = {b, -b} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [← hb]
    exact sq_eq_sq_iff_eq_or_eq_neg
  rw [hset, Finset.card_pair hbneg]

theorem twice_square_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    2 * (squares p).card = p + 1 := by
  have hz := zero_mem_squares p
  have hzero : (Finset.univ.filter (fun x : ZMod p => x ^ 2 = 0)).card = 1 := by
    have hzset : Finset.univ.filter (fun x : ZMod p => x ^ 2 = 0) = {0} := by
      ext x
      simp
    rw [hzset]
    rfl
  have hsum := Finset.card_eq_sum_card_image (fun x : ZMod p => x ^ 2) Finset.univ
  change Fintype.card (ZMod p) =
    ∑ y ∈ squares p, (Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card at hsum
  rw [ZMod.card p] at hsum
  rw [← Finset.sum_erase_add _ _ hz, hzero] at hsum
  have herase :
      (∑ y ∈ (squares p).erase 0,
        (Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card) =
        2 * ((squares p).erase 0).card := by
    calc
      _ = ∑ _y ∈ (squares p).erase 0, 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact nonzero_square_fiber_card p hp y (Finset.mem_of_mem_erase hy)
          (Finset.ne_of_mem_erase hy)
      _ = _ := by simp [Nat.mul_comm]
  rw [herase] at hsum
  have hcard := Finset.card_erase_of_mem hz
  have hpos : 0 < (squares p).card := Finset.card_pos.mpr ⟨0, hz⟩
  omega

theorem image_card_eq_square_card (p : ℕ) [Fact p.Prime] (c : ZMod p) :
    (imageSet p c).card = (squares p).card := by
  have hset : imageSet p c = (squares p).image (fun y => y + c) := by
    simp only [imageSet, squares, Finset.image_image, Function.comp_def]
  rw [hset]
  exact Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)

theorem twice_image_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (c : ZMod p) :
    2 * (imageSet p c).card = p + 1 := by
  rw [image_card_eq_square_card]
  exact twice_square_card p hp

theorem exact_image_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (c : ZMod p) :
    (imageSet p c).card = (p + 1) / 2 := by
  have h := twice_image_card p hp c
  omega

theorem normalized_image_ge_half (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (c : ZMod p) :
    (1 / 2 : ℝ) ≤ ((imageSet p c).card : ℝ) / p := by
  have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have heq : 2 * ((imageSet p c).card : ℝ) = (p : ℝ) + 1 := by
    exact_mod_cast twice_image_card p hp c
  apply (le_div_iff₀ hpos).mpr
  nlinarith

theorem claimed_constant_lt_half : 1 - Real.sqrt (Real.pi / 8) < (1 / 2 : ℝ) := by
  have hnonneg : 0 ≤ Real.pi / 8 := by positivity
  have hsquare := Real.sq_sqrt hnonneg
  have hsqrt := Real.sqrt_nonneg (Real.pi / 8)
  have hpi := Real.pi_gt_three
  nlinarith

theorem no_claimed_limit (ps : ℕ → ℕ) [∀ n, Fact (ps n).Prime]
    (hodd : ∀ n, ps n ≠ 2) (cs : (n : ℕ) → ZMod (ps n)) :
    ¬ Tendsto (fun n => ((imageSet (ps n) (cs n)).card : ℝ) / ps n)
      atTop (nhds (1 - Real.sqrt (Real.pi / 8))) := by
  intro ht
  have hle : (1 / 2 : ℝ) ≤ 1 - Real.sqrt (Real.pi / 8) :=
    ge_of_tendsto' ht (fun n => normalized_image_ge_half (ps n) (hodd n) (cs n))
  exact (not_le_of_gt claimed_constant_lt_half) hle

#print axioms exact_image_card
#print axioms no_claimed_limit

end TLMC75
