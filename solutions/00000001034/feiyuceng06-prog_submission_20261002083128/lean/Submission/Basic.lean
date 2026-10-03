import Mathlib

/-!
# Conjecture 00000001034 is false

A *perfect Lee code* of radius `e` in `𝔽_q^n` is a set `C` of codewords such that
the Lee balls of radius `e` around the codewords partition `𝔽_q^n`: every word lies
within Lee distance `e` of exactly one codeword. The Lee weight of `a ∈ ℤ/q` is
`min(a, q - a)` (for `0 ≤ a < q`), and the Lee distance of two words is the sum of
the Lee weights of their coordinatewise differences.

Conjecture 00000001034 asserts that nontrivial perfect Lee codes exist only for
`n = 1` (with `q ≥ 5`) and for `n = 3` (with `q = 2`). This fails for `n = 2`:

  `C = {(x, y) ∈ 𝔽₅² : x + 2y = 0} = {(0,0), (1,2), (2,4), (3,1), (4,3)}`

is a perfect Lee code of radius `1` in `𝔽₅²` with five codewords. Each Lee ball of
radius `1` has `5` points (the centre and its four neighbours `±e₁, ±e₂`), and the
`5` balls cover all `25` points without overlap. This is the classical
two-dimensional perfect Lee code of Golomb and Welch.
-/

namespace Submission00000001034

/-- The Lee weight of `a ∈ ℤ/q`: the distance from `a` to `0` around the cycle,
`min(a, q - a)` for the representative `0 ≤ a < q`. -/
def leeWeight {q : ℕ} (a : ZMod q) : ℕ := min a.val (q - a.val)

/-- The Lee distance between two words of length `n` over `ℤ/q`. -/
def leeDist {q n : ℕ} (x y : Fin n → ZMod q) : ℕ := ∑ i, leeWeight (x i - y i)

/-- `C` is a perfect Lee code of radius `e` in `(ℤ/q)^n`: every word lies within Lee
distance `e` of exactly one codeword, i.e. the Lee balls of radius `e` around the
codewords partition the space. -/
def IsPerfectLeeCode (q n e : ℕ) (C : Finset (Fin n → ZMod q)) : Prop :=
  ∀ x : Fin n → ZMod q, (C.filter fun c => leeDist x c ≤ e).card = 1

/-- Conjecture 00000001034: a nontrivial perfect Lee code in `𝔽_q^n` (for `q` prime,
where `𝔽_q = ℤ/q`), with radius `e ≥ 1` and at least two codewords, exists only for
`n = 1` with `q ≥ 5`, or for `n = 3` with `q = 2`. -/
def ConjectureHolds : Prop :=
  ∀ (q n e : ℕ) (C : Finset (Fin n → ZMod q)), q.Prime →
    IsPerfectLeeCode q n e C → 1 ≤ e → 2 ≤ C.card →
      (n = 1 ∧ 5 ≤ q) ∨ (n = 3 ∧ q = 2)

/-- The Golomb–Welch code `{(x, y) : x + 2y = 0}` in `𝔽₅²`. -/
def C5 : Finset (Fin 2 → ZMod 5) :=
  {![0, 0], ![1, 2], ![2, 4], ![3, 1], ![4, 3]}

/-- It is a perfect Lee code of radius `1`: checked over all `25` words. -/
theorem isPerfectLeeCode_C5 : IsPerfectLeeCode 5 2 1 C5 := by
  unfold IsPerfectLeeCode
  decide

theorem card_C5 : C5.card = 5 := by
  decide

/-- Conjecture 00000001034 is false: `C5` is a nontrivial perfect Lee code with
`n = 2`. -/
theorem conjecture_00000001034_false : ¬ ConjectureHolds := by
  intro h
  have := h 5 2 1 C5 (by norm_num) isPerfectLeeCode_C5 le_rfl (by rw [card_C5]; norm_num)
  omega

end Submission00000001034

#print axioms Submission00000001034.conjecture_00000001034_false
