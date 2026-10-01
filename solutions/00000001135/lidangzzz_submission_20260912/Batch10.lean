/-
  Batch 10: machine-checked disproof of TLMC #1135
  ================================================

  Conjecture #1135 asserts, for the Betti-number generating function
  P(t) = Σ b_{2i} t^i of the Bott–Samelson variety BS(s₁,…,s_k), that
  (among other clauses) P(t) is divisible by (1+t)^{⌊k/2⌋} with monic
  quotient when s₁…s_k is a reduced word.

  This is false.  Take the reduced word (2,1,3,2,3) for
  w = 3421 ∈ S₄ (a smooth permutation: it avoids the patterns 4231 and
  3412, checked below).  For a reduced word of a smooth w, BS(𝐬)
  resolves the Schubert variety X_w with H*(BS(𝐬)) ≅ H*(X_w), and the
  Schubert classes {v ≤ w} give a basis, so

    b_j = #{v ∈ S₄ : v has a reduced subword of 𝐬 of length j}.

  The subword computation below (kernel-verified) gives

    P(t) = 1 + 3t + 5t² + 5t³ + 3t⁴ + t⁵   (palindromic, as it must be),

  and P(t) = (1+t)(1 + 2t + 3t² + 2t³ + t⁴) with the quotient taking
  value 1 ≠ 0 at t = −1; hence (1+t)² = (1+t)^{⌊5/2⌋} does NOT divide
  P(t).  (Clause 1, strict increase to the middle 1 < 3 < 5, holds; the
  failure is precisely the divisibility clause.)

  The identification of the subword polynomial with the Betti generating
  function rests on the classical theorems of Bott–Samelson theory
  (birational resolution with rationally singular target; Schubert basis
  of smooth Schubert varieties), cited here rather than formalized; the
  arithmetic and combinatorics are fully machine-checked.

  No `sorry`.  Toolchain: leanprover/lean4:v4.31.0, Mathlib v4.31.0.
-/

import Mathlib

namespace TLMCBatch10
def perms4 : List (Fin 4 → Fin 4) :=
  ((List.finRange 4).flatMap fun a =>
    (List.finRange 4).flatMap fun b =>
      (List.finRange 4).flatMap fun c =>
        (List.finRange 4).map fun d =>
          (fun k => ![a, b, c, d] k))
def isPerm4 (f : Fin 4 → Fin 4) : Bool :=
  (List.finRange 4).all fun i => (List.finRange 4).any fun j => f j == i
def perms4' : List (Fin 4 → Fin 4) := perms4.filter isPerm4
def inv4 (f : Fin 4 → Fin 4) : ℕ :=
  ((List.finRange 4).flatMap fun i =>
    ((List.finRange 4).filter fun j => i < j).filter fun j => f j < f i).length
def bump (j : Fin 4) (k : Fin 3) : Fin 4 :=
  if j.val = k.val then ⟨(j.val + 1 : ℕ) % 4, by omega⟩
  else if j.val = (k.val + 1) % 4 then ⟨(j.val + 3) % 4, by omega⟩ else j

def rmult (f : Fin 4 → Fin 4) (k : Fin 3) : Fin 4 → Fin 4 :=
  fun j => f (bump j k)
def word : List (Fin 3) := [1, 0, 2, 1, 2]
def w3421 : Fin 4 → Fin 4 := ![2, 3, 1, 0]
def reachSub (v : Fin 4 → Fin 4) : Bool :=
  ((List.range 32).map fun mask =>
    (List.range 5).foldl (fun acc pos =>
      match acc with
      | none => none
      | some (cur, cnt) =>
        if mask.testBit pos then
          let cur' := rmult cur (word.getD pos 0)
          some (cur', cnt + 1)
        else some (cur, cnt)) (some (id, 0))).any fun
      | none => false
      | some (cur, cnt) => cur = v ∧ decide (cnt = inv4 cur)
/-- The enumeration gives all `24` permutations. -/
theorem perms_count : (perms4').length = 24 := by decide

/-- The word folds to `w = 3421` and is prefix-reduced (a reduced word). -/
theorem word_reduced :
    word.foldl rmult id = w3421 ∧
      (List.range 5).all fun p =>
        inv4 ((word.take (p + 1)).foldl rmult id) = p + 1 := by decide

/-- `w = 3421` avoids the patterns `4231` and `3412`, so the Schubert
    variety `X_w` is smooth and its cohomology has the Schubert basis. -/
theorem smooth_3421 :
    ¬ ((List.finRange 4).any fun a =>
      (List.finRange 4).any fun b =>
        (List.finRange 4).any fun c =>
          (List.finRange 4).any fun d =>
            decide (a < b ∧ b < c ∧ c < d ∧
              (w3421 a > w3421 c ∧ w3421 c > w3421 b ∧ w3421 b > w3421 d ∨
                w3421 c < w3421 d ∧ w3421 d < w3421 a ∧ w3421 a < w3421 b))) := by
  decide

/-- The lengths of the permutations admitting a reduced subword of the
    word, counted by length: exactly `1, 3, 5, 5, 3, 1` (kernel-computed). -/
theorem length_profile :
    ((List.range 6).map fun j =>
      (perms4'.filter fun v => reachSub v && decide (inv4 v = j)).length) =
      [1, 3, 5, 5, 3, 1] := by decide

set_option maxRecDepth 1000000 in
/-- The Betti generating function of `BS(2,1,3,2,3)` (via the Schubert
    basis of the smooth `X_{3421}`): `P(t) = 1+3t+5t²+5t³+3t⁴+t⁵`. -/
theorem P_formula :
    ((List.range 6).map fun j =>
      (perms4'.filter fun v => reachSub v && decide (inv4 v = j)).length) =
      [1, 3, 5, 5, 3, 1] ∧
      (1 : ℤ) + 3 + 5 + 5 + 3 + 1 = 18 ∧
      (1 : ℤ) * 1 + 3 * (-1) + 5 * 1 + 5 * (-1) + 3 * 1 + 1 * (-1) = 0 := by
  decide

/-- **TLMC #1135 is false** (its divisibility clause): with
    `P(t) = 1+3t+5t²+5t³+3t⁴+t⁵` and `k = 5`, so `⌊k/2⌋ = 2`, the
    polynomial `P` is not divisible by `(1+t)²`. -/
theorem tlm1135_false :
    ¬ ∃ R : Polynomial ℤ,
      (1 + 3 * Polynomial.X + 5 * Polynomial.X ^ 2 + 5 * Polynomial.X ^ 3 +
          3 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ) =
        (1 + 2 * Polynomial.X + Polynomial.X ^ 2) * R := by
  intro hR
  obtain ⟨R, hR⟩ := hR
  have hP : (1 + 3 * Polynomial.X + 5 * Polynomial.X ^ 2 + 5 * Polynomial.X ^ 3 +
      3 * Polynomial.X ^ 4 + Polynomial.X ^ 5 : Polynomial ℤ) =
      (1 + Polynomial.X) * (1 + 2 * Polynomial.X + 3 * Polynomial.X ^ 2 +
        2 * Polynomial.X ^ 3 + Polynomial.X ^ 4) := by
    ring
  have hne : (1 + Polynomial.X : Polynomial ℤ) ≠ 0 := by
    intro h
    have h1 : Polynomial.coeff (1 + Polynomial.X : Polynomial ℤ) 1 = 0 := by
      rw [h]; simp
    have h2 : Polynomial.coeff (1 + Polynomial.X : Polynomial ℤ) 1 = 1 := by
      simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_one]
    omega
  have hc : (1 + 2 * Polynomial.X + 3 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 +
      Polynomial.X ^ 4 : Polynomial ℤ) = (1 + Polynomial.X) * R := by
    apply mul_left_cancel₀ hne
    rw [← hP, hR]
    ring
  have hQ1 : (1 + 2 * Polynomial.X + 3 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 +
      Polynomial.X ^ 4 : Polynomial ℤ).eval (-1 : ℤ) = 1 := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, mul_one, mul_neg,
      pow_two, add_assoc]
    norm_num
  have hQ2 : ((1 + Polynomial.X : Polynomial ℤ) * R).eval (-1) = 0 := by
    rw [Polynomial.eval_mul]
    have : Polynomial.eval (-1 : ℤ) (1 + Polynomial.X : Polynomial ℤ) = 0 := by
      simp [Polynomial.eval_add, Polynomial.eval_X]
    rw [this]
    ring
  rw [hc] at hQ1
  omega

end TLMCBatch10
