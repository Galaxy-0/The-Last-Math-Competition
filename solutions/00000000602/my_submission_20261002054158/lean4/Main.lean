/-
TLMC conjecture 00000000602 — machine-checked disproof.

Conjecture (restated): for every alternating knot K, with V_K the Jones
polynomial and ω a primitive fourth root of unity (ω = ± i),
  (1) |V_K(ω)|² divides det(K)², and
  (2) det(K)² / |V_K(ω)|² = |V_K(i)|².

Attack (ω = ± i ⇒ |V_K(ω)|² = |V_K(i)|²): clause (2) collapses to
det(K)² = |V_K(i)|⁴.  Counterexample K = right-handed trefoil 3_1
(alternating): V(t) = t + t³ − t⁴, so V(i) = V(−i) = −1, hence
|V(ω)|² = |V(i)|² = 1 for both ω = ± i, while det(3_1) = 3.  Clause (1)
happens to hold (1 ∣ 9), but clause (2) demands 9 / 1 = 9 = 1 — false.

Everything below is pure, constructive kernel computation on Gaussian
integers: no Mathlib, no `sorry`, and — as audited in Check.lean —
no axioms whatsoever (not even propext / Quot.sound / Class.choice).
-/

namespace Tlmc602

/-- Gaussian integer `a + b·i`, encoded as the pair `(a, b)`. -/
abbrev G : Type := Int × Int

/-- Componentwise addition of Gaussian integers. -/
def gadd : G → G → G
  | (a, b), (c, d) => (a + c, b + d)

/-- Additive inverse of a Gaussian integer. -/
def gneg : G → G
  | (a, b) => (-a, -b)

/-- Subtraction of Gaussian integers. -/
def gsub : G → G → G
  | x, y => gadd x (gneg y)

/-- Multiplication of Gaussian integers:
`(a+bi)(c+di) = (ac−bd) + (ad+bc)i`. -/
def gmul : G → G → G
  | (a, b), (c, d) => (a * c - b * d, a * d + b * c)

/-- Powers by repeated multiplication (natural-number exponent). -/
def gpow : G → Nat → G
  | _, 0 => (1, 0)
  | z, n + 1 => gmul (gpow z n) z

/-- Squared complex norm `|a + bi|² = a² + b²`. -/
def gnormSq : G → Int
  | (a, b) => a * a + b * b

/-- The imaginary unit `i`. -/
def gi : G := (0, 1)

/-- `−i`, the other primitive fourth root of unity. -/
def gni : G := (0, -1)

/-- Jones polynomial of the right-handed trefoil `3_1` in the standard
normalization `V(unknot) = 1`, evaluated at a Gaussian-integer point `t`:
`V(t) = t + t³ − t⁴`. -/
def Vtrefoil (t : G) : G := gsub (gadd t (gpow t 3)) (gpow t 4)

set_option maxHeartbeats 1000000 in
/-- Evaluating the trefoil Jones polynomial at `ω = i` gives `−1`. -/
theorem Vtrefoil_at_i : Vtrefoil gi = (-1, 0) := rfl

set_option maxHeartbeats 1000000 in
/-- Evaluating at `ω = −i` gives `−1` as well (the coefficients are real). -/
theorem Vtrefoil_at_negi : Vtrefoil gni = (-1, 0) := rfl

set_option maxHeartbeats 1000000 in
/-- Hence `|V(ω)|² = 1` for both primitive fourth roots `ω = ± i`. -/
theorem normSq_Vtrefoil_roots :
    gnormSq (Vtrefoil gi) = 1 ∧ gnormSq (Vtrefoil gni) = 1 := ⟨rfl, rfl⟩

/-- The determinant of the trefoil: `det(3_1) = |Δ(−1)| = 3` from the
Alexander polynomial `Δ(t) = t⁻¹ − 1 + t`. -/
def det31 : Int := 3

set_option maxHeartbeats 1000000 in
/-- So `det(3_1)² = 9`. -/
theorem det31_sq : det31 * det31 = 9 := rfl

set_option maxHeartbeats 1000000 in
/-- The conjecture's quotient identity, specialized to `K = 3_1` and
`ω = ± i`, would require `det(3_1)² = |V(ω)|² · |V(i)|²`, i.e. `9 = 1 · 1`.
That is false. -/
theorem conjecture_identity_fails_31 :
    ¬ (det31 * det31 = gnormSq (Vtrefoil gi) * gnormSq (Vtrefoil gni)) := by
  intro h
  rw [show det31 * det31 = 9 from rfl,
      show gnormSq (Vtrefoil gi) = 1 from rfl,
      show gnormSq (Vtrefoil gni) = 1 from rfl] at h
  exact absurd h (by decide)

set_option maxHeartbeats 1000000 in
/-- **Main disproof of TLMC 00000000602.**  Counterexample `K = 3_1`
(an alternating knot): `|V(ω)|² = |V(i)|² = 1` for `ω = ± i`, and the
divisibility clause holds (`1 ∣ 9`), but the required quotient is
`9 / 1 = 9 ≠ 1 = |V(i)|²`. -/
theorem counterexample_00000000602 :
    gnormSq (Vtrefoil gi) = 1
      ∧ gnormSq (Vtrefoil gni) = 1
      ∧ det31 * det31 = 9
      ∧ ¬ (det31 * det31 = gnormSq (Vtrefoil gi) * gnormSq (Vtrefoil gni)) :=
  ⟨rfl, rfl, rfl, conjecture_identity_fails_31⟩

end Tlmc602
