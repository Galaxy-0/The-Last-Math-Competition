/-!
# Conjecture 00000000603: the peak of the Conway polynomial of T(p,q)

The conjecture claims that for every torus knot `T(p,q)` the coefficient
sequence of the Conway polynomial `∇(z)` peaks at position
`⌊(p-1)(q-1)/4⌋`.  We refute this for the torus knots `T(2,n)`.

`T(2,n)` is the closure of the 2-strand braid `σ₁ⁿ`; write `L n` for this
closure (so `L 0` is the 2-component unlink and `L 1` is the unknot).
Changing one crossing of `σ₁^(n+2)` gives `σ₁ⁿ`, and smoothing it gives
`σ₁^(n+1)`, so the Conway skein relation `∇(L₊) - ∇(L₋) = z ∇(L₀)` reads

  `∇(L (n+2)) - ∇(L n) = z ∇(L (n+1))`.

`ConwaySkein c` records exactly these facts about a family `c n` of
polynomials in `z` (as coefficient functions `Nat → Int`).  We prove that they
determine every coefficient (`skein_unique`), that they are consistent
(`ref_skein`), and then compute the coefficients of `∇(T(2,25))` and
`∇(T(2,61))` with kernel-checked `decide`.  No Conway polynomial values are
assumed.
-/

namespace TorusConway

/-- A polynomial in `z` with integer coefficients, as its coefficient function. -/
abbrev Poly := Nat → Int

/-- Multiplication by `z`: shift every coefficient up by one degree. -/
def zmul (p : Poly) : Poly
  | 0 => 0
  | k + 1 => p k

/-- The Conway skein facts for the closures `L n` of the braids `σ₁ⁿ`. -/
structure ConwaySkein (c : Nat → Poly) : Prop where
  /-- `L 0` is the 2-component unlink: `∇ = 0`. -/
  unlink : ∀ k, c 0 k = 0
  /-- `L 1` is the unknot: `∇ = 1`. -/
  unknot : ∀ k, c 1 k = if k = 0 then 1 else 0
  /-- Skein relation at one crossing of `σ₁^(n+2)`. -/
  skein : ∀ n k, c (n + 2) k - c n k = zmul (c (n + 1)) k

/-! ## Reference computation with coefficient lists -/

/-- Pointwise sum of coefficient lists (padding with zeros). -/
def addL : List Int → List Int → List Int
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

/-- Coefficient `k` of a coefficient list. -/
def coeff (l : List Int) (k : Nat) : Int := l.getD k 0

theorem coeff_nil (k : Nat) : coeff [] k = 0 := by
  simp [coeff]

theorem coeff_cons_zero (a : Int) (l : List Int) : coeff (a :: l) 0 = a := by
  simp [coeff]

theorem coeff_cons_succ (a : Int) (l : List Int) (k : Nat) :
    coeff (a :: l) (k + 1) = coeff l k := by
  simp [coeff]

theorem coeff_addL (l m : List Int) (k : Nat) :
    coeff (addL l m) k = coeff l k + coeff m k := by
  induction l generalizing m k with
  | nil => simp [addL, coeff_nil]
  | cons a l ih =>
    cases m with
    | nil => simp [addL, coeff_nil]
    | cons b m =>
      cases k with
      | zero => simp [addL, coeff_cons_zero]
      | succ k => simp [addL, coeff_cons_succ, ih]

theorem coeff_zero_cons (l : List Int) (k : Nat) :
    coeff (0 :: l) k = zmul (coeff l) k := by
  cases k with
  | zero => simp [coeff_cons_zero, zmul]
  | succ k => simp [coeff_cons_succ, zmul]

/-- One skein step: `(∇ Lₙ, ∇ Lₙ₊₁) ↦ (∇ Lₙ₊₁, ∇ Lₙ + z ∇ Lₙ₊₁)`. -/
def step (p : List Int × List Int) : List Int × List Int :=
  (p.2, addL p.1 (0 :: p.2))

/-- `(∇ Lₙ, ∇ Lₙ₊₁)` as coefficient lists. -/
def pair : Nat → List Int × List Int
  | 0 => ([], [1])
  | n + 1 => step (pair n)

/-- The reference coefficient list of `∇(L n)`. -/
def ref (n : Nat) : List Int := (pair n).1

theorem ref_succ (n : Nat) : ref (n + 1) = (pair n).2 := rfl

theorem ref_add_two (n : Nat) :
    ref (n + 2) = addL (ref n) (0 :: ref (n + 1)) := rfl

/-- The skein facts determine every coefficient of every `∇(L n)`. -/
theorem skein_unique {c : Nat → Poly} (h : ConwaySkein c) :
    ∀ n k, c n k = coeff (ref n) k := by
  have two : ∀ n, (∀ k, c n k = coeff (ref n) k) ∧
      (∀ k, c (n + 1) k = coeff (ref (n + 1)) k) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun k => ?_, fun k => ?_⟩
      · rw [h.unlink k]; simp [ref, pair, coeff_nil]
      · rw [h.unknot k]
        cases k with
        | zero => rfl
        | succ k => simp [ref, pair, step, coeff_cons_succ, coeff_nil]
    | succ n ih =>
      refine ⟨ih.2, fun k => ?_⟩
      have hs := h.skein n k
      have hc : c (n + 2) k = c n k + zmul (c (n + 1)) k := by omega
      rw [hc, ref_add_two, coeff_addL, coeff_zero_cons, ih.1 k]
      have hz : zmul (c (n + 1)) k = zmul (coeff (ref (n + 1))) k := by
        cases k with
        | zero => rfl
        | succ k => exact ih.2 k
      rw [hz]
  exact fun n => (two n).1

/-- The reference family satisfies the skein facts, so they are consistent. -/
theorem ref_skein : ConwaySkein (fun n => coeff (ref n)) where
  unlink := fun k => by simp [ref, pair, coeff_nil]
  unknot := fun k => by
    cases k with
    | zero => rfl
    | succ k => simp [ref, pair, step, coeff_cons_succ, coeff_nil]
  skein := fun n k => by
    show coeff (ref (n + 2)) k - coeff (ref n) k = zmul (coeff (ref (n + 1))) k
    rw [ref_add_two, coeff_addL, coeff_zero_cons]
    omega

/-! ## The coefficients of `∇(T(2,25))` and `∇(T(2,61))` -/

/-- `∇(T(2,25))`, coefficients of `z⁰, z¹, …, z²⁴`. -/
theorem ref_25 : ref 25 =
    [1, 0, 78, 0, 1001, 0, 5005, 0, 12870, 0, 19448, 0, 18564, 0, 11628, 0,
     4845, 0, 1330, 0, 231, 0, 23, 0, 1] := by decide

theorem ref_61_values :
    coeff (ref 61) 15 = 0 ∧
    coeff (ref 61) 26 = 421171648758 ∧
    coeff (ref 61) 28 = 416714805914 ∧
    coeff (ref 61) 30 = 344867425584 := by decide

/-- In `∇(T(2,61))` the coefficient of `z²⁶` is strictly larger than every
other coefficient. -/
theorem ref_61_peak : ∀ k, k < 70 → k ≠ 26 → coeff (ref 61) k < coeff (ref 61) 26 := by
  decide

theorem ref_61_length : (ref 61).length = 61 := by decide

/-- The coefficient of `z²⁶` in `∇(T(2,61))` is strictly larger than every
other coefficient (beyond degree 60 all coefficients vanish). -/
theorem ref_61_unique_peak : ∀ k, k ≠ 26 → coeff (ref 61) k < coeff (ref 61) 26 := by
  intro k hk
  by_cases hlt : k < 70
  · exact ref_61_peak k hlt hk
  · have hz : coeff (ref 61) k = 0 := by
      have hn : (ref 61)[k]? = none := by
        rw [List.getElem?_eq_none_iff, ref_61_length]; omega
      simp [coeff, hn]
    rw [hz]; decide

/-! ## Cross-check with the Alexander polynomial

Independently of the skein recursion, the Alexander polynomial of the torus knot
`T(2,n)` (`n` odd) is `Δ(t) = (t^{2n}-1)(t-1)/((t^2-1)(t^n-1)) = (t^n+1)/(t+1)
= 1 - t + t² - ⋯ + t^{n-1}` (up to units), and Conway's normalization is
`∇(s - s⁻¹) = s^{-(n-1)} Δ(s²)`.  Clearing denominators, this says
`Σᵢ aᵢ (s²-1)ⁱ s^{n-1-i} = Σⱼ (-1)ʲ s^{2j}`, where `aᵢ = [zⁱ] ∇`.
We check this polynomial identity in `s` for `n = 25` and `n = 61`. -/

/-- Product of coefficient lists. -/
def mulL : List Int → List Int → List Int
  | [], _ => []
  | a :: l, m => addL (m.map (a * ·)) (0 :: mulL l m)

/-- `s^k` as a coefficient list. -/
def monoL (k : Nat) : List Int := List.replicate k 0 ++ [1]

/-- `Σᵢ aᵢ (s²-1)ⁱ s^{d-i}` for a coefficient list `a` (with `d = n - 1`). -/
def conwayToS (a : List Int) (d : Nat) : List Int :=
  (go a 0 [1]).reverse.dropWhile (· == 0) |>.reverse
where
  go : List Int → Nat → List Int → List Int
    | [], _, _ => []
    | x :: l, i, pw =>
      addL ((mulL pw (monoL (d - i))).map (x * ·)) (go l (i + 1) (mulL pw [-1, 0, 1]))

/-- `Σ_{j<n} (-1)ʲ s^{2j}`, the Alexander polynomial of `T(2,n)` in `s = t^{1/2}`. -/
def alexanderS (n : Nat) : List Int :=
  (List.range (2 * n - 1)).map fun k =>
    if k % 2 = 1 then 0 else if (k / 2) % 2 = 0 then 1 else -1

theorem alexander_25 : conwayToS (ref 25) 24 = alexanderS 25 := by decide
/-- Checked by kernel reduction (`decide +kernel`). -/
theorem alexander_61 : conwayToS (ref 61) 60 = alexanderS 61 := by decide +kernel

/-! ## The conjecture's peak clause and its refutation -/

/-- Position `⌊(p-1)(q-1)/4⌋` for `T(p,q)`. -/
def predicted (p q : Nat) : Nat := (p - 1) * (q - 1) / 4

/-- The peak clause for the knots `T(2,n)` (n odd, n ≥ 3), read with a
convention `pos` turning a sequence position into a power of `z`:
the coefficient at the predicted position is a maximum (ties allowed). -/
def PeakClaim (c : Nat → Poly) (pos : Nat → Nat) : Prop :=
  ∀ n, n % 2 = 1 → 3 ≤ n → ∀ k, c n k ≤ c n (pos (predicted 2 n))

/-- Reading 1: the position is the power of `z`. -/
def posExp (i : Nat) : Nat := i
/-- Reading 2: the sequence is `[z⁰], [z²], [z⁴], …`, indexed from 0. -/
def posEven0 (i : Nat) : Nat := 2 * i
/-- Reading 3: the sequence is `[z⁰], [z²], [z⁴], …`, indexed from 1. -/
def posEven1 (i : Nat) : Nat := 2 * (i - 1)

theorem predicted_25 : predicted 2 25 = 6 := by decide
theorem predicted_61 : predicted 2 61 = 15 := by decide

/-- `T(2,25)`: the predicted position 6 is not a peak under readings 1 and 2. -/
theorem T_2_25_counterexample {c : Nat → Poly} (h : ConwaySkein c) :
    c 25 (posExp (predicted 2 25)) < c 25 10 ∧
    c 25 (posEven0 (predicted 2 25)) < c 25 10 := by
  simp only [skein_unique h, ref_25]
  decide

/-- `T(2,61)`: the predicted position 15 is not a peak under any reading. -/
theorem T_2_61_counterexample {c : Nat → Poly} (h : ConwaySkein c) :
    c 61 (posExp (predicted 2 61)) < c 61 26 ∧
    c 61 (posEven0 (predicted 2 61)) < c 61 26 ∧
    c 61 (posEven1 (predicted 2 61)) < c 61 26 := by
  simp only [skein_unique h]
  decide

theorem not_peakClaim (pos : Nat → Nat) {c : Nat → Poly}
    (hlt : c 61 (pos (predicted 2 61)) < c 61 26) : ¬ PeakClaim c pos := by
  intro hp
  have := hp 61 (by decide) (by decide) 26
  omega

/-- The peak clause of conjecture 00000000603 fails for the Conway polynomial
(any family satisfying the skein facts), under each of the three readings. -/
theorem conjecture_00000000603_false {c : Nat → Poly} (h : ConwaySkein c) :
    ¬ PeakClaim c posExp ∧ ¬ PeakClaim c posEven0 ∧ ¬ PeakClaim c posEven1 :=
  let t := T_2_61_counterexample h
  ⟨not_peakClaim _ t.1, not_peakClaim _ t.2.1, not_peakClaim _ t.2.2⟩

/-- The hypotheses are satisfiable, so the refutation is not vacuous. -/
theorem conjecture_00000000603_false_ref :
    ¬ PeakClaim (fun n => coeff (ref n)) posExp ∧
    ¬ PeakClaim (fun n => coeff (ref n)) posEven0 ∧
    ¬ PeakClaim (fun n => coeff (ref n)) posEven1 :=
  conjecture_00000000603_false ref_skein

end TorusConway

#print axioms TorusConway.skein_unique
#print axioms TorusConway.ref_skein
#print axioms TorusConway.ref_25
#print axioms TorusConway.ref_61_peak
#print axioms TorusConway.ref_61_unique_peak
#print axioms TorusConway.alexander_25
#print axioms TorusConway.alexander_61
#print axioms TorusConway.T_2_25_counterexample
#print axioms TorusConway.T_2_61_counterexample
#print axioms TorusConway.conjecture_00000000603_false
#print axioms TorusConway.conjecture_00000000603_false_ref
