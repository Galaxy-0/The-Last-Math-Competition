/-!
# Disproof of TLMC conjecture 00000001236

Counterexample graph: the path `1-2-3` on three non-sink vertices with the
sink attached to vertex `3`.

* Reduced Laplacian `L = [[1,-1,0],[-1,2,-1],[0,-1,2]]`, `det L = 1`.
* `L⁻¹ = [[3,2,1],[2,2,1],[1,1,1]]` is integral, so *every* rounding
  convention yields the same `M`; we prove `L · M = I` entrywise.
* "Row-minimal sum" of `M` is `3` under **both** readings: sum of the row
  minima (`1+1+1`) and minimum of the row sums (`min(6,5,3)`).
* Max-stable configuration `(0,1,1)`, weight `2`; by Dhar's burning test it is
  recurrent, and since `det L = 1` it is the *only* recurrent configuration,
  so the minimal recurrent weight is `2`.
* The conjecture predicts `2 - 3 = -1 ≠ 2` under either reading. Disproved.

Core Lean 4 only; no Mathlib, no `sorry`, no custom axioms. All named
theorems are axiom-free (`#print axioms` audit in `Check.lean`).
-/

/-- A configuration on the three non-sink vertices (chip counts). -/
structure Cfg where
  c1 : Nat
  c2 : Nat
  c3 : Nat
deriving DecidableEq, Repr

/-- Degrees of the non-sink vertices, sink-adjacencies included:
vertex 0 adjoins 1 only; vertex 1 adjoins 0 and 2; vertex 2 adjoins 1 and
the sink. -/
def deg : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | _ => 0

/-- Stability: `c.v < deg v` componentwise, i.e. `c ≤ (0,1,1)`. -/
def Stable (c : Cfg) : Prop := c.c1 ≤ 0 ∧ c.c2 ≤ 1 ∧ c.c3 ≤ 1

/-- Total weight. -/
def Weight (c : Cfg) : Nat := c.c1 + c.c2 + c.c3

/-! ## The reduced Laplacian `L` and its exact integral inverse `M` -/

/-- The 3×3 reduced Laplacian of path 1-2-3 with the sink at vertex 3. -/
def L : Nat → Nat → Int
  | 0, 0 => 1  | 0, 1 => -1 | 0, 2 => 0
  | 1, 0 => -1 | 1, 1 => 2  | 1, 2 => -1
  | 2, 0 => 0  | 2, 1 => -1 | 2, 2 => 2
  | _, _ => 0

/-- `M`: the exact integral inverse of `L`, so the conjecture's "rounding of
the inverse of the reduced Laplacian" equals `M` under every convention. -/
def M : Nat → Nat → Int
  | 0, 0 => 3  | 0, 1 => 2  | 0, 2 => 1
  | 1, 0 => 2  | 1, 1 => 2  | 1, 2 => 1
  | 2, 0 => 1  | 2, 1 => 1  | 2, 2 => 1
  | _, _ => 0

/-- A triple successor never lands below 3. -/
theorem not_succ3_lt_three (j : Nat) (h : j + 1 + 1 + 1 < 3) : False := by
  have h1 : Nat.succ (j + 1 + 1) < Nat.succ 2 := h
  exact Nat.not_lt_zero j
    (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h1)))

/-- Two stacked successors never fit under a budget of 1. -/
theorem not_succ_succ_le_one (e : Nat) (h : e + 1 + 1 ≤ 1) : False := by
  have h1 : Nat.succ (e + 1) ≤ Nat.succ 0 := h
  exact Nat.not_succ_le_zero e (Nat.le_of_succ_le_succ h1)

/-- Entrywise identity `L · M = I` on the 3×3 block. -/
theorem LmulM_eq_I : ∀ (i j : Nat), i < 3 → j < 3 →
    (L i 0 * M 0 j + L i 1 * M 1 j + L i 2 * M 2 j)
      = if i = j then 1 else 0 := by
  intro i j hi hj
  cases i with
  | zero =>
    cases j with
    | zero => decide
    | succ j =>
      cases j with
      | zero => decide
      | succ j =>
        cases j with
        | zero => decide
        | succ j => exact absurd hj (not_succ3_lt_three j)
  | succ i =>
    cases i with
    | zero =>
      cases j with
      | zero => decide
      | succ j =>
        cases j with
        | zero => decide
        | succ j =>
          cases j with
          | zero => decide
          | succ j => exact absurd hj (not_succ3_lt_three j)
    | succ i =>
      cases i with
      | zero =>
        cases j with
        | zero => decide
        | succ j =>
          cases j with
          | zero => decide
          | succ j =>
            cases j with
            | zero => decide
            | succ j => exact absurd hj (not_succ3_lt_three j)
      | succ i => exact absurd hi (not_succ3_lt_three i)

/-- The 3×3 determinant by cofactor expansion. -/
def det3 (m : Nat → Nat → Int) : Int :=
  m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 2 1)
    - m 0 1 * (m 1 0 * m 2 2 - m 1 2 * m 2 0)
    + m 0 2 * (m 1 0 * m 2 1 - m 1 1 * m 2 0)

/-- `det L = 1`: the sandpile group is trivial, so exactly one recurrent
configuration exists. -/
theorem detL_eq_one : det3 L = 1 := by decide

/-! ## The row-minimal sum of `M`, under both readings -/

/-- Minimum entry of row `i` of `M`. -/
def rowMin (i : Nat) : Int :=
  if M i 0 ≤ M i 1 then
    (if M i 0 ≤ M i 2 then M i 0 else M i 2)
  else
    (if M i 1 ≤ M i 2 then M i 1 else M i 2)

/-- Sum of row `i` of `M`. -/
def rowSum (i : Nat) : Int := M i 0 + M i 1 + M i 2

/-- Reading A: the sum of the row minima. -/
def sumRowMinima : Int := rowMin 0 + rowMin 1 + rowMin 2

/-- Reading B: the minimum of the row sums. -/
def minRowSum : Int :=
  if rowSum 0 ≤ rowSum 1 then
    (if rowSum 0 ≤ rowSum 2 then rowSum 0 else rowSum 2)
  else
    (if rowSum 1 ≤ rowSum 2 then rowSum 1 else rowSum 2)

theorem sumRowMinima_eq_three : sumRowMinima = 3 := by decide

theorem minRowSum_eq_three : minRowSum = 3 := by decide

/-! ## Dhar's burning test on this graph

The sink burns from the start; at each step a vertex `v` ignites once
`deg v ≤ c v + (number of burning neighbours of v)`, the sink-adjacency of
vertex 2 counting from the beginning. Ignition is monotone in the burned set,
so the parallel closure computed by four rounds equals the sequential one. -/

/-- One parallel ignition round. -/
def burnStep (c : Cfg) (b : Bool × Bool × Bool) : Bool × Bool × Bool :=
  let i1 := decide (deg 0 ≤ c.c1 + (if b.2.1 then 1 else 0))
  let i2 := decide (deg 1 ≤ c.c2 + (if b.1 then 1 else 0) + (if b.2.2 then 1 else 0))
  let i3 := decide (deg 2 ≤ c.c3 + (if b.2.1 then 1 else 0) + 1)
  (b.1 || i1, b.2.1 || i2, b.2.2 || i3)

/-- Four rounds suffice for three vertices. -/
def recurrentAux (c : Cfg) : Bool :=
  decide (burnStep c (burnStep c (burnStep c (burnStep c (false, false, false))))
    = (true, true, true))

/-- Recurrence, characterised by Dhar's burning test (a classical
equivalent definition of recurrent configurations). -/
@[reducible]
def Recurrent (c : Cfg) : Prop := recurrentAux c = true

/-! ## Max-stable configuration and its weight -/

/-- `(deg v - 1)` componentwise. -/
def maxStable : Cfg := ⟨0, 1, 1⟩

theorem maxStable_weight : Weight maxStable = 2 := by decide

theorem maxStable_recurrent : Recurrent maxStable := by decide

theorem maxStable_stable : Stable maxStable := ⟨by decide, by decide, by decide⟩

/-! ## Uniqueness of the recurrent configuration -/

/-- Every stable configuration is one of the four listed. -/
theorem stable_cases (c : Cfg) (h : Stable c) :
    c = ⟨0, 0, 0⟩ ∨ c = ⟨0, 0, 1⟩ ∨ c = ⟨0, 1, 0⟩ ∨ c = ⟨0, 1, 1⟩ := by
  cases c with
  | mk a b d =>
    have h1 : a ≤ 0 := h.1
    have h2 : b ≤ 1 := h.2.1
    have h3 : d ≤ 1 := h.2.2
    cases a with
    | succ e => exact absurd h1 (Nat.not_succ_le_zero e)
    | zero =>
      cases b with
      | succ e =>
        cases e with
        | succ e => exact absurd h2 (not_succ_succ_le_one e)
        | zero =>
          cases d with
          | succ e =>
            cases e with
            | succ e => exact absurd h3 (not_succ_succ_le_one e)
            | zero => exact Or.inr (Or.inr (Or.inr rfl))
          | zero => exact Or.inr (Or.inr (Or.inl rfl))
      | zero =>
        cases d with
        | succ e =>
          cases e with
          | succ e => exact absurd h3 (not_succ_succ_le_one e)
          | zero => exact Or.inr (Or.inl rfl)
        | zero => exact Or.inl rfl

/-- The three non-maximal stable configurations are not recurrent. -/
theorem not_recurrent_000 : ¬ Recurrent ⟨0, 0, 0⟩ := by decide
theorem not_recurrent_001 : ¬ Recurrent ⟨0, 0, 1⟩ := by decide
theorem not_recurrent_010 : ¬ Recurrent ⟨0, 1, 0⟩ := by decide

/-- The unique recurrent configuration on this graph (hence unique up to
isomorphism) is the max-stable one. -/
theorem unique_recurrent (c : Cfg) (hs : Stable c) (hr : Recurrent c) :
    c = maxStable := by
  cases stable_cases c hs with
  | inl h => rw [h] at hr; exact absurd hr not_recurrent_000
  | inr h =>
    cases h with
    | inl h => rw [h] at hr; exact absurd hr not_recurrent_001
    | inr h =>
      cases h with
      | inl h => rw [h] at hr; exact absurd hr not_recurrent_010
      | inr h => exact h

/-- The minimum recurrent weight: every recurrent configuration weighs at
least `2`, and the bound is attained. -/
theorem min_recurrent_weight (c : Cfg) (hs : Stable c) (hr : Recurrent c) :
    2 ≤ Weight c := by
  rw [unique_recurrent c hs hr]
  decide

/-! ## The refutation -/

/-- Weights are nonnegative, so the conjecture's negative prediction is
absurd on its face. -/
theorem weight_nonneg (c : Cfg) : 0 ≤ Weight c := Nat.zero_le _

theorem maxStable_weight_int : ((Weight maxStable : Nat) : Int) = 2 := by decide

/-- The conjectured value, reading A of "row-minimal sum". -/
theorem predictionA : ((Weight maxStable : Nat) : Int) - sumRowMinima = -1 := by
  decide

/-- The conjectured value, reading B of "row-minimal sum". -/
theorem predictionB : ((Weight maxStable : Nat) : Int) - minRowSum = -1 := by
  decide

/-- Main disproof: the conjectured formula yields `-1` under both readings of
"row-minimal sum", while the true minimal recurrent weight is `2`. -/
theorem conjecture_1236_false :
    ((Weight maxStable : Nat) : Int) - sumRowMinima = -1
      ∧ ((Weight maxStable : Nat) : Int) - minRowSum = -1
      ∧ (∀ c : Cfg, Stable c → Recurrent c → 2 ≤ Weight c)
      ∧ Stable maxStable ∧ Recurrent maxStable ∧ Weight maxStable = 2 := by
  refine ⟨predictionA, predictionB, min_recurrent_weight, maxStable_stable,
    maxStable_recurrent, maxStable_weight⟩
