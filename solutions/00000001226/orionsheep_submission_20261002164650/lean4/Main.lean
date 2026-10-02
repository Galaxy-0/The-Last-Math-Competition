/-!
# Disproof of TLMC conjecture 00000001226

Conjecture (verbatim): "The expected firefighter survival on 3-regular
graphs is 0.65n for an explicit constant (random firefighting expectation)."

The smallest 3-regular graph is `K4` (n = 4).  Under the standard firefighter
process (fire breaks out at one vertex; each turn `f` vertices are protected,
then fire spreads to every unprotected neighbour of a burning vertex; it ends
when no unprotected vertex neighbours the fire) the whole process on `K4` is
*forced*: every strategy - random or not - produces the same outcome.

* `f = 1`: exactly 1 vertex survives  (`0.25n`)
* `f = 2`: exactly 2 vertices survive (`0.5n`)
* `f = 3`: exactly 3 vertices survive (`0.75n`)

The conjecture requires the expected survival to be `0.65 * 4 = 13/5`.
For a forced (constant) outcome the expectation equals the outcome itself,
so `5 * E[saved]` would have to be `13` - impossible for every natural
number, since `5 * s ≠ 13` for all `s : ℕ` (13 is not a multiple of 5).
Hence the claim is false on the very first member of the class, under every
reading of the undefined randomness and every number of firefighters.

Everything below is pure `Nat`/`List` computation proved by `decide`:
no `sorry`, no axioms.
-/

/-- The four vertices of `K4`, labelled `0,1,2,3`.  Fire starts at `0`. -/
def U : List Nat := [0, 1, 2, 3]

/-- Unprotected, unburned vertices (the pool a defender may act on and the
only vertices the fire could still reach).  `K4` is complete, so after any
spread every unprotected unburned vertex is adjacent to the fire. -/
def pool (b d : List Nat) : List Nat :=
  U.filter (fun v => !(b.contains v) && !(d.contains v))

/-! ### f = 1: one firefighter per turn -/

/-- Turn 1: defend `c`, then fire at `0` ignites every other vertex. -/
def burnAfter1 (c : Nat) : List Nat :=
  0 :: U.filter (fun v => v != 0 && v != c)

/-- Full f = 1 play of `K4` with first (and only) move `c`: after turn 1 the
unburned-unprotected set is empty, so the fire is out.  Saved = 4 - |burning|. -/
def savedF1 (c : Nat) : Nat :=
  let b1 := burnAfter1 c
  if pool b1 [c] = [] then U.length - b1.length else 0

theorem savedF1_1 : savedF1 1 = 1 := by decide
theorem savedF1_2 : savedF1 2 = 1 := by decide
theorem savedF1_3 : savedF1 3 = 1 := by decide

/-- Every f = 1 strategy (the whole strategy space is the choice of the
first defended vertex among {1,2,3}) saves exactly one vertex. -/
theorem every_strategy_f1 (c : Nat) (h : c = 1 ∨ c = 2 ∨ c = 3) :
    savedF1 c = 1 := by
  rcases h with h | h | h
  · rw [h]; exact savedF1_1
  · rw [h]; exact savedF1_2
  · rw [h]; exact savedF1_3

/-- Expectation over the three equally likely moves (uniform random
firefighting): `(1 + 1 + 1) / 3 = 1`. -/
theorem expectation_uniform_f1 :
    (savedF1 1 + savedF1 2 + savedF1 3) / 3 = 1 := by decide

/-- Distribution-free form: under ANY probability distribution on the three
moves (weights `w1 w2 w3`), the outcome is the constant `1`, so the weighted
outcome sum equals the weight sum, i.e. `E[saved] = 1` in every reading. -/
theorem expectation_any_f1 (w1 w2 w3 : Nat) :
    w1 * savedF1 1 + w2 * savedF1 2 + w3 * savedF1 3
      = w1 + w2 + w3 := by
  have h1 : savedF1 1 = 1 := savedF1_1
  have h2 : savedF1 2 = 1 := savedF1_2
  have h3 : savedF1 3 = 1 := savedF1_3
  rw [h1, h2, h3, Nat.mul_one, Nat.mul_one, Nat.mul_one]

/-! ### f = 2: two firefighters per turn -/

/-- f = 2 play with first-turn defence `{c1, c2}`: the third neighbour burns;
turn 2 defends it; the fire is out.  Saved = 4 - 2 = 2. -/
def savedF2 (c1 c2 : Nat) : Nat :=
  let b1 := 0 :: U.filter (fun v => v != 0 && v != c1 && v != c2)
  let d1 := [c1, c2]
  let d2 := d1 ++ pool b1 d1
  if pool b1 d2 = [] then U.length - b1.length else 99

theorem savedF2_12 : savedF2 1 2 = 2 := by decide
theorem savedF2_13 : savedF2 1 3 = 2 := by decide
theorem savedF2_23 : savedF2 2 3 = 2 := by decide

/-! ### f = 3: three firefighters per turn -/

/-- f = 3 play: defend all of {1,2,3}; the fire cannot spread. -/
def savedF3 : Nat :=
  let b1 := [0]
  if pool b1 [1, 2, 3] = [] then U.length - b1.length else 99

theorem savedF3_val : savedF3 = 3 := by decide

/-! ### The arithmetic kill

`0.65 * 4 = 13/5`.  The forced outcome `s` gives `5 * E[saved] = 5 * s`,
and `5 * s = 13` has no natural-number solution: `13` is not a multiple
of 5.  This kills all three readings `f ∈ {1,2,3}` at once. -/

theorem no_solution : ∀ s : Nat, 5 * s ≠ 13 := by
  intro s
  match s with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | s + 3 =>
    -- 5 * (s + 3) is definitionally 5 * s + 15 ≥ 15 > 13
    have h15 : (15 : Nat) ≤ 5 * (s + 3) := by
      show (15 : Nat) ≤ 5 * s + 15
      exact Nat.le_add_left 15 (5 * s)
    have h213 : ¬ ((15 : Nat) ≤ 13) := by decide
    intro hc
    exact absurd (Nat.le_trans h15 (Nat.le_of_eq hc)) h213

/-- The expected survival under uniform random firefighting with `f = 1`
cannot be `0.65 * 4`: that would force `5 * 1 = 13`. -/
theorem claim_false_f1 :
    (5 : Nat) * ((savedF1 1 + savedF1 2 + savedF1 3) / 3) ≠ 13 := by
  decide

theorem claim_false_f2 :
    (5 : Nat) * ((savedF2 1 2 + savedF2 1 3 + savedF2 2 3) / 3) ≠ 13 := by
  decide

theorem claim_false_f3 : (5 : Nat) * savedF3 ≠ 13 := by
  decide

/-- Main statement: on the 3-regular graph `K4` (n = 4) the firefighter
process is forced for every number of firefighters `f ∈ {1,2,3}` and every
strategy; the expected survival is `1`, `2` resp. `3` - never `0.65n = 13/5`. -/
theorem conjecture_1226_false :
    (∀ c : Nat, c = 1 ∨ c = 2 ∨ c = 3 → savedF1 c = 1)
      ∧ savedF2 1 2 = 2 ∧ savedF2 1 3 = 2 ∧ savedF2 2 3 = 2
      ∧ savedF3 = 3
      ∧ ((savedF1 1 + savedF1 2 + savedF1 3) / 3 = 1)
      ∧ ((5 : Nat) * ((savedF1 1 + savedF1 2 + savedF1 3) / 3) ≠ 13)
      ∧ ((5 : Nat) * ((savedF2 1 2 + savedF2 1 3 + savedF2 2 3) / 3) ≠ 13)
      ∧ ((5 : Nat) * savedF3 ≠ 13)
      ∧ (∀ s : Nat, 5 * s ≠ 13) := by
  refine ⟨every_strategy_f1, savedF2_12, savedF2_13, savedF2_23, savedF3_val,
    expectation_uniform_f1, claim_false_f1, claim_false_f2, claim_false_f3,
    no_solution⟩
