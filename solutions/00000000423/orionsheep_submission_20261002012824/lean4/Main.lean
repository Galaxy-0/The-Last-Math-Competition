/-!
# Disproof of conjecture 00000000423 (promotion orbit divisibility)

Conjecture 00000000423 claims that promotion (Schutzenberger cyclic sliding)
orbit lengths on standard Young tableaux (SYT) divide the tableau size.

Attack: shape `(2,1)` has `n = 3` cells and exactly two SYT,

```
A = | 1 2 |     B = | 1 3 |
    | 3 |         | 2 |
```

encoded here as the triples `(a, b, c)` = entries at cells `(1,1), (1,2),
(2,1)`, i.e. `A = (1,2,3)` and `B = (1,3,2)`. Schutzenberger promotion
(delete `1`, jeu-de-taquin slide, subtract `1`, place `3`) maps `A ↦ B` and
`B ↦ A`, so the whole tableau set is one orbit of length `2`, and `2 ∤ 3`
(since `(3 : Nat) % 2 = 1`).

Everything is closed computation over the finite candidate set of 27 triples;
all theorems are proved by `rfl` / `decide` / term mode and depend on no
axioms (audited in `Check.lean`).
-/

set_option maxHeartbeats 1000000

/-- Standard-tableau predicate for shape `(2,1)`: entries are distinct values
from `{1,2,3}` (so they are exactly `{1,2,3}`), with `a < b` (row) and
`a < c` (column). -/
def SYT21 (t : Nat × Nat × Nat) : Bool :=
  1 <= t.1 && t.1 < t.2.1 && t.1 < t.2.2 && t.2.1 <= 3 && t.2.2 <= 3 &&
    t.2.1 != t.2.2

/-- All 27 fillings of shape `(2,1)` with values from `{1,2,3}`. -/
def candidates : List (Nat × Nat × Nat) :=
  (List.range 3).flatMap fun x =>
    (List.range 3).flatMap fun y =>
      (List.range 3).map fun z => (x + 1, y + 1, z + 1)

/-- The standard Young tableaux of shape `(2,1)`, by filtering the 27
candidate fillings. -/
def syt21s : List (Nat × Nat × Nat) :=
  candidates.filter SYT21

/-- Schutzenberger promotion on shape `(2,1)` by jeu-de-taquin: delete the
entry `1` at cell `(1,1)`; the smaller of the right neighbour `b` and the
lower neighbour `c` slides in, and the vacated cell is a corner (the slide
stops immediately); subtract `1` from every entry; place `3` in the vacated
corner. (The entry `a = 1` at cell `(1,1)` is deleted, so the result does not
depend on it.) -/
def promT (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  if t.2.1 < t.2.2 then (t.2.1 - 1, 3, t.2.2 - 1)
  else (t.2.2 - 1, t.2.1 - 1, 3)

/-- The SYT of shape `(2,1)` are exactly `A = (1,2,3)` and `B = (1,3,2)`:
there are exactly two of them. -/
theorem syt21s_eq : syt21s = [(1, 2, 3), (1, 3, 2)] := by rfl

/-- Promotion sends `A = (1,2,3)` to `B = (1,3,2)`. -/
theorem prom_A : promT (1, 2, 3) = (1, 3, 2) := by rfl

/-- Promotion sends `B = (1,3,2)` to `A = (1,2,3)`. -/
theorem prom_B : promT (1, 3, 2) = (1, 2, 3) := by rfl

/-- Promotion is an involution on the tableau set. -/
theorem prom_involutive :
    promT (promT (1, 2, 3)) = (1, 2, 3) ∧ promT (promT (1, 3, 2)) = (1, 3, 2) :=
  ⟨prom_B, prom_A⟩

/-- The two tableaux are distinct, so promotion is not the identity on the
orbit and the single orbit `{A, B}` genuinely has length `2`. -/
theorem A_ne_B : (1, 2, 3) ≠ (1, 3, 2) := by decide

/-- The tableau size `n = 3` leaves remainder `1` when divided by the orbit
length `2`: i.e. `2 ∤ 3`. -/
theorem three_mod_two : (3 : Nat) % 2 = 1 := by rfl

/-- Divisibility by the orbit length `2`, as a Bool computation (avoids the
axiom-using `Decidable (a ∣ b)` instance). -/
def dividesTwo (n : Nat) : Bool := n % 2 == 0

/-- Divisibility form of the failure: the orbit length `2` does not divide
the tableau size `3` (the remainder `3 % 2` is nonzero). -/
theorem two_not_dvd_three : dividesTwo 3 = false := by rfl

/-- **Main disproof of conjecture 00000000423.** The tableau set of shape
`(2,1)` is exactly `{A, B}`, promotion is the transposition `A ↦ B ↦ A`, so
its single orbit has length `2`; the tableau size is `n = 3`, and `2 ∤ 3`
(`3 % 2 = 1`). Hence promotion orbit lengths need not divide the tableau
size. -/
theorem conjecture_00000000423_false :
    syt21s = [(1, 2, 3), (1, 3, 2)]
      ∧ promT (1, 2, 3) = (1, 3, 2)
      ∧ promT (1, 3, 2) = (1, 2, 3)
      ∧ promT (promT (1, 2, 3)) = (1, 2, 3)
      ∧ (1, 2, 3) ≠ (1, 3, 2)
      ∧ (3 : Nat) % 2 = 1
      ∧ dividesTwo 3 = false := by
  exact ⟨syt21s_eq, prom_A, prom_B, prom_involutive.1, A_ne_B, three_mod_two,
    two_not_dvd_three⟩
