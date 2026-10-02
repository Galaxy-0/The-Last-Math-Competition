# Disproof of TLMC conjecture 00000001211

**Conjecture (verbatim).** *Definition: A poset game (delete an element and everything above
it). Conjecture: The P-positions of the poset game on Young's lattice have an explicit
characterization via perfect square partitions (the Young poset game).*

**Verdict: DISPROVED.** Under both natural readings of "poset game on Young's lattice" the
perfect-square characterization fails; a single machine-checked Lean development (zero axioms,
no `sorry`) and an independent Python enumeration over all 252 Young diagrams in the 5x5 box
certify every number below.

Positions are Young diagrams (partitions, written as non-increasing row lengths, e.g. `(2, 1)`).
A move chomps a cell `(i, j)` (1-indexed row and column): the cell together with everything
above-right of it is removed.

## Reading 1 — literal poset game (normal play, every cell may be taken)

Chomping the corner cell `(1, 1)` removes the entire diagram, so **every** nonempty position is
an N-position and the unique P-position is the empty diagram `()`. Consequently the perfect
square `(2, 2)` — two rows of length two — is an N-position, not a P-position.

* Theorem `isPLit_nil` / `isPLit_cons` (Lean): `isPLit [] = true` and, for every nonempty
  partition, `isPLit (n :: rest) = false`; i.e. the P-positions are exactly `{∅}`.
* Counterexample `literal_counterexample`: `isSquare [2, 2] = true` but `isPLit [2, 2] = false`.

(If one insists that the empty partition is the 0x0 "perfect square", the inclusion
"P ⊆ squares" survives for the trivial reason that P = {∅}; the other inclusion still fails
because `(2, 2)` is a square that is not P. Either way the explicit characterization is false.)

## Reading 2 — Chomp with a poison corner

Under the standard Chomp convention the corner `(1, 1)` is poison: taking it loses, which has
identical game values to forbidding the move (a player facing the lone poison cell `(1,)` has
no winning move, so `(1,)` is a P-position, exactly as in Chomp).

Over all 252 diagrams in the 5x5 box there are 24 P-positions:
`(), (1,), (2,1), (2,2,1), (3,1,1), (3,2), (2,2,2,1), (4,1,1,1), (4,3), (3,3,1,1), (4,2,2),
(2,2,2,2,1), (4,2,1,1,1), (5,1,1,1,1), (5,2,1,1), (5,4), (3,3,2,1,1), (5,3,2), (3,3,3,2,2),
(4,4,3,1,1), (5,3,3,2), (5,5,3), (4,4,2,2,2), (5,5,2,2)` — see `reproduce.py` for the exact
list. The characterization fails **in both directions**:

* `(2, 1)` is a P-position but is not a perfect square (it is an L-tromino);
* the perfect squares `(2, 2)` and `(3, 3, 3)` are N-positions (so are the 2x3 rectangle
  `(3, 3)` and, apart from the degenerate `(1,)`, every k x k square in the box).

The small 3x3 corner of the table:

| position | reading 1 | reading 2 (Chomp) |
|----------|-----------|-------------------|
| `()`     | P         | — (not reached)   |
| `(1)`    | N         | P (poison)        |
| `(2)`    | N         | N                 |
| `(1,1)`  | N         | N                 |
| `(2,1)`  | N         | **P** (not a square) |
| `(2,2)`  | N         | **N** (a square)  |

## Machine-checked certificate

`lean4/Main.lean` defines the chomp move on `List Nat`-encoded partitions and two fuel-based
win oracles (`winLit`, `winChomp`); fuel `total lam + 1` is sufficient because every enumerated
move is a genuine cell and therefore removes at least one cell. Main theorems:
`literal_counterexample` and `chomp_counterexample`. `lean4/Check.lean` runs `#print axioms`
on every theorem: **all 18 report "does not depend on any axioms"** (no `sorry`, no
`Classical.choice`, no `Quot.sound`, not even `propext`).

## Files

* `README.md` — this file.
* `main.tex` — full write-up (PDF in `build/`).
* `reproduce.py` — independent enumeration; asserts every number above. Run `python3 reproduce.py`.
* `lean4/Main.lean` — Lean formalization; `lean4/Check.lean` — axiom audit.
  Build with `lake build` inside `lean4/` (toolchain v4.33.1), audit with `lake env lean Check.lean`.

## Conclusion

Conjecture 00000001211 is false under both the literal reading (P-positions = {∅} ≠ squares)
and the Chomp reading (P ⊄ squares and squares ⊄ P). The perfect-square characterization of
P-positions of the Young poset game does not exist in the conjectured form.
