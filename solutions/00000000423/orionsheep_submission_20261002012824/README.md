# Disproof of conjecture 00000000423 (promotion orbit divisibility)

**Verdict: FALSE.**

## Conjecture

Promotion (Schützenberger's cyclic sliding) acts on the standard Young tableaux
(SYT) of a fixed shape. The conjecture states that promotion orbit lengths
divide the tableau size.

## Attack

Shape `(2,1)` has exactly two SYT (entries `1,2,3`; top row strictly increasing,
first column strictly increasing):

```
A = | 1 2 |      B = | 1 3 |
    | 3 |          | 2 |
```

Schützenberger promotion on `A`: delete the entry `1`; of the entries to its
right (`2`) and below (`3`), the smaller, `2`, slides left; the vacated cell is
a corner so the slide stops; subtract `1` from every entry; place `3` in the
vacated corner. Result: `B`. Symmetrically promotion maps `B ↦ A`. So promotion
is the transposition `A ↔ B`: the whole tableau set is a single orbit of
**length 2**.

The tableau size (number of cells) is `n = 3`, and `2 ∤ 3`. The conjecture
fails at the second-smallest non-rectangle shape.

## Boundary

* Rectangular shapes do *not* refute the conjecture: by Haiman's theorem the
  promotion order on an `a × b` rectangle with `n = ab` cells is
  `n / gcd(n, a)`, which divides `n`. The failure requires a non-rectangle.
* `(2,1)` is the smallest counterexample under the "size = number of cells"
  reading (`n = 3`, orbit length `2`).
* The alternative reading "size = number of tableaux of the shape" is refuted
  one step later: for shape `(3,2)` there are `#SYT = 5` tableaux and the
  promotion orbits have lengths `{3, 2}` (lcm `6`); neither `3` nor `2`
  divides `5`, and `6` divides neither `3` nor `5`. Both readings of the
  conjecture are false.

## Files

* `main.tex`, `build/main.pdf` — write-up.
* `reproduce.py` — standalone recomputation of the attack numbers.
* `lean4/` — machine-checked proof (core Lean 4, no Mathlib, **zero axioms,
  zero `sorry`**); see `lean4/README.md`.

## Reproduce

```
python3 reproduce.py
cd lean4 && lake build && lake env lean Check.lean
```
