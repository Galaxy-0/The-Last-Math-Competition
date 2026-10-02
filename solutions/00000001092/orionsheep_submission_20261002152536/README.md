# Disproof of Conjecture 00000001092

**Original conjecture (definition sentence quoted verbatim):** "Definition: A complete cap of PG(2,27) is a maximal set with no three collinear points. Conjecture: Its minimum size is 21, with exactly two isomorphism classes attaining this value; the second-smallest complete cap has size 22."

**Verdict: FALSE.** We exhibit an explicit complete cap of PG(2,27) with **14 points**, so the minimum size is at most 14 < 21. Moreover, complete caps of sizes 14, 15, 16 and 17 all exist (found by an independent randomized greedy search, 40 restarts, all restarts landing in 14-17), so the "second-smallest = 22" claim is also false.

## Model

- Field: F_27 = F_3[a] with a^3 = a + 1 (the polynomial t^3 - t + 2 has no root in F_3, hence is irreducible). Elements are encoded as integers 0..26 in base 3: v = c0 + c1*a + c2*a^2.
- Plane: the 757 canonical representatives (x:y:z) whose first nonzero coordinate is 1; three points are collinear iff the determinant of their coordinate matrix vanishes in F_27.

## The counterexample (14 canonical points (x, y, z) as base-3 digit triples)

```
P1  (1,0,0) (2,1,1) (2,2,2)      P8  (1,0,0) (1,0,1) (0,2,0)
P2  (1,0,0) (1,0,0) (2,1,1)      P9  (1,0,0) (1,1,1) (1,2,1)
P3  (1,0,0) (2,0,1) (0,0,0)      P10 (1,0,0) (2,0,1) (1,2,1)
P4  (0,0,0) (1,0,0) (1,2,1)      P11 (1,0,0) (0,1,0) (2,1,0)
P5  (1,0,0) (1,1,0) (0,1,2)      P12 (1,0,0) (1,2,1) (1,1,0)
P6  (1,0,0) (2,0,2) (1,2,0)      P13 (1,0,0) (1,0,0) (2,0,2)
P7  (1,0,0) (2,1,1) (1,1,0)      P14 (1,0,0) (0,0,0) (0,1,1)
```

## Verification (two independent checkers)

1. `python3 reproduce.py` - deterministic, stdlib-only. Rebuilds F_27 and PG(2,27), checks that the 14 points are canonical and distinct, that no three are collinear, and that every one of the remaining 743 points lies on a secant of the cap (i.e., the cap is complete/maximal). Prints PASS.
2. `lean4/Main.lean` - a zero-axiom, zero-`sorry` Lean 4 certificate (plain kernel `decide`, no Mathlib): `plane_size : plane.length = 757`, `cap_small : cap.length = 14 ∧ cap.length < 21`, `cap_is_cap`, `cap_is_complete`, `main_disproof`. `Check.lean` runs `#print axioms` on every theorem; all report "does not depend on any axioms".

## Files

- `main.tex` - the note (compiles with tectonic).
- `reproduce.py` - deterministic counterexample checker.
- `lean4/Main.lean`, `lean4/Check.lean` - axiom-free formal certificate.
