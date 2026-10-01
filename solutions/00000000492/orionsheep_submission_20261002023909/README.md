# Disproof of TLMC Conjecture 00000000492

**Verdict: FALSE.**

## The conjecture

"A random version of the hook length formula. The expectation of the multiset of
hook lengths of a uniformly random standard tableau equals (Σ hooks)/n²,
explicitly (n²−1)/3."

## The attack (f_queue attack point)

`n格钩长各≤n ⇒ Σhooks ≤ n² ⇒ (Σhooks)/n² ≤ 1 < (n²−1)/3`

Every hook length of a standard tableau with n cells is at most n: the hook of a
cell consists of the cell itself plus cells strictly to its right in the same row
and strictly below in the same column, and there are only n cells total. Hence

    Σ hooks ≤ n · n = n²,   so   (Σ hooks)/n² ≤ 1.

The conjectured value (n²−1)/3 is strictly greater than 1 whenever n² − 1 > 3,
i.e. for every n ≥ 3. So the conjectured value lies strictly above the absolute
a-priori cap of the left-hand side — impossible, for every tableau with n ≥ 3
cells and every shape. (The multiset of hook lengths depends only on the shape,
so the "expectation over uniformly random standard tableaux" is just a constant
per shape; the cap applies to it verbatim.)

## Concrete counterexample (n = 3 cells, row shape (3))

The row shape (3) has exactly one standard tableau, so the expectation is
deterministic. Hook lengths: 3, 2, 1. Sum = 6.

    (Σ hooks)/n² = 6/9 = 2/3      conjectured (n²−1)/3 = (9−1)/3 = 8/3.
    2/3 ≠ 8/3.  FALSE.

## Alternative readings also collapse

- **Square reading (tableau is n×n, n² cells).** The hook length of cell (i,j) is
  (n−i)+(n−j)+1, so Σ hooks = n³ and (Σ hooks)/n² = n exactly, deterministically.
  Setting n = (n²−1)/3 gives n²−3n−1 = 0, whose discriminant 13 is not a perfect
  square: no integer n works. Example: 3×3 square has hooks 5,4,4,3,3,3,2,2,1,
  sum 27, ratio 27/9 = 3 ≠ 8/3.
- **Divide-by-n reading ((Σ hooks)/n = (n²−1)/3).** Σ/n ≤ n, and (n²−1)/3 > n for
  every n ≥ 4 (n²−3n−1 > 0 there). Examples: n = 3: 6/3 = 2 ≠ 8/3; n = 4:
  10/4 = 5/2 ≠ 5.
- **Genuine randomization does not help.** Shape (2,1) (n = 3 cells) has 2
  standard tableaux, both with the same hook multiset {3,1,1}; E[Σ] = 5,
  E[Σ]/9 = 5/9 ≠ 8/3 and E[Σ]/3 = 5/3 ≠ 8/3.

## Boundary

- n = 1: LHS = 1/1 = 1 (÷n²) or 1 (÷n), conjectured 0 — already false.
- n = 2: row shape gives 3/4 (÷n²) or 3/2 (÷n) vs conjectured 1 — false;
  2×2 square gives 8/4 = 2 vs 1 — false.
- The universal cap argument kills every n ≥ 3 under ÷n² and every n ≥ 4 under ÷n,
  regardless of shape; the square reading fails for every n ≥ 1.

## Files

- `main.tex`, `build/main.pdf`, `build/log.txt` — full write-up (tectonic build).
- `reproduce.py` — standalone recomputation (`python3 reproduce.py`, stdlib only).
- `lean4/` — Lean 4 (v4.33.1, no Mathlib) machine-checked concretization of the
  attack numbers; `Check.lean` verifies every theorem `does not depend on any
  axioms` (zero axioms, zero `sorry`).

Rebuild the PDF: `cd build-parent-dir && tectonic main.tex --outdir build`.
Re-verify Lean: `cd lean4 && lake build && lake env lean Check.lean`.
