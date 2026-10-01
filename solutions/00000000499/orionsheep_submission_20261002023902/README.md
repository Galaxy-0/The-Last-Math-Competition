# Disproof of Conjecture 00000000499

**Verdict: FALSE.**

## Conjecture (paraphrase)

Let `p_n` be the probability that `n` nonintersecting simple random walks go from
fixed starting points to fixed endpoints without ever intersecting. The conjecture
asserts that `p_n` equals, at the corresponding endpoints, the joint density of the
ordered eigenvalues of an `n x n` GUE matrix times the explicit Vandermonde factor
`prod_{i<j} (y_j - y_i - (x_j - x_i))`, and that this identity holds for
**all times T > 0**.

## Attack

Same endpoints, different times. Take `n = 2`, starts `x = (0, 4)` (ordered),
endpoints `y = (1, 3)`, each walk moving `+/-1` per step. Brute-force enumeration of
all `4^T` equally likely joint step sequences (exact rational arithmetic); "good"
means both walks end at `(1, 3)` and `w1(t) < w2(t)` at every time `t = 0..T`:

| T | good / total | p(T)     |
|---|--------------|----------|
| 1 | 1 / 4        | 1/4      |
| 2 | 0 / 16       | 0        |
| 3 | 8 / 64       | 1/8      |
| 4 | 0 / 256      | 0        |
| 5 | 75 / 1024    | 75/1024  |

- `T = 1`: the only surviving joint path is `(+1, -1)`: `(0,4) -> (1,3)`; `p = 1/4`.
- `T = 2`: parity — a displacement of `+1` in 2 steps is impossible; `p = 0`.
- `T = 3`: 8 of the 64 joint paths survive (e.g. `w1: 0->1->0->1` with
  `w2: 4->3->4->3`); `p = 8/64 = 1/8`.

## Why this disproves the conjecture

The right-hand side — the GUE ordered-eigenvalue joint density evaluated at
`(y1, y2) = (1, 3)` multiplied by the Vandermonde factor
`(y2 - y1) - (x2 - x1) = (3 - 1) - (4 - 0) = -2` — contains **no `T`**. It is a
single fixed constant `c` (and it is nonzero: the density at two distinct endpoints
is strictly positive and the factor is `±2`; under the literal reading `c` is even
negative, while a probability satisfies `p_n >= 0`).

But the left-hand side takes the distinct values `1/4`, `0`, `1/8` at the *same*
endpoints. A constant cannot equal three different numbers, so the identity fails
for some `T > 0`; concretely `p(1) = 1/4 != 1/8 = p(3)` while the right-hand side
is the same number at both times.

**Verdict: FALSE.**

## Reproduction

- `python3 reproduce.py` — standalone exact recomputation (stdlib only).
- `lean4/` — core Lean 4 (no Mathlib) proof: full enumeration of the 4, 16 and 64
  joint paths for `T = 1, 2, 3`, the counts `C1 = 1`, `C2 = 0`, `C3 = 8`, and the
  cross-multiplied inequality `C1 * 64 != C3 * 4` (i.e. `1/4 != 1/8`).
  Zero axioms, zero `sorry` — audited by `lean4/Check.lean`.
- `main.tex` / `build/main.pdf` — write-up.
