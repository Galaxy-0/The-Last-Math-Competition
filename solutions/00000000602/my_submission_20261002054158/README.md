# Disproof of TLMC conjecture 00000000602

**Verdict: FALSE.**

## The conjecture

For every alternating knot `K`, with `V_K` the Jones polynomial and `ω` a
primitive fourth root of unity (`ω = ± i`):

1. `|V_K(ω)|² divides det(K)²`, and
2. the quotient `det(K)² / |V_K(ω)|²` equals `|V_K(i)|²`.

## The attack

Since the only primitive fourth roots of unity are `ω = ± i`, clause (2)
collapses to `det(K)² = |V_K(i)|⁴`. The smallest alternating knot already
violates this.

**Counterexample: `K = 3₁` (right-handed trefoil).**

- Jones polynomial (standard normalization `V(unknot) = 1`):
  `V(t) = t + t³ − t⁴`. Recomputed from scratch in `reproduce.py` via the
  Kauffman bracket state-sum on the PD code
  `X(1,4,2,5), X(3,6,4,1), X(5,2,6,3)`: bracket `<3₁> = A⁻⁷ − A⁻³ − A⁵`,
  giving exactly `V(t) = t + t³ − t⁴` (sanity check `V(1) = 1` passes).
- Exact Gaussian-integer evaluation: `V(i) = V(−i) = −1`, so
  `|V(ω)|² = |V(i)|² = 1` (both primitive fourth roots give the same value).
- Determinant: `det(3₁) = |Δ(−1)| = 3` (Alexander polynomial
  `Δ(t) = t⁻¹ − 1 + t`), so `det(3₁)² = 9`.
- Clause (1) happens to hold: `1 ∣ 9`.
- Clause (2) fails: the quotient is `9 / 1 = 9`, but `|V(i)|² = 1`,
  and `9 ≠ 1`.

Secondary witnesses (same computation, published Jones polynomials), all
alternating, all fail clause (2) with `|V(i)|² = 1`:

| K   | det | det² | `|V(i)|²` | quotient | clause (2) |
|-----|-----|------|-----------|----------|------------|
| 3₁  | 3   | 9    | 1         | 9        | fails      |
| 4₁  | 5   | 25   | 1         | 25       | fails      |
| 5₁  | 5   | 25   | 1         | 25       | fails      |
| 5₂  | 7   | 49   | 1         | 49       | fails      |
| 7₁  | 7   | 49   | 1         | 49       | fails      |

## Boundary (what this does and does not show)

- The failure is in the **quotient identity** (clause 2) only; the
  divisibility clause (clause 1) is not refuted by this counterexample
  (`|V(ω)|² = 1` divides everything).
- In every alternating knot tested, `|V_K(i)|² = 1`; under that pattern the
  identity clause would force `det(K) = 1`, i.e. it can only hold for
  knots with trivial determinant, so no repair by restricting to
  high-crossing knots is possible — the counterexample is the trefoil.
- Since `V_K(t̄) = conj(V_K(t))` for real coefficients and
  `V_{mirror}(t) = V_K(1/t)`, the numbers `|V(±i)|² = 1` are mirror- and
  conjugation-stable: the chirality convention of the trefoil does not
  matter for the disproof.

## Machine verification (Lean 4, core only)

`lean4/Main.lean` re-encodes Gaussian-integer arithmetic and proves, with
`rfl`/`decide` only:

- `Vtrefoil_at_i`, `Vtrefoil_at_negi`: `V(±i) = (−1, 0)`;
- `normSq_Vtrefoil_roots`: `|V(ω)|² = 1` for `ω = ± i`;
- `det31_sq`: `det(3₁)² = 9`;
- `counterexample_00000000602`: the conjecture's identity fails for `3₁`.

Zero `sorry`, and `lean4/Check.lean` audits that every theorem **does not
depend on any axioms** (not even `propext` / `Quot.sound` / `Class.choice`).

## Files

- `README.md` — this file.
- `main.tex`, `build/main.pdf` — write-up (compiled with Tectonic).
- `build/log.txt` — build log.
- `reproduce.py` — standalone, dependency-free recomputation of every
  attack number (`python3 reproduce.py`).
- `lean4/` — Lean verification package (`Main.lean`, `Check.lean`,
  `lakefile.toml`, `lean-toolchain`, `README.md`).

## Reproduce

```sh
python3 reproduce.py
cd lean4 && lake build && lake env lean Check.lean
```
