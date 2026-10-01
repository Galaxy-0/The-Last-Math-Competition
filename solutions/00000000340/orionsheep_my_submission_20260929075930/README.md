# Disproof of TLMC Conjecture 00000000340

**Verdict: FALSE.**

## Conjecture (00000000340)

Let `G_N(α) = (Π_{j≤N} a_j)^{1/N}` be the geometric mean of the first `N` continued-fraction
partial quotients of `α`. The conjecture claims: for every algebraic irrational `α`,

- `liminf_N G_N(α) = 1`, and
- `limsup_N G_N(α) = ∞`.

## Attack

Take `α = √2 = [1; 2, 2, 2, …]`. This is algebraic irrational (root of `x² − 2`), and its
partial quotients are `a_1 = 1`, `a_j = 2` for all `j ≥ 2` (exact: the convergents satisfy the
Pell equation `p_k² − 2 q_k² = (−1)^{k+1}`, and the standard CF recurrence gives all partial
quotients after the first equal to 2). Hence for every `N ≥ 1`

    Π_{j≤N} a_j = 2^{N−1},     G_N(√2) = (2^{N−1})^{1/N} = 2^{(N−1)/N}  →  2.

So the sequence `(G_N)` is strictly increasing, bounded, and converges to `2`:

| N    | G_N = 2^{(N−1)/N} |
|------|-------------------|
| 10   | 1.866065983       |
| 100  | 1.986184991       |
| 1000 | 1.998614186       |

Consequently `liminf G_N = limsup G_N = 2`:

- `limsup = ∞` fails: `G_N ≤ 2` for every `N` (in fact `G_N < 2`);
- `liminf = 1` fails: `G_N ≥ √2 > 1` for every `N ≥ 2` (in fact `G_N ≥ 1.99` for every `N ≥ 139`,
  with the threshold exactly 139 — at `N = 138` one has `G_N < 1.99`).

Both claims of the conjecture are contradicted by a single algebraic irrational.

## Boundary (where the disproof stops)

- The counterexample is not an artifact of √2: **every** quadratic irrational has an eventually
  periodic CF, hence bounded partial quotients, hence `(G_N)` bounded with `liminf G_N > 1`
  (the geometric mean of one period is already > 1). The conjecture fails on the entire class
  of badly approximable numbers.
- A.e.-version is also false: for Lebesgue-a.e. `α`, Birkhoff's ergodic theorem for the Gauss
  measure gives `G_N → K ≈ 2.685452001` (Khinchin's constant), so `limsup = ∞` fails a.e. as well.
- What remains open is whether *some* non-quadratic algebraic irrational (e.g. a cubic irrational
  such as ∛2) even has unbounded partial quotients — that classical open problem is untouched by
  this disproof; the conjecture as stated, however, is refuted outright.

## Files

- `main.tex`, `build/main.pdf` — full write-up (compile: `tectonic main.tex --outdir build`).
- `reproduce.py` — standalone exact recomputation (integer CF of √2, geometric means,
  threshold check). Run: `python3 reproduce.py`.
- `lean4/Main.lean` — self-contained Lean 4 certificate (core Lean, **no Mathlib, no axioms,
  no sorry**): identity `Π_{j<N} a_j = 2^{N−1}`, the bounds `G_N ≤ 2` and `G_N² ≥ 2` (N ≥ 2),
  the sharp eventual bound `G_N ≥ 1.99` for `N ≥ 139`, and concrete values at `N = 1000`
  (`199^1000 ≤ 2^999·100^1000 ≤ 201^1000`, i.e. `1.99 ≤ G_1000 ≤ 2.01`).
- `lean4/Check.lean` — `#print axioms` audit for every main theorem.
- `lean4/lakefile.toml`, `lean4/lean-toolchain` (`leanprover/lean4:v4.33.1`), `lean4/README.md`.

## Verification

    cd lean4 && lake build && lake env lean Check.lean
    # every theorem: "does not depend on any axioms"
    python3 reproduce.py   # all checks pass
