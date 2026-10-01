# Disproof of TLMC conjecture 00000000142

**Verdict: FALSE.**

## The conjecture

TLMC conjecture 00000000142: the empirical spectral distribution (ESD) of the
prime-indicator matrix `M_n = (1_{i+j prime})_{1 <= i,j <= n}` tends to the semicircle
law, and its linear spectral statistics satisfy a CLT.

## The attack (exact trace identities + divergence of the ESD second moment)

The matrix is symmetric with 0/1 entries, so two trace identities are exact:

1. **`tr M_n = 1`** for every `n >= 1`: the diagonal entries are `1_{2i prime}`, and the
   only prime of the form `2i` is `2` (at `i = 1`). ESD mean = `1/n -> 0` (consistent
   with the semicircle; not the contradiction).
2. **`tr M_n^2 = N(n) := #{(i,j) in [n]^2 : i+j prime}`**, because
   `tr M^2 = sum_{i,j} M_{ij} M_{ji} = sum_{i,j} M_{ij}^2 = sum_{i,j} M_{ij}`.
   Hence the **ESD second moment** is `m2(n) = (1/n) tr M_n^2 = N(n)/n`, and
   `N(n) ~ n^2 / log(2n)` (PNT + partial summation over the triangular weight), so
   **`m2(n) ~ n / log(2n) -> infinity`**, whereas the semicircle law has second moment
   exactly **1** (and support `[-2,2]`).

Consequences under the two possible readings of "ESD of the matrix":

* **Raw matrix `M_n`:** the conjecture's own second clause (LSS CLT) presupposes the
  moment convergence `(1/n) tr f(M_n) -> int f dsigma_sc` for polynomial `f`; for
  `f(x) = x^2` it predicts `m2(n) -> 1`. The truth is `m2(n) -> infinity`.
  Refuted. Numerics show the spectrum genuinely spreads (RMS eigenvalue 7.2 at n=300,
  12.1 at n=1000, 16.3 at n=2000; fraction with `|lambda| <= 1` falls 0.120 -> 0.032
  versus the semicircle's 0.609), i.e. there is no tight limit at all, not even delta_0.
* **Normalized `M_n / n`:** `||M_n/n||_op <= sqrt(N(n))/n ~ sqrt(2/log(2n)) -> 0`
  (PNT), so the ESD of `M_n/n` tends to `delta_0`, not the semicircle. Refuted
  unconditionally. (This is the precise sense in which the original verdict's
  "limit can only be delta_0" is right.)

Under either reading the conjecture is **false**.

## Exact numbers (independently recomputed; matches the recorded verdict)

| n | N(n) | N/n^2 | 1/log(2n) | N/n (= ESD 2nd moment) | n/log(2n) |
|------|---------|-------|-------|--------|--------|
| 300 | 15439 | 0.1715 | 0.1563 | 51.46 | 46.90 |
| 600 | 56237 | 0.1562 | 0.1410 | 93.73 | 84.63 |
| 1000 | 145171 | 0.1452 | 0.1316 | 145.17 | 131.56 |
| 2000 | 528537 | 0.1321 | 0.1206 | 264.27 | 241.14 |
| 4000 | 1944355 | 0.1215 | 0.1113 | 486.09 | 445.08 |
| 8000 | 7187475 | 0.1123 | 0.1033 | 898.43 | 826.42 |

The recorded verdict's recomputation `tr M^2/n^2`: n=300 -> 0.172, n=600 -> 0.156,
n=1000 -> 0.145 is confirmed exactly (0.1715 / 0.1562 / 0.1452). One correction: that
quantity is the Frobenius-squared *density*, not the ESD second moment; under the
standard ESD normalization `(1/n) tr M^2` the second moment **diverges** (`N(n)/n`), so
the limit is not `delta_0` for the raw matrix — the spectrum escapes to scale
`~sqrt(n/log n)`. Either way, "ESD -> semicircle" is false, and stronger than recorded.

Eigenvalue statistics (numpy `eigvalsh`, symmetric matrix):

| n | lambda_max | lambda_min | RMS = sqrt(m2) | frac |lambda|<=1 | frac lambda<0 | frac |lambda|>3 |
|------|--------|---------|-------|------|------|-------|
| 300 | 51.72 | -51.71 | 7.17 | 0.1200 | 0.5000 | 0.5767 |
| 600 | 94.03 | -94.03 | 9.68 | 0.0667 | 0.5000 | 0.7400 |
| 1000 | 145.62 | -145.61 | 12.05 | 0.0520 | 0.5000 | 0.7860 |
| 2000 | 264.96 | -264.95 | 16.26 | 0.0320 | 0.5000 | 0.8690 |

Semicircle reference: second moment 1; `P(|lambda| <= 1) = 1/3 + sqrt(3)/(2*pi) ~ 0.609`;
`P(|lambda| > 3) = 0`. The negative fraction is exactly 1/2 at all n because `M_n` is
bipartite up to the single entry `e_11` (prime > 2 is odd), so the spectrum is symmetric
up to a 1/n Weyl perturbation — the ± symmetry matches the semicircle, everything else
does not.

## What is proven / what is heuristic (boundary)

* Proven (and machine-checked in Lean): both trace identities; `tr M_n = 1` for all n;
  `tr M_n^2 = N(n)` for all n; exact values `N(8)=23, N(64)=941, N(128)=3239`;
  `N(n) > n` at n = 64, 128; growth `N(128)/128 > N(64)/64`.
* Proven at PNT level (cited, not Lean-formalized): `N(n) ~ n^2/log(2n)`; hence
  `m2(n) -> infinity`; and `||M_n/n||_op -> 0` hence `ESD(M_n/n) -> delta_0`.
* Heuristic/numerical (stated as such): the bulk of the spectrum spreads over a
  symmetrized quarter-circle/Marchenko-Pastur-type shape at scale `~sqrt(2n/log(2n))`;
  the outlier pair +-lambda_1 has `lambda_1 ~ n/log(2n)` (Rayleigh lower bound
  `lambda_max >= N(n)/n` is tight numerically: 51.72 vs 51.46 at n=300).
* Open: rigorous identification of the rescaled bulk limit; rigorous
  positive-fraction escape (`tr M^2` counting alone yields only >= c log n eigenvalues
  outside any fixed compact); LSS behavior of any rescaled model.

## Reproduction

```bash
python3 reproduce.py            # trace identities + exact counts + verdict comparison (pure python)
python3 reproduce.py --eigen    # additionally the numpy eigvalsh statistics
```

## Machine verification (Lean 4, zero axioms)

```bash
cd lean4
lake build
lake env lean Check.lean
```

All 18 theorems report `does not depend on any axioms` (no `sorryAx`, no `propext`,
no `Quot.sound`, no `Classical.choice`; `decide`/`rfl`/explicit term proofs only —
`omega`, `simp`, `native_decide` are deliberately not used). Key theorems:
`diag_eq_one` (`tr M_n = 1`), `traceSq_eq_pairCount` (`tr M_n^2 = N(n)`), and the
`decide`-verified values `pairCount_64`, `pairCount_128`, `moment_gt_one_*`,
`moment_growth`.
