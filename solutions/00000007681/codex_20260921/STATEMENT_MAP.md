# TLMC 00000007681 — statement alignment and counterexample

Status: the complete local Lean source passed on substantive attempt 4, exit 0, at 2026-09-20 17:25:10 UTC (2026-09-21 01:25:10 Asia/Shanghai). Its ten printed axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. Final combined build, fresh-process audit, kernel replay, and submission-package checks remain the coordinator's separate responsibility. No submission or acceptance claimed.

Verified source SHA-256: `55b0371fe870e33c6a4cdd14f163277e29ac3db620f44d993094baa723a46ac7`. `logs/7681-attempt4.json` records matching before/after source hashes and `sources_unchanged_during_command=true`.

## Frozen source

Organizer commit: `95acb520ec5607c826b8a997b1ef2fc82d6f7c57`.

Source: <https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/95acb520ec5607c826b8a997b1ef2fc82d6f7c57/conjectures/00000007681.md>.

The English and Chinese statements use exactly the same recurrence and inequality. The source first defines q-Hermite polynomials by

`2x H_n(x|q) = H_(n+1)(x|q) + (1-q^n) H_(n-1)(x|q)`

and lists their roots in increasing order. Its first assertion is

`x_(n+1,2k) < x_(n,k) < x_(n+1,2k+1)` for `0<q<1`.

Its second assertion concerns monotone convergence of root differences. Refuting the first assertion suffices to refute the conjunction; this package does not formalize or claim to settle that second assertion independently.

## Standard family and the missing initial values

The source does not explicitly give initial conditions. We use the conventional **continuous q-Hermite** family, with `H_0=1` and `H_1=2x`, rather than a different sequence satisfying a recurrence with unspecified starting data.

This normalization was checked against the primary reference NIST Digital Library of Mathematical Functions, equation [18.28.16](https://dlmf.nist.gov/18.28.E16), accessed 2026-09-21. Its finite-sum definition yields `H_0(cos θ|q)=1`; for n=1 its two terms have coefficient one and sum to `e^(iθ)+e^(-iθ)=2cos θ`. Thus it gives exactly these initial polynomials. DLMF calls the family continuous q-Hermite. The bridge from that published definition to the chosen initial conditions is a documented mathematical derivation, not a separately formalized complex-exponential identity in the Lean package.

The Lean definition `Counterexample7681.H` consists of actual polynomials over ℝ with these initial values and the source recurrence. No abstract root values are assumed.

## Explicit witness

Take q=3/4, n=2, k=1. This is strictly inside the allowed parameter interval. Every displayed index is in range: the degree-2 polynomial's first root and the degree-3 polynomial's second and third roots.

Direct recurrence calculations give

`H_2(x|3/4) = 4x²−1/4 = 4(x+1/4)(x−1/4)`

and

`H_3(x|3/4) = x(8x²−11/8)`.

The complete increasing root lists are

- Degree 2: `−1/4, 1/4`.
- Degree 3: `−√11/8, 0, √11/8`.

The required inequality specializes to `0 < −1/4 < √11/8`; its left-hand inequality is false. This is an exact real-algebraic argument, with no floating-point evidence or statistical inference.

## Formal statement map

Source file: `lean/Results/Counterexample7681.lean`.

| Lean declaration | Mathematical role |
|---|---|
| `H` and `recurrence` | Conventional polynomial family and the stated three-term recurrence |
| `H_two_eval`, `H_three_eval` | Exact degree-2/3 evaluations at q=3/4 |
| `H_two_roots`, `H_three_roots` | If-and-only-if characterization of every real root |
| `OrderedRoots` | Strictly increasing and exhaustive enumeration of real roots |
| `ordered_roots_two`, `ordered_roots_three` | Verification of the two concrete ordered root tables |
| `ConjecturedInterlacing` | First conjunct for all permitted q, n, and all indices for which both comparison roots exist |
| `valid_parameter` | q=3/4 lies in (0,1) |
| `counterexample_indices` | Failure at the identified roots |
| `conjectured_interlacing_false` | Formal negation of the first conjunct |
| `full_conjecture_false` | The first conjunct cannot hold in conjunction with any further assertion |

The source uses 1-based indices; Lean `Fin n` uses 0-based indices. If a Lean index has value j, its source index is k=j+1. The source's degree-(n+1) indices 2k and 2k+1 therefore have Lean values 2j+1 and 2j+2. The formal bound `2j+2<n+1` requires both to exist. The witness is j=0, corresponding exactly to source k=1. Restricting to valid indices strengthens the fairness of the counterexample; it does not rely on the source's missing index-range clarification.

## Novelty and scope

No occurrence of 07681 was found in all 100 current organizer PR titles and bodies in the complete API snapshot checked at `2026-09-21T01:13:39.468771+08:00`. An exact-ID public web search found no additional result. This is a bounded prior-submission check, not a priority guarantee; PR files/comments, all forks, and unpublished work are not exhaustively covered.

The result diagnoses an indexing error in an AI-generated statement. It is not a new theorem about the general theory of orthogonal polynomials, and it does not refute the correctly indexed ordinary interlacing theorem.
