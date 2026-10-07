# Solution Review — Conjecture 00000000810 (PR 764)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005213730`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000000810.md` read in full (bilingual); shipped `conjecture.md` is byte-identical to it (`diff` clean). Note: the shipped `verification/SHA256SUMS.txt` lists two stale hashes (`conjecture.md`, `proof.tex`); both files were verified correct by direct diff/rebuild, so this is a bookkeeping artifact only.
- LaTeX rebuild: `latexmk -pdf` in a scratch dir succeeds; shipped and rebuilt `proof.pdf` match after whitespace/ligature normalization; remaining differences are font glyph-extraction artifacts only (`\x14`/`\x15`/`\x00` vs ≤/≥/−, `{`/`}` extracted as `f`/`g` in the monospace font, `_` handling) — cosmetic.
- Lean build: `lake build` succeeds with zero errors and zero warnings (Lean 4.33.1, Mathlib v4.33.1, pool rev `0df444a360`, ~105 s).
- Axioms: independent `lake env lean Check.lean` with `#print axioms` for ALL seven theorems (`not_star_minimizer`, `not_star_minimizer_among_stars`, `star_not_minimal`, `star_no_eigenvalue_le`, `path_eigenvalue`, `twoLong_eigenvalue`, `star_beaten`) — each depends only on `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `native_decide`, `extern`, `unsafe`, or declared `axiom` anywhere in the project.
- Aux code: `verification/build.txt` and `verification/axioms.txt` match the reviewer's fresh rebuild and axiom output exactly; no runnable scripts shipped (none needed).
- Metadata: `metadata.csv` lists 00000000810 as unsolved; no other solution folder for this conjecture in the submission.

## Semantic audit

The conjecture asserts that among quantum graphs of fixed total length and vertex count the minimum of the first (positive) Kirchhoff eigenvalue is attained by the star graph, with strict uniqueness for more than three vertices. The submission refutes the attainment conjunct for every vertex count n = k+1 >= 4 and every length L > 0, which suffices to refute the conjunction; the λ₀ = 0 reading is correctly identified as trivially non-unique and deliberately left unformalized, and "first eigenvalue" is read as the smallest positive eigenvalue, the standard reading in the quantum-graph literature (under which the conjecture is a genuine, and false, extremal claim).

The Lean definitions are the conjecture's own objects, not a surrogate: `MetricGraph n` is a finite metric multigraph with positive edge lengths (loops and multiple edges allowed), `IsEigenfunction` is the strong Kirchhoff eigenproblem (f″ = −λf on each closed edge with one-sided endpoint derivatives, continuity through common vertex values, vanishing of the sum of outgoing derivatives — with loops correctly contributing at both ends), and `IsEigenvalue` requires an eigenfunction nonzero at some point of some edge; since every eigenfunction satisfies the ODE, this is equivalent to genuine nontriviality and admits no degenerate exploit. The two main theorems are exact negations of the two natural readings of star-minimality (against all metric graphs R1, against stars only R2, covering any exclusion of degree-two vertices): they refute "some star has a least positive eigenvalue μ ≤ every positive eigenvalue of every competitor", which is a necessary consequence of the star attaining the minimum (λ₁(G) is at most each positive eigenvalue of G), and `IsLeast` includes membership, so no empty-spectrum loophole exists.

The mathematics is correct; the reviewer re-derived it independently. Every star eigenfunction is forced by the leaf Neumann conditions and ODE uniqueness (lemma `ode_cos`, an energy/constant-of-motion argument) into the form f_e(x) = a_e cos(s(ℓ_e − x)); continuity at the centre gives a_e cos(sℓ_e) = c and Kirchhoff gives Σ a_e sin(sℓ_e) = 0; for sL ≤ π and k ≥ 3 the trigonometric lemma `star_trig` (strict superadditivity of tan on (0, π/2), with the obtuse case handled via tan R ≤ tan(π − θ_max)) forces all a_e = 0. Hence no star has any eigenvalue in (0, π²/L²]. The path P_{k+1} of length L has the eigenvalue π²/L² (cos(πt/L) is an explicit eigenfunction, verified vertex by vertex in Lean), so every star loses to the path; and for any μ > π²/L² the star with two long edges of length t/2 = (L+r)/2, r = π/√μ < L, and j short edges carries the eigenvalue (π/2a)² = (π/t)² < μ (the ±cos pair on the two equal edges with the other edges identically zero is an explicit eigenfunction), so stars lose even among themselves. Numerical sanity checks agree: the equilateral k-star (k ≥ 3) has least positive eigenvalue (kπ/2L)² > π²/L², and no root of Σ cot(sℓ_e) = 0 exists for s ≤ π/L in tested uneven length profiles.

## Issues found

None blocking. Two cosmetic notes: (1) `verification/SHA256SUMS.txt` contains stale hashes for `conjecture.md` and `proof.tex` (the files themselves are correct); (2) the report states `#print axioms` was run for five theorems while the shipped `Axioms.lean` prints two — the reviewer ran all seven and confirmed the standard three axioms only.

## Verdict

APPROVED. A rigorous, faithful, fully machine-checked disproof of the conjecture as written: for n ≥ 4 vertices and every total length, no metric star minimizes the first positive Kirchhoff eigenvalue — the path (and even other stars) strictly beat every star. The quantifier structure matches the official bilingual text, the formalization uses the conjecture's own objects, the Lean build is clean with only the three permitted axioms, and the report matches the code.
