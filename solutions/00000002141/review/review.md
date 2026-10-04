# Solution Review — Conjecture 00000002141 (PR 467)

**Submission:** jilint777 — `jilint777_submission_20261004060351`
**Reviewer:** independent competition review (graphs, spectra, build, enumeration)
**Date:** 2026-10-04

## Checklist
- [x] Official bilingual conjecture read; uniqueness clause identified as the decisive conjunct
- [x] Full LaTeX source and four-page PDF read; independent PDF build passed
- [x] Full self-contained Lean project independently rebuilt
- [x] Direct warnings-as-errors Lean check passed
- [x] Only standard core axioms used; decisive computations use none
- [x] Auxiliary Python run in full with nauty installed
- [x] Independent spectral, invariant, canonical-label, and matrix-certificate checks passed
- [x] No incomplete-proof marker, native decision tactic, custom axiom, unsafe construct, external hook, or kernel bypass
- [x] Submission adds only its own correctly named folder
- [x] Conjecture unsolved in base metadata

## Counterexample
The submission gives two distinct cospectral pairs of simple 4-regular graphs on ten vertices:

\[
(A_1,B_1),\qquad (A_2,B_2).
\]

Their characteristic polynomials are respectively

\[
x^{10}-20x^8-16x^7+110x^6+136x^5-180x^4-320x^3+9x^2+200x+80
\]

and

\[
x^{10}-20x^8-14x^7+108x^6+104x^5-183x^4-188x^3+80x^2+68x-16.
\]

The two graphs in each pair share the corresponding polynomial; the two pairs have different spectra.

## Non-isomorphism
A triangle-free edge and an isolated triangle-free edge are isomorphism invariants. A1 has no triangle-free edge, unlike B1, A2, and B2. A2 has the isolated triangle-free edge 36, unlike B2. Thus each pair is non-isomorphic, and A1 is not isomorphic to either graph in the second pair. Therefore the two unordered order-10 cospectral regular pairs are genuinely different.

## Formal audit
Lean represents actual ten-vertex adjacency functions. `Cospectral` uses equality of \(\operatorname{tr}(A^k)\) for \(k\le10\), equivalent to equal spectra by Newton's identities. It proves regularity, both cospectralities, the invariant preservation lemmas, all needed non-isomorphisms, both cospectral-regular pairs, and negation of the unordered-pair uniqueness statement. It also provides explicit integer matrices satisfying \(MM^T=4I\) and \(MA=B M\), giving an independent orthogonal-similarity proof.

Fresh `lake build` and direct warnings-as-errors elaboration both passed. Final and intermediate proofs use either no axioms or only `propext` and `Quot.sound`.

## Independent computation
`verify.py` was run in full after installing nauty. It checked two exact characteristic-polynomial methods, exhaustive non-isomorphism search, connectivity, orthogonal certificates, and every regular graph through order 10. It found no smaller cospectral regular pair and exactly two 4-regular pairs plus their two 5-regular complements at order 10.

I also independently reproduced both characteristic polynomials and triangle-free-edge invariants with SymPy, checked both \(MM^T\) certificates, found all four submitted graph6 strings in nauty's enumeration, and confirmed four distinct canonical labels with `labelg`.

## Documentation
The report states both official clauses, takes the weakest reasonable unordered-pair reading of uniqueness, and explains why refuting uniqueness refutes the conjunction. Independent pdfLaTeX compilation succeeded twice; the shipped and fresh PDFs differ only in extraction of five bullet glyphs, not content.

## Verdict
APPROVED — ready for integration.
