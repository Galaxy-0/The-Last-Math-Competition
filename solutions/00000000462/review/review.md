# Solution Review — Conjecture 00000000462 (PR 466)

**Submission:** earthking11 — `earthking11_submission_20261004212700`
**Reviewer:** independent competition review (combinatorics, algebra, build, computation)
**Date:** 2026-10-04

## Checklist
- [x] Official bilingual conjecture read; both translations and both natural readings addressed
- [x] Full LaTeX source and eight-page PDF read; independent PDF builds passed
- [x] Full self-contained Lean project independently rebuilt, including exhaustive graph enumeration
- [x] Direct warnings-as-errors checks passed
- [x] Axiom audit passed; enumeration layer has no axioms
- [x] Auxiliary Python rerun and independently reimplemented
- [x] No incomplete-proof marker, native decision tactic, custom axiom, unsafe construct, external hook, or kernel bypass
- [x] Submission adds only its own correctly named folder
- [x] Conjecture unsolved in base metadata

## Result
For \(n\ge5\), the number of spanning trees of the actual circulant graph \(C_n(1,2)\) is

\[
\tau(n)=\frac{n\left(L(2n)+2(-1)^{n-1}\right)}5.
\]

Consequently

\[
\tau(n+6)=4\tau(n+5)-10\tau(n+3)+4\tau(n+1)-\tau(n),
\]

whose annihilator is

\[
p(x)=x^6-4x^5+10x^3-4x+1
=((x+1)(x^2-3x+1))^2.
\]

Its largest real root is \(\varphi^2=(3+\sqrt5)/2\). By contrast,

\[
\alpha^2=(2+\sqrt3)^2=7+4\sqrt3
\]

is not a root: exact \(\mathbb Z[\sqrt3]\) arithmetic gives

\[
p(\alpha^2)=2615536+1510080\sqrt3\ne0.
\]

Since the minimal annihilator of the sequence divides \(p\), \(\alpha^2\) cannot be a characteristic root of any constant-coefficient recurrence satisfied by \(\tau(C_n(1,2))\). Under the alternative growth-rate reading, \(\lim \tau(n)^{1/n}=\varphi^2\), also not \(\alpha^2\).

## Formal and computational audit
The Lean project defines the actual graph \(C_n(1,2)\), defines spanning trees as \(n-1\)-edge connected subgraphs, enumerates all of them for \(n=5,6,7\), and kernel-certifies counts 125, 384, and 1183. It proves the recurrence, integrality, initial values, factorization, and exact algebraic obstruction. The full build succeeded, including `Trees` after 556 seconds. Direct warnings-as-errors checks passed. All audited theorems use no axioms or only `propext` and `Quot.sound`; the graph-enumeration layer uses none.

The report supplies the full general matrix-tree/root-of-unity proof and honestly marks the general-n bridge and minimal-polynomial fact as not formalized. Those standard steps are mathematically complete in the report and are supported by exact independent computations.

## Independent recomputation
`reproduce.py` passed every exact check. I also independently implemented exact rational determinants, Lucas values, polynomial arithmetic, \(\mathbb Z[\sqrt3]\) evaluation, and union-find enumeration of the actual graphs. The determinant matched the closed form for \(5\le n\le30\); direct enumeration produced 125, 384, and 1183; the recurrence checked through \(n=48\); and the polynomial/algebraic evaluations matched exactly.

## Documentation
The shipped and independently XeLaTeX-compiled eight-page PDFs have identical normalized extracted text. pdfLaTeX also compiled successfully. The report includes the complete proof, values, root comparison, formalization boundary, and reproduction commands.

## Verdict
APPROVED — ready for integration.
