# Solution Review — Conjecture 00000008565 (PR 759)

**Submission:** Jackmeson1 — `solutions/00000008565/Jackmeson1_submission_20261005211645`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Conjecture read/copy check:** official `conjectures/00000008565.md` read in full (bilingual, four conjoined laws). Shipped `conjecture.md` is byte-identical (`diff` clean). The second law — "simple spectrum (no multiplicity) is generic for cyclic generating sets of abelian groups" — is the one refuted; refuting one conjunct refutes the conjunction, and the submission says so explicitly.
- **LaTeX rebuild + PDF comparison:** `latexmk -pdf -interaction=nonstopmode` succeeds in a scratch dir. Extracted text matches; residual differences are cosmetic extraction artifacts only (ligatures; math glyphs `∼`, `≥`, `∈`, `≠`, braces `{g}` mapping to stray codes in the shipped PDF's font encoding). No content discrepancy.
- **Lake build:** zero errors, `Build completed successfully (8708 jobs)` on Lean v4.33.1, Mathlib v4.33.1 (manifest rev `0df444a360eaa60ab8c11dca51a86af692955474`, prebuilt pool). Reproduced independently; matches shipped `verification/build.txt`.
- **Axioms:** `lake env lean Axioms.lean` re-run independently: both decisive theorems `C8565.not_hasSimpleSpectrum` and `C8565.simple_spectrum_not_generic` depend on exactly `[propext, Classical.choice, Quot.sound]`. Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, `axiom` declarations: no hits. Matches `verification/axioms.txt`.
- **Aux code:** axiom audit re-run, matches. Note: 1 of 13 entries in `verification/SHA256SUMS.txt` (`conjecture.md`) is stale; the shipped copy is nonetheless byte-identical to the official file. Non-blocking.
- **Metadata unsolved:** `metadata.csv` lists `00000008565` with `proven=false, disproven=false, completed_by_ai=false`.
- **Numeric sanity:** brute force over all generating connection sets of ZMod n for n = 3…8 (3, 6, 15, 27, 63, 120 sets): in every case 0 sets yield a simple-spectrum adjacency matrix, confirming the theorem's content. Spot check: Cay(Z/5, {±1}) = C_5 has eigenvalue (−1+√5)/2·2 = 2cos(72°) with multiplicity 2.

## Semantic audit

The conjecture is a conjunction of four laws. The submission refutes the second, the "abelian simple spectrum law". The counterexample family satisfies all stated hypotheses: G = Z/nZ (n ≥ 3) is an abelian group, and the claim is refuted for every generating set S whatsoever (so under any reading of "cyclic generating set": any generating set of a cyclic group, singleton {g}, symmetric pair {g, −g}), which is precisely the negation of genericity — a property failing at every member of a nonempty family is not generic in any sense (all-but-finitely-many, density 1, probability 1, open dense). The formalization is on the conjecture's own objects: Mathlib's actual undirected Cayley graph `SimpleGraph.addCayley S` on the actual group `ZMod n` and its complex adjacency matrix, with a Lean-proved faithfulness lemma (`addCayley_adj_iff_sub_mem`) identifying it with the textbook graph u ~ v ↔ v − u ∈ S for symmetric S not containing 0, and a separate theorem (`connMatrix_not_hasSimpleSpectrum`) covering the textbook matrix A(u,v) = [v − u ∈ S] with loops allowed. This is not a toy surrogate.

The mathematics is correct and classical. The adjacency matrix of a Cayley graph on a cyclic group is circulant, A(u,v) = f(v − u); any multiplicative ψ (here the standard additive character χ(x) = e^{2πix/n}) is an eigenvector with eigenvalue Σ_w f(w)ψ(w) (`mulVec_of_mul`). Since the graph is undirected the neighbourhood of 0 is negation-closed, so f is even and χ and its conjugate χ(−·) share the eigenvalue μ; since n ≥ 3, χ(1) ≠ χ(−1), so they are linearly independent and the μ-eigenspace has dimension ≥ 2. Geometric multiplicity ≤ algebraic multiplicity gives a double root of the characteristic polynomial. I verified numerically that no generating set of ZMod n for n = 3…8 gives simple spectrum. The scope discussion is honest: the directed-digraph reading is explicitly not refuted (with the directed n-cycle as a counterexample to over-claiming), clauses 1, 3, 4 are not addressed (clause 1's finite case is sketched correctly — eigenvalues of an integer matrix are algebraic integers), and the undirected reading is justified by the conjecture's own words ("adjacency operator", "spectral norm").

The decisive theorem is the exact negation of the relevant conjunct (indeed stronger: universal non-simple spectrum rather than mere non-genericity), no hypotheses are strengthened, and no definition trivializes the claim — `HasSimpleSpectrum` is the standard every-eigenspace-≤-1-dimension condition, and it is refuted rather than restated.

## Issues found

None blocking. Non-blocking notes: one stale checksum entry in `verification/SHA256SUMS.txt` (see checklist); the report leaves the directed reading open, which is appropriate scope disclosure rather than a defect.

## Verdict

APPROVED (as a disproof). The submission rigorously refutes the second conjunct of conjecture 00000008565 on the conjecture's own objects — every undirected Cayley graph of every cyclic group Z/nZ, n ≥ 3, over every connection set, fails to have simple spectrum, so simple spectrum is not generic for cyclic generating sets of abelian groups — with a zero-error Lean build under only the standard three axioms, a faithfully rebuilt PDF, and brute-force numerical confirmation. Since the conjecture is a conjunction, this refutes it.
