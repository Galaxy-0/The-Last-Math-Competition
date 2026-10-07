# Solution Review — Conjecture 00000005640 (PR 640)

**Submission:** Jackmeson1 — `solutions/00000005640/Jackmeson1_submission_20261005071249`
**Head:** `64055e7886bc7d38eb9d6015c961e6af459c156e`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06
**Result:** Approved

## Checklist results

- Official conjecture (`conjectures/00000005640.md`, English + Chinese) read in full; the submission's `conjecture.md` is byte-identical to it. Source-md check: pass.
- LaTeX report read in its entirety; independent `latexmk -pdf` rebuild succeeded; extracted text of shipped and rebuilt PDFs matches modulo standard glyph/ligature extraction artifacts (`ff`/`ft` ligatures, word-boundary spacing). PDF-match check: pass.
- `lake build` (Lean v4.33.1, Mathlib v4.33.1) exits 0 with zero errors and zero warnings. Lean-build check: pass.
- No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. `#print axioms` for `conjecture5640_false` and `conjecture5640_separate_false` → `[propext, Classical.choice, Quot.sound]` only, independently re-run via the shipped `Axioms.lean`. Axiom check: pass.
- Auxiliary `verification/` material agrees with independently reproduced results; two SHA256SUMS entries (`conjecture.md`, `proof.tex`) hash CRLF newline variants — bookkeeping artifact, content identical. Aux check: pass.
- Semantic audit: pass (details below).

## Semantic audit

This is a disproof, and the crux is the reading of the conjecture's final clause. The conjecture asserts three things at once: (A) two convex-set families with the same intersection spectrum, (B) non-isomorphic intersection graphs, and (C) the separation realized by an explicit redrawing pair preserving intersections. The submission observes that (B) and (C) are jointly unsatisfiable: a redrawing pair preserving intersections is a bijection `σ` between index sets such that for distinct `i, j`, `F i ∩ F j ≠ ∅` iff `G (σ i) ∩ G (σ j) ≠ ∅` — and such a `σ` is precisely a graph isomorphism between the intersection graphs (`interGraph`, adjacency `i ≠ j ∧ (F i ∩ F j).Nonempty`; `isoOfPreserves` builds the `SimpleGraph.Iso` explicitly). This reading is the natural one for both the English ("redrawing pair preserving intersections") and the Chinese (交保留的显式重画对) texts, and it also holds a fortiori for stronger readings of "preserving intersections" (preserving the intersection poset, or the intersections as sets).

Because "intersection spectrum" is not defined in the source, the submission formalizes it as an arbitrary relation `SameSpectrum` and disproves the statement for every instantiation (`conjecture5640_false : ∀ SameSpectrum, ¬ Statement SameSpectrum`). This is the correct logical scheme: whatever the intended meaning is, it is one particular relation, and the contradiction between (B) and (C) never mentions the spectrum. The submission also handles the objection that the separating pair and the redrawing pair might be allowed to differ (`conjecture5640_separate_false`, where only the redrawing pair's existence is required — still contradictory), the nerve reading (`PreservesNerve` implies pairwise preservation by taking the two-point subfamily), and the one-sided reading (`KeepsInter`): for finite families, a one-sided redrawing together with equal edge counts already forces equality of the pulled-back graph with the intersection graph (`preservesInter_of_keeps`, via `SimpleGraph.edgeFinset_inj`), and when the spectrum is the adjacency characteristic polynomial, equal spectra force equal edge counts because `trace(A²) = Σλ²` is charpoly-determined (spectral theorem) and `trace(A²) = 2|E|` (`card_edges_eq_of_charpoly`) — so the adjacency-spectrum variant of the conjecture fails under the one-sided reading too. Non-vacuity is addressed (`sampleFamily`, `sample_redrawing`): the objects of the conjecture exist; it is the conjunction that is impossible.

The report is unusually honest about scope: it states that the refuted readings are the pairwise and nerve readings (for any meaning of "spectrum") and the one-sided reading whenever the spectrum determines the edge count, and it does not claim more. The transport argument mirrors the accepted disproof of the sibling conjecture 00000005400, which this competition has already accepted as the right treatment of a self-contradictory final clause. I verified the key lemma myself; it is a two-line argument (bijectivity of `σ` gives `i ≠ j ↔ σ i ≠ σ j`) and the formalization is exact.

Build hygiene: zero errors/warnings; axiom profile is the allowed minimum, replayed independently; the disproof uses no classical machinery beyond the standard three axioms.

## Issues found

- Minor: two entries of `verification/SHA256SUMS.txt` hash CRLF newline variants of `conjecture.md` and `proof.tex` (verified by re-hashing after newline normalization). Non-blocking hygiene issue.

## Verdict

APPROVED. The conjecture, as written, requires its separating pair to be a redrawing pair that preserves intersections, and any such pair is an isomorphism of the intersection graphs; the submission refutes the literal statement for every instantiation of the undefined "intersection spectrum", covers the plausible weaker and alternative readings, and documents the boundary of what it refutes.
