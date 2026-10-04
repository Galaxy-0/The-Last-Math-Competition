# Solution Review — Conjecture 00000003476 (PR 491)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004153343`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — subdividing any edge of `K9` has low betweenness but increases the Wiener index.
- Eligibility: base metadata is unsolved; the earlier unsound/closed PR 225 is not a solved submission.
- LaTeX: independent build exit 0, two A4 pages, references resolved; shipped/fresh content matches.
- Lean: shared official pinned dependencies linked; `lake build` exit 0 (`[977/978] Built Main`) and direct warnings-as-errors elaboration exit 0.
- Axioms: all ten audited theorems use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none.
- Hashes: all validation hashes match.
- Auxiliary programs: none needed.
- Non-blocking hygiene: CRLF endings in some evidence/config files cause whitespace-check reports but do not affect correctness.

## Semantic audit

For an edge `e={a,b}` of `K9`, the unique shortest path for each distinct pair is the direct edge, so exactly one unordered pair contributes to edge betweenness: `B(e)=1<9/4` (or 2 under the ordered convention, still below 9/4). The Wiener index is 36. Subdivision creates a connected 10-vertex graph; its 45 unordered distances are all positive, already forcing Wiener index at least 45, and the exact distance analysis gives 53. Therefore the conjectured decrease is false while the betweenness condition is true. Lean defines actual Mathlib graphs, subdivision, distances, shortest walks, Wiener index, and both betweenness conventions; proves the complete-graph walk counts; proves connectivity; proves the Wiener increase; and negates both universal readings of the criterion. This is genuine graph-level non-isomorphism to the earlier arithmetic-only attempt and is non-vacuous.

## Verdict

APPROVED — the `K9` counterexample and its complete graph-level formalization decisively refute the stated criterion.
