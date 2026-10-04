# Solution Review — Conjecture 00000002604 (PR 488)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004152418`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — the source claims layer-vector rigidity; two nonisomorphic eight-element distributive lattices refute it.
- Eligibility: clean-base metadata is unsolved; the earlier invalid PR 48 was removed and is not a solved base submission. This PR adds only its own directory.
- LaTeX: independent build exit 0, three A4 pages, no substantive warnings; shipped/fresh content matches.
- Lean: official shared pinned dependencies linked; `lake build` exit 0 (`[795/796] Built Main`) and direct warnings-as-errors elaboration exit 0.
- Axioms: all eleven printed central theorems use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none in Lean source.
- Hashes: all supplied validation hashes match.
- Auxiliary programs: none needed.
- Non-blocking hygiene: CRLF endings in some evidence/config files cause `git diff --check` trailing-whitespace reports but do not affect correctness or builds.

## Semantic audit

`C4×C2` and `(C3×C3)\{(2,0)\}` are genuine distributive lattices: the second is proved closed under ambient joins and meets. Both have eight elements and rank layers `(1,2,2,2,1)`; because both top elements have rank 4, their corank/coatom-layer vectors are also equal. Nevertheless `(1,1)` in the second lattice has two incomparable elements below and above, while no element of the product has that order-invariant branch-point property. Lean proves the actual lattice structures, rank and corank covering laws, every layer equality, and `IsEmpty (L1 ≃o L2)`. This is true non-isomorphism, unlike the earlier PR's theorem that merely said not every bijection was an isomorphism. The negated universal rigidity claims are faithful and non-vacuous.

## Verdict

APPROVED — the equal-layer nonisomorphic pair decisively disproves the rigidity conjecture, and the corrected formalization independently builds with standard axioms only.
