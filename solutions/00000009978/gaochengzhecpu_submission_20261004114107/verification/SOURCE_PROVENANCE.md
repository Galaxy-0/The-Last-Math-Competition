# Source provenance: 00000009978

`SOURCE.md` contains the upstream file bytes with no added heading, normalization, or appended newline.

- Read-only source URL: https://raw.githubusercontent.com/The-Last-Math-Competition/The-Last-Math-Competition/main/conjectures/00000009978.md
- Checked at UTC: 2026-10-04T11:28:54.948796+00:00
- Git blob SHA: `28a28faca3962f4717c823078d1129cd17b9d55b`
- SHA-256: `9db4b12bbd00f619351bd7c4f39f6ac5a38c6190ae831ee33ccce53b6b2620e8`
- Blob identity matches the supplied `round5/upstream-tree.json` snapshot.
- The supplied metadata has proven=false and disproven=false; no same-ID PR was found in the supplied all-pull-requests snapshot. Parent will repeat the live duplicate check before publication.

## Statement and definition boundary

The finite-termination clause is explicit in both language versions. Neither imposes an Artinian or finite-dimensional-ring hypothesis. We use the descending finite intersections F_N = intersection_{0 <= j <= N} J(R)^j and prove F_N = J(R)^N. A zero infinite intersection is a different assertion and is proved for the same counterexample.

The counterexample is the actual formal power series ring R = Q[[X]], which Mathlib proves is Noetherian. Its commutative FBN qualification is proved from the standard prime-quotient/essential-ideal condition, rather than asserted as a label.

## Definition reference

S. Caenepeel and T. Guedenon, *Fully bounded noetherian rings and Frobenius extensions*, arXiv:math/0503686v3 (2006), Introduction, page 1: https://arxiv.org/pdf/math/0503686v3 . The paper states the prime-quotient and essential-right-ideal criterion and notes that commutative Noetherian rings satisfy it. Our text paraphrases that definition; Lean verifies its specialization to the exhibited commutative ring.
