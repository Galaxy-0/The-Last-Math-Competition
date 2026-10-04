# Authoring-agent adversarial review

This is self-review by the proof's authoring agent, not an external independent review. A parent review is required before publication.

## Statement and asymptotic scope

- Both source languages quantify over every fixed prime and discuss degrees tending to infinity; neither excludes the prime 2 nor restricts to odd degrees.
- A single small-degree failure would be insufficient. The formal proof covers every even degree at least 2 and explicitly gives a degree beyond every threshold.
- The formalized claim is eventual validity for each fixed prime. The family also rules out validity at density one, since every even degree fails. No claim is made about the separate weaker assertion that infinitely many successful degrees might exist.
- `SOURCE.md` is copied byte-for-byte from the parent's current raw source, without a provenance prefix.

## Polynomial and field-theoretic objects

- The source polynomial is an actual element of `Q[X]`; its degree is derived for every `d>=2`.
- The rational-root calculation is proved generically from evenness. The factor theorem provides a genuine rational polynomial quotient, and its degree `d-1` follows from the degree of a product of nonzero polynomials.
- The quotient is nonzero because the original polynomial has degree at least 2. No silent cancellation or zero-polynomial degree convention is used.
- The group is Mathlib's `Polynomial.Gal`, the rational algebra automorphisms of an actual splitting field. It is not an arbitrary finite group introduced as a surrogate.
- The general factorial bound comes from a faithful action on actual roots. The root cardinality is at most the degree, so repeated-root issues cannot invalidate the upper bound.
- A rational linear factor has trivial Galois group. Mathlib's injective restriction homomorphism for a product then bounds the group's cardinality by that of the quotient's group.
- The final obstruction concerns an actual `MulEquiv` to the full symmetric group, not merely intransitivity in a chosen representation. The strict factorial inequality rules out abstract isomorphism as well.

## Generic and finite checks

- All polynomial, cardinality, and group-theoretic claims are proved for arbitrary allowed degrees in Lean.
- The optional Python script checks exact polynomial arithmetic for six sample degrees. Its output explicitly disclaims exact Galois-group computation; it is supplementary evidence only.
- Direct Lean with warnings treated as errors passed after the final proof edit, and the eight printed theorems depend only on standard foundational axioms.
- Fresh-build and actual export results are recorded in `BUILD.json` and their logs. The submission's own Lean artifacts are not reused for the clean build.
- The native compiler's platform failure is preserved honestly; Tectonic produces the delivered PDF. Every final rendered page must be viewed before setting `pdf_visual_review` to exact `PASS`.
