# Authoring-agent adversarial review

This self-review is by the agent that adapted and built the proof. It is not an external independent review; parent review is required before publication.

## Quantifiers and reuse

- Both source languages quantify over every fixed nonzero integer, with degrees tending to infinity. The final Lean proposition uses `p : Int` and `p != 0`, not the prime predicate from Conjecture 95.
- The witness constant is exactly the nonzero integer 2. For every threshold, the generic proof produces an even degree beyond it, so the result is not merely a finite exception to an eventual claim.
- The constant-2 rational-root construction and general Galois lemmas are shared with the solution of 95. This is plainly disclosed in the paper and README and is not described as a different mathematical construction.
- The project is independently complete: all local proof code is in its own Main module and no cross-submission imports or PR dependencies are used.
- The exact source bytes are preserved separately from provenance text.

## Full mathematical chain

- The polynomial is the actual `Q[X]` object with an integer constant mapped into the rational field. Its degree is proved for every degree at least 2.
- Evaluation at `-1` is zero for every even degree. The actual polynomial factor theorem yields the quotient; the quotient is nonzero and has degree one less than the original.
- The group is the actual automorphism group of a splitting field. A faithful permutation action on the actual roots supplies the factorial order bound.
- A rational linear factor has trivial Galois group. The injective restriction map for a product bounds its Galois group by the quotient's group.
- No assumption of quotient irreducibility is used. Counting distinct roots by degree suffices even without a separate separability proof.
- The contradiction is to an actual abstract `MulEquiv` with `S_n`. Reducibility alone is not substituted for the required conclusion.

## Actual verification

- Direct Lean with warnings treated as errors passed for the final integer-parameter proof. Eight printed generic results depend only on standard axioms.
- The fresh build and exact source hashes are recorded in BUILD.json; no prior Main artifacts are reused.
- The auxiliary exact arithmetic samples do not compute Galois groups and are explicitly labeled as supplementary checks.
- Native LaTeX compilation has the documented platform-directory failure. The actual PDF comes from Tectonic, with every final rendered page reviewed before `pdf_visual_review` is set to exact `PASS`.
