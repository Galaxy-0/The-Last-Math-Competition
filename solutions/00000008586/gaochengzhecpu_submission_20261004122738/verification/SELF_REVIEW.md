# Authoring-agent self-review of 00000008586

Reviewer: the agent developing this submission. This is not an external independent review.

## Adversarial checks against the source

1. **Was the source's definition replaced by the conventional one?** No. `statedRange` uses the printed condition that the k-dimensional isometric compression of `lambda I - T` have rank at most `k-1`. The conventional scalar-compression range is explicitly separate. Both give the same failure of the claimed direction of inclusion for the exhibited point.
2. **Are the frames actual isometric embeddings?** Yes. They are complex matrices with `Qᴴ * Q = I`. A general Lean theorem proves that this matrix equation induces an actual `Isometry` between standard complex Euclidean spaces, via the Hilbert-space adjoint bridge.
3. **Is the first-order membership exact?** Yes. The concrete column has both entries `1/sqrt(2)`. Lean proves the square of this real normalization embedded into the complex numbers is 1/2, then calculates `QᴴQ=1` and `QᴴTQ=1/2`.
4. **Does second-order exclusion check only the identity compression?** No. It quantifies over every complex two-by-two Q satisfying `QᴴQ=I`. Multiplicativity of the determinant yields the fixed nonzero determinant -1/4 for every compression. Mathlib's actual matrix invertibility and rank results then give rank 2.
5. **Is matrix rank a numerical label?** No. It is Mathlib `Matrix.rank`, defined by the dimension of the image of the corresponding linear map. The value 2 follows from invertibility and the actual matrix dimension.
6. **Could complex phases alter the answer?** No. Q is an arbitrary complex frame, and the conjugate transpose is used throughout. The determinant argument applies to all complex entries.
7. **Could the source's later nonemptiness threshold restrict the inclusion?** The inclusion is stated unconditionally in both languages. The later generic nonemptiness statement is separate. The delivered claim refutes this unconditional inclusion, using the valid dimensions 1 and 2 in a two-dimensional space. It makes no claim about a revised restricted statement.
8. **Is the witness non-Hermitian or unbounded?** No. It is the finite Hermitian matrix diag(0,1). Lean checks its conjugate transpose equals itself. Finite-dimensional compression suffices to refute the universal claim.
9. **Does finite numerical testing masquerade as a proof for all frames?** No. Lean proves the universal exclusion. The Python cross-check expands the exact polynomial identity with eight independent indeterminates; it performs no floating-point or random sampling.
10. **What remains outside the delivered conclusion?** General compactness, the proposed generic nonemptiness threshold, polynomial boundary envelopes, and a full general theory of higher-rank numerical ranges. The disproof of one universal conjunct is complete without those claims.

## Validation record

Actual commands, exit codes, source hashes, nine theorem-axiom lists, auxiliary algebra output, PDF compilation, rendered-page locations, and final visual-review status are recorded in `BUILD.json` and the adjacent logs. The visual PASS field is set only after every final page is opened with `view_image`. Parent review and current upstream duplicate/source checks are separate steps before publication.

- Fresh `lake build` and direct Lean with warnings treated as errors: passed.
- All nine printed theorem-axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Exact Python checks: passed, including the generic determinant identity expanded over eight independent indeterminates.
- Final Tectonic export: exit code 0, two pages, no TeX warnings or overfull boxes. The log retains the platform's Fontconfig default-configuration/cache messages; all actual fonts and mathematical glyphs were reviewed and render correctly.
- Both final page images under `round5/qa/00000008586/6542f1afc7f5/` were opened with `view_image`. No clipping, overlap, missing symbols, or overflowing equations were found.
- The source SHA-256 and byte-for-byte equality to the fresh raw statement were verified.
