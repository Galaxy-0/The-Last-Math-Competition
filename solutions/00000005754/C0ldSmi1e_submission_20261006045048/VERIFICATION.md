# Verification of conjecture 00000005754

## Mathematical coverage

`Counterexample5754.continuous_valuation_counterexample` supplies a concrete continuous Hahn valuation whose intrinsic value group is not any integer power. `mem_valueGroup_iff` identifies the group with exactly the finite values attained at nonzero elements. `valueGroupEquiv` identifies it with the rationals. `valueGroup_not_integer_power` is universe-polymorphic in the index type; the bundled theorem also explicitly negates every natural-rank power.

The exact domain topology is the topology induced by `Valued.mk' valuation`. Continuity is proved for two explicitly checked codomain topologies. The independent semantic review read both originals, the complete report, the mathematical source, and the supporting standard-library definitions. It found no material issue; its scope and interpretation limits are recorded in `verification/semantic-review.json`.

## Builds and proof audit

- Independent fresh full project build succeeded with Lean 4.19.0 and the pinned nine dependencies (`verification/root-rebuild.json`). Missing standard Hahn-series dependencies were built normally by Lake.
- Portable verification rebuilds the authored project from the frozen submitted input files and replays `Counterexample.lean`, `Inspect.lean`, `SemanticChecks.lean`, and `Audit.lean` with warnings treated as errors.
- The compiled inventory contains 24 mathematical declarations, including 6 generated declarations. Every type and direct dependency is compared with `verification/compiled-inventory.json`; transitive axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.
- There are no proof placeholders, custom axioms, unsafe mathematical definitions, or native decision proofs in the mathematical source. `Audit.lean` is a separately reviewed metaprogram for inspection, not a mathematical assumption.
- The portable runner checks package revisions and tracked-source cleanliness before and after execution and verifies that frozen inputs remain unchanged.

`verification/portable-verification.json` records the final portable run. `verification/verifier-controls.json` and `verification/verifier-unit-tests.txt` record 19 controls and three actual compiled negative fixtures. The latter must reject a custom axiom, an unsafe definition, and a proof placeholder; strict source replay also rejects the placeholder fixture. Their deliberate nonzero exit codes are expected test outcomes. No external numerical or symbolic computations are required by this proof.

## Report and identities

The native LaTeX compiler succeeded. Tectonic exported the matching four-page PDF, and all four rendered pages were visually inspected. The final export has empty stderr and no TeX warning, overfull, or underfull diagnostics. Records are `verification/pdf-export.json`, `verification/report.log`, and `verification/pdf-visual-review.json`.

`verification/source-manifest.json` binds the portable verification inputs. The top-level `SHA256SUMS.json` binds all submitted files except itself. `verification/author-freeze.json` preserves the historical author-side freeze, including scratch-file identities; its initial report hash predates root updates to verification prose and typesetting. The final report/PDF identities are bound by the top-level manifest, PDF records, and final semantic review. The mathematical source remained identical throughout packaging. Author scratch files are not needed to reproduce the submitted proof; the complete pinned Lean project and portable verification are included.

These records document local validation, not maintainer acceptance.
