# Local verification record

This records author-side execution and independent internal scrutiny, not official maintainer acceptance.

## Faithful mathematical coverage

Both complete contribution guides and the exact bilingual source were checked at upstream `fe1d06d431b0591b65d759c60035b1d2e293a819`. Both languages explicitly assert strictly alternating coefficients for the ordinary KL polynomial of a parallel-thickened uniform matroid. The proof refutes this necessary sign clause with an actual two-copy thickening of U(3,4).

- `uniform` constructs the actual Mathlib matroid from the independence axioms, with independent sets precisely those of cardinality at most the specified rank.
- `thickened34` is the actual `Matroid.comap` of U(3,4) along the first-coordinate map on `Fin 4 × Fin 2`. Its ground set, independence condition, rank three, closure and actual rank formulas are proved. Looplessness, two-element parallel-class cardinalities and genuine two-element circuits are proved.
- `comapFlatOrderIso` proves that a surjective pullback preserves the entire actual flat lattice, including actual extended-natural ranks. The twelve-element presentation is proved order-isomorphic to all `Matroid.IsFlat` sets of the witness; it is not just a list of selected flats. Empty and full endpoints and finite actual ranks are established.
- The full Möbius incidence recurrences are proved and the finite values are identified with Mathlib's actual `IncidenceAlgebra.mu`. Characteristic polynomials sum over every flat in each genuine interval with the actual rank difference. The whole characteristic polynomial is proved to be `X^3 - 4*X^2 + 6*X - 3`.
- `IsKLFamily` is the standard ranked-flat characterization: diagonal value one, the strict half-rank degree bound on each positive interval, and the complete characteristic/KL recurrence including both endpoints. Reflection uses interval rank. The coefficient formulation of the degree bound includes the zero polynomial correctly and implies that no support exceeds the reflection rank.
- The candidate family is certified on every interval. Finite checks cover all five coefficients permitted by proved global degree bounds on both sides; the resulting identity is a full polynomial identity, not a truncated numerical test.
- A general induction proves uniqueness on all comparable intervals against arbitrary competing families. Values at incomparable pairs are unconstrained; no uniqueness is claimed there. Existence and uniqueness of each interval's polynomial value are proved separately.
- The entire Möbius/characteristic/KL construction is transported through the same proved order isomorphism onto the actual matroid flat subtype, with rank defined from actual `eRk.toNat`. Actual characteristic sums and both Möbius recurrences are proved there. The final polynomial is selected from proved existence and uniqueness of the actual bottom-to-top value, then derived to equal `1 + 2X`.
- The actual coefficients in degrees zero and one are one and two. Their positive product violates a necessary condition for strict alternation, allowing either starting sign. The formal target is this necessary sign instance of the full conjecture. No unspecified hypergeometric definition is invented, and no signed-variable substitution or direct-sum interpretation is introduced.

## Fresh independent execution

A separate verification agent copied only the seven Lean files and three configuration files to `/private/tmp/tlmc574-independent`. No compiled submission outputs were copied. The pinned dependency cache was reused; this was not a rebuild of all dependency sources.

| Check | Result |
|---|---|
| Lean compiler | 4.19.0, exact commit `6caaee842e9495688c1567e78c0e68dbb96942aa` |
| Mathlib | v4.19.0, exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| All nine dependency revisions | Exact manifest matches; tracked sources clean before and after |
| Fresh complete project build | Exit 0 |
| Direct strict replay of all seven Lean files | All exit 0, warnings treated as errors |
| Actual definition/abbreviation/structure printouts | All 30 matched |
| Actual theorem and instance type/axiom audits | All 80 matched: 75 theorems and five named instances |
| Transitive axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound` |
| Proof-bypass scan | No code matches |
| Source/config identity | All ten files identical and unchanged across both directories |

`verification/strict-replay.json` records commands, exit codes, emitted outputs, compiler identity, all pinned revisions and source hashes. `verification/build.txt` and `verification/axioms.txt` preserve the actual build and audit output. `Check.lean` prints the definitions and types actually being proved; expected names are reconciled against the emitted output rather than only counted from source. The scan includes admitted proofs, custom axioms, native decision proofs and kernel-bypass mechanisms. Finite computation is performed by ordinary kernel-checked Lean proofs. No auxiliary numerical program is required.

## Report and independent review

The exact final `main.tex` compiles successfully with the desktop editor compiler and Tectonic 0.17.0. All three final PDF pages were rendered with Poppler and visually inspected in full after the final edit. Page one contains the source scope and actual matroid; page two contains the complete recurrence, uniqueness argument and contradiction; page three contains formal scope and the primary reference. Text, formulas, conditions and references are legible. No clipping, overlap, missing glyphs, blank page or orphan reference page was found. The final TeX log has no warnings or overfull/underfull boxes. Text extraction supplies an additional content check.

`verification/pdf.json` records exact source/PDF hashes, compilation, rendering and visual inspection scope. `verification/report.txt` preserves the final TeX log with trailing whitespace removed. `SEMANTIC_REVIEW.md` records independent internal scrutiny of the exact bilingual source, all proof modules, report, documentation and verification evidence. The semantic reviewer, execution verifier and coordinating agent's PDF inspection are distinct; each record attributes its scope accurately.

## Eligibility and package identity

`verification/eligibility.json` preserves the initial live source/rule hashes, unsolved metadata, all-state PR/comment and topic searches, and current/historical solution-path checks. The snapshot covers 546 PRs through #550. Three KL topic matches concern unrelated Coxeter/Hecke conjectures; no prior or competing matroid submission for 00000000574 was found. No prior-error account applies to the checked records. `verification/prepublication.json` records the final refresh separately.

Only the personal submission folder is changed. Dependency folders, compiled Lean outputs and scratch probes are excluded. `verification/SHA256SUMS.json` covers every other submitted file, and exact staged Git bytes are checked against it before commit. These are checks at recorded times and within the stated search scope, not guarantees about future repository changes.
