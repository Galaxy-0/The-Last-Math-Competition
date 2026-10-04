# Verification record for conjecture 00000000978

These are local validation and independent internal scrutiny records. Maintainer acceptance is a separate decision.

## Independent execution

A separate execution agent copied all six final Lean files and three configuration files into a fresh directory without project build outputs. It independently reconciled every actual source declaration with the complete audit inventory and checked all frozen source/configuration hashes before running the proof.

- Lean 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Fresh default `lake build`: exit 0. Its import graph covers every implementation module.
- Direct warnings-as-errors replays of all six Lean files, including `Check.lean`: all exit 0.
- Actual emitted output includes all 20 definitions and all 50 theorem types and transitive axiom lists, matching the complete 70-declaration source inventory. There are no named instances, anonymous or private proof declarations.
- Every theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. The independent lexical scan found zero raw or code matches for admitted proofs, custom axioms, `native_decide`, execution shortcuts, or kernel-trust modifications.
- All nine source/configuration hashes and the supplied inventory stayed unchanged. The copied files match the frozen originals. All nine manifest dependencies had exact revisions and clean tracked sources before and after execution; the compiler identity was rechecked too.

The run finished at `2026-10-04T21:10:19.734164+00:00`. Its fresh build took 8.448 seconds. Full commands, outputs, independent source-inventory reconciliation, dependency/compiler checks and identities are in `verification/strict-replay.json`. `verification/build.txt` is the build log; `verification/axioms.txt` contains the actual definition, theorem-type and axiom output. `Check.lean` reproduces those audits.

## Mathematical scope

The witness is the actual complex matrix `[[0,2],[0,0]]`. Its conjugate-transpose Hermitian parts give the genuine determinant polynomial `w²-u²-v²`, with actual polynomial derivative gradient `(-2u,-2v,2w)`. The formalization proves the generic evaluation/determinant bridge and the witness's degree, homogeneity, projective smoothness, nilpotence and characteristic polynomial `X²`.

The dual cone is the actual complex `zeroLocus (vanishingIdeal ...)` of all nonzero scalar multiples of gradients at nonzero smooth polynomial zeros. The polynomial vanishes on this image and hence its closure. Conversely, every point `(x,y,1)` on the complex conic is already in that image. These two directions prove the exact complex affine-chart identity, then the real-chart unit-circle identity. No whole-cone equality, general reduced-polynomial construction, or universal Kippenhahn theorem is assumed.

The numerical range is the actual Hermitian quadratic form on vectors whose sum of squared coordinate norms is one. Its equivalence to the usual Hermitian unit equation is proved. Both disk inclusions are proved; the reverse inclusion constructs an actual unit vector for every point of the disk. The topological boundary is the complex unit circle. The real algebraic boundary is defined as the real Zariski closure of that frontier in real coordinates, and the polynomial zero-locus identity proves that this closure equals the circle.

An injective rational parametrization by all real numbers proves that both real curve constructions are infinite. Extended cardinality (`Set.encard`) retains infinity, so every finite bound fails. The final theorem negates the necessary dimension-two specialization of the source, even with a homogeneous projectively smooth determinant pencil. Separate theorems negate the dual-chart specialization and the unrestricted all-dimension real-algebraic-boundary bound. The source's real-point count is not silently restricted to isolated points, singularities or components; no normality or simple-spectrum hypothesis is added.

No auxiliary mathematical program, numerical approximation or simulation is used. The only mathematical computations are kernel-checked Lean proofs. The external background reference explains conventional projective duality; no cited numerical or symbolic output replaces a proved bridge.

The separate semantic reviewer authored none of the proof, report or submission documentation. Its final review covers the exact bilingual statement, both current guides, complete proof/configuration files, full report and documentation, and the actual execution and eligibility records. Its file-specific conclusions and scope are in `SEMANTIC_REVIEW.md`; its source review is distinct from the independent execution and visual page checks.

## Matching report and PDF

The final source compiled successfully in the built-in LaTeX compiler. Tectonic 0.17.0 exported its matching 4-page PDF with exit 0 and no warning or box diagnostics. The report author and coordinating agent separately viewed every complete final rendered page; both found no clipping, overlap, missing mathematical glyphs or problematic page breaks. Exact source, PDF and page identities are in `verification/pdf.json`. The normalized compiler log is `verification/report.txt`; only trailing log-line whitespace was removed.

- `main.tex` SHA256: `6ab3fc6fac1dcbf8643ce1dcef02a910587b927536a1cf54ed130096b443f477`.
- `main.pdf` SHA256: `06c852069416ec5fd48f0603810cca0b41646e43c88c142b12a7b20de6b04b13`.
- PDF: 4 pages, 69,389 bytes.

## Eligibility and package scope

The initial audit checked the exact bilingual source, both complete current contribution guides, unsolved metadata, 565 all-state pull requests through PR569, padded/short identifiers, English and Chinese topic/comment searches, and current plus historical solution paths. No prior or competing submission was found. The two broad Chinese indexed discussion hits were read fully and classified as unrelated: PR5 is an administrative corpus-scoring discussion, and PR511 concerns the rank bound in conjecture8822. Neither discusses a solution to conjecture978.

The prepublication refresh examined 570 all-state pull requests through PR574. New PR bodies were read and classified as unrelated; the complete direct discussions for PR5/511 were fetched again and matched the previously reviewed bytes. The exact source, both guides and unsolved metadata stayed unchanged. All timestamps, search results, classifications and limitations are preserved in `verification/prepublication.json`; the unchanged original record is `verification/eligibility.json`.

Only the prescribed personal submission folder is included. The bundled conjecture is a byte-for-byte copy of the source. Official conjectures, guides, metadata, leaderboard and review files are not modified. `verification/SHA256SUMS.json` hashes every submitted file except itself. Eligibility is a timestamped search result, not a guarantee about future submissions.

## Frozen Lean file identities

Paths are relative to `lean/`.

| File | SHA256 |
| --- | --- |
| `Conjecture978/Pencil.lean` | `0e898f9552e9ed8b63382125db4965f748c995fd29e49d7005ed56cff7950532` |
| `Conjecture978/DualCurve.lean` | `8477f12ddcd824eb1b0ffd270afd993670062c5e39da47466408dec612397ea8` |
| `Conjecture978/NumericalRange.lean` | `850c01ba06a9fc30d8843e74c9cbe895ff810b2347944b48ec021df0890b5bba` |
| `Conjecture978/Boundary.lean` | `6ce6305dc1bf664ba45aef1d7929a219275d094fea2a340fd9d12f94ee6a192d` |
| `Conjecture978.lean` | `ad6451d360443f1ab7f847bd455c18640dfcb37cf3ad50c60f4d4e8e6f8daaa6` |
| `Check.lean` | `26f568645629c12f47ec41eb6db841c1928ee8932c80ac5785ba1551da76a78b` |
| `lakefile.toml` | `86b4473ea2f0a0546cb730d30e7548b8900bf34d0b5d39aede68058396213922` |
| `lake-manifest.json` | `7db95ab4e82070da47d81ecc01cada3a24cacd461b7c8a4b4d2cce85d3d9ff96` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
