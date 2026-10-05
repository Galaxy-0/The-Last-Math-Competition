# Verification record for conjecture 00000007718

These are local validation and independent internal scrutiny records. Maintainer acceptance is a separate decision.

## Independent execution

A separate execution agent copied all five final Lean files and three configuration files into a fresh directory without project build outputs. It independently scanned the actual declarations, reconciled them with the complete audit inventory, and checked every frozen file hash before execution. Cached dependencies were shared; project build outputs were fresh.

- Lean 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Fresh default `lake build`: exit 0. Its import graph includes every implementation module.
- Direct warnings-as-errors replays of all five Lean files, including `Check.lean`: all exit 0.
- The complete source inventory has 64 declarations: 21 definitions/abbreviations and 43 theorems, with no named instances or anonymous/private proof declarations. All 21 definitions, 43 theorem types and 43 transitive axiom lists were actually emitted and matched the requested targets.
- Every theorem uses only `propext`, `Classical.choice`, and `Quot.sound`, or a subset. The independent lexical scan found zero raw or code matches for admitted proofs, custom axioms, `native_decide`, execution shortcuts or kernel-trust modifications.
- All eight source/configuration hashes and the inventory stayed unchanged. The copied files match the frozen originals. All nine manifest dependencies had exact revisions and clean tracked sources before and after execution; the compiler commit was also rechecked.

Execution finished at `2026-10-04T22:15:28.295423+00:00`. The fresh build took 6.253 seconds. Full commands, outputs, inventory reconciliation, dependency/compiler checks and identities are in `verification/strict-replay.json`. `verification/build.txt` is the build log; `verification/axioms.txt` contains the actual definition, type and axiom output. `lean/Check.lean` reproduces these audits.

## Mathematical fidelity and scope

The construction starts with actual words on `Fin 3`, using repetition and concatenation. Matrix columns are defined by `List.count`; their displayed entries are proved. Every word has length `3m+3` and is nonempty. For `m ≥ 1`, every letter occurs in every single-letter image, proving the standard word-iteration primitivity condition. Positivity of the first matrix power is also proved directly. The matrix is symmetric, so changing the row/column convention has no effect.

The geometric certificate uses three colored unit intervals and the actual word entries as colors. Adjacent closed unit intervals cover the full expanded interval, including its right endpoint; their actual interiors are pairwise disjoint. Each tile is a translate of the correctly colored prototile. Reconstructing the word from the tile colors proves that the geometric incidence counts agree with the word-count matrix. This is a finite geometric substitution rule, with expansion greater than one.

The spectrum is Mathlib's actual complex matrix spectrum. The determinant of the actual resolvent is computed and linked to spectral membership through noninvertibility. The actual characteristic polynomial factors as `(X-(3m+3))(X-3)(X-1)`. For `m ≥ 1`, these three roots are strictly ordered and positive, hence simple. The proof identifies the greatest spectral modulus as `3m+3` and the greatest modulus after removing the Perron value as `3`. It additionally proves an actual strictly positive Perron eigenvector and actual matrix rank three.

`OrderedSpectralData` requires this characteristic polynomial and the actual maximum-modulus statements, not a list of numbers assigned eigenvalue labels. `AdmissibleRatio` quantifies over primitive, nonempty, three-letter geometric substitutions with full-rank matrices and ordered simple positive spectra. Every family member with `m ≥ 1` has such a certificate. The extra restrictions specify a subclass, so a universal lower bound asserted by the source must hold on this subclass as well.

The ratio is exactly `3/(3m+3)=1/(m+1)`. At `m=2`, it is `1/3`; the inequality `1/3 < (3-√5)/2` is proved from the exact square and nonnegativity of the real square root. `conjecture_00000007718_false` negates the necessary universal lower-bound consequence, not merely an isolated inequality. The Archimedean property supplies `m` with `0 < ratio_m < ε` for every `ε > 0`, yielding both no positive universal lower bound and no least positive admissible ratio.

The source does not separately define `r`. The submission states its alphabet/matrix-size convention explicitly and also proves rank three. It does not silently interpret `r` as ambient dimension or algebraic degree. Neither language adds aperiodicity, unimodularity, irreducible characteristic polynomial or a substitution-length bound. The finite geometric rule suffices for the explicit matrix-ratio clause. No infinite fixed tiling, hull, invariant measure, pattern-frequency calculation, or aperiodicity theorem is claimed as formalized. The trace-error and algebraic-degree conjuncts are not separately settled; the false minimum clause already refutes the conjunction.

All mathematical steps used in this disproof are kernel-checked Lean proofs. No auxiliary numerical, simulation or symbolic program supplies a mathematical result.

A separate semantic reviewer authored none of the proof, report or submission documentation. Its final review covers the exact bilingual source, both complete current guides, all proof/configuration files, complete report and documentation, actual execution output, PDF verification and eligibility records. Its conclusions and exact input hashes are in `SEMANTIC_REVIEW.md`. Source-level semantic scrutiny is distinct from independent execution and visual page checks.

## Matching LaTeX report and PDF

The final source compiled successfully in the built-in LaTeX compiler. Tectonic 0.17.0 exported the matching 4-page PDF with exit 0 and no warning or box diagnostics. The report author and coordinating agent separately viewed every complete final rendered page. Both found no clipping, overlap, missing mathematical glyphs or problematic page breaks. Source, PDF and rendering identities are in `verification/pdf.json`; the export log is `verification/report.txt`.

- `main.tex` SHA256: `a80a1ba11afd92dab6310de5b6a8d21405c3352fdcc05c8e6511454d87dd71aa`.
- `main.pdf` SHA256: `7d98006f2344e5e9ff3601e2fd9c7c49f9c4ab43a220214816075bbd227168c4`.
- PDF: 4 pages, 67,894 bytes.

## Eligibility and submission scope

The initial audit checked the exact bilingual source, both complete current guides, unsolved metadata, 587 all-state pull requests through PR591, padded/short identifiers, English and Chinese topic/comment searches, and current plus historical solution paths. No prior or competing submission was found. Thirteen broad topic leads were classified from their full bodies and all available direct discussions. The closest substitution/Perron submissions concern different conjectures: PR80 on factor complexity, PR426 on non-real Tribonacci eigenvalues, and PR546 on minimal Perron matrix realizations. The initial record is preserved unchanged in `verification/eligibility.json`.

The prepublication refresh examined 587 all-state pull requests through PR591. New or changed full bodies, indexed searches, relevant topic discussions, current/historical solution paths, source, guides and metadata were checked again. Search scope, timestamps, classifications, source identities and limitations are recorded in `verification/prepublication.json`.

Only the prescribed personal submission folder is included. The bundled conjecture is a byte-for-byte copy of the official source. No official conjecture, guide, metadata, leaderboard or review file is changed. `verification/SHA256SUMS.json` hashes every submitted file except itself. Eligibility is a timestamped search result, not a guarantee about future submissions.

## Frozen Lean file identities

Paths below are relative to `lean/`.

| File | SHA256 |
| --- | --- |
| `Conjecture7718/Substitution.lean` | `6c49b67e44b22af1a6a8e428ad1278a551bba0719b3e68b80f18237ed0296cd8` |
| `Conjecture7718/Tiling.lean` | `2aeb6d5894b35209701264619df9e80cda785161058e899475836a23c0dabf41` |
| `Conjecture7718/Spectrum.lean` | `5a58456c04605acf19ad4af374f774efcff09721ec4a5a4b00b12a03c65603c6` |
| `Conjecture7718.lean` | `8b810dc00bdf3f3740e18bceca899f5ddaad2b8a0a79108efa55430bb7558857` |
| `Check.lean` | `417b68fee198b487e8936b98a2ef02137c858913805db2fbf9c49221de9bb38f` |
| `lakefile.toml` | `fd8a99266a1ecc51a16d7fa79e683889d7a5e7e6df8109cfff1496d9cff1b3e0` |
| `lake-manifest.json` | `781674693be1bf96bd27a7f4ecc0e44db0878908d554b6f504ba1b4b30be9b43` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
