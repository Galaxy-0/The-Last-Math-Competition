# Verification record for conjecture 00000002802

These are local validation and independent internal scrutiny records. Maintainer acceptance is a separate decision.

## Independent execution

A separate execution agent copied all six final Lean sources and three configuration files into a fresh directory without project build outputs. It independently scanned the actual source declarations, reconciled them with the complete audit inventory, and checked all frozen file hashes before execution. Cached dependencies were shared; project build outputs were fresh.

- Lean 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Fresh default `lake build`: exit 0. Its import graph includes every implementation module.
- Direct warnings-as-errors replays of all six Lean files, including `Check.lean`: all exit 0.
- The complete source inventory has 62 declarations: 13 definitions, 48 theorems and one named instance. All 13 definitions, all 49 theorem/instance types and all 49 transitive axiom lists were actually emitted and matched the requested targets.
- The probability instance `Conjecture2802.fairBernoulli_isProbabilityMeasure` was independently found as an instance declaration and required to occur exactly once in the inventory, emitted type checks and emitted axiom audit. There are no anonymous or private proof declarations.
- Every audited theorem and instance uses only `propext`, `Classical.choice`, and `Quot.sound`. The independent lexical scan found zero raw or code matches for admitted proofs, custom axioms, `native_decide`, execution shortcuts or kernel-trust modifications.
- All nine source/configuration hashes and the supplied inventory stayed unchanged. Copied files match the frozen originals. All nine manifest dependencies had exact revisions and clean tracked sources before and after execution; the compiler commit was also rechecked.

Execution finished at `2026-10-04T21:42:42.258869+00:00`. The fresh build took 8.001 seconds. Full commands, outputs, independent inventory reconciliation, dependency/compiler checks and identities are in `verification/strict-replay.json`. `verification/build.txt` is the build log; `verification/axioms.txt` is the actual definition, type and axiom output. `Check.lean` reproduces these audits.

## Mathematical fidelity and scope

The witness is the actual fair Bernoulli measure `(1/2) • dirac 0 + (1/2) • dirac 1` on the Borel real line. Its total mass, both atom masses, nondegeneracy and membership in the arithmetic lattice with offset 0 and positive spacing 1 are proved. The moment generating function is derived from the actual integral, not assigned to a surrogate distribution. Every real exponential tilt is integrable.

The Cramér rate is the actual extended-real supremum of `t*x - cgf id μ t`, restricted to parameters where the exponential is integrable. The restriction handles the library's totalized nonintegrable real integral correctly; for the witness it is proved equivalent to the full real-parameter supremum. The closed form is defined separately as an auxiliary expression, then identified with the supremum by a bound for every parameter and equality at the explicit optimizer `log x - log (1-x)`.

For every probability measure, the zero tilt proves rate nonnegativity. For the witness, the rate is finite on `(0,1)` and is positive infinity outside `[0,1]`. This proves `(0,1) ⊆ D ⊆ [0,1]` for `D = {x | I(x) < +∞}`, and hence `interior D = (0,1)`. Endpoint values and equality of the full effective domain with `[0,1]` are not claimed.

Ordinary topological support is defined by the usual open-neighborhood measure condition and proved to be `{0,1}`. Its real interior is empty, so the literal differentiability claim there is vacuous. Convex support is proved to be `[0,1]`, with nonempty interior `(0,1)`. It is never substituted silently for ordinary support. Both convex-support and effective-domain interior certificates are substantive.

Ordinary logarithm calculus proves a `ContDiffOn ℝ ∞` real representative on `(0,1)`. A one-way bridge turns a C² representative on an open set into the exact twice-differentiability predicate: differentiability of both the representative and its ordinary derivative, with pointwise equality to the actual EReal-valued rate. Mere twice differentiability is not identified with C² regularity, analytic order is not confused with C∞, and no totalized projection of infinity is used.

Both language versions entail the necessary implication from the stated differentiability to a non-lattice law. The final theorems refute this implication under the three explicit interior readings, even restricted to nondegenerate probability laws with every exponential moment. The restriction is a weaker universal consequence, not an assumption added to the source. The submission does not separately formalize or settle the unspecified variance-functional clause, periodic correction, converse implication or full Cramér large-deviation principle. All mathematical steps used for this counterexample are kernel-checked Lean proofs; no auxiliary numerical, simulation or symbolic program is used.

A separate semantic reviewer authored none of the proof, report or submission documentation. Its final review covers the exact bilingual source, both full current guides, all proof/configuration files, complete report and documentation, actual execution output, PDF verification and eligibility records. Its file-specific conclusions and input hashes are in `SEMANTIC_REVIEW.md`. Source-level semantic scrutiny is distinct from the independent execution and the visual page checks.

## Matching LaTeX report and PDF

The final source compiled successfully in the built-in LaTeX compiler. Tectonic 0.17.0 exported the matching 4-page PDF with exit 0 and no warning or box diagnostics. The report author and coordinating agent separately viewed every complete final rendered page. Both found no clipping, overlap, missing mathematical glyphs or problematic page breaks. The source, PDF and rendering identities are in `verification/pdf.json`; the normalized export log is `verification/report.txt` (only trailing log-line whitespace removed).

- `main.tex` SHA256: `ae973e03bee78c8198db83c2450d2d3119a2cad61c88bbb332d605071b70ca31`.
- `main.pdf` SHA256: `44a5e485183c7cd1df70ad4810e7c9e481c62552bf7e4c010bc5a1fed27fe94e`.
- PDF: 4 pages, 66,515 bytes.

## Eligibility and submission scope

The initial audit checked the exact bilingual source, both complete current contribution guides, unsolved metadata, 572 all-state pull requests through PR576, padded/short identifiers, English and Chinese topic/comment searches, and current plus historical solution paths. No previous or competing submission was found. All 45 broad lattice/Legendre topic leads were classified from full bodies; 24 nonempty discussions were read, with all 135 issue-comment/review/inline API responses preserved. Their lattice or Legendre topics concern other problems. The initial record is preserved unchanged in `verification/eligibility.json`.

The prepublication refresh examined 586 all-state pull requests through PR590. All new or changed full PR bodies and any new broad topic leads were classified, and the prior topic discussions were compared with their reviewed bytes. The exact source, both guides and unsolved metadata were checked again. The full search scope, timestamps, classifications, source hashes, prior-record identity and limitations are in `verification/prepublication.json`.

Only the prescribed personal submission folder is included. The bundled conjecture is a byte-for-byte copy of the official source. No official conjecture, guide, metadata, leaderboard or review file is changed. `verification/SHA256SUMS.json` hashes every submitted file except itself. Eligibility is a timestamped search result, not a guarantee about future submissions.

## Frozen Lean file identities

Paths below are relative to `lean/`.

| File | SHA256 |
| --- | --- |
| `Conjecture2802/Law.lean` | `5371b69f5e2c75a3db077507a6a0607f61978c8fe9898b22277412d3facc6707` |
| `Conjecture2802/Formula.lean` | `17aea3d3c0448ae243de5107e86e74d620db36455fac8556777ed4514e0fd091` |
| `Conjecture2802/Transform.lean` | `d484c5c1c66cbfee6b231fae2620991f56fd27acff2c0d19ba686ee650ea423d` |
| `Conjecture2802/Regularity.lean` | `8254e9f00f4a574b4293f4d1b6fcaec9d3c81e626206b8aeee387022bbf258ea` |
| `Conjecture2802.lean` | `9d3b1af90220e4469adac3b3c2a3eceb9509e5ffe069cf99d443bc08a56991ae` |
| `Check.lean` | `e010117bd01a983ce5dec88e6b799e1ae031fa97ccbd80e081b5eadfb12b73f1` |
| `lakefile.toml` | `139d77b2432e6fece9416bbea4ddeccffa7ee85e1a493fe16b63098c92b3d74b` |
| `lake-manifest.json` | `bf70b08ac67109e303ee4a5cc7168b68799e60b8cb5fb88cb081185bac299bda` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
