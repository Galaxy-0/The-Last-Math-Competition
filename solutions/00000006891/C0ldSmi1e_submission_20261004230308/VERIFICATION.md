# Verification of conjecture 00000006891

These are local validation and independent internal review records. They do not assert maintainer acceptance.

## Independent formal execution

A separate agent copied the six frozen Lean files and three pinned configuration files to a fresh project directory with no project build outputs. It shared only the cached dependencies. Its independent source scanner reconciled every authored declaration with the supplied audit inventory before execution.

- Lean 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Fresh default `lake build`: exit 0; all five implementation modules are in its import graph.
- All six source files, including `Check.lean`, replayed with warnings treated as errors: every exit code 0.
- Complete authored inventory: 102 declarations, comprising 33 definitions/abbreviations and 69 theorems, with no authored instances. Every definition, theorem type and transitive theorem axiom list was actually emitted and reconciled.
- Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, or a subset. The source scan found no admitted proof, custom axiom, `native_decide`, unsafe declaration or kernel-trust modification.
- All nine source/configuration files and the declaration inventory retained their frozen hashes. Every one of the nine dependency repositories had the exact lockfile revision and clean tracked sources before and after execution. Compiler identity was also rechecked.

The additional environment audit enumerated every constant by its actual originating module, without a name-prefix filter. All 147 constants were emitted and audited: the 102 authored declarations plus 45 generated declarations. This includes generated proofs, equations and runtime support constants. Eleven `_cstage1`/`_cstage2` compiler-generated runtime artifacts are identified separately from the safe authored kernel declarations; they remain in the audit. There were no unexpected unsafe constants, partial declarations or axiom declarations, and all transitive axiom lists used only the same standard foundational axioms.

All 102 authored declarations are safe. The environment-inventory harness is read-only, inspection-only metaprogramming and is not imported by any proof module. It prints existing types and collects axiom dependencies; it proves none of the submitted mathematics. Its source, complete output and structured inventory are included under `verification/`. To reproduce it after building, run `lake env lean -DwarningAsError=true ../verification/environment-inventory.lean` from `lean/`.

Independent execution finished at `2026-10-04T22:52:14.640476+00:00`. The fresh default build took 14.745 seconds. `verification/strict-replay.json` contains commands, results, identity checks and declaration reconciliation; `build.txt`, `axioms.txt` and `environment-inventory.txt` preserve actual output.

## Semantic fidelity

The tensor space is Mathlib's actual nested tensor product of three copies of `Fin 2 → ℂ`. A tensor-product basis supplies a genuine coordinate linear equivalence; pure tensors have the expected coordinate products. Every tensor has a finite simple decomposition by basis expansion. `tensorRank` is the true minimum of these decomposition lengths, and the proof establishes zero padding and invariance under nonzero scaling.

The W tensor has the three displayed simple summands and no two-summand decomposition. The lower bound eliminates the two first-factor slices using polynomial identities without dividing by a potentially zero determinant. It then uses the absence of nonzero square-zero complex numbers and the nonzero 100-coordinate. Every algebraic calculation is a kernel-checked Lean proof.

The geometry uses actual `Projectivization` points and `Projectivization.Subspace.span`. Its generic bridge proves that projective span membership is equivalent to membership in the vector submodule span of chosen nonzero representatives. In the Segre case, absorbing coefficients and replacing zero summands proves that the unclosed r-span locus is exactly ordinary rank at most r, for every nonzero representative.

Projective polynomial vanishing quantifies over every nonzero representative. The homogeneous scaling identity proves equivalence with evaluation on any one representative. `projectiveZariskiClosure` is the common zero set of all homogeneous equations of the input locus. It contains that locus, is itself projective algebraic, and is contained in every projective algebraic superset. This is the standard homogeneous-equation characterization of projective Zariski closure; no unrelated topology or surrogate rank predicate is used.

The polynomial arc has nonzero 010-coordinate for every parameter. At each nonzero parameter its point lies on the actual line through two distinct nonzero Segre points. Continuity of every homogeneous equation forces vanishing at W, proving second-secant membership. A homogeneous quadratic slice determinant vanishes on the first span locus but evaluates to -1 at W, excluding the first closed secant. The zeroth secant is separately proved empty using the homogeneous constant polynomial 1.

The total `secantIndex` is an actual minimum, whose existence follows from finite tensor decomposition and the span bridge. The hierarchy is monotone. The final theorem proves W is nonzero, has ordinary rank 3 and least secant index 2. It negates the rank/index equality for all nonzero complex 2×2×2 tensors, a necessary special case of the source's unqualified first conjunct. Both languages reserve the genericity qualification for the separate dimension-counting conjunct; that conjunct is not independently resolved. The example is the classical rank/border-rank distinction, with no novelty claim.

No auxiliary numerical, simulation or external symbolic calculation supplies a mathematical premise. All mathematics used in the disproof is contained in the checked Lean project. A separate semantic reviewer authored none of the proof or report; its final exact-input assessment is in `SEMANTIC_REVIEW.md`.

## Matching report and PDF

The standalone LaTeX source compiled successfully in the built-in editor and was exported with the existing Tectonic engine. The matching 5-page PDF was rendered and every complete page was visually inspected by the report author and coordinating agent. Both found no clipping, overlap, missing mathematical glyphs or problematic page breaks. The native compilation result, export diagnostics and exact source/PDF/page identities are in `verification/pdf.json`; the export log is `verification/report.txt`.

- LaTeX SHA256: `a24adea8c34c15f6048760f1d6cd8dd34375c667d6b88056764f3cdde0b7fd7e`.
- PDF SHA256: `1233b6d002b7cb0536eef2a1d1cb4b575f1bb105de0532cf040e6840b77c9fa4`.
- PDF size: 71,545 bytes.

## Eligibility and publication scope

The initial full eligibility audit checked unsolved metadata, current and historical solution paths, 588 all-state pull requests through PR592, padded and short identifiers, English/Chinese tensor/secant/border-rank topics, indexed comments, and direct discussions. All 12 topic leads were read in full with all 36 direct discussion responses; the three comments concerned other conjectures. The closest tensor-related PRs256,502,566 address group representations, Hopf algebra primitives and reflection-equation degree, respectively. No prior or competing submission was found. The initial immutable record is `verification/eligibility.json`.

The prepublication refresh checked 588 all-state pull requests through PR592, plus source, guides, metadata, histories, searches and relevant discussions. Its exact scope, classifications, timestamps and limitations are in `verification/prepublication.json`. These are timestamped eligibility checks, not a guarantee about future submissions.

Only the prescribed personal submission folder is submitted. The bundled bilingual conjecture is an exact copy of the official source. No official conjecture, README, metadata, leaderboard or review file is modified. `verification/SHA256SUMS.json` records every submitted file except itself.

## Frozen formal sources

Paths are relative to `lean/`.

| File | SHA256 |
| --- | --- |
| `Conjecture6891/Core.lean` | `5b03b887e0a3547fa484966243e84f95abf349d86b384b27b9acfc8b52a91898` |
| `Conjecture6891/Rank.lean` | `90c1cfb8b9d76b6311bf697401e54b4092e7d0cf05d184db925999a1a2c0b99b` |
| `Conjecture6891/Projective.lean` | `ca4fab215bcb3b94c09c4988dc5ce3fd47f45374915ef45c32d23396cf45d2a0` |
| `Conjecture6891/Arc.lean` | `90d1f8e863b12636014c8bd96bfbe1d3a41341b03ee6dc7205b68848acfafa57` |
| `Conjecture6891.lean` | `b2a408f374022672574ea19e56da07f0aec5eb911d7282d15cbdf8dbb91ef7e0` |
| `Check.lean` | `060559f910abf209844b719235c9cc1ecd2e1b79d309bc364378ccba9f00e411` |
| `lakefile.toml` | `709c2281d68750a80a7ab40e75f1becd09c8964007b5680e6f7d5ad19f356df4` |
| `lake-manifest.json` | `c3b981fdf0a076d7be53cfddf2b82cec0274d51df1a945f36b6fabcfe5906b43` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
