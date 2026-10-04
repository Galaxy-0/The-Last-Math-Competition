# Verification record for conjecture 00000001277

These are local validation records, distinct from maintainer acceptance.

## Independent execution

A separate execution agent copied the six final Lean files and three project configuration files into a fresh directory, with no project build outputs. It independently reconciled the source inventory and frozen hashes before execution. The shared dependency cache was checked against all nine exact manifest revisions, with clean tracked sources before and after the run.

- Finished: `2026-10-04T20:16:36.745702+00:00`.
- Lean 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, verified before and after execution.
- Mathlib v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Fresh `lake build`: exit 0, 6.165 seconds. The default target imports every implementation module and builds the final disproof.
- Direct `lake env lean -DwarningAsError=true` replays of all six Lean files, including `Check.lean`: all exit 0.
- All 73 source declarations were independently inventoried. The actual emitted output contains all 16 definition printouts and 57 type/axiom audits: 56 theorems plus the named `instFintypeWord` instance. No anonymous or private declaration was omitted from the audit.
- Every actual axiom list is confined to `propext`, `Classical.choice`, and `Quot.sound`; emitted names and counts match the source inventory exactly.
- The proof-bypass scan found zero raw or code matches for admitted proofs, custom axiom declarations, `native_decide`, unsafe execution/elaboration shortcuts, or kernel-trust modifications. The actual axiom audit supplies a separate check.
- All nine source/configuration hashes and the supplied declaration-inventory hash stayed unchanged. The independently copied files match the frozen originals; compiler and dependency identity checks also passed after the build.

The complete execution commands, outputs, declaration reconciliation, compiler/dependency identities and source hashes are in `verification/strict-replay.json`. The fresh build log is `verification/build.txt`; actual definition, theorem-type and axiom output is in `verification/axioms.txt`. The shipped `Check.lean` reproduces the declaration audit. No auxiliary numerical program or simulation-derived assumption is used.

## Mathematical scope and scrutiny

The exact bilingual conjecture asserts a support property for entropy-maximizing chains under transition constraints. The disproof uses a valid first-order instance: three states, with self transitions forbidden. The initial law is uniform, and every allowed transition has probability one half. The kernel preserves the initial law and the first two states have a joint distribution different from independent uniform draws.

The proof uses genuine PMF-valued kernels and their recursively generated finite trajectory laws. Prefix consistency and positive-history conditional transition probabilities are proved. An explicit equivalence identifies stored histories with ordinary time-indexed tuples, and entropy is preserved under this relabeling. The finite laws provide the actual chain representation used in the entropy calculation. The formal project does not separately construct an infinite-path-space probability measure or prove shift-stationarity as an independent theorem.

Shannon entropy is calculated from actual PMF masses with the zero-mass convention, and `HasEntropyRate` is the limit of normalized block entropies. The joint entropy chain rule is proved, rather than assumed. The familiar stationary weighted-row formula is derived as a theorem; it is not the definition of the rate.

Every admissible row has at most two positive coordinates. The binary entropy bound yields `H(X₀,…,Xₙ) ≤ H(X₀)+n log 2` for every initial law and every fixed admissible transition kernel. This does not assume stationary competitors or assume that their rate limits exist. It implies that every such limit, when it exists, is at most `log 2`. The witness has the exact block entropy `log 3+n log 2` and an actual rate limit `log 2`, proving maximality.

The support predicate gives the usual at-most-one-positive-entry condition in each row and column of a partial permutation support. Every kernel with that property has point-mass rows. Its block entropy remains the initial entropy and its rate is zero for every initial law. Consequently no partial-permutation kernel can maximize this problem, even under the weaker existence reading. The final theorem negates this necessary first-order instance of the source's support clause. That refutes the conjunction; it does not separately assign or disprove an unspecified permutation-block formula.

A separate semantic reviewer, who authored none of the proof modules, report, or submission documentation, reviews the full bilingual statement, both complete guides, every final source/configuration file, complete report, documentation, and actual execution evidence. Its hash-specific findings are recorded in `SEMANTIC_REVIEW.md`. This scrutiny is separate from the execution agent's rebuild and the report's visual checks.

## Matching LaTeX and PDF

The built-in LaTeX compiler reported success. Tectonic 0.17.0 exported the matching three-page PDF with exit 0 and zero warnings or overfull/underfull box diagnostics. The report author rendered and inspected every complete page. The coordinating agent independently viewed all three rendered pages and read the full LaTeX source. Both inspections found no clipping, overlap, missing glyphs, broken formulas, or problematic page breaks. Their exact source/PDF/page identities are recorded in `verification/pdf.json`; this is separate from the semantic reviewer's textual scrutiny.

- `main.tex` SHA-256: `2ea0eceec56e0952e70520bbc4f4efc6bfe37845c8b902dd089e7c8217883467`.
- `main.pdf` SHA-256: `26dc6acde70a932941e1e924eae7069bb95b131b682770251c37cf08ce9eb7bc`.
- PDF: 3 pages, 61,966 bytes.
- `verification/report.txt` contains the compiler log with only trailing line whitespace normalized; diagnostic text is retained. A no-index source whitespace check returned the normal difference exit code 1 with no diagnostics, and a direct scan found zero trailing source spaces. The final staged package is checked separately.

## Contribution eligibility and package scope

The initial live eligibility check examined upstream main, the exact bilingual source, both complete contribution guides, unsolved metadata, 550 all-state PR titles/bodies/head branches through PR554, exact/short-ID and topic/comment searches, and current plus historical solution paths. No prior or competing submission for 00000001277 was found. Five broad topic matches were individually read and classified as other conjectures.

The final recorded refresh at 20:17:05 UTC examined 553 all-state PRs through PR557. The three newer submissions are unrelated; all five broader topic hits have unchanged bodies and heads. Upstream main remains `fe1d06d431b0591b65d759c60035b1d2e293a819`; source, full guides and unsolved metadata remain unchanged. The exact/short-ID/comment and solution-history checks remain empty. The initial record is preserved as `verification/eligibility.json`, with the final refresh in `verification/prepublication.json`. Their stated search scopes and limitations are retained.

Only the personal submission folder is included. The official conjecture, guides, metadata, leaderboard and review files are not modified. The bundled `conjecture.md` is copied byte-for-byte from upstream. `verification/SHA256SUMS.json` covers every submitted file except itself. Local execution, internal mathematical scrutiny and PDF checks do not establish maintainer acceptance.

## Exact Lean source identities

Paths below are relative to `lean/`.

| File | SHA-256 |
| --- | --- |
| `Conjecture1277/Entropy.lean` | `0d4116fe456a23913338c626989d86df58b0ecdbb94f34d90703a8730a783d6c` |
| `Conjecture1277/Words.lean` | `2d3f54274d03a413ca0b4e31acb8f566bd1b84e2da1bc1ac1e6051ae62dde41f` |
| `Conjecture1277/Markov.lean` | `c4d655e947657f6493163c835053f0928aa9772ac0a201dafbd7e4c053393cb0` |
| `Conjecture1277/Counterexample.lean` | `a29e6a489161af547a2e02711e17dfc13100c21eca46602de112b946391fb8e9` |
| `Conjecture1277.lean` | `478bcd3638a2578f7fe25b6cc0b7f6978bb620a34a044f8fadbe6f2b76e1e2d8` |
| `Check.lean` | `52968040bd4b11bbad3b8b13026f3409fc74ddf69ab6b2d7725e4a1aa3e38146` |
| `lakefile.toml` | `4b0db07a2fd7a06bef49c7c89f2afb2e71685e7ac645c792ce9fb7d687e16331` |
| `lake-manifest.json` | `57bd03044879b9010c1f6861ec75a212a9fda68b25861872ebd51b52087844d1` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
