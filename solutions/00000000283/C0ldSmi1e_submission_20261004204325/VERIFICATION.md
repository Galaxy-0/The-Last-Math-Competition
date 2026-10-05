# Verification record for conjecture 00000000283

These are local validation and independent internal scrutiny records. Maintainer acceptance is a separate decision.

## Independent execution

A separate execution agent copied all five final Lean files and three configuration files into a fresh directory without project build outputs. It independently reconciled the actual source declarations with the audit inventory, including the escaped `prefix` identifier, and checked exact frozen file hashes before running the proof.

- Lean 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Fresh default `lake build`: exit 0. Its import graph covers every implementation module.
- Direct warnings-as-errors replays of all five Lean files, including `Check.lean`: all exit 0.
- Actual emitted output includes all five definitions and all 25 theorem types and transitive axiom lists, matching the complete 30-declaration source inventory. No unnamed, private, or instance declaration is omitted.
- Every theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. The independent scan found zero raw or code matches for admitted proofs, custom axioms, `native_decide`, execution shortcuts, or kernel-trust modifications.
- All eight source/configuration hashes and the supplied inventory stayed unchanged. The copied files match the frozen originals. All nine manifest dependencies had exact revisions and clean tracked sources before and after the build; the compiler identity was also rechecked.

The run finished at `2026-10-04T20:42:35.173567+00:00`. Its fresh build took 6.928 seconds. Full commands, outputs, source-inventory reconciliation, dependency/compiler checks, and identities are in `verification/strict-replay.json`. `verification/build.txt` is the build log; `verification/axioms.txt` contains the actual definition, theorem-type, and axiom output. `Check.lean` reproduces those audits.

## Mathematical scope

The formal objects are the real cosine factors `a_n = cos(π/(n+3))`, their genuine finite products, and their genuine infinite product. Summable cosine deficits give logarithm summability; the equality with an exponential proves positivity, while `HasProd` certifies actual product convergence. This does not infer convergence from the totalized `tprod` definition alone.

The source-indexed product is the actual finite product over `Finset.Icc 3 N`. Its exact indexing bridge and convergence are proved. Monotonicity and the first omitted cosine factor yield `S_N-K ≥ 2K/(N+1)^2` for every `N ≥ 3`. The final quantitative theorem violates the cubic bound for every real constant and every natural cutoff, and the main theorem negates Mathlib's standard `IsBigO` relation at infinity.

This refutes the explicit convergence-rate conjunct of the exact English and Chinese statement, hence the combined conjecture. It does not settle transcendence, Gamma-value independence, or the sharp convergence order. The report gives a conventional sine-bound and logarithm-integral explanation; Lean uses the corresponding established cosine bounds and general logarithm-summability theorem. No numerical approximation, auxiliary mathematical program, or simulation is used.

A separate semantic reviewer who authored none of the proof, report, or submission documentation examines the complete source statement, both current guides, final proof/configuration files, full report and documentation, and actual verification records. Its hash-specific conclusions are in `SEMANTIC_REVIEW.md`. That review is distinct from the execution agent's rebuild and the visual page checks.

## Matching report and PDF

The final source compiled successfully in the built-in LaTeX compiler. Tectonic 0.17.0 exported its matching 3-page PDF with exit 0 and no warning or box diagnostics. The report author and the coordinating agent separately viewed every complete final rendered page; both found no clipping, overlap, missing mathematical glyphs, or problematic page breaks. Exact source, PDF and page identities are in `verification/pdf.json`. The normalized compiler log is `verification/report.txt`; only trailing log-line whitespace was removed.

- `main.tex` SHA256: `cbfed52fe4bf1719ba2105ed64bf0b5307619be77ccf09e9450431c72e452d9c`.
- `main.pdf` SHA256: `f6eecf9e2028ff32cf25c308267da5d2dcb13dee9e6995506c939d9c74ba49ee`.
- PDF: 3 pages, 68,517 bytes.

## Eligibility and package scope

The initial recorded audit checked the exact bilingual source, both full current contribution guides, unsolved metadata, 557 all-state pull requests through PR561, padded/short identifiers, English and Chinese topic/comment searches, and current plus historical solution paths. No earlier or competing submission was found. The two bare-number matches were read and classified as unrelated: PR199 contains the integer 283 in a pandigital-prime table for conjecture117, and PR283 concerns conjecture3883.

The final refresh examined 560 all-state pull requests through PR564. Its exact times, search results, classifications, unchanged-source checks and limitations are preserved in `verification/prepublication.json`; the original record is `verification/eligibility.json`. The conjecture remains marked unsolved, and no prior or competing submission was found in that recorded scope.

Only the prescribed personal submission folder is included. The bundled conjecture is a byte-for-byte source copy. Official conjectures, guides, metadata, leaderboard and review files are not modified. `verification/SHA256SUMS.json` hashes every submitted file except itself. Eligibility is a timestamped search result, not a guarantee about future submissions.

## Frozen Lean file identities

Paths are relative to `lean/`.

| File | SHA256 |
| --- | --- |
| `Conjecture283/Factors.lean` | `54a98fe4cc35ee19e8a61be81b3907c4eb1fa126281e69cba8df2d0a1fc9a8a0` |
| `Conjecture283/Prefixes.lean` | `6ed9086190b565755c7b0edd980e47b11d0ba6eaa6f22ebe5ed8436c70a1c5d4` |
| `Conjecture283/Rate.lean` | `d713947f666a689c7291fe849953528c1688119d2c174999f7c5d72eb79eb1a3` |
| `Conjecture283.lean` | `db916b5897a71468be0ef36f4f7987f1b5b08cab20f3a6a75aa39334168a2896` |
| `Check.lean` | `c87752f9d464ab5400ed1635bb79c8436aed1fea2e3f3e6abc9e4f1a3bee9e7b` |
| `lakefile.toml` | `6c12330ebe0db54376007ba420b1b078c60751ac92f453a6a82e9b4378f7508b` |
| `lake-manifest.json` | `df1f2fce49683ae7af41cb3172a1791a7976ecbfcdbf164415232c80d4f75e5d` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
