# Independent internal review of conjecture 00000000331

**Verdict: PASS for the repository's literal fixed-numerator assertion.** No mathematical, formal-verification, or report blocker was found in the frozen inputs. This is an independent nonauthor internal validation, not maintainer acceptance or a claim to settle the named inhomogeneous Duffin–Schaeffer research problem.

Reviewer: `review_331`. Review completed on 2026-10-05 UTC. The reviewer first performed the candidate-free preassessment preserved in `verification/semantic-preassessment.txt`, then inspected the frozen submission. No other conjecture, prior mathematical submission, or old solution was inspected. No authored input, original project, report, or repository file was edited. Independent work was confined to `/private/tmp/tlmc331-semantic/`.

## Identity and complete coverage

The frozen input manifest `/private/tmp/tlmc331-review-inputs.json` has SHA-256 `5173186c4716d1bb3e141a70d0d6f5c43622b81c953b38a16ed983cebc93e6ca`. Every one of its 31 entries was read or, for binary artifacts, parsed/rendered and visually inspected as appropriate. All 31 SHA-256 values were independently checked before and after review and remained unchanged. The complete manifest coverage and hashes appear below.

Principal identities:

- Bilingual statement: `f1e6613129913c38936392b8bace5d3f7ead6d7a43fc1f16d8deb39bee50a534`.
- Complete proof source: `e74af17c4c8116a1ef08490f532df48c029bff44997cb6e2174e9ed95c5194d2`.
- Complete `Check.lean`: `52b5dcaf785d43c85f29e2f2e7d0473b236f3db144e251d10d434d501b7485be`.
- Complete report source: `0ea67e0c841b1f81089ecfa532ad0a314a536b189637d116646872f1e7efe7fb`.
- Frozen report PDF: `a192de8c20308af39364afe21184fcd6908698fbaf30c4da4ea6ae1c38f9d542`.

Coverage includes both complete bilingual contribution guides; the exact bilingual conjecture; every authored proof and definition; all configuration files; the entire LaTeX report and both PDF pages; package README and verification summary; all inventory, axiom, build, strict-replay, identity, PDF, and initial-eligibility records; and both complete auxiliary Python scripts plus the full Lean environment-inspection harness. Repeated embedded records were checked against their fully read originals, including exact agreement of the strict-replay Check output with `axioms.txt` and of its complete environment record with `environment-inventory.json`.

## Mathematical and semantic review

The English “a arbitrary but fixed” and Chinese “a 任意给定” agree. The displayed implication quantifies over an approximation function, then asserts infinitely many positive integer denominators for Lebesgue-almost every alpha, with a single numerator held fixed as denominators vary. The submission preserves this reading. It does not substitute a varying integer numerator, an additive shift, a coprimality condition, or a different approximation radius.

The source omits several domains. The submission explicitly chooses positive integer denominators and finite real-valued approximation functions; it treats both strictly positive and nonnegative radii. Its result holds for **every real fixed numerator**, so the plausible integer, rational, and positive-integer numerator interpretations are all covered. The source does not impose convergence of the radius to zero. The chosen constant function is admissible under the displayed hypotheses and is also positive, bounded by one half, and nonincreasing; the report accurately limits its claim accordingly.

I independently checked the complete argument. With radius one quarter, each partial sum is one quarter of the ordinary harmonic partial sum. In the report, the block from `2^j` through `2^(j+1)-1` has `2^j` terms each at least `1/(4*2^(j+1))`, giving at least one eighth per block. Thus the partial sum through `2^k-1` is at least `k/8`, and monotonicity gives eventual exceedance of every real threshold. This establishes genuine divergence to positive infinity.

For each fixed real a, the report chooses a positive integer N greater than `4|a|`. If n is at least N and alpha is at least one half, then `|alpha-a/n| >= alpha-a/n >= alpha-|a|/n > 1/4`. Successful positive denominators are therefore finite. The formal proof uses the sufficient weaker bound N greater than `4a`, showing directly that `a/n < 1/4`; together with a putative hit and alpha at least one half this is contradictory. This remains valid when a is zero or negative; the formal bound need not itself be positive because each successful denominator is separately required to be positive. The difference between the report's bound and the formal bound is mathematically harmless and transparently documented.

The failure interval `[1/2,3/4]` has Lebesgue measure exactly one quarter. It is contained in `[0,1]`, `(0,1)`, and `[0,1)`. Consequently the exceptional set is non-null under both real-line Lebesgue measure and each stated restricted unit-interval measure. This disproves an almost-everywhere conclusion, rather than merely exhibiting exceptional points. The report's full proof is complete and agrees with the formal result.

## Complete formalization review

All eight definitions were read and checked against their printed elaborations:

- `partialSum` sums exactly denominators 1 through N by the substitution n = k + 1; zero never appears as a denominator.
- `Diverges` is `Filter.Tendsto (partialSum psi) atTop atTop` over the real numbers, not a totalized infinite-sum value or a non-summability surrogate.
- `hitSet` retains `0 < n` and the strict inequality with radius `psi n` and fixed real a.
- `InfinitelyApproximable` uses Mathlib's actual `Set.Infinite` on that set of natural denominators.
- `LiteralClaim` and `NonnegativeLiteralClaim` universally quantify over functions with the stated positive-index sign condition before divergence and the almost-everywhere conclusion. The function is independent of alpha; a is a fixed parameter.
- `radius` and `failureInterval` are precisely the constant one quarter and `[1/2,3/4]`.

All 20 authored theorem proofs were inspected in full:

1. `radius_pos` proves strict positivity, including all positive indices.
2. `divergence_means_exceeding_every_bound` proves the exact threshold/eventual-partial-sum bridge in both directions.
3. `infinite_means_arbitrarily_large_denominators` proves the exact arbitrarily-large-distinct-index bridge using infinitude of subsets of the natural numbers.
4. `partialSum_radius` proves the exact harmonic partial-sum identity, including the shifted natural-number cast.
5. `radius_diverges` applies the pinned Mathlib harmonic partial-sum limit and positive scalar multiplication to that identity.
6. `hits_bounded` proves a finite upper bound for every successful denominator whenever alpha is at least one half.
7. `hits_finite` embeds all hits in a finite natural-number range.
8. `fails_on_interval` obtains failure of actual `Set.Infinite` throughout the interval.
9. `failureInterval_volume` computes its genuine real Lebesgue measure as `ENNReal.ofReal (1/4)`.
10. `failureInterval_volume_pos` proves strict positivity of that measure.
11. `not_ae_of_interval_positive` uses the definition of almost everywhere and measure monotonicity to contradict a positive-measure subset of the failure set. It does not assume a bespoke “almost everywhere” predicate.
12. `not_ae_real` instantiates genuine Lebesgue volume.
13. `failureInterval_subset_unit` proves the closed-unit-interval inclusion.
14. `unit_failureInterval_volume` correctly applies restriction to the measurable failure interval and computes its intersection with the unit interval.
15. `not_ae_unit` proves failure for restricted Lebesgue measure on `[0,1]`.
16. `not_ae_restrict` generalizes to any domain containing the failure interval; the measurable set needed for restriction is the failure interval itself.
17. `not_ae_unit_open` applies this to `(0,1)`.
18. `not_ae_unit_half_open` applies this to `[0,1)`.
19. `literal_claim_false` negates both real-line and closed-unit-interval universal positive-radius implications for every real a, by instantiating the witness.
20. `nonnegative_literal_claim_false` does the same for nonnegative-radius implications.

These are the actual negations needed for the literal assertion. The open and half-open a.e. failures use the same proven positive, divergent witness, so they likewise negate the corresponding displayed implications. There is no gap from a sequence-level example to the claimed quantified disproof.

## Independent execution and trust audit

I created `/private/tmp/tlmc331-semantic/fresh-project` with only copies of the two frozen Lean sources and three frozen configuration files. There were no candidate build outputs in this directory. The existing pinned dependency packages were linked as authorized; no candidate `.olean` was copied. I used the existing Lean 4.19.0 runtime and checked its reported commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. The executable SHA-256 values were:

- Lean: `5c1fe58db7d10b1cd0ddff1a1cbc49db2396fff9c6c983cc3b49f1c5c1ae241b`.
- Lake: `8b4ff4094a842500f9987336926c5fb2e20b4df8cd92d4e6ba70052a9c246574`.

All nine package Git revisions matched the frozen manifest: mathlib, plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, and Cli. Independent before-and-after `git status --porcelain --untracked-files=all` checks were empty; all revisions remained unchanged. The full exact pins and command evidence are retained in `executions.json`. Existing library caches were reused; this review does not claim to have rebuilt the Lean compiler or the entire dependency graph from source.

The fresh `lake build`, strict proof-source replay, and strict `Check.lean` replay all exited zero. The explicit default target built `Conjecture331`. I also compiled the exact source followed by all Check commands in one stdin invocation, removing only Check's now-redundant import. This independently ties the inspection to the exact source in the same elaboration. Both this and the imported Check execution passed. Their first raw-output comparison differed only because the source's open namespaces remained active in the combined invocation, shortening printed names and changing wrapping. The complete diff was inspected. Repeating both with `-Dpp.fullNames=true` produced **byte-identical output**. No authored mathematics was changed to obtain this result.

I independently reran the full module-of-origin inventory harness. The fresh result contains exactly 37 constants, including all eight authored definitions, all 20 authored theorems, and nine generated declarations. Every record, full type, declaration kind, safety flag, and transitive axiom list equals the frozen inventory. The nine generated entries are the equation theorems for `partialSum`, `hitSet`, `InfinitelyApproximable`, `radius`, and `failureInterval`; three generated numeral-denominator proofs; and the generated helper for the infinitude equivalence. They are all included, not filtered out by name.

All 37 declarations are safe, nonpartial, and have no custom axiom declarations. Every transitive axiom closure is a subset of `propext`, `Classical.choice`, and `Quot.sound`; the three numeral helper proofs have empty axiom closures. All 20 named theorem audits are present. Manual source inspection and an additional lexical check found no admitted proof, `sorry`, `native_decide`, custom axiom, unsafe/partial definition, kernel-skip setting, external oracle, or authored metaprogram that could bypass proof checking. The environment harness's `run_elab` only prints existing environment data and is not imported into the proof module.

The full original inspection/export scripts were reviewed, and both Python files passed syntax compilation into reviewer-owned output files. Their functions are operational inspection and rendering, not mathematical premises. I used separate reviewer-owned runners to reproduce their substantive checks because executing the original fixed-path scripts would overwrite frozen records or encounter their fresh-directory guard. The inspection scripts' regular-expression scans are supplementary; manual full-source review and exhaustive environment inspection provide the necessary additional coverage. No numerical computation, finite search, or external computed certificate is claimed or required by this proof.

Independent execution evidence is saved under `/private/tmp/tlmc331-semantic/`, principally `executions.json`, `fresh-build.txt`, `strict-source.txt`, `strict-check.txt`, `same-process*.txt`, `check-fullnames.txt`, `environment.json`, and `environment.txt`. Execution ran from 2026-10-05T04:08:07Z through 2026-10-05T04:10:47Z. The initial reviewer-only output-comparison failure and its explained resolution are preserved in the execution record.

## PDF and source correspondence

I read the complete exact LaTeX source and visually inspected both original page images using `view_image`. I copied the exact source into the separate reviewer directory `pdf-rebuild`, compiled it successfully with the built-in desktop LaTeX compiler, independently exported it with the existing Tectonic binary, and rendered both the fresh PDF and the frozen PDF again using Poppler. The fresh export exited zero without warnings, overfull/underfull boxes, or error diagnostics. Both PDFs have two pages.

For page 1 all original/fresh-frozen/fresh-export image hashes equal `c055a0a0c068ddd30e96a862f7db238ba6fcee30f73070c73ef7854e89d39fef`. For page 2 all three equal `b920f1cafc1ff0b76bb4459a15b12657259b62752eb915c1e4b39ab57e68d005`. I additionally visually inspected both fresh-export pages. Equations, prose, proof continuation, commands, and page numbers are complete and legible, with no clipping, overlap, or missing symbols. Independent pypdf extraction yields identical page text for the frozen and fresh PDFs.

The fresh PDF hash is `eb5a8ab45ea52a8686cabebb55835ab82b6ce63c77e9b629d8720bdc02b84745`, different from the frozen PDF. Fresh export changes the recorded creation time and trailer IDs; identical extracted page text and byte-identical rendered pages establish the relevant content/layout correspondence. No claim of PDF binary reproducibility is made. Detailed evidence is in `pdf-rebuild/pdf-replay.json` and the associated export/render outputs.

## Operational records and limits

The package README, verification summary, frozen identities, audit names, logs, and structured records are internally consistent with the reviewed source and the independent results. Both full guides require complete report/formal agreement and all relevant computational checks. Those requirements are satisfied for the reviewed mathematical material. The future package references to `SEMANTIC_REVIEW.md`, a submission checksum manifest, and current publication eligibility records concern assembly by the coordinating agent; this review itself does not assert that an external pull request has already been submitted or accepted.

I read the frozen initial eligibility result and the separately supplied prepublication eligibility result at `/private/tmp/tlmc331-prepublication/eligibility-result.json` as operational records. They report no same-ID submission and no unresolved retrieval gap; the refresh reports 595 unchanged PRs, 34 complete searches, 105 unchanged direct lead responses, and 40 local refs spanning 1,128 reachable commits. I did not independently repeat that remote corpus audit or read other solutions; its time-dependent publication gate remains the coordinating agent's responsibility. This limitation does not affect the mathematical/formal verdict. A later change to the statement, proof, report, or relevant frozen configuration invalidates this identity-specific approval until reviewed.

A subsequent operational-only eligibility update was also read in full at SHA-256 `ca249df56c300a58f622d667c3d16cebf2c903ff4724f14b80ad1c01a5c3a60d`. It records that an unqualified numeric search returned pull-request number 331 about a different conjecture; the coordinating agent reviewed the collision and retained the failed first gate record. I read only this operational disambiguation record, not the other submission or its mathematics. All 31 frozen semantic inputs remained unchanged; the mathematical verdict is unaffected.

**Final assessment: PASS.** The complete report and checked Lean source rigorously disprove the literal fixed-numerator implication, with explicit domain conventions and an actual positive-measure obstruction. This conclusion is independent of the source's named-conjecture label and independent of maintainer acceptance.

## Frozen-file coverage ledger

All entries below were fully covered as described above and matched before/after hashing.

| Frozen input | SHA-256 |
|---|---|
| `README.md` | `d2833eb9d742fd7f79205109290b417baf1cd6b59dc5d8b69fe6696e5019cdb1` |
| `conjecture.md` | `f1e6613129913c38936392b8bace5d3f7ead6d7a43fc1f16d8deb39bee50a534` |
| `lean/Check.lean` | `52b5dcaf785d43c85f29e2f2e7d0473b236f3db144e251d10d434d501b7485be` |
| `lean/Conjecture331.lean` | `e74af17c4c8116a1ef08490f532df48c029bff44997cb6e2174e9ed95c5194d2` |
| `lean/lake-manifest.json` | `4843cea7b582e98e34a27f15409e3f7f212c8bff455f7066da7ec03ef4616bb2` |
| `lean/lakefile.toml` | `8469dff02299e5909a81f8d80130c66daa8ce2cdcf78813d2aaac4114ef49c60` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `main.pdf` | `a192de8c20308af39364afe21184fcd6908698fbaf30c4da4ea6ae1c38f9d542` |
| `main.tex` | `0ea67e0c841b1f81089ecfa532ad0a314a536b189637d116646872f1e7efe7fb` |
| `verification.txt` | `ee8fa57dc0ef15caae8a07fd10114b88e28bca4a819fbe5b7b3b352213ee8287` |
| `verification/audit-names.json` | `72838dd1a847a7d6ed4af5fc55c2b895fecbfae43e5175c8ad4a31697acf048d` |
| `verification/axioms.txt` | `c9b3f870bedabef1ec8fed72c35e825ccf374d62d71a6d7a24319ed3d4de1ee5` |
| `verification/build.txt` | `3e3dc4010f520641f1a1dfb9303d6ae546bda08b804c056ee848169d61545a01` |
| `verification/contribution-rules-en.md` | `84cd9992c3b4027d90044109df969e22390051df4a5f7f21ca81138e5f717795` |
| `verification/contribution-rules-zh.md` | `167c69fba1d5592feb55117da9a0151b0355ff6b2a0fb773115f367e58c59b47` |
| `verification/environment-inventory.json` | `9784060ad83c361192ad4babc996546d9394b3686597a75d15b909773b5a4fed` |
| `verification/environment-inventory.lean` | `a12373f03341c3a31528f393795065b465fd67717383e509ee49beb868cf0034` |
| `verification/environment-inventory.txt` | `0e1954bec6006c9ba0ddbbcccb8e6e4d915af9fe771f88246ea682dd85f04916` |
| `verification/export-pdf.py` | `5cb326d69379859266e23d2581408775178b34b4af49a43f62d4105c87bcdd15` |
| `verification/frozen-sources.json` | `1142be3556f65e3069277e7bcc569580ea1321728c3bd8bca40e0da1822c46f8` |
| `verification/independent-verify.py` | `5ea3431dfffd5fb06de56d6e9f24cc686a812838767bead44f2102d98296c198` |
| `verification/initial-eligibility.json` | `a0b37ad440b366227618f8a2297c0a885bd15447fb5cfb563df38ccfa1dd888f` |
| `verification/pdf.json` | `31b59e1cf6da43c81abf5c76e8ef60bf9211b98fdee05a26de460244a2658fd1` |
| `verification/pdfinfo.txt` | `0c751941371e32801433872319d2d7bc8853b544aec5d0fd24685110ee88c81f` |
| `verification/pdftext.txt` | `1aa7f71abf44b5faadd87af1dac8167e3428f01acac3cb9c8aa20880fe24affe` |
| `verification/report-export-raw.txt` | `7f2afe2b35474873d0d716755b7296700d0c2b580862af1541175331390d01e0` |
| `verification/report-export.txt` | `7f2afe2b35474873d0d716755b7296700d0c2b580862af1541175331390d01e0` |
| `verification/report-page-1.png` | `c055a0a0c068ddd30e96a862f7db238ba6fcee30f73070c73ef7854e89d39fef` |
| `verification/report-page-2.png` | `b920f1cafc1ff0b76bb4459a15b12657259b62752eb915c1e4b39ab57e68d005` |
| `verification/semantic-preassessment.txt` | `aa4723fadbec4ca4016af982c92931a29c3f3bf85a02e36cf6ce009b0f3445a8` |
| `verification/strict-replay.json` | `0c07397f2cf3a73687c8dd93d5a6edb0e241f4517ffcae0949e3fedf1b00e725` |
