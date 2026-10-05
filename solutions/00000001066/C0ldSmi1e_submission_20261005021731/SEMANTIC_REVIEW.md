# Independent semantic and artifact review: conjecture 00000001066

**Decision: PASS for the literal exact-attainment disproof in the frozen submission. No blocking mathematical, formalization, or report findings.** This is independent local validation, not repository maintainer acceptance or the final operational publication gate.

Reviewer: `/root/review_1066`, a nonauthor reviewer. The reviewer first assessed the bilingual conjecture and both complete rule files without receiving a candidate proof or constructing a witness. After the independent solver supplied the argument, the reviewer performed preliminary mathematical scrutiny and then this separate full artifact review. The reviewer did not author or modify the submitted proof, report, configurations, dependencies, or repository files.

Review completed on 2026-10-05 UTC. The strict reviewer replays ran from 02:12:59.876951Z through 02:13:17.132556Z; the final input/dependency checks completed at 02:14:33.841649Z.

## Exact reviewed identity and coverage

This decision is bound to all 31 entries in `/private/tmp/tlmc1066-review-inputs.json`, whose SHA-256 is:

`97b997d664dc15bc59a2f40389d1c301d3bb8c624362ccb0179f3b20391b4c1b`

The reviewer independently hashed the manifest and every listed file before review and again after all replay and PDF inspection work. All expected hashes matched; all 31 inputs remained unchanged. The five copied project inputs in `/private/tmp/tlmc1066-independent` also matched their frozen source hashes before and after replay.

Principal identities:

| Input | SHA-256 |
| --- | --- |
| Exact bilingual conjecture | `3051cfeae80b95c8f45c10caf14614047105c56d8df444877d26efbe8a4f9020` |
| `Conjecture1066.lean` | `dcb71282ff369fbd0e94d28f2ae2f75e5ad6b75bfb6efcb0abbe07d59e4507be` |
| `Check.lean` | `8f536a7d19002db4a5a10be9d6bf09829013be7c236abfecfe070b1a4feb3fac` |
| `main.tex` | `bc4da7471300ca9e672506a6c7397b094a3bb97dc2fad54b1549cb6a76896f40` |
| `main.pdf` | `d994ed37181d1cdd4eb4b56bcba74be20dbb9fe26d3951a7d381cb4bb93b6985` |

Every listed textual input was read in full: the proof and Check source, all three project configuration/pin files, full LaTeX report, submission README and verification summary, bilingual conjecture, both complete current contribution guides, all build/type/axiom/environment records, complete strict-replay JSON, complete independent Python verifier and PDF exporter, declaration and frozen-source inventories, PDF diagnostics/text/export logs, initial eligibility record, and candidate-free semantic preassessment. Both listed page images were visually inspected in full. The PDF was independently checked against those renders as described below.

## Semantic contract and faithful negation

For a prime natural number p, `ZMod p` is the prime field. `Finset (ZMod p)` represents actual finite subsets of that field, with genuine natural-number cardinality; every subset of a finite prime field is finite. The implementation does not replace a field subset by an unconstrained surrogate size.

`IsSidon` states injectivity of `(a,b) -> a-b` on ordered pairs of members of B with `a != b`. Both pairs in the comparison exclude the diagonal. Equal differences imply `a = c` and `b = d`. This is the agreed conventional difference interpretation of the supplied definition.

`UpperBound p` is the displayed inequality for every Sidon finite subset, with the cardinality and p cast into the reals. `ExactAttainment p` requires existence of a Sidon subset whose real-valued cardinality equals `Real.sqrt (p : Real)`. The square root is the nonnegative real square root, not a natural square root, floor, ceiling, approximation, or asymptotic scale.

Both English "is attained" and Chinese "达到" support exact equality. Neither version supplies rounding, an asymptotic qualifier, or replacement of primes by prime powers. Both join the bound and attainment by conjunction. The report openly states this literal interpretation and the compressed prime quantifier.

`UniversalConjecture` says that for every prime p, the upper bound and exact attainment both hold. `ExistentialPrimeConjecture` retains the universal upper bound and weakens attainment to existence at some prime. Both definitions match the formulas in the report. Their negation is sufficient to disprove the written conjunction under either disclosed reading. The submission consistently leaves the separate upper-bound clause, rounded extremality, maximal Sidon cardinalities, and asymptotic statements unresolved.

## Mathematical scrutiny

The central theorem assumes a natural number n has real cast equal to the real square root of a prime p. Squaring is valid because the real cast of p is nonnegative. `Real.sq_sqrt` yields equality of the real square of n and the cast of p. Exact cast transfer yields the natural equality `n ^ 2 = p`. Rewriting primality through this equality contradicts `Nat.Prime.not_prime_pow` at exponent two. There is no missing positivity hypothesis, special-case gap, division, or approximate calculation.

The report's elementary proof treats n equal to zero or one and otherwise uses the proper divisor n of n squared; it proves the same mathematical fact. Applying that fact to `B.card` establishes nonattainment for every finite subset, a stronger assertion than needed for Sidon subsets. Discarding the Sidon assumption in this stronger obstruction is valid.

`no_exact_attainment` extracts the alleged subset and contradicts its cardinality equality. `no_prime_conjunction` rejects the attainment conjunct. `universal_conjecture_false` specializes the universal claim to the actual prime 2. `no_prime_exact_attainment` rules out every prime witness, and `existential_prime_conjecture_false` rejects the existential-attainment conjunct. Each of the seven theorem statements and proof steps was checked against the report and full printed types.

## Independently executed formal validation

The reviewer used the already-created independent project directory, without changing any project input. The runtime was independently checked before and after replay:

- Lean 4.19.0, release build for arm64-apple-darwin23.6.0.
- Compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`.
- Mathlib v4.19.0, manifest revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- All nine manifest package revisions independently matched their checked-out Git HEADs; all nine tracked source trees were clean before and after replay. This includes Mathlib and the eight supporting packages. No dependency source was modified.

All reviewer Lean commands used the pinned runtime's `lake env lean -DwarningAsError=true` from `/private/tmp/tlmc1066-independent`, with inherited `LEAN_PATH` and `LEAN_SRC_PATH` removed before Lake established its environment.

| Reviewer execution | Exit | Seconds |
| --- | ---: | ---: |
| Exact frozen `Conjecture1066.lean`, direct source replay | 0 | 8.425 |
| Exact frozen `Check.lean`, direct replay | 0 | 2.394 |
| Exact proof source plus the unchanged Check body, one `--stdin` process | 0 | 2.669 |
| Exact frozen compiled-origin environment inventory harness | 0 | 3.766 |

For the single-process replay, the sole `import Conjecture1066` line was removed from Check and the remaining inspection commands were appended in memory to the exact frozen proof source. No proof text was altered, no source file was written, and no saved candidate proof module was imported for this check. Its complete printed definition/type/axiom output exactly matched the direct Check output. This independently ties the audited results to freshly elaborated proof source rather than relying solely on a possibly stale proof object.

The seven theorem axiom lists contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The full compiled-origin inventory independently returned exactly twelve constants: five definitions and seven theorems. Its names match the complete source declaration inventory; there are no additional/generated constants, custom axiom declarations, unsafe declarations, or partial declarations. All inventoried axiom dependencies are within the same standard set. Full manual source inspection confirms there are no admissions, `native_decide` calls, custom proof-generating metaprograms, or kernel-checking bypasses.

The supplied fresh-build record was also read in full and cross-checked with its verifier: it records a fresh source/config copy with no copied candidate build outputs, a successful default-target build, strict replay, and complete trust audit. The reviewer did not rerun that file-writing coordinator script or overwrite its frozen records. The reviewer's independent executions above provide a separate replay.

## Auxiliary code and computation coverage

No auxiliary mathematical search, numerical approximation, finite experiment, or externally computed witness is used or required by the proof. The only explicit `decide` application certifies the numeral proposition `2 <= 2` using ordinary kernel-checked computation. No unrelated finite tests are needed to cover this argument.

The Python verifier and Lean inventory harness inspect existing sources, declarations, dependencies, and execution results; they are not extra mathematical assumptions or unverified numerical proofs. The exporter creates the PDF and its inspection records. Both Python scripts were read completely and independently parsed successfully for syntax without executing their file-writing workflows. The inventory harness was independently run successfully as shown above. The recorded successful coordinator execution/export and their outputs were reviewed in full. The README appropriately identifies the coordinator verifier as a historical inspection runner rather than a portable installer.

## Report and PDF review

The full LaTeX report, README, verification summary, extracted PDF text, and both full rendered pages agree on the mathematical argument, formal statements, toolchain, trust audit, and limits of the result. The report names the actual definitions and final theorems correctly. The English quote agrees with the exact bilingual source, which is separately preserved.

Both A4 pages are legible with consistent margins and page numbers. Mathematical symbols and monospaced theorem identifiers render correctly; no clipping, overlap, or broken glyphs were found. The theorem statement ends page 1 and its proof starts page 2, with a clear continuation. All four report sections and the scope statement are present.

The reviewer rendered each page afresh in memory with the recorded Poppler runtime and settings. The resulting PNG bytes exactly matched the inspected frozen page images: page 1 SHA-256 `3c024b0968a2e5304a440811abf95c91e30c8acf8dba39411ff08406b7669d94`, page 2 SHA-256 `6037d9621bb561b20e890a5bd4088c663ffa94cd5f65f8485421502cff86edf0`. A fresh `pdfinfo` run exactly matched the frozen record, confirming two pages and the recorded PDF properties. The supplied native-compiler success and Tectonic export records were reviewed; the PDF was not re-exported or modified.

An optional additional `pdftotext` replay could not run because that executable is absent from the observed bundled override directory. This is not an approval denial and did not affect full visual/text review or exact fresh-render comparison. The frozen extracted text was read completely; no claim is made that it was independently re-extracted.

## Rules, operational boundaries, and conclusion

Both complete current guide files were reread. An independent comparison with the earlier guide files confirmed the only differences are the leaderboard overview totals; the contribution and review rules are unchanged. The frozen initial eligibility record was read and reports PASS, with no same-conjecture conflict or prior-invalid submission requiring an error account. This reviewer did not independently repeat remote eligibility searches or inspect prior mathematical solution bodies. The coordinator's separate operational checks and final publication gate remain distinct from this exact-file review.

The README's references to the final semantic review, packaged hashes, and publication records must be fulfilled by final packaging; those later administrative artifacts are outside the frozen 31-input manifest. This review may accompany byte-identical reviewed materials. Any change to the mathematical source or report requires renewed review of the affected content and identities.

**Final assessment:** the frozen submission contains a complete, correct disproof of literal exact square-root attainment over prime fields and therefore of the supplied conjecture's conjunction under both formalized prime-quantifier readings. The formal source, theorem statements, report, and PDF are consistent. Local semantic and artifact validation passes. Repository acceptance, merge, and publication eligibility are not asserted by this review.
