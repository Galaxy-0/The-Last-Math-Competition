# Independent internal review of conjecture 00000002531

**Verdict: PASS, under the disclosed ordinary Euclidean and standard normalized-Hausdorff interpretation.** The complete report and formal proof correctly disprove a necessary first clause of the conjecture. No mathematical, formal-correspondence, auxiliary-execution, or report/PDF defect was found. This is local independent verification, not competition maintainer acceptance, merge approval, or an independent live eligibility certification.

## Independence and reviewed scope

I began this nonauthor review without prior mathematical context or proof strategies. I did not author or edit the candidate mathematics, report, or frozen package. I read the entire exact bilingual source, both full current contribution guides, all source/configuration files, author correspondence notes, candidate-free semantic preassessment, verification code, audits and their outputs, the complete two-page LaTeX report, and the package README and verification summary. I read the two supplied administrative eligibility records as records rather than repeating their live searches; I did not consult the mathematics in other submissions or unrelated problems. All my writes were confined to new `/private/tmp/tlmc2531-review*` scratch.

Every one of the 40 input files was read or decoded in its appropriate form and checked against the frozen manifest. Repeated build/type/axiom/environment transcripts were additionally compared byte-for-byte against independently reproduced outputs. All compiled declaration records were decoded and checked, including the generated declarations and full logical-dependency issue fields. Both supplied PDF page images and both independently exported page images were visually inspected in full; all extracted PDF text was read.

The manifest is `/private/tmp/tlmc2531-review-inputs.json`, SHA256 `a5fd32ca801cc29bdef13a7d274dd0b6f3fd1f9a7af0c357c5f93f653fdd3e0a`, frozen at `2026-10-05T08:42:00.526713+00:00`. All 40 mapped inputs matched at initial and final checks. The table below binds every reviewed file by its intended package name. The manifest supplies the original absolute locations.

## Mathematical and source correspondence review

Both languages use the denominator `r^k` and assert that the density exists and belongs to `{0,1}` after discarding a Hausdorff-null set. They then join further nonexistence-exception dimension and sharpness assertions. Neither language adds a finite-total-measure or geometric regularity hypothesis. The disclosed interpretation uses the ordinary Euclidean real line, `k = n = 1`, balls centered at the point of evaluation, and all positive real radii tending to zero. Those conventions are ordinary specializations of the source's intended setting, not claims that its omitted full ambient class or parameter range have been uniquely determined.

For `E = R`, the measure of every radius-`r` open ball is `2r`. The explicitly declared Hausdorff normalization is `omega_1 / 2^1`; the unit one-ball volume is two, so this factor equals one. Therefore the unchanged quotient is `(2r)/r^1 = 2` for every positive real radius, at every real point. Its full right-hand limit exists and equals two. Uniqueness excludes both allowed targets zero and one. If an admissible null set removed every binary-density failure, it would contain every real point and equal `R`, whose measure is infinite, contradicting nullity. Thus this is an almost-everywhere counterexample, not merely one bad point. Infinite total measure is permitted by the source; all relevant ball numerators and positive-radius denominators are finite.

The library objects are genuine. The proof uses `Measure.hausdorffMeasure 1`, whose pinned implementation is the diameter-gauge Hausdorff construction. Its arbitrary-set outer values are characterized by `hausdorffMeasure_apply`. The normalization coefficient is explicitly represented and proved equal to one, and `hausdorffMeasure_real` identifies the resulting real-line measure with length. The actual metric is certified as `dist x y = |x-y|`; the actual `Metric.ball` is the strict metric ball. There is no substitute measure or metric and no unverified dimension-dependent identification. The word “spherical” in the source describes its ball-based density formula; no ball-cover-only spherical Hausdorff measure is substituted.

I independently checked the pinned primary Mathlib source for the Hausdorff construction, real-line equality, real ball/universe volume, real Borel measurable space, Caratheodory splitting, a.e. restriction, and positive-radius nontriviality. I also checked [Leon Simon's author-hosted text](https://math.stanford.edu/~lms/ntu-gmt-text.pdf), Chapter 1 formulas 2.1–2.2 and 3.1: its measure uses the coefficient `omega_k/2^k`, and its separate density definition uses `omega_k r^k` below the fraction. The submission correctly imports only the measure convention and retains the conjecture's different denominator. This reference supports the disclosed convention; the formal proof does not depend on an unformalized external theorem.

`HausdorffMeasurable` is the actual outer-measure `IsCaratheodory` predicate, quantified over every test set. The real `MeasurableSet` predicate is Borel measurability; the proof establishes Borel-to-Caratheodory inclusion rather than equating those classes. `BorelDensityClause` and `CaratheodoryDensityClause` are explicitly necessary first-clause specializations. The former follows from the latter. `NullExceptionalBinaryDensity` retains an arbitrary null set allowed to depend on `E`, followed by the assertion at every point of `E` outside that set. No unnecessary measurability assumption on the density predicate or null exception is introduced. The restricted-a.e. equivalence for Borel `E` is proved, and the separate ambient-a.e. implication is correct. With `E = R`, the two a.e. scopes also coincide directly.

The quotient is extended-nonnegative-real-valued. It contains no `toReal` conversion, default-valued limit, or assumption erasing an infinite value. For positive radii, `ofReal (r^1)` is positive and finite. Values at zero and negative radii have no effect on `nhdsWithin 0 (Ioi 0)`. This full real-radius filter is nontrivial. The usual Hausdorff topology on `ENNReal` supports the actual limit-uniqueness step, so convergence is neither filter-vacuous nor limited to a selected sequence.

The source-to-necessary-clause implication is semantic reasoning under the stated conventions: the ordinary one-dimensional Euclidean case is admitted, Borel sets are Hausdorff measurable, either natural a.e. reading implies the null-exception condition, and the finite allowed values and denominator agree. The generic Lean theorem `not_statement_implying_borelDensityClause` correctly proves the logical implication once that necessity premise is supplied. It does not, by itself, formalize the missing natural-language conventions. The report, README and verification summary correctly maintain this distinction. Likewise, `not_borelDensityClause_and` has an uninterpreted remaining-conjunct parameter rather than a fake definition of the entire source. Refuting the necessary first conjunct is sufficient for disproof; the submission does not separately claim to refute existence, the dimension bound, or sharpness. In this example the limit exists everywhere.

## Independent Lean and auxiliary execution

I read and executed the exact frozen `independent-verify.py` into the previously nonexistent `/private/tmp/tlmc2531-review-build`, with evidence at `/private/tmp/tlmc2531-review-execution`. The compiler is Lean 4.19.0, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all nine dependency revisions and their tracked-source cleanliness were checked before and after. Inherited `LEAN_PATH` and `LEAN_SRC_PATH` were removed for each invocation.

- Fresh complete project build: PASS.
- Direct replay of `Conjecture2531.lean` and `Check.lean` with warnings treated as errors: PASS.
- Five frozen source/configuration files unchanged throughout: PASS.
- All nine genuine definitions and all 22 authored theorem types and axiom reports: PASS.
- Exhaustive origin-module inventory: PASS, covering 37 declarations: 31 authored plus six generated.
- Every logical declaration and dependency closure has no unsafe, partial or missing dependency: PASS.
- No custom axiom or proof-bypass source construct; no `sorry`, `admit`, or `native_decide`: PASS.
- All axiom sets are subsets of `propext`, `Classical.choice`, `Quot.sound`: PASS. One generated arithmetic proof has no axioms.

The six generated declarations are the equation lemmas for `densityQuotient`, `hausdorffNormalization`, `normalizedHausdorff1` and `unitBallVolume`, plus `hausdorffNormalization._proof_1` and `normalizedHausdorff1._proof_2`. None was silently omitted. There are no authored instances or generated unsafe runtime constants in this module. Build, definition/type/axiom, inventory-harness and inventory raw-output files reproduce the supplied bytes exactly; all 37 parsed declaration records agree exactly.

I also copied the exact auxiliary `Inspect.lean` into my fresh build and executed it with warnings treated as errors. It printed all 31 authored declarations and their axiom dependencies, with output byte-identical to the supplied author inspection. Both the Python verifier and PDF export helper were actually executed after review; the inventory's metaprogramming only inspects the checked environment and proves no mathematical result. No separate numerical computation is required.

## Full report and PDF review

The frozen report source is `bdf34598a729336ece9a96e96a518f92fd9bad15d83b3037f7d955e1d6cfceac`; the submitted PDF is `711e39b5c352d1f805b4bdafec02871188fb8d65f94c6e1b2c40ea0cdb700f18`.

I copied the exact TeX to `/private/tmp/tlmc2531-review-report/main.tex`, requested its native editor view, and invoked `mcp__codex_app__compile_latex_document`. The actual compiler result was `kind: success`; its raw tool response is preserved in my native compilation record. I independently executed the exact frozen export helper with this native confirmation and my own report/evidence directories. Tectonic export succeeded with no warnings, errors, overfull or underfull boxes and produced two pages. I separately rendered the original submitted PDF in my own scratch.

I visually inspected both complete supplied pages and both complete reproduced pages, and read the complete text extracted from both PDFs. The proof, mathematical symbols, theorem correspondence, references and page numbers are complete and readable with no clipping, overlaps or missing glyphs. Both independently rendered submitted pages are byte-identical to the supplied images and to the independently exported pages. The extracted text also matches byte-for-byte, SHA256 `f163e2149be5b3618b813fde51693cce409e325dabc337bc633a248a0c6f39eb`.

The independently reproduced PDF has SHA256 `8e439c5778f3b041271b0ecf524dd2fbfd1a2db981c3b179714ee98c6d5e83ee`. The files differ in creation metadata and document identifiers; exact PDF-byte equality is not asserted. Their complete text and every rendered page match. The page-image SHA256 values are `53ca04ae2dd019557f8e3ff1d75bb04dc8110ef8fd924e0240a543a992715106` and `1d8313aefde480f5169744a1542d8e973ca4c27ccc0e4ff7b85af00ec6d80beb`.

## Precise limitations and contribution status

The verdict applies under the openly stated conventional interpretation. The source leaves its complete ambient class, parameter range, normalization, a.e. scope and later exceptional-dimension/sharpness quantifiers implicit. The submission does not claim a unique formalization of all conceivable resolutions. Changing the measure by a factor of one half or changing the denominator to `2r` would change this example; neither change is made here. The later conjuncts are not individually settled.

The project was freshly rebuilt and re-elaborated, but it reused the specified pinned dependency artifacts. I did not rebuild the Lean compiler or all of Mathlib from foundational source. The two administrative eligibility results were read and hash-verified, not independently recertified against live external records. Their accessible-public-record and timestamp limitations remain in force, and final publication deltas remain the coordinator's separate responsibility.

The full bilingual guides require a matching LaTeX source, PDF, Lean project and successful auxiliary checks. The frozen materials and this review satisfy those local review checks. I made no repository or external-state mutations. Final personal-folder-only publication, current eligibility, maintainers' disposition, merge, and leaderboard changes are outside this internal verdict. No report or proof changes are required by this review.

## Exact reviewed input identities

| Intended package path | SHA256 |
|---|---|
| `README.md` | `14830bffdcc116f366ce0299fd777572269ef387222ba78b1333b52ce2d2f7b8` |
| `verification.txt` | `7b0730f4f0cff820ae4d61c06fabff915d5ea0ed80f426304df3e4023c6611b5` |
| `conjecture.md` | `25031258d307ecfb18f81ee107ba8633b8e188ac7c5400f589498d589e1a0075` |
| `main.tex` | `bdf34598a729336ece9a96e96a518f92fd9bad15d83b3037f7d955e1d6cfceac` |
| `main.pdf` | `711e39b5c352d1f805b4bdafec02871188fb8d65f94c6e1b2c40ea0cdb700f18` |
| `lean/Conjecture2531.lean` | `e8c4fe7476cc700cbdd95510f6e868d5bb62fb38f57acce9e607ed029ca44e0a` |
| `lean/Check.lean` | `9ec22f76874ec18b241b752f0990a4b4c124da52df4161f64df83e7fc282cb57` |
| `lean/lakefile.toml` | `a5e371dc2a2a328621da6bb86e578896850ea9d82d6f5f1c16cc04a549a11167` |
| `lean/lake-manifest.json` | `0e25feb8fe0bb12655b975e29e4be4fedcadf3a1788150242d3d57048b71c3b1` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `verification/audit-names.json` | `61a907da99ac6d440aca72f9ecd3471aebefd34728718674f1b5a141b7afefa6` |
| `verification/frozen-sources.json` | `2cd0cac66dd4fe4f197d2fa723c6e4cb333eda0d6cbae9a8025afd57bfd89533` |
| `verification/independent-verify.py` | `245b26e2b55dc0acb8ad22825d88d9bdeecb25ac72a4374d4e3359cdc4703de3` |
| `verification/export-pdf.py` | `a7520c2244941f0d7e3a3639c1c93574d7bd602dd5da1b1f8e8886b8eca4f109` |
| `verification/initial-eligibility.json` | `80e0a0af1e3a53f2ec12e4aea14e8c5dc93785ef0d18d6761dee6a9501c4fb02` |
| `verification/prepublication.json` | `9da9da0c30f29e8787f192899e350e3cb596c561991144cc72d73c4abe0bc782` |
| `verification/contribution-rules-en.md` | `baf790af419e0070f593eecea4861fd865cc7b544d2cde6ec674f8fc587b01d1` |
| `verification/contribution-rules-zh.md` | `d07ac1ccd888b8ee08fed8eb2e06ae15f6aa4025dbafe98790f8e2b2fc18eba7` |
| `verification/semantic-preassessment.txt` | `a8f84d04099f87488c650405f3edc79021837fcc344cfd3bd1d4de6f405d38f0` |
| `verification/formal-correspondence.txt` | `df99e4ea8f1659753e0cd65041d4aa2f0ca272c7fbf0f0a0793a46a9fc77451a` |
| `verification/auxiliary-replay.json` | `56ba29a5d302fc08e6e412c5b62f565d9a26a8881d090372aa3ee13acd0a2dea` |
| `verification/auxiliary-replay.txt` | `d5a522931766c2bb872a75f97e50d6f098f4553c09bea58d08d58017752a5f82` |
| `verification/axioms.txt` | `2d557c10a23573acfab9dafedfcdf7dedd23ffc5adbebdeb3041457c0877a2bf` |
| `verification/build.txt` | `441d29e1b7b3244b4512e0d7162ba51b60a20559ca1080978f08ab7fdc60b190` |
| `verification/environment-inventory.json` | `82472daa08763fe943fc98a94961187fa2fbbf3f9c90f3b8b51a21eb3d75cb55` |
| `verification/environment-inventory.lean` | `9effcfff1a5f2e82eb8adc0243accb1320a7586b06cfabf7934f47d65ad12086` |
| `verification/environment-inventory.txt` | `844f62c0d3ebd40b72bd6c74d1681b7b290b049f2f4702d3c133e117b693ef1d` |
| `verification/native-compile.json` | `a8d3d0165e2c2281fdb4af207986d05996cb2415ad7407e4cf7029a149056d15` |
| `verification/pdf.json` | `a37cfb2185abf03d9840377fe1caa70f4faef19b500e20dfabd06eabc68a951c` |
| `verification/pdfinfo.txt` | `7aa56d4d20ef133bf918c8957eb663923a7ecdf640e99adf8028105a23f0bbdc` |
| `verification/pdftext.txt` | `f163e2149be5b3618b813fde51693cce409e325dabc337bc633a248a0c6f39eb` |
| `verification/report-export.txt` | `4edf5775268462a55669ba9a2ee4820f611d228d94fdb6138950996749112e76` |
| `verification/strict-replay.json` | `bab063ab3f16db5426d6e4e1cd762841560d74ba330ba3932d35f4f6db7460c2` |
| `verification/author/Inspect.lean` | `6ed95a4591c43b79021d9c54ea9758ebbcbf9a08dc507667d5752c4a9fe5aa6b` |
| `verification/author/build.txt` | `441d29e1b7b3244b4512e0d7162ba51b60a20559ca1080978f08ab7fdc60b190` |
| `verification/author/strict-replay.txt` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `verification/author/inspection.txt` | `d5a522931766c2bb872a75f97e50d6f098f4553c09bea58d08d58017752a5f82` |
| `verification/report-export-raw.txt` | `4edf5775268462a55669ba9a2ee4820f611d228d94fdb6138950996749112e76` |
| `verification/report-page-1.png` | `53ca04ae2dd019557f8e3ff1d75bb04dc8110ef8fd924e0240a543a992715106` |
| `verification/report-page-2.png` | `1d8313aefde480f5169744a1542d8e973ca4c27ccc0e4ff7b85af00ec6d80beb` |

## Independent reproduction records

The following records were produced by this reviewer in `/private/tmp/tlmc2531-review-execution`. Their exact identities bind the separate build, auxiliary replay, native compiler response, complete visual review and final input recheck.

| Record | SHA256 |
|---|---|
| `strict-replay.json` | `37116caed58a79311cd7f3e2e707385efd2ac692381ccda0200b63cc633c7f24` |
| `auxiliary-replay.json` | `9cc5a73626f257c0228b5873b597c07c0beda317b57b3d5f7e5f2b58a43a9bc4` |
| `native-compile.json` | `20605e44370479bc1b06fb4d19cc84e0ab53d0d619afa73a8630210d91239d35` |
| `pdf.json` | `d23704744c8ca49c74596b19517bfe9ac7895cf2ef394c28dd0e609835cd59c5` |
| `pdf-reproduction-comparison.json` | `94d63e74ed097784f5268d543b593b9e0bd8bbf759532bfe7c44e699439683ae` |
| `pdf-metadata-comparison.json` | `f546205df2b2a4b5197bd5e287bc50143276c99b70ca0064c8b57f73095f711d` |
| `full-input-hash-check-final.json` | `2358781745dd5de69709a10cf5cf67fb50d106b6a3d4bb2c496af5dcb1ce6f53` |

Final local review completed: 2026-10-05T08:46:21.145005+00:00.
