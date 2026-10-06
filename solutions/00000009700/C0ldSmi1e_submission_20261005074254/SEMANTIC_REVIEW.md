# Independent semantic and reproducibility review: conjecture 00000009700

**Disposition: PASS.** The frozen candidate gives a complete disproof of the stated conjunction under its explicitly declared, standard real/rational interpretation. It supplies a genuine nonempty qualifying set whose genuine Hausdorff dimension is zero, thereby contradicting the universally asserted dimension one. No correction to the frozen proof or report is required.

This is an independent nonauthor internal review, not maintainer acceptance, a merge decision, or authorization to update competition standings. Review completed on October 5, 2026. The reviewer did not read previous submissions, unrelated candidate mathematics, previous chats, or agent inventories; did not author or modify this candidate; and did not commit, push, comment, or make any external post. A limited attempt to delegate report reproduction was refused by the concurrency limit; no assisting reviewer was created. All scrutiny and replays described below were performed by this reviewer.

## Frozen scope and integrity

The review input was the complete 50-file manifest `/private/tmp/tlmc9700-review-inputs.json`, SHA256:

`4340af703c62136608e42132316db64375b061227ac4407d79ddbe16d2fd61c1`

I read every textual input in full. I inspected the complete TeX report, extracted and read the PDF's full text, and visually inspected both pages. Both supplied PNG inputs were also viewed, and fresh rendering of the actual frozen PDF reproduced them exactly. Before and after the review, all 50 complete-file hashes matched the manifest; the manifest hash itself remained unchanged. The final table below enumerates all 50 names and hashes. Evidence is saved only under `/private/tmp/tlmc9700-semantic/review-evidence/`; no frozen source, configuration, report, image, script, or original log was overwritten.

Key identities:

- Complete bilingual source: `c5981f9f79d7718626657135ef176acbacaeb15827c5603c9997944ef70bb1a9`.
- Entire proof module: `3180becac5ea37a91bcb2d03d5e83969e64f2a196156eae1c211b0c7ea5e8d0d`.
- TeX report: `311dcd37646aad1aa1c12c6572eda489d1c51fd0a2509f64f24192651ab547f2`.
- Frozen PDF: `9a085a6635f208a2c0d537ed7c54d4decc860ac1d926e8a6cc0c6a04bfb56d22`.

The complete English and Chinese contribution guides were read, including the submission-scope rules and the requirement to review the whole report, compile the entire Lean proof, exclude admissions and other incompleteness, check source correspondence, and execute all auxiliary code. Their recorded prohibitions on `native_decide` and additional axioms were also applied. The guide's maintainer/reviewer merge and leaderboard actions are outside this internal review's authority.

## Independent source interpretation

The English “Every” and Chinese “一切” both universally quantify over algebraically independent sets of transcendental numbers. Both require Hausdorff dimension exactly one. The word “and” and its Chinese counterpart “且” make the complement-spectrum assertion another conclusion about the same qualifying set. The later full-measure/dense/G-delta sentence also asserts a conclusion; it does not add an antecedent to the first clause.

Neither version imposes infinitude, uncountability, maximality, a transcendence-basis property, positive measure, or any other condition excluding a singleton. “Algebraically independent” does not by itself mean maximal algebraic independence or a transcendence basis. The report accurately quotes the English assertion and describes the Chinese one. Its finite nonempty counterexample therefore addresses the source's unrestricted quantifier, rather than a weakened or repaired surrogate.

The source does not literally specify either the ambient real line or the rational coefficient field. I independently accept the candidate's explicit convention: ordinary real numbers with the usual metric, and transcendence and algebraic independence over the rationals. The rational field is the ordinary meaning of unqualified transcendental numbers; calling dimension one “full,” together with the Lebesgue measure terminology, supports the real-line reading. These are inferences, correctly disclosed in the source comments, report, README, and verification record. I do not upgrade them into explicit source text or claim that the Lean proof treats arbitrary coefficient fields, arbitrary metrics, a complex ambient space, or a prescribed interval.

The undefined “box dimension spectrum” phrase does not make the separately stated first conjunct disappear. Its exact parameters, complement ambient space, and spectrum convention are not specified. The submission appropriately neither invents these nor claims to formalize them. Under the disclosed standard domain, refuting the mandatory first conjunct suffices to refute the entire written conjunction. A strengthened conjecture restricted to infinite or maximal sets would be a different claim and is outside this verdict.

The preassessment and author handoff were treated as claims to check, not as evidence of validity. In particular, the preassessment's `MeasureTheory.dimH` spelling is not the pinned declaration name. I checked the pinned source and compiled body: the genuine API is root-level `dimH`. The separate clarification accurately identifies a namespace correction, with no substitution of a mathematical invariant.

## Definitions and mathematical argument

For clarity, let `I(S)` mean `AlgebraicIndependent ℚ (Subtype.val : S → ℝ)`, and let `T(S)` mean `∀ x ∈ S, Transcendental ℚ x`. The only new definition is exactly

`HausdorffClause := ∀ S : Set ℝ, I(S) → T(S) → dimH S = 1`.

I checked the full elaborated body with explicit arguments, rather than relying on the abbreviated display of `Subtype.val`. Its index type is the subtype of members of the very same set `S`; its coefficient ring is `Rat`; its target is `Real`; its rational algebra is the standard one; and dimension uses `Real.metricSpace` through `MetricSpace.toEMetricSpace`. Both zero and one in the dimension equations are the corresponding `ENNReal` values. No alternative set, metric, algebra structure, or numerical codomain is hidden by notation.

The actual pinned definitions are appropriate:

- `AlgebraicIndependent` is injectivity of the evaluation algebra homomorphism on `MvPolynomial S ℚ`, not a custom unary predicate or an unrelated family. The distinct set members index the variables.
- `IsAlgebraic ℚ x` asserts existence of a nonzero rational univariate polynomial vanishing at `x`; `Transcendental ℚ x` is its negation. Mere irrationality is never substituted.
- `dimH` takes the supremum of nonnegative exponents at which the Hausdorff measure of the set is infinite, with values in `ENNReal` and the Borel measurable structure of the actual metric space. The inspected `hausdorffMeasure` body is `mkMetric (fun r => r ^ d)`; its covering formula takes infima over countable covers with arbitrarily small bounded diameter. The characteristic theorems and singleton theorem therefore concern standard Hausdorff dimension.

The cited [Stacks Project definition 9.26.1](https://stacks.math.columbia.edu/tag/030E) was independently opened and checked. It uses injectivity of polynomial evaluation for algebraic independence and separately defines transcendence bases, supporting the correspondence and the absence of an implicit maximality condition. Pinned Mathlib definitions and proofs were read directly from the authorized dependency tree, including `AlgebraicIndependent/Defs.lean`, `Algebraic/Defs.lean`, `AlgebraicIndependent/Transcendental.lean`, `Algebra/AlgebraicCard.lean`, `Data/Real/Cardinality.lean`, `Topology/MetricSpace/HausdorffDimension.lean`, and the relevant Hausdorff measure definitions and covering formula. No external mathematical result is needed to fill a gap in the formal proof.

The proof is mathematically valid, as follows.

1. The rational polynomials form a countable set and each nonzero one has finitely many real roots. Thus the real numbers algebraic over the rationals are countable. The library proof `Algebraic.countable` establishes exactly the required countability, with its field/domain hypotheses supplied by the standard rational and real instances. The uncountability theorem is about the entire genuine real line. If no transcendental real existed, every real would be algebraic, making that line countable. Classical negation elimination in the proof implements this contradiction correctly.
2. Choose such a real `x` and take the actual set `{x}`. `Set.singleton_nonempty x` establishes nonemptiness independently of the algebraic claim. The singleton subtype is a subsingleton and contains the displayed element. `algebraicIndependent_singleton_iff` applies directly to its inclusion. Its library proof reindexes the polynomial algebra on a unique type to the ordinary one-variable polynomial algebra and proves the evaluation maps agree. Therefore transcendence of `x` establishes the exact set-level algebraic independence needed here. Every member of the singleton equals `x`, so all its members are transcendental.
3. `dimH_singleton` establishes dimension exactly zero in the usual metric. Its proof uses the genuine Hausdorff-measure dimension characterization and the finite zeroth measure of a subsingleton. The report's covering explanation for every positive exponent gives the same conclusion. It does not rely on a numerical approximation. In `ENNReal`, zero is not one, so the witness fails the conjectured equality.
4. Applying `HausdorffClause` to this same witness and both proved hypotheses would give dimension one, contrary to its proved inequality. Thus `hausdorff_clause_false` is the required negation of the necessary universal clause.
5. For any predicate `P` on the same qualifying sets, a conclusion `dimH S = 1 ∧ P S` projects to the first equality. The arbitrary-conjunct theorem refutes every such universal conjunction, without assigning a meaning to `P`. The final proposition-level theorem similarly derives `¬P` whenever `P` entails the already refuted clause. This is a sound source-to-clause logical bridge, not an assumption that the source is false or a replacement definition for its unspecified spectrum.

## Every candidate declaration checked

All names in this table have prefix `Conjecture9700.`. The displayed summaries retain every hypothesis and conclusion; the full compiled types and bodies are preserved in the evidence.

| Declaration | Exact mathematical content checked | Closure size |
|---|---|---:|
| `HausdorffClause` | Definition `∀ S : Set ℝ, I(S) → T(S) → dimH S = 1` | 16064 |
| `exists_transcendental_real` | `∃ x : ℝ, Transcendental ℚ x` | 16985 |
| `singleton_independent_iff` | For every real `x`, `I({x}) ↔ Transcendental ℚ x` | 12022 |
| `singleton_members_transcendental` | For every real `x`, transcendence of `x` implies `T({x})` | 11356 |
| `singleton_dimension_zero` | For every real `x`, `dimH {x} = 0` | 16227 |
| `exists_nonempty_counterexample` | `∃ S : Set ℝ, S.Nonempty ∧ I(S) ∧ T(S) ∧ dimH S = 0 ∧ dimH S ≠ 1` | 20239 |
| `hausdorff_clause_false` | `¬HausdorffClause` | 20241 |
| `conjunction_implies_hausdorff_clause` | Every `P : Set ℝ → Prop` and proof of `∀ S, I(S) → T(S) → dimH S = 1 ∧ P S` yield `HausdorffClause` | 16065 |
| `universal_conjunction_false` | For every `P : Set ℝ → Prop`, negation of that universal conjunction | 20243 |
| `not_statement_implying_hausdorff_clause` | For every `P : Prop`, `(P → HausdorffClause) → ¬P` | 20242 |

The source contains exactly this one definition and nine theorems, with no custom axioms, anonymous proofs, private declarations, named instances, or further mathematical modules. `Check.lean` contains inspection commands only. The compiled-origin enumeration confirms exactly these ten constants, with zero generated/additional constants. I checked the actual records against my own explicit ten-name inventory, not only against the supplied JSON's PASS flag.

Each of the ten declarations is safe and nonpartial. Each axiom closure is exactly `{propext, Classical.choice, Quot.sound}`. Every unsafe, partial, and missing-dependency list is empty. The code contains no `sorry`, `admit`, `native_decide`, custom axiom, skipped kernel check, unsafe/partial proof definition, or elaborator/runtime proof bypass.

The verifier itself was read in full before execution. Its traversal combines every declaration's type with definition, theorem, or opaque body; it also follows mutual inductive groups and constructors, and recursor groups, constructors, and reduction-rule right-hand sides. Constructor types lead back to their inductives. It inventories by originating compiled module, not merely a chosen name prefix. There are no compiler runtime exceptions to excuse in this candidate because no such additional constants exist. The auxiliary harness's `partial` traversal and `run_elab` are inspection machinery outside the proof module; they print existing declarations and do not establish any submitted mathematical theorem. This distinction was checked in code and in the dependency output.

## Independent execution and reproduction

The pinned compiler reported Lean 4.19.0, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The full nine-package manifest was read; all nine exact Git revisions and clean tracked source trees were checked before and after the strict run. Compiler version and reported commit were unchanged. Inherited `LEAN_PATH` and `LEAN_SRC_PATH` were cleared by both checkers.

The strict build directory did not exist before this command; it was created by the verifier, with no candidate build outputs present. Only the two frozen Lean sources and three frozen configurations were copied. The shared dependency packages were linked as authorized.

```sh
python3 /private/tmp/tlmc9700-independent-verify.py --ready \
  --build-dir /private/tmp/tlmc9700-semantic/review-evidence/strict-build \
  --evidence-dir /private/tmp/tlmc9700-semantic/review-evidence/strict
```

Exit status was zero. The actual subprocesses were the pinned `lake build`, strict `lake env lean -DwarningAsError=true Conjecture9700.lean`, strict replay of `Check.lean`, and the generated complete environment inspector. They all exited zero. The fresh default build compiled `Conjecture9700`; the only other candidate Lean file is the inspection-only `Check.lean`, which was separately replayed. Every frozen and copied source/configuration hash matched before and after all audits. The run completed at `2026-10-05T07:30:45.086756+00:00`.

The strict replay's entire JSON was compared with the original frozen execution record. Its only differences are the independent build path, timestamps, and elapsed times. All declaration records, types, direct dependencies, closure sizes, safety flags, axiom sets, source identities, compiler identity, and dependency checks agree exactly. The raw environment transcript and `Check` output are byte-identical to the frozen transcripts. This comparison is recorded in `review-evidence/replay-crosscheck.json`.

For the corrected author checker, a second initially empty project directory was created at `review-evidence/auxiliary-build`. It contains only `Conjecture9700.lean`, `Check.lean`, the three configurations, and the dependency link. The generated strict inspector was deliberately not included as an authored proof source. The exact final auxiliary script was then run:

```sh
python3 /private/tmp/tlmc9700-auxiliary/verify_author.py \
  --project /private/tmp/tlmc9700-semantic/review-evidence/auxiliary-build \
  --lake /private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin/lake \
  --output /private/tmp/tlmc9700-semantic/review-evidence/auxiliary-replay
```

Exit status was zero. The default build, proof replay, `Check` replay, and the exact supplied `Inspect.lean` all succeeded. That harness prints the real definitions and all ten axiom audits. The corrected checker requires the emitted audit list to match its declaration list exactly. Its final summary is byte-identical to the frozen corrected-replay summary. All nonbuild transcript bodies also agree exactly after their path-bearing command headers; the fresh build additionally reports compiling the candidate, as expected.

I also created an inspection-only `review-evidence/ReviewedBodies.lean` outside the candidate source trees. It imports the fresh candidate, enables full names, universes, explicit arguments and proof bodies, prints all ten candidate declarations, and prints the complete definitions of algebraic independence, transcendence, algebraicity, Hausdorff dimension, and Hausdorff measure. It proves nothing. This command exited zero from the strict build directory:

```sh
env -u LEAN_PATH -u LEAN_SRC_PATH \
  PATH=/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin:/usr/bin:/bin \
  /private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin/lake env lean \
  -DwarningAsError=true \
  /private/tmp/tlmc9700-semantic/review-evidence/ReviewedBodies.lean \
  > /private/tmp/tlmc9700-semantic/review-evidence/reviewed-bodies.txt
```

The entire resulting 44,247-byte transcript was read. Its SHA256 is `912d3426dec46d75df534b06473629fe6d9fd76ac81df84a8b74b2b805fe22b5`. This independently resolves implicit index types, actual metric and algebra instances, numeric types, all proof bodies, and the logical projections.

## Auxiliary history and provenance

The original author logs are correctly labeled historical. Their summary lists the original proof source and all ten declarations but lacks the later fields for the emitted-axiom list, `Check` replay, and checker hash. The separately frozen corrected replay includes those fields, has checker hash `7d1aa2904f26fb4537e1a265d67eefe7c8a7b2f08428730f7f3ce554b75c681d`, and its summary hash agrees with `auxiliary-correction.json`. The current script actually implements all three documented changes: it handles inspection-only `Check.lean`, demands complete parsed axiom coverage, and clears inherited Lean search paths. The proof hash is unchanged across these records and all fresh replays.

The record's old checker hash is a historical attribution: the old script itself is not among the frozen inputs, so that former script's bytes were not independently reconstructed. This does not leave a current execution gap. The exact final script, exact inspection source, current proof and every current check were all read and rerun. No numerical mathematical computation, approximation, generated certificate, or external calculation is claimed or needed; the Python scripts perform execution, identity, inspection, and report-export work.

## Complete TeX/PDF review and reproduction

I read every section of `main.tex`: the abstract, complete source quotation and conventions, definitions and quantifier, existence lemma, counterexample theorem and proof, necessary-conjunct explanation, formal verification claims, and references. They match the Lean result and the source scope described above. The statements about fresh compilation and the ten safe declarations are supported by both frozen and independently reproduced evidence.

A direct independent call to `compile_latex_document` on the exact frozen `/private/tmp/tlmc9700-report/main.tex` returned `kind: success` and “The current source compiled successfully with the desktop editor's compiler.” Its source hash was checked, and a separate observation record is in `review-evidence/native-compile.json`. No source edit was made.

The final export script was read completely, and the exact TeX was copied to a separate report directory. The following command exited zero:

```sh
python3 /private/tmp/tlmc9700-export-pdf.py \
  --report /private/tmp/tlmc9700-semantic/review-evidence/report-replay \
  --evidence /private/tmp/tlmc9700-semantic/review-evidence/pdf-replay
```

Its default exporter was `/private/tmp/tlmc310-pdf/tectonic`; its rendering tools were the bundled Poppler binaries. No native-confirmation option was passed. The fresh export correctly records `native_compiler.kind = not_invoked`: the script itself does not invoke or establish native compilation. The separate observed tool success above must not be confused with that export record.

Tectonic reported no warnings, overfull/underfull boxes, or errors. The output has two letter-size pages. I independently rendered the actual frozen PDF with the same `pdftoppm -scale-to 1600 -png` settings into `review-evidence/original-render/`. Both independently rendered page PNGs match the supplied frozen PNGs byte-for-byte. Both regenerated report page PNGs also match byte-for-byte and pixel-for-pixel. I viewed both original page images and both regenerated page images. The title, full source quotation, equations, proof, theorem names, references and page numbers are readable; there is no clipped text, overlap, missing glyph, blank spill page, or omitted proof portion.

The complete extracted PDF text was read and matches between original and replay. The original extraction also matches the supplied frozen text. Both page content streams are exactly equal. The PDF files themselves are **not byte-identical**:

- Frozen PDF: 36,505 bytes, SHA256 `9a085a6635f208a2c0d537ed7c54d4decc860ac1d926e8a6cc0c6a04bfb56d22`.
- Independent export: 36,506 bytes, SHA256 `03a41b7154a5e550c43345cc9582ff3365a31a24ba84e9b424b8065e6e17bdac`.

The decoded comparison covers all 91 PDF objects. The Info object's creation date changes from `D:20261005072101-00'00'` to `D:20261005073131-00'00'`; the enclosing object stream is equal after replacing only that timestamp. Document IDs differ. The sole cross-reference offset change is object 91 moving from byte 36057 to 36058, consistent with the one-byte file-size difference. Other logical objects and decoded content agree. Thus the reproduction succeeds in content and layout; no claim of PDF byte identity is made. Detailed records are `review-evidence/pdf-comparison.json` and `pdf-metadata-detail.json`.

## Issues, limits, and final disposition

No mathematical, formal, report, or current reproducibility defect was found. The naming clarification is accurate; the historical/final checker distinction is accurately documented; the PDF hash difference is explained by observed metadata and PDF packaging differences; and the exporter truthfully separates native compilation from its own work. These are resolved or explicitly bounded matters, not outstanding corrections.

The verdict retains the following limits:

- The real/rational interpretation is standard and supported but inferred, as the report explicitly says. No broader alternative-domain formal theorem is claimed.
- The unknown spectrum is not defined, and the later measure/topology assertions are not individually settled. The necessary universal Hausdorff clause is nevertheless formally false, which is enough for the written conjunction.
- Reproduction used the authorized pinned Lean compiler and existing dependency packages/cache. The candidate build itself was fresh. This review did not reconstruct the compiler or rebuild every dependency from source; normal Lean, Mathlib and platform trust remain.
- Both timestamped eligibility records were read in full, including their coverage limits. This semantic review did not independently repeat live remote eligibility or certify deleted/private records. A publication-time delta check remains a separate workflow obligation, as the package already states.
- Subsequent changes to any reviewed mathematical/report/configuration input require renewed review; this verdict binds the exact manifest above. Packaging additions such as this review, final checksums and later eligibility evidence are not preclaimed as frozen mathematical inputs.

**Final verdict: PASS / READY for the separate authorized publication workflow, subject to its live eligibility gate.** This is a valid nonempty counterexample to a necessary clause of the actual bilingual source under the disclosed convention. There are no requested corrections and no live review shell sessions. All original frozen files remain unchanged.

## Complete frozen-input hash coverage

Every row below passed both pre-review and post-review SHA256 verification. All 47 textual inputs were read completely; the PDF was read through full extraction and every page image, and both PNG inputs were visually inspected and tied to independently rendered PDF pages. The manifest maps these intended submission-relative names to the exact frozen paths.

| Intended submission-relative name | SHA256 (before = expected = after) |
|---|---|
| `README.md` | `8b8f67dbdde7e18b95063da1908dfd585b4e1379779b17011335296a9ee8545f` |
| `verification.txt` | `127b53f6f3f13f410c1da4a928d771865747cc4b233798e91e9c46cadb5fce56` |
| `conjecture.md` | `c5981f9f79d7718626657135ef176acbacaeb15827c5603c9997944ef70bb1a9` |
| `main.tex` | `311dcd37646aad1aa1c12c6572eda489d1c51fd0a2509f64f24192651ab547f2` |
| `main.pdf` | `9a085a6635f208a2c0d537ed7c54d4decc860ac1d926e8a6cc0c6a04bfb56d22` |
| `lean/Conjecture9700.lean` | `3180becac5ea37a91bcb2d03d5e83969e64f2a196156eae1c211b0c7ea5e8d0d` |
| `lean/Check.lean` | `8c520b65d65c851e469e4f54697a99250a1af9b9e20fd058d16c063923bcbd28` |
| `lean/lakefile.toml` | `f2df51cc1755a8521837c982dc800b29d470acafacf2a5396616d1b16998fcdd` |
| `lean/lake-manifest.json` | `490567857761bd362b825695c10ae6918ca4de5a3ef417b004684a8a801e7273` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `verification/audit-names.json` | `5c19de8f24af7d55d8dd7e048e9535dbef199b7536736903fb7f6fded5d514f4` |
| `verification/frozen-sources.json` | `2ca53b07741f0baa7dd691fcdc711771049420bf05f6893fbd5454e41308e838` |
| `verification/independent-verify.py` | `e0d4b9c2921a308f50082d5ac8d08f019a814544a3b49529e591dc2baa10c0b8` |
| `verification/export-pdf.py` | `83ae5b959e9f090584f6c646bae4d7bd5bec81ab4139078e899e1fae74dfeecb` |
| `verification/initial-eligibility.json` | `1c7479384f6a45bfbbbb2347087b0192e8704e38d881de0acc63d421a8bfa097` |
| `verification/prepublication.json` | `8dce08dd92e4e96884e6c9d84ab0990cc3d99f44df39e11d975d307dd0ff11d4` |
| `verification/contribution-rules-en.md` | `84cd9992c3b4027d90044109df969e22390051df4a5f7f21ca81138e5f717795` |
| `verification/contribution-rules-zh.md` | `167c69fba1d5592feb55117da9a0151b0355ff6b2a0fb773115f367e58c59b47` |
| `verification/semantic-preassessment.txt` | `f59f737fa39526fd7181c233cac68f3fc28ed6dcc1e9e3156f04cf63e49df4bd` |
| `verification/formal-correspondence.txt` | `d57fa07a567857f77554685ebbb6830b60fa886fbebae2f0ee83a6e97a5dbfed` |
| `verification/build.txt` | `52b3cba695cbded2de649b2b178bc8bf548a4e5b4676a13b35196bf3fbc55964` |
| `verification/axioms.txt` | `0bbd0948bf3d3a83124633ce706f342c7b0c32a4d8d576b41ee1b86c0a6a98e9` |
| `verification/strict-replay.json` | `2a8fbdb61065670375762891efd692bdcba481b269a3ea5c388d577fc2975c3e` |
| `verification/environment-inventory.json` | `be5abc27d3f2a5c3e5ea356257c6e9c977eedb01b74b65ec72eef26508e999d1` |
| `verification/environment-inventory.lean` | `5bed38a9df9351d20d0d3639091d07e979b05a25605c7a58cec08f77ef7f970f` |
| `verification/environment-inventory.txt` | `2c57f7310e224d87d345d4006d5e5d8b185667a02d238d0472139b7f4b372375` |
| `verification/auxiliary-correction.json` | `92d4518198d0fb50c57a4b57779a1c9aadbfca6501817c93326fc9e6289b8616` |
| `verification/preassessment-clarification.txt` | `59318980d18126d3555b102a1b9480212a6a8037d03bd1175616ea282f00dc31` |
| `verification/pdf.json` | `71e20a318ff9a29317143f301fe2fd76125d21e76aeda92e7676ab990cbd7e43` |
| `verification/native-compile.json` | `3a888c1ca4e42f7a244127978db750c074082a98ec4df2d31afd3976a82a9677` |
| `verification/pdfinfo.txt` | `3129223f67c8d91d3d3e414606600c285708201a478966019eb3e9269dc15010` |
| `verification/pdftext.txt` | `e9d25f69ebabe95d8c3389d1068cb18409ca1b286374fca70d16fc90881add3b` |
| `verification/report-export.txt` | `89dda862650a630a44d2fa8a4c7d82f718db6fbf6c500700f585b63a4cb80798` |
| `verification/report-export-raw.txt` | `89dda862650a630a44d2fa8a4c7d82f718db6fbf6c500700f585b63a4cb80798` |
| `verification/author/Inspect.lean` | `af7e4fa44d9775b79465f9c133fe377f88e64a9afe3b9bdfa8034e9b0cc69a8e` |
| `verification/author/author-checks/default-build.txt` | `77888c360e43bd87b4d0bd5246516ab6e3c040956b4cb0d9da552717bdcdb404` |
| `verification/author/author-checks/lean-version.txt` | `9274c147aff7886cd4eaecdb3161ff8379f6f6a6dc578f8418db3e46ccb8effd` |
| `verification/author/author-checks/types-and-axioms.txt` | `b338cc8e25c140408c20c4007b42b9e26bc4412dd271c65e82af4fcf3ab18ce0` |
| `verification/author/author-checks/verification-summary.txt` | `a881f17ba5d310571d3b26c333dab15fa9109d9343cce30d760e5492d975eb62` |
| `verification/author/author-checks/warning-replay-Conjecture9700.txt` | `fbc73ad5c8be9064f37feacc418cc859b9fc442f7666c4579c8f2a1b7b8ba749` |
| `verification/author/initial-build.txt` | `fb6303ac8909b596e0292a861b14bfa9e92f5d4a51f1d1ab2d6697a9c88f0106` |
| `verification/author/verify_author.py` | `7d1aa2904f26fb4537e1a265d67eefe7c8a7b2f08428730f7f3ce554b75c681d` |
| `verification/auxiliary-replay/default-build.txt` | `77888c360e43bd87b4d0bd5246516ab6e3c040956b4cb0d9da552717bdcdb404` |
| `verification/auxiliary-replay/lean-version.txt` | `9274c147aff7886cd4eaecdb3161ff8379f6f6a6dc578f8418db3e46ccb8effd` |
| `verification/auxiliary-replay/types-and-axioms.txt` | `b338cc8e25c140408c20c4007b42b9e26bc4412dd271c65e82af4fcf3ab18ce0` |
| `verification/auxiliary-replay/verification-summary.txt` | `27131a7c0251bdabae17829c31faf37f7b2863d6585645a5bb038bed7c80c9bd` |
| `verification/auxiliary-replay/warning-replay-Check.txt` | `a937b14cf1d6001dab0a1d7a4603ebee606a93ec2f17ca100329351b276e6b7d` |
| `verification/auxiliary-replay/warning-replay-Conjecture9700.txt` | `fbc73ad5c8be9064f37feacc418cc859b9fc442f7666c4579c8f2a1b7b8ba749` |
| `verification/report-page-1.png` | `3e972a46a8bea0abb7f3e60bf461d2a8dc2434e5821a43ed27d955b1b2fae1df` |
| `verification/report-page-2.png` | `fba87211894f0e06ac46b5b3eb94967b349e2c998a4c2f2fb35201468964e600` |

Before/after machine-readable coverage: `review-evidence/hashes-before.json` and `review-evidence/hashes-after.json`. Independent results: `review-evidence/strict/`, `review-evidence/auxiliary-replay/`, `review-evidence/replay-crosscheck.json`, `review-evidence/reviewed-bodies.txt`, `review-evidence/native-compile.json`, `review-evidence/pdf-replay/`, and both PDF comparison records.
