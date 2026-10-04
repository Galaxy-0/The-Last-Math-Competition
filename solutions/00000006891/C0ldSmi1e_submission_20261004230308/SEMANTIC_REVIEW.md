# Independent semantic and evidence review: conjecture 00000006891

**Verdict: PASS.** I found no unresolved mathematical, formalization, report-correspondence, or recorded-execution blocker in the exact inputs listed below. The submission proves that a nonzero actual complex tensor has ordinary tensor rank 3 and least closed projective secant index 2. This disproves the unqualified rank/index equality in the source's first clause.

## Independence and review scope

I am the independent reviewing agent, distinct from the authors of the five mathematical implementation files and the report. I did not author or modify those files. I did author and execute the auxiliary independent verification runner and its read-only environment-inspection harness. My independence is therefore from mathematical and report authorship, not from verification-tool authorship.

I read all five implementation modules, `Check.lean`, the three configuration files, the exact English and Chinese conjecture, both complete current contribution guides, the final report source, README, and VERIFICATION document. I inspected the actual build, direct replay, theorem, environment, PDF, and eligibility records. I personally viewed all five final PDF page renders and checked their recorded identities. The final report was reread after its five-page layout was frozen.

This is local, internal scrutiny. It is not an official competition review, acceptance, merge decision, or claim that a future publication diff has been inspected. The scope is precisely the 26 frozen inputs below, with the additional current-guide identities stated separately. Publication staging and any later live eligibility gate remain separate checks.

## Source interpretation and the exact negation

Both source languages define rank by the minimum number of simple summands, then identify tensor rank with the secant-variety hierarchy index. The qualification concerning general tensors occurs in the separate dimension-counting clause. It does not qualify the earlier rank/index identification. The implemented necessary consequence is

`∀ (t : Tensor) (ht : t ≠ 0), tensorRank t = secantIndex (Projectivization.mk ℂ t ht)`.

A counterexample in the ordinary complex three-factor tensor setting contradicts this consequence and hence the stated conjunction. The final theorem `conjecture_00000006891_false` negates this predicate by an explicit witness. It does not purport to disprove generic-rank dimension counting, classify other tensor formats, or establish a new result about border rank. The report and README make these limits explicit. There is no extra hypothesis in the source that excludes this tensor format or requires the witness itself to be general.

For the terminology, I checked the primary discussion in [Buczyński–Landsberg, *On the third secant variety*, §1.1 and Proposition 1.1(c)](https://arxiv.org/abs/1111.7005), and the projective homogeneous-zero-locus construction in [Milne, *Algebraic Geometry*, Chapter 6a, Proposition 6.2](https://www.jmilne.org/math/CourseNotes/AG.pdf). They support the distinction between actual rank and closed-secant index and the projective closure convention used here. The submission proves the required witness properties directly; neither reference is used as an unproved Lean assumption.

## Actual objects and mathematical proof

**Tensor space and rank.** `Tensor` is the actual Mathlib nested tensor product of three copies of `Fin 2 → ℂ`. `pure` is the tensor-product constructor, not an assigned coordinate table. The tensor-product basis gives the actual linear equivalence `coords`; `coords_pure` and `tensor_ext` connect all coordinate calculations to tensors. The displayed W tensor is a sum of three genuine simple tensors, and a coordinate equal to 1 proves it nonzero.

`RankLE r t` quantifies over actual decompositions into `r` simple terms. Zero padding is proved, so it expresses rank at most `r`. Finite basis expansion supplies a decomposition for every tensor before `Nat.find` defines `tensorRank`. The minimality, decomposition, monotonicity, and nonzero-scalar invariance theorems are proved. Thus the minimum is not a default value or an assumed witness rank.

For the lower bound, the proof assumes an arbitrary two-summand decomposition. Coordinate identities and the scalar determinant `a₀d₁−a₁d₀` give the needed vanishing statements without dividing by that determinant. Applying the argument in both summand orders forces the relevant first-factor coordinates to vanish, contradicting W's 100-coordinate. This handles dependent, zero, and degenerate summands as well as independent ones. Together with the explicit three-term decomposition, it proves exactly `tensorRank W = 3`. The report's slice-elimination account faithfully describes the same argument.

**Projective points, spans, and closure.** The projective space is actual `Projectivization ℂ Tensor`. Segre points are precisely projectivizations of nonzero simple tensors. The unclosed `secantSpanLocus r` is the union of actual Mathlib projective spans of `r` Segre points. The generic `projective_span_mk_iff` theorem connects those projective spans with linear spans of representatives. The further rank/decomposition bridge proves that membership of a nonzero tensor's projective point in this locus is equivalent to rank at most `r`, including the handling of zero summands by zero coefficients and nonzero substitute generators.

Projective vanishing quantifies over every nonzero representative. The homogeneous scaling theorem proves the expected representative independence. `projectiveZariskiClosure` tests every homogeneous polynomial equation vanishing on the whole input locus. Its inclusion, monotonicity, algebraicity, least-algebraic-superset property, and idempotence are proved. This is the standard homogeneous-equation definition of projective algebraic closure; it is not a renamed arbitrary affine predicate. No separate projective Zariski `TopologicalSpace` instance is installed, and none is needed for this definition or proof. The report states the construction accurately.

Repeated generators are permitted in the span-locus definition, as appropriate for an at-most-r hierarchy. The concrete degeneration additionally uses two distinct Segre points whenever its parameter is nonzero, so that particular membership is robust to the convention requiring distinct generators. The zeroth span locus and its algebraic closure are proved empty, rather than left to an implicit indexing convention.

**Second-layer membership and first-layer exclusion.** The actual tensor arc has coordinates `(0,1,1,t,1,t,t,t²)` and is nonzero for every complex parameter. Multilinearity is proved to give `t • arc t = (e₀+t e₁)⊗(e₀+t e₁)⊗(e₀+t e₁) − E₀₀₀`. For every nonzero `t`, its projective point therefore lies on the actual line spanned by two nonzero distinct Segre points.

The closure argument takes an arbitrary homogeneous polynomial vanishing on the entire two-point span locus. Its evaluation along the arc is continuous, vanishes on the dense set `ℂ \ {0}`, and consequently vanishes at zero. Homogeneity then transfers this to every representative of W. Continuity is used to verify all defining equations; no equality between Euclidean and Zariski closures is assumed.

The homogeneous quadratic `X₀₀₀X₀₁₁−X₀₀₁X₀₁₀` vanishes on every actual simple tensor and takes value −1 on W. Since the one-point span locus is proved equal to the Segre set, this equation excludes W from its algebraic closure. Thus W lies in the second closed secant and outside the first.

Finally, hierarchy monotonicity and existence of a finite level for every projective point are proved before the total least index is defined. Empty level zero and exclusion from level one establish exact index 2. This supplies the genuine quantified counterexample `W ≠ 0 ∧ tensorRank W = 3 ∧ secantIndex projectiveW = 2`. I found no vacuous hypothesis, assigned invariant, incomplete representative bridge, unsupported finite test, or gap between the closed secant and the ordinary rank.

## Independent execution and complete environment audit

I ran the independent verifier against byte-identical copies of only the six Lean files and three configuration files in a fresh project directory. It completed successfully at `2026-10-04T22:52:14.640476+00:00`. Existing pinned dependency caches were shared, but project build outputs were initially absent. The actual `build.txt`, `axioms.txt`, and structured record agree: the default build and all six direct source replays with warnings treated as errors returned exit code 0. There was no failed execution attempt requiring a proof change.

The compiler was Lean 4.19.0, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, before and after execution. All nine dependency revisions matched the pinned manifest, with tracked source trees clean before and after; Mathlib was `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine source/config identities remained unchanged in the original and fresh copy through all audits. The source scan found no proof-bypass code or raw matches.

The authored inventory contains 102 declarations: 33 definitions/abbreviations and 69 theorems, with no named source instances. Actual `Check.lean` output contains all 33 definition printouts and all 69 theorem types and transitive axiom lists. These match the frozen inventory and source declaration scan. Every listed theorem uses only the permitted standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

The additional environment harness enumerated by originating module, not merely a name prefix, and emitted full types, declaration kinds, safety flags, and transitive axiom dependencies for all 147 constants originating in the five implementation modules. It included all 102 authored declarations plus all 45 generated constants, including private proof helpers. All 102 authored declarations are safe. There are 11 unsafe-marked compiler runtime artifacts: the `_cstage1`/`_cstage2` artifacts associated with `e0`, `e1`, and `segre`, including their closed-value helpers. These are explicitly listed and audited in the records; they were not silently omitted or conflated with authored unsafe proofs. No unexpected unsafe declaration, partial declaration, or custom axiom was found. All 147 transitive axiom lists contain only the permitted standard axioms, or are empty.

The submitted environment harness uses elaborator inspection to read imported metadata and print it. It is not imported by the mathematical proof, asserts no mathematical result, and supplies no unproved computation to that proof. The distinction and the 11 compiler artifacts are accurately disclosed in `VERIFICATION.md`. The separate orchestration runner's recorded SHA-256 is `9c3efba08e6c270584918c78a81fd621734fe236d65213308bfd1a417343f4a3`; it is auxiliary local execution tooling, not an additional mathematical dependency or one of the 26 packaged inputs.

## Report, PDF, rules, and eligibility

The complete final report, including its formalization section and references, matches the implemented definitions and theorem scope. Its five-page PDF has the exact recorded source and PDF hashes. I personally inspected every final rendered page: equations, text, commands, references, and page endings are readable with no observed clipping or missing content. The separate native compiler and Tectonic export records report success; I inspected those records rather than claiming to have run those two report compilers myself. The export log contains no warning or box diagnostic. The preliminary six-page layout and its correction are disclosed; the reviewed deliverable is the final five-page version.

Both complete current guides require a full report, PDF, Lean project, semantic fidelity, and prior-solution screening, and restrict changes to a personal submission folder. These materials satisfy the inspected content requirements. The future Git diff and assembled outer file-hash manifest are outside this certificate. This review does not create an official `review` directory or assert authority to merge or update metadata.

I inspected the initial eligibility record and the final prepublication record, including its source/guide identities, metadata, all-state corpus result, topic classifications, discussion checks, and recorded limitations. The final reviewed record is PASS through `2026-10-04T22:52:53.165387+00:00`, at upstream main `fe1d06d431b0591b65d759c60035b1d2e293a819`. It covers 588 all-state PRs through #592, no exact-ID submission match, no existing solution path or recorded path history, and unchanged unsolved metadata. Twelve topic leads were classified as unrelated; direct discussion-response comparisons supplement indexed searches. No prior #6891 submission was identified that would require an error account. These remote collection operations were performed by the eligibility agent; my claim is inspection of its preserved evidence, not an independent repetition of every remote query. Search-index lag remains a documented limitation, and eligibility is time-bounded.

Additional full-guide SHA-256 identities, independently checked against the recorded current files:

- English guide: `cd54d17f51e08212ee9557ef74568f6f2c388279ac74339dc4a3bab7c283f27e`.
- Chinese guide: `ffedf1385079b9741fce4176c7aa1662720c29391116b34e5e78ba154b4fa244`.

## Exact frozen review inputs

The review-input manifest SHA-256 is `c525ddf656ceac2ea9b5bdd005dc2529a67dde9ec627c7ee2ccfce70e7ccbb4e`. All 26 input identities were checked before and after this review. Paths below are the manifest's packaged relative names, not an assertion that a later staged copy has already been reviewed.

| Manifest-relative path | SHA256 |
| --- | --- |
| `lean/Conjecture6891/Core.lean` | `5b03b887e0a3547fa484966243e84f95abf349d86b384b27b9acfc8b52a91898` |
| `lean/Conjecture6891/Rank.lean` | `90c1cfb8b9d76b6311bf697401e54b4092e7d0cf05d184db925999a1a2c0b99b` |
| `lean/Conjecture6891/Projective.lean` | `ca4fab215bcb3b94c09c4988dc5ce3fd47f45374915ef45c32d23396cf45d2a0` |
| `lean/Conjecture6891/Arc.lean` | `90d1f8e863b12636014c8bd96bfbe1d3a41341b03ee6dc7205b68848acfafa57` |
| `lean/Conjecture6891.lean` | `b2a408f374022672574ea19e56da07f0aec5eb911d7282d15cbdf8dbb91ef7e0` |
| `lean/Check.lean` | `060559f910abf209844b719235c9cc1ecd2e1b79d309bc364378ccba9f00e411` |
| `lean/lakefile.toml` | `709c2281d68750a80a7ab40e75f1becd09c8964007b5680e6f7d5ad19f356df4` |
| `lean/lake-manifest.json` | `c3b981fdf0a076d7be53cfddf2b82cec0274d51df1a945f36b6fabcfe5906b43` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `conjecture.md` | `20f67bec1053ec616ffb2d1965eb1351fd68dc36b73f1f47cc330279d450ff28` |
| `main.tex` | `a24adea8c34c15f6048760f1d6cd8dd34375c667d6b88056764f3cdde0b7fd7e` |
| `main.pdf` | `1233b6d002b7cb0536eef2a1d1cb4b575f1bb105de0532cf040e6840b77c9fa4` |
| `README.md` | `9f7fe94d6119f8d42ef3d7970a56815d3daabb4b1c363e1869969c4772a814e3` |
| `VERIFICATION.md` | `e0b09427420077b8009b8a195c3c5212859cfafcba92d4d4aed9d50c463350e3` |
| `verification/strict-replay.json` | `867f46a9a13b6c0283b6c3bd6d42180f343e0c9cd29edcc9378f1f8bb895d383` |
| `verification/build.txt` | `c87f4b7a2992f3976acc974d8737a40beb3d492a53e7a673969695e4a634af1c` |
| `verification/axioms.txt` | `835d7f1ff18fc7c05c713a2ebbe217f01cacddf6b3fe3d03552f0d5110de6011` |
| `verification/pdf.json` | `ba24e3e3ea81c7beb70445009425a3ef963de8dc95b3ca59139288405f471cbe` |
| `verification/report.txt` | `d951d92d4b0a0410c5eec62ca6e2a2213fca2b14bb84a968f678c6dc7c0a4976` |
| `verification/prepublication.json` | `bea5fc33d9ac80424f18ad84c63b148eadadecf6e84dec0917ef20c6936c4471` |
| `verification/environment-inventory.lean` | `d8ba69fc58b5f7d0522d94f9eb695c8ba8140c610605ddc3580e0949fe7d2953` |
| `verification/environment-inventory.json` | `15fe612c87d806c508932f8753215da8d4539d866f298cf7c69e0432d6960a92` |
| `verification/environment-inventory.txt` | `e76d7790c103ead7e03de67f06319c44e475ab5d341a2129a9ec3aa4bc461c31` |
| `verification/eligibility.json` | `d03fbfa161cdfcb625d4507522f13dea60fc91a3a2fbe0c325f2b97fa39fe3c3` |
| `verification/audit-names.json` | `c7b191c9cbb4ab3a79c8a8ca1eacd80cc09a4a75015525352c7d1a6b5e58d33c` |
| `verification/frozen-sources.json` | `aa8fae3472366e2d60514123af6cc916295af923698ea0ca12b525a8a93475f8` |

No reviewed input was modified. This PASS is limited to the mathematical and evidence findings above; maintainer acceptance remains separate.
