# Independent internal semantic review: conjecture 00000006480

**Verdict: PASS for the frozen source and report identified below.** No mathematical or formalization correction is required by this audit. This is an independent internal source review, not an official competition review, maintainer approval, or acceptance. Compilation and PDF rendering were executed separately; this reviewer inspected their completed records and independently checked the relevant file identities.

## Scope and source interpretation

The exact English source asks for two processes with the same covariance matrix but different extremal distributions, realized by an explicit non-Gaussian pair with different jointness. The Chinese source makes the same existential assertion. Neither version requires an infinite index set, stationarity, continuous paths, or an asymptotic extreme-value limit. A process indexed by three points therefore meets the stated domain. The report explicitly interprets the extremal distribution as the law of the maximum over those three indices and proves different joint laws separately.

This is a direct existence proof. Fixing one common eight-point probability space and one three-point index set supplies concrete witnesses; it does not replace a universally quantified domain by a smaller one. The final theorem has no additional hypotheses. The report does not claim to settle an unstated infinite-time or asymptotic variant.

Standard context is consistent with this reading. Rasmussen and Williams, *Gaussian Processes for Machine Learning*, §2.2, explicitly allow finite index sets and define covariance by the centered second moment: [author-hosted chapter](https://gaussianprocess.org/gpml/chapters/RW2.pdf). Gardner, *Introduction to Random Processes with Applications to Signals and Systems*, §2.3.4, p. 39, gives the real-linear-combination criterion for jointly Gaussian variables: [author-hosted text](https://faculty.engineering.ucdavis.edu/gardner/wp-content/uploads/sites/146/2014/05/Introduction_to_Random_Processes_with_applications_to_Signal.pdf). These references support conventions; the finite calculations and non-Gaussian obstruction are proved directly.

## Actual objects and mathematical argument

`Processes.lean` uses `Ω = Fin 8` with its full measurable space and the actual probability measure `(PMF.uniformOfFintype Ω).toMeasure`. The `μ_probability` instance establishes mass one. The displayed coordinate arrays enumerate all eight sign triples exactly once. Thus they implement the report's uniform sign cube, with `X = (A,B,C)` and `Y = (A,B,A*B)` on the same space. The unused third input for `Y` correctly gives each of its four sign patterns mass one quarter.

The following links were checked in the source and again in the compiler's printed definitions/types:

- `mean` is a Bochner integral against this measure. `covarianceMatrix` is the integral of the product of centered coordinates. It is not a separately assigned numerical matrix. All coordinates and centered products are proved measurable/integrable; the proof does not exploit the integral's behavior on nonintegrable functions.
- `integral_uniform` and `measure_uniform` derive finite-sum formulas from the PMF measure APIs. Exact finite computations then prove every mean zero and both full covariance matrices equal to the real identity matrix. In particular, all nine entries, including the diagonal variances, are checked.
- `jointLaw` is the actual pushforward into `Fin 3 → ℝ`. Its value on the singleton all-negative vector is `1/8` for `X` and zero for `Y`. These unequal measurable-set values prove inequality of the two joint measures.
- `peak` is the nested maximum of the three actual coordinates. The general theorems `coordinate_le_peak` and `peak_attained` verify that it is their genuine maximum. `extremeLaw` is its actual pushforward measure, with a probability-measure instance.
- Both maximum laws are proved as equalities of measures: `extremeLaw X = (1/8) • dirac (-1) + (7/8) • dirac 1`, and `extremeLaw Y = dirac 1`. Their proofs use measure extensionality over arbitrary measurable sets. They are stronger than a finite table asserted without a bridge to distributions. The separate singleton calculations also directly prove unequal extremal laws. `peak_Y_eq_one` establishes the constant maximum pointwise.

The arithmetic is exact. Where extended nonnegative real arithmetic is converted to real arithmetic, the required finiteness conditions are discharged; there is no reliance on equality after an unsafe conversion of infinity. Every coordinate takes only the values `-1` and `1` in the explicit arrays. The all-coordinate half-atom lemmas, together with these values and total mass one, justify the report's fair-marginal statement.

## Non-Gaussian condition, including degenerate laws

`GaussianProcess μ Z` quantifies over every real coefficient vector and requires the actual pushforward of its linear combination to equal some Mathlib `gaussianReal a v`, with arbitrary real mean and `v : ℝ≥0`. This is the standard finite joint-Gaussian condition and permits zero variance. It does not weaken non-Gaussianity to a failure of a merely numerical Gaussian formula.

`GaussianProcess.coordinate` selects a basis coefficient vector, proving that this condition implies each coordinate has a Gaussian law. The generic Gaussian predicate does not bundle measurability or a probability hypothesis, but the final witness theorem explicitly establishes both, and all linear combinations on the finite space are measurable.

The obstruction handles both variance cases. Mathlib's positive-variance `gaussianReal` is absolutely continuous with respect to volume, so every singleton has mass zero. Its zero-variance branch is the Dirac measure, whose singleton masses are zero or one. `gaussianReal_singleton_zero_or_one` proves this dichotomy for every mean, nonnegative variance, and singleton. Each witness has first-coordinate mass `1/2` at `-1`, hence cannot be jointly Gaussian, including a degenerate Gaussian process. No nonsingularity or positive-variance assumption is silently imposed.

## Final theorem and report correspondence

`ExplicitWitnessClaim` includes the genuine probability space, two processes, coordinate measurability and integrability, integrability of every covariance product, non-Gaussianity of both processes, equal covariance matrices, unequal joint laws, and unequal maximum laws. `conjecture_true` supplies `X` and `Y` and proves every conjunct without hypotheses. This establishes every substantive clause of the bilingual existential source.

The final `main.tex` agrees with the formal construction, centered covariance convention, exact probabilities, and Gaussian argument. Its sign-cube presentation is the mathematical enumeration implemented by `Fin 8`; independence is not an unproved formal premise. The report's full maximum-law table is supported by full formal measure equalities. Its claims about the proof's scope and independent review are appropriately limited.

## Build and trust evidence inspected

The completed `strict-replay.json` records a fresh project build in `/private/tmp/tlmc6480-independent`, with no initial project build outputs, followed by strict compilation of all four Lean files using `-DwarningAsError=true`. The build and all four strict replays exit zero. I read the actual `build.txt` and `axioms.txt`, not only the summary status.

All 12 printed definitions and all 42 checked theorem/instance types match the expected lists. All 42 axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. The source scan finds no proof bypasses, additional axioms, `sorry`, `admit`, or `native_decide`. The pinned compiler is Lean 4.19.0, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib is commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine dependency revisions match their manifest entries and have clean tracked files before and after the build. This was a fresh project build using already available dependency artifacts, not a claimed complete rebuild of Mathlib from source.

I independently recomputed the seven Lean/configuration input hashes and checked equality with the build record and the managed submission copies. The final report also matches its managed copy byte for byte. The PDF record reports successful native and Tectonic compilation and visual inspection of both pages by the packaging agent; this reviewer did not independently render or visually inspect the PDF. Its recorded PDF SHA256 is `63e29d661a53d2208a94ff6cbf477c94dbd06adbb0031ab23e1f109c2dd1fa93`.

The review addresses semantic fidelity, source completeness, and the inspected build evidence. Live eligibility, final publication bookkeeping, and official acceptance remain separate responsibilities. There is no claim that internal review substitutes for the competition's independent review process.

## Exact reviewed files

Lean/configuration paths are relative to `/private/tmp/tlmc6480-proof`; the report is `/private/tmp/tlmc6480-package/main.tex`; the conjecture source is under `/Users/daniel/The-Last-Math-Competition`. The managed mirror is `solutions/00000006480/C0ldSmi1e_submission_20261004092136` in the `conjecture-420` worktree, with Lean/configuration files under `lean/`.

| File | SHA256 |
| --- | --- |
| `Conjecture6480/Processes.lean` | `05ff195f6231ba5828dc3336b35915071e88d56125bcec6dcc2d9f20c877d3fa` |
| `Conjecture6480/Gaussian.lean` | `79724535556a8fcf37f44ca39c2f6a13b21976b3e0d82cb139bfc241ce8d039c` |
| `Conjecture6480.lean` | `fd0f1a24e7f518a424facb259466278ba23a31b271fc805174e7673a73371ac8` |
| `Check.lean` | `87e80f24c4e93586b4a9dd72f1ba1d888dd91df641bb0df69de1a76c6c43d7fc` |
| `lakefile.toml` | `be8c185557c71b64316e70dc75536f58f17741b857128203dcfeed9139ed31d4` |
| `lake-manifest.json` | `5d0955d3640a259fe42ef233a3861572564c9837c3e38c5c793b8c42ff7b07f5` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `main.tex` | `e79429719e8ab03545c91020fdfabf474810ff67ec6a65b18f275d69bd533a9e` |
| `conjectures/00000006480.md` | `46cac8dbc1c3be83885efbe612b81c213e01e3a6174cea3f1c08561b319c6e7a` |

The contribution rules read in the repository's `README.md` have SHA256 `1d392f2136e6b6c83c86b92e7d23e6bf34e9012f4a0933c5e2373e6be3b213af`.

Evidence paths are relative to `/private/tmp/tlmc6480-verification`:

| Evidence | SHA256 |
| --- | --- |
| `strict-replay.json` | `8cf6b865ee3996792c0768471aa11ed5dc57f9f2a2070b8bb17f07e61e858e82` |
| `build.txt` | `6a90f7db24efc1dc20bc40a66b0d96ceb7adcdc8ccc6f6743b13819121c843a2` |
| `axioms.txt` | `6cf88769225bfbfe98efd68ea2a39acafae2a7c8de26a9b013d9371e9ce12f82` |
| `pdf.json` | `778304c4d729c320535e25450fa765af135ffedb1dd6068b8ef02387cfc65aeb` |
