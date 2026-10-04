# Independent semantic review: conjecture 00000005960

**Verdict: PASS.** The reviewed construction proves the full existential assertion in both source languages. It supplies actual non-Dirac matrix ensembles, identical complete spectra, different laws of an intrinsic eigenvector statistic, and one explicit continuous all-real family that changes orientation while preserving the spectrum. I found no mathematical or statement-fidelity blocker in the frozen materials identified below.

This review is by the separate `semantic5960` reviewer, who authored none of the Lean proof modules, report, or submission documentation. I personally read the exact bilingual conjecture, both complete repository guides, every final Lean source and project configuration file, the entire LaTeX report, README and verification document, and the emitted definition/type/axiom output. I examined the execution and PDF records and recomputed the input file hashes. I did not personally rerun the Lean build, compile the report, or visually inspect its rendered pages. Those checks were performed by other agents and are separately attributed below. This is an internal submission review, not an official repository review or maintainer acceptance.

## Source statement and scope

The exact English source reads:

> Definition: The spectrum and the eigenvector statistics are two layers. Conjecture: There exist two ensembles with the same eigenvalue spectrum but different eigenvector statistics, and the separation is realized by an explicit free parametrization with the same spectrum but different orientation. (same spectrum-different vector orientation separation)

The exact Chinese source reads:

> 定义：谱与特征向量统计指两层。猜想：存在两系综的特征值谱相同而特征向量统计不同,分离由同谱异定向的显式自由参数化实现。（谱同-向量统计异定向分离）

Both versions make an existence claim. Neither imposes Gaussianity, independent matrix entries, orthogonal invariance, increasing dimension, asymptotics, or a particular distributional class. A finite probability law on real symmetric 2×2 matrices is therefore an admissible ensemble witness. Proving this particular example satisfies the original existential statement; it does not replace a universal or asymptotic claim by a special case. The words “free parametrization” are realized by a freely varying real parameter, with a globally defined continuous formula and injectivity on a nontrivial interval. Neither source invokes freeness in noncommutative probability or requires a globally injective chart.

I read both full repository guides, including the solver scope and reviewer completeness requirements. The current source and guide hashes agree with the source identities in the eligibility records. Eligibility itself was checked by the corpus agent; I have not repeated that agent's full repository and PR search.

## Actual matrices and the complete spectrum

The family is defined, not merely named, as

\[
c(t)=\frac{1-t^2}{1+t^2},\qquad s(t)=\frac{2t}{1+t^2},\qquad
Q(t)=\begin{pmatrix}c(t)&-s(t)\\s(t)&c(t)\end{pmatrix},\qquad
M(t)=Q(t)\operatorname{diag}(1,3)Q(t)^\mathsf T.
\]

`Mat2` is Mathlib's actual `Matrix (Fin 2) (Fin 2) ℝ`. The operations in the definition are actual matrix multiplication and transpose. `denominator_pos` covers every real parameter. The rotation identity, both orthogonality identities, determinant one, entry formula and symmetry are proved for all real parameters.

The spectral claims do not depend on an assigned list or a surrogate scalar. `charpoly_matrixFamily` proves the actual characteristic polynomial `(X−1)(X−3)`. `spectrum_matrixFamily` proves the actual algebra spectrum is `{1,3}`, and `spectrum_operator_matrixFamily` also identifies the spectrum of the associated Euclidean continuous linear map. The characteristic polynomial has degree two and distinct roots, so it preserves algebraic multiplicities and rules out omitted eigenvalues. In particular the report's increasingly ordered list `(1,3)` follows. Lean expresses the spectral laws using the actual characteristic polynomial and spectrum, rather than defining a list to be `(1,3)`.

The family provides actual unit eigenvectors `(c,s)` and `(-s,c)` for eigenvalues 1 and 3. Their orthogonality and a decomposition of every vector are proved. The eigenvalue facts therefore concern actual linear actions on vectors as well as the characteristic polynomial.

## Intrinsic statistic and sign independence

`Plane` is `EuclideanSpace ℝ (Fin 2)`, so the norm is the Euclidean norm, not the supremum norm on a function space. `eigenspaceOne A` is the actual `Module.End.eigenspace` of `Matrix.toEuclideanLin A` for eigenvalue 1. The statistic is fixed globally by

\[
S(A)=\|\Pi_{E_1(A)}(1,0)\|_2^2.
\]

The definition invokes the actual submodule orthogonal projection. It does not define the answer to be `c(t)^2` or allow the final theorem to choose an arbitrary statistic. All eigenspaces here are finite-dimensional subspaces, so the projection is well-defined.

`eigenspaceOne_matrixFamily` identifies the entire actual eigenspace as the span of the displayed first eigenvector. `projection_matrixFamily` derives its orthogonal projection formula, and only then does `statistic_matrixFamily` derive `S(M(t))=c(t)^2`. Crucially, `statistic_eq_normalized_eigenvector` applies to **every** Euclidean unit vector in that eigenspace and proves that `S(M(t))` equals its squared first coordinate. Thus the statistic measures a genuine eigenvector/eigenline observable and is unchanged by reversing a unit eigenvector's sign.

I independently consulted Section 1.1 and Remark 1.8 of [Knowles–Yin, *Eigenvector Distribution of Wigner Matrices*](https://arxiv.org/pdf/1102.0057). They use Euclidean normalization and coordinate products that remove global phase; equal coordinate indices give squared moduli. This supports the report's terminology. Their universality assumptions and theorems are not used in this proof. Different laws of one genuine scalar eigenvector observable suffice to establish different eigenvector statistics.

## Genuine ensembles and measurable pushforwards

`fairPMF` is the actual uniform PMF on `Fin 2`, with mass one half at each point. Both random matrices are actual functions on that probability space, and both matrix laws are PMF pushforwards. The definitions give

\[
A(0)=\operatorname{diag}(1,3),\quad A(1)=\operatorname{diag}(3,1),
\]
\[
B(0)=\frac1{25}\begin{pmatrix}57&-24\\-24&43\end{pmatrix},\quad
B(1)=\frac1{25}\begin{pmatrix}57&24\\24&43\end{pmatrix}.
\]

These entries agree with the rational family formula. The two values within each ensemble are distinct. The formal project proves both nonconstancy of the random variables and that their actual matrix measures differ from every Dirac measure. In particular, the fact that the scalar statistic of B is constant does not make B a deterministic matrix ensemble.

Every matrix outcome has the same characteristic polynomial and spectrum. The corresponding two PMF law equalities are proved using the actual maps `Matrix.charpoly` and `spectrum ℝ`. Meanwhile the exact statistic laws are

\[
\operatorname{Law}(S\circ A)=\tfrac12\delta_0+\tfrac12\delta_1,
\qquad \operatorname{Law}(S\circ B)=\delta_{9/25}.
\]

These are proved laws of a derived statistic, not a probability table substituted for a random matrix construction. Matrix Borel measurable instances are the usual coordinate measurable structure and are themselves included in the type/axiom audit. The matrix-valued maps and the statistic compositions are proved measurable because their source is the finite discrete space. The PMF-to-measure equalities identify the actual matrix and scalar pushforward measures. `different_actual_statistic_pushforwards` proves that these scalar measures differ.

No global measurable eigenvector selection is required, and the proof does not silently assume global measurability of the projection statistic on every matrix. The needed finite-domain compositions are explicitly measurable. The formal law inequality uses the event `{0}`; the report uses `{1}`. Both correctly have mass one half for A and zero for B under the exact laws above.

## The real parameter and final theorem

The denominator is positive on all of ℝ. Continuity of both rational coordinates, the rotation, matrix family and actual exhibited eigenvectors is proved. The interval-injectivity proof is valid: on `[0,1]`, equality of `c²` implies equality of the nonnegative `c`; clearing positive denominators then gives equal nonnegative parameters. This is a genuinely varying continuum of orientations. The report correctly disclaims global injectivity and correctly notes `M(t)=M(−1/t)` for nonzero t.

The final statement is connected. `parameterA` and `parameterB` are explicit functions on the common fair sample space, and `randomMatrixA_eq_parameter` and `randomMatrixB_eq_parameter` place both random matrices inside the same `matrixFamily`. `ParametricSeparation F a b` contains continuity, interval injectivity, all-real symmetry and complete spectral identities, non-Dirac laws for both `F∘a` and `F∘b`, equal actual characteristic-polynomial and spectrum laws, and unequal actual intrinsic-statistic measure pushforwards. Every occurrence uses the same F. `explicit_parametric_separation` proves this for the displayed rational family and parameter maps; `conjecture_5960` existentially exhibits them.

The statistic's definition remains the actual eigenspace projection in this final theorem. Its universal normalized-eigenvector bridge is proved for this exact witness in the imported module. There is no unrelated scalar surrogate, vacuous conditional hypothesis, admitted spectral assumption, or disconnected probability example. The complete report and submission documentation agree with this formal content.

## Execution, PDF and eligibility evidence

The `corpus_metadata` execution agent reports a fresh build in a separate directory containing only the five final Lean files and three configuration files, with no project build outputs. The build and all five warning-as-error replays exited 0. I read the build log and actual `Check.lean` output. The latter exposes the actual definitions and theorem types and includes 80 axiom reports for all 78 theorems and two named instances, alongside 21 definition/abbreviation printouts. Each axiom report contains only the standard `propext`, `Classical.choice`, and `Quot.sound`. The agent's independent declaration reconciliation covers all 101 source declarations; its lexical bypass scan found no hits. Its execution record verifies the exact Lean compiler commit and nine clean manifest-pinned dependency revisions before and after the run, with source/configuration hashes unchanged. These are that agent's executed checks, not my own fresh-build claim.

The report-author agent's `pdf.json` records successful built-in compilation, successful Tectonic export, and visual inspection of all three rendered pages after the final source cleanup. It records no clipping, overlap, broken glyphs or compiler box diagnostics. I read the full LaTeX proof and checked the report/PDF hashes against this record. I did not personally perform the page-image visual QA; it remains explicitly author QA.

The corpus agent's final `prepublication.json` reports unchanged source and guides at upstream commit `fe1d06d431b0591b65d759c60035b1d2e293a819`, unsolved metadata, no relevant prior or competing submission among its available searches, 548 all-state PRs through 552, and classification of all 18 broader topic hits as other conjectures. Its main scan is current through 19:50:21 UTC on 4 October 2026, with its sole topic-comment recheck through 19:50:58 UTC. I reviewed these recorded findings and their limitations; I did not independently repeat that corpus scan. The personal-submission-only scope remains a packaging responsibility, separate from mathematical validity and repository acceptance.

## Exact reviewed input identities

The following SHA-256 values were recomputed from the final reviewed bytes. Paths are submission-relative except the two repository guides. The PDF hash binds the artifact whose author QA is reported; it does not imply that this semantic reviewer personally viewed its pages.

| File | SHA-256 |
| --- | --- |
| `README.md` | `5aa75dd34c37c0835744626242033d549a6f6432520a124176e3626f20ab1872` |
| `VERIFICATION.md` | `0d35c77e6eaf85da65edecae5f7dcbd573b871d38b9759f07643c788b6be1ec9` |
| `conjecture.md` | `0d190893ecdbfcf50fa7bdafd9770b86e1ccd4b5bc64640a075dc86e3fb324fc` |
| `lean/Check.lean` | `7552003c6c8386d773ad67b2b068396bd50a04ca949666da5f586379f9241618` |
| `lean/Conjecture5960.lean` | `28e491f6f771b536f6df17e434f9ad2e457942661c65e48accbb1227f9ca228a` |
| `lean/Conjecture5960/Eigenvectors.lean` | `2999a60476556cfcdb3150b8435514646f9046e687dc02758eb5dc690ad857d0` |
| `lean/Conjecture5960/Ensembles.lean` | `854c515112a08c106fe3f947542fec1f1c87c5d3b3ad9fc79226001de551d53c` |
| `lean/Conjecture5960/Family.lean` | `c1615f8bc27d9d2cc95543efc62c94699d2acfc380075d8705aa75dcd719484f` |
| `lean/lake-manifest.json` | `def2a89f4a67281ff33c92f7aa020a040ff0708828085f07541614661b532cfb` |
| `lean/lakefile.toml` | `5c37fc093e35fa841517306238f78a8f3034509f33fde318b6fa9feabc49ac86` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `main.pdf` | `41c08fd25ec84239f9912f3957da42b9c2274b0edd9f63113f6c326ce6f79f9b` |
| `main.tex` | `d32a20c3c523b848241d7117443fd350bf277ff310c6534960a7ac834dc534ca` |
| `verification/axioms.txt` | `3d710d8f26db2da0ef911f69409794a41d3078df608aa79388db1d9d4bf40d28` |
| `verification/build.txt` | `901780e3b5259576d717ace5a985e69fea16f4efd944d245a634fdc84ef2b8b5` |
| `verification/eligibility.json` | `0662687b2115afbcd70e13bc1496d9cc397d602013d5e06146649fc1f8502042` |
| `verification/pdf.json` | `5d0ada64a1a0c1f7868b5c180268911fd62e471f2ab76b0a3b96e27d87b64a28` |
| `verification/prepublication.json` | `cd45be3a93d07caf4d384b0d4a7667fb7ea9610fb5a85c919d54f93893478086` |
| `verification/report.txt` | `b34431a967bbeff939d10f93f8240137b3f83e2f9f1e478935c88a7ce10e0727` |
| `verification/strict-replay.json` | `bcd9309c042c1c4a7d7c1de89355497565bb9c65555b9a8ffa02fc6b714b0eb0` |

Repository guides read in full:

- Repository `README.md`: `cd54d17f51e08212ee9557ef74568f6f2c388279ac74339dc4a3bab7c283f27e`.
- Repository `README.zh-CN.md`: `ffedf1385079b9741fce4176c7aa1662720c29391116b34e5e78ba154b4fa244`.

No proof or report modification was made by this reviewer. This PASS applies to the identified bytes and the full source assertion, with execution, visual review, and repository eligibility attributed as above.
