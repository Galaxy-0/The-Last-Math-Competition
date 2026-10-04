# Independent semantic review — conjecture 00000000283

**PASS.** The frozen Lean project proves that the actual Kepler–Bouwkamp partial-product error is not \(O(N^{-3})\). This contradicts an explicit conjunct of the exact English and Chinese source and therefore disproves the combined conjecture. No unresolved mathematical or semantic concern was found. The result does not decide transcendence, the proposed Gamma-value reduction, or the sharp convergence order.

This review was performed by a separate semantic-review agent that authored none of the submitted proof, report, README, or verification documentation. I read the complete bilingual source, both complete current contribution guides, all five Lean files and three configuration files, the complete final LaTeX report, README and VERIFICATION, the actual emitted definition/type/axiom output, and the execution, PDF and eligibility records. I also read the proposed PR body. I independently recomputed every input hash in the table below. I did not edit any of those inputs, rerun the Lean build, or personally inspect the PDF page images. Execution and visual findings are attributed to the agents that performed them below.

## Exact source and scope

The bundled `conjecture.md` matches the original source bytes. The English statement reads:

> Definition: The Kepler–Bouwkamp constant K_B = ∏_{n≥3} cos(π/n) ≈ 0.1149 is the limiting radius in the construction of successively inscribed regular polygons in the unit circle. Conjecture: K_B is transcendental; the partial products converge at rate n^{-3}, and the transcendence reduces, via a Gamma-function representation of the cosine product, to algebraic independence of Gamma values. (Kepler-Bouwkamp transcendence)

The Chinese statement reads:

> 定义：Kepler–Bouwkamp 常数 K_B=∏_{n≥3}cos(π/n)≈0.1149 为单位圆内逐次内接正多边形构造的半径极限。猜想：K_B 是超越数；部分积逼近以 n^{-3} 速率收敛，超越性可由余弦乘积的 Gamma 函数化归为 Γ 值的代数无关性。（Kepler-Bouwkamp 超越）

Both assert the cubic convergence rate for the ordinary partial products. Interpreting that rate as an eventual absolute-error upper bound is faithful; a claim of exact cubic order would imply this upper bound as well. Neither language introduces an extrapolated sequence or a correction subtracted from the raw products. Refuting this conjunct suffices to disprove the conjunction. The final theorem appropriately names and negates this precise analytical clause; it does not invent a substitute formalization of the unspecified Gamma reduction or purport to settle the untouched clauses.

## Actual product and convergence certificates

The printed definitions and source agree:

\[
a_n=\cos\bigl(\pi/((n:\mathbb R)+3)\bigr),\quad
P_n=\prod_{j\in\operatorname{range}(n)}a_j,\quad
K=\prod'_n a_n.
\]

`factor` uses Mathlib's real cosine and pi. `prefix` is the actual finite product. `constant` is the actual infinite product, not an assigned value or an assumed positive parameter. All factors are proved positive and at most one. The proved estimates are

\[
\frac{2}{(n+3)^2}\le1-a_n\le\frac{\pi^2}{2(n+3)^2}.
\]

The upper estimate and the shifted reciprocal-square series establish `summable_factor_sub_one`; the general logarithm-summability theorem then gives `summable_log_factor`. The equality `constant_eq_exp_logSum` proves

\[
K=\exp\left(\sum'_n\log a_n\right)>0.
\]

Crucially, `hasProd_factor : HasProd factor constant` and `tendsto_prefix` separately certify product convergence and convergence of the actual finite prefixes. Thus the argument does not infer convergence from a totalized `tprod` expression alone. I inspected the pinned Mathlib statements and implementations used for logarithm summability, exponentiation of sums to products, and the cosine estimates; their hypotheses match these applications.

## Exact source indexing and lower bound

`partialProduct N` is explicitly

\[
S_N=\prod_{k\in\operatorname{Icc}(3,N)}\cos(\pi/(k:\mathbb R)).
\]

`partialProduct_add_two` proves \(S_{n+2}=P_n\) for every natural \(n\), including the empty-product case \(n=0\). The proof is an induction on the actual interval product. `tendsto_partialProduct` transports the proved limit across this shift. `error_lower` applies the identity after obtaining the required natural-number decomposition from \(3\le N\); it does not silently mishandle truncated subtraction.

Positive factors at most one make the prefixes antitone, and the established limit gives \(K\le P_n\). The next factor then yields

\[
P_n-K\ge P_n-P_{n+1}
=P_n(1-a_n)\ge K(1-a_n)
\ge\frac{2K}{(n+3)^2}.
\]

Therefore the proved source-indexed theorem is

\[
S_N-K\ge\frac{2K}{(N+1)^2}>0\qquad(N\ge3).
\]

The denominator \(N+1\) is exactly the first omitted polygon size. No altered sequence, surrogate error, numerical approximation, or unproved infinite-product property enters the argument.

## Every constant and cutoff, and standard Big-O

The generic rate lemma assumes the displayed positive quadratic lower bound and proves that for every real \(C\) and every natural cutoff \(N_0\), some \(N\ge N_0\) has \(C<N^3|e_N|\). Internally it chooses \(N\ge3\) and large enough that \(N>2C/K\). The elementary comparison \((N+1)^2\le4N^2\) gives the underlying inequality \(N^3|e_N|\ge KN/2\). Positivity of \(K\), \(N\), and all denominators is supplied explicitly.

The concrete `cubic_bound_counterexample` consequently has the unrestricted statement

\[
\forall C\in\mathbb R\;\forall N_0\in\mathbb N\;
\exists N\ge\max(N_0,3),\qquad C/N^3<|S_N-K|.
\]

This is stronger than restricting \(C\) to nonnegative values. `CubicConvergence` is Mathlib's actual `Asymptotics.IsBigO` at `Filter.atTop`, for the error function and \(N\mapsto((N:\mathbb R)^3)^{-1}\). I inspected its pinned definition: it requires some real constant bounding the norm ratio eventually. `not_cubic_bigO_of_lower` extracts that constant and cutoff and contradicts the quantitative theorem. Hence `conjecture_283 : ¬ CubicConvergence` establishes the ordinary source rate negation. All contradictions occur at \(N\ge3\), so the real inverse convention at zero is irrelevant.

A quadratic lower bound is sufficient to rule out a cubic upper bound. It does not assert that the true error has exact order \(N^{-2}\). The report, README, VERIFICATION, and proposed PR body consistently maintain this distinction and explicitly leave the transcendence and Gamma claims undecided.

## Report correspondence and background citation

I read the entire final report and checked its inequalities and quantifiers against the source. Its sine concavity/tangent argument proves the cosine estimates, and its elementary logarithm-integral bound proves logarithm summability. Lean reaches those same required conclusions through established cosine inequalities and the general logarithm-summability theorem; the report does not require an additional unproved assertion in the formal disproof. The positive infinite-product construction, exact index shift, first-omitted-factor bound, and unrestricted Big-O contradiction agree throughout the report and proof.

I independently opened the report's background citation, Chamberland and Straub, [On gamma quotients and infinite products](https://arxiv.org/pdf/1309.3455), §4.1. That section indeed treats the same Kepler–Bouwkamp product and its numerical evaluation. The submission correctly treats it as background only; no numerical value or theorem from it is assumed in the disproof.

## Execution evidence and trust boundary

The separate execution agent's `strict-replay.json` records a fresh project directory without project build outputs, a successful default build in 6.928 seconds, and direct warnings-as-errors replays of all five Lean files with exit code zero. The run finished at `2026-10-04T20:42:35.173567+00:00`. I inspected these records and the actual `build.txt` and `axioms.txt` output; I did not perform that execution myself.

The actual output prints all five definitions and all 25 theorem types and transitive axiom lists. These match the complete 30-declaration inventory, including normalization of the source's escaped `prefix` identifier. There are no omitted unnamed, private, or instance declarations. Every displayed theorem's axiom dependencies are confined to `propext`, `Classical.choice`, and `Quot.sound`. The execution agent's lexical scan reports no admitted proofs, custom axioms, `native_decide`, unsafe execution shortcuts, or kernel-trust changes, consistent with my source reading.

Lean 4.19.0 is pinned to compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib v4.19.0 resolves to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The execution record checks all nine exact dependency revisions and clean tracked sources before and after execution, and rechecks the compiler. It records unchanged source/configuration and inventory identities. My own recomputation confirms that all eight source/configuration files match the frozen manifest and both original and copied identities in the execution record. No auxiliary mathematical computation is required or claimed.

## PDF evidence and eligibility boundaries

`pdf.json` records successful compilation of the final source in the built-in editor and successful Tectonic 0.17.0 export of a three-page, 68,517-byte PDF. The source and PDF hashes match my recomputation. The recorded final export has no warnings or box diagnostics, consistent with the inspected compiler log. It also records the earlier repaired export issue rather than hiding it.

The report-author agent personally inspected all three complete rendered final pages and reported PASS. The coordinating agent separately viewed those same three final pages and reported PASS. Their findings include no clipping, overlap, missing mathematical glyphs, or problematic page breaks. I read and hash-bound this evidence; I did not personally view the PDF images and do not present those visual checks as my own.

I read the initial and final eligibility records. The separate corpus agent's final snapshot at `2026-10-04T20:43:06.438616+00:00` covers 560 all-state pull requests through PR564, unchanged source/guides/main and unsolved metadata, identifier and topic searches, and current/historical solution paths. Its two bare-number matches are explicitly classified as unrelated, as are the three new PRs since the initial audit. No prior or competing solution was found within that recorded scope. I did not independently rerun these network/corpus searches. Indexed-search lag, unavailable private work, and submissions after the snapshot remain outside the guarantee.

The full current contribution guides were read from the upstream copies in the eligibility materials; their exact hashes are listed separately below. This is an independent internal semantic review of the identified inputs, not a maintainer acceptance, merge decision, or verification of a future assembled commit. The reviewed README and VERIFICATION accurately describe this boundary. No changes to any reviewed input are requested.

## Exact reviewed input identities

I recomputed these SHA256 hashes immediately before finalizing this review. Paths below are intended submission-relative paths; all 20 inputs match the final ready list. This table excludes this review itself and the later package manifest.

| Submission-relative input | SHA256 |
| --- | --- |
| `README.md` | `973bc58526dde145909069c24a96ad09c2cc8eba4122615cd797e6093472b3d0` |
| `VERIFICATION.md` | `113d1cdd313085c1d544118bf8dab8696767ff65327f7ae5adc7a4d855ba55d5` |
| `conjecture.md` | `5d522a04f47e658edc49f73e6a4f281827807545e630749497202a01d329e14d` |
| `lean/Check.lean` | `c87752f9d464ab5400ed1635bb79c8436aed1fea2e3f3e6abc9e4f1a3bee9e7b` |
| `lean/Conjecture283.lean` | `db916b5897a71468be0ef36f4f7987f1b5b08cab20f3a6a75aa39334168a2896` |
| `lean/Conjecture283/Factors.lean` | `54a98fe4cc35ee19e8a61be81b3907c4eb1fa126281e69cba8df2d0a1fc9a8a0` |
| `lean/Conjecture283/Prefixes.lean` | `6ed9086190b565755c7b0edd980e47b11d0ba6eaa6f22ebe5ed8436c70a1c5d4` |
| `lean/Conjecture283/Rate.lean` | `d713947f666a689c7291fe849953528c1688119d2c174999f7c5d72eb79eb1a3` |
| `lean/lake-manifest.json` | `df1f2fce49683ae7af41cb3172a1791a7976ecbfcdbf164415232c80d4f75e5d` |
| `lean/lakefile.toml` | `6c12330ebe0db54376007ba420b1b078c60751ac92f453a6a82e9b4378f7508b` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `main.pdf` | `f6eecf9e2028ff32cf25c308267da5d2dcb13dee9e6995506c939d9c74ba49ee` |
| `main.tex` | `cbfed52fe4bf1719ba2105ed64bf0b5307619be77ccf09e9450431c72e452d9c` |
| `verification/axioms.txt` | `fa63b0b0e9244689f56860aec60e5b55db1496f118a30aba19f6058493effc4e` |
| `verification/build.txt` | `8a029ffada32f8841c491f498d6ef3b8a732ea07e8e2131f053abd4ce6926782` |
| `verification/eligibility.json` | `749d524a94fbf1eec16fc8de4d21ee4adac92ddede739c374c06626828998b36` |
| `verification/pdf.json` | `e84d6855d7cd48b33d09afdb9f6547ca0f42d9db60bbb15b5ea6e8a8cfd4e90c` |
| `verification/prepublication.json` | `2e7dce7ed56aaeb6c4bb4b4cb215c1642c756c20e93e62106a52ed0f5b1a7ce1` |
| `verification/report.txt` | `020f6bde6012a074f0e73b6323bc05d5e4c9eaee079e21bb6b84828319ff74b2` |
| `verification/strict-replay.json` | `7d605dcde700710672c21138ead32539102469eece185642fbd8368ba4d1f366` |

Current upstream repository guides, read in full and separate from the 20 submission inputs:

- `README.md`: `cd54d17f51e08212ee9557ef74568f6f2c388279ac74339dc4a3bab7c283f27e`.
- `README.zh-CN.md`: `ffedf1385079b9741fce4176c7aa1662720c29391116b34e5e78ba154b4fa244`.

These guide identities belong to recorded main `fe1d06d431b0591b65d759c60035b1d2e293a819`. The local workspace copies had older leaderboard content; both complete local guides were also read during preassessment, and the current upstream copies govern this review.
