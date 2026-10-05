# Independent semantic review — conjecture 00000000978

**PASS / GO.** The frozen project gives a faithful disproof of the literal bound on all real points. For the actual matrix `[[0,2],[0,0]]`, it proves that both the real affine chart of the complex projective dual and the real algebraic boundary of the numerical range are the unit circle, and proves that this set is infinite. This contradicts the proposed bound one in dimension two, and indeed every finite bound. No unresolved mathematical or semantic issue was found, and no changes to the reviewed inputs are requested.

I am the separate semantic reviewer and authored none of the submitted proof, report, README, or verification documentation. I read the complete exact bilingual source, both complete current contribution guides, every final Lean/configuration file, the complete final LaTeX report, README and VERIFICATION, the proposed PR body, the actual definition/type/axiom output, and the execution, PDF and eligibility records. I independently recomputed the 21 input hashes below. I did not run the fresh build or personally inspect the PDF page images. Those checks are attributed to their actual performers below. This is an internal review of the identified frozen inputs, not maintainer acceptance or a check of a later assembled commit.

## Original statement and logical scope

The bundled source is byte-identical to the original. The English text reads:

> Definition: The Kippenhahn curve (the algebraic boundary of the numerical range of a matrix). Conjecture: The number of real points of the Kippenhahn curve is bounded above by the combination n(n−1)/2 of eigenvalue multiplicities (real-point counting).

The Chinese text reads:

> 定义：Kippenhahn 曲线(矩阵数值域的代数边界)。猜想：Kippenhahn 曲线的实点数为特征值的重数的组合上界 n(n−1)/2(实点计数)。

Neither version limits the count to isolated points, singularities, nodes, or connected components. Neither assumes normality, diagonalizability, or simple spectrum. The submission correctly addresses all real points and does not introduce a hidden restriction of this kind.

The phrase about combining eigenvalue multiplicities is imprecise. The actual characteristic-polynomial certificate is `witness.charpoly = Polynomial.X ^ 2`, so the witness has dimension two and its only eigenvalue has algebraic multiplicity two. The displayed expression is one for n=2. Moreover, the proved failure of every finite bound makes the counterexample robust to alternative finite multiplicity expressions; it does not depend on assigning fictitious spectral data.

The smooth-pencil restrictions in `RealPointBoundClaim` and `DualPointBoundClaim` define necessary specializations, not additional hypotheses attributed to the source. A universal bound would hold on that subclass, and the concrete matrix is proved to satisfy it. The root module also directly negates the unrestricted all-dimension real-algebraic-boundary bound. The report explains these logical relationships accurately.

## Actual matrix, Hermitian pencil, and smoothness

The definition `witness` is the actual complex 2-by-2 matrix. `hermitianPart` and `imaginaryPart` use matrix conjugate transpose and the scalar factors 1/2 and 1/(2i). Both are proved Hermitian. Their computed values for the witness are

\[
H_1=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
H_2=\begin{pmatrix}0&-i\\i&0\end{pmatrix}.
\]

`pencilPolynomial` is constructed by taking the actual determinant of a matrix over complex multivariate polynomials. The generic theorem `eval_pencilPolynomial` connects evaluation of that polynomial to `det(u H₁ + v H₂ + w I)`. The witness computation proves

\[
p(u,v,w)=w^2-u^2-v^2.
\]

`gradient` evaluates the actual `MvPolynomial.pderiv` operators; its computed value is `(-2u,-2v,2w)`. The project proves that the polynomial is nonzero, homogeneous of degree two, has total degree two, and is projectively smooth. The smoothness predicate excludes the cone origin and requires nonzero gradient at every nonzero polynomial zero. This is appropriate; no false smoothness claim is made at the affine cone's origin. Nilpotence and characteristic polynomial X² are proved from the matrix operations.

## The complex projective-dual chart is computed

`scaledGradientImage` consists of all nonzero scalar multiples of gradients at nonzero smooth complex zeros. The project proves nonzeroness and invariance under nonzero scaling. `dualCone` is its actual complex algebraic closure, implemented as `MvPolynomial.zeroLocus (MvPolynomial.vanishingIdeal ...)`. I inspected those pinned Mathlib definitions: they are respectively the common polynomial zero locus and the ideal of polynomials vanishing at every point of the set. The closure is not Euclidean closure or an assigned conic.

For a smooth homogeneous plane curve, gradient coordinates represent its tangent lines; the nonzero scalar representatives and Zariski closure give the coordinate-cone version of its projective dual. During preassessment I independently read Paparella, Ramirez and Wang, [A proof of the elliptical range theorem via Kippenhahn’s theorem](https://arxiv.org/pdf/1807.04268), §2.1, Theorem 2.1 and §3(i), confirming these determinant-pencil and projective-dual conventions. Its nilpotent example scales to this witness. Here the explicit matrix and curve calculations are proved, rather than imported from the citation.

For the witness, the polynomial vanishes on every actual scaled gradient because

\[
p(c\nabla p(q))=4c^2p(q).
\]

It therefore vanishes on the algebraic closure, supplying the required upper containment. Conversely, if `x²+y²=1` over ℂ, the point `q=(-x,-y,1)` is a nonzero smooth zero, and `(x,y,1)=(1/2)∇p(q)` lies directly in the nonzero scaled-gradient image. These two directions prove the exact complex affine-chart identity `x²+y²=1`, followed by the real-chart circle identity under the real-to-complex embedding.

This argument proves the needed chart equality. It does not claim an unproved full-cone equality or rely on the zero scalar being in the image. Fixing the last coordinate to one gives unique affine representatives, so distinct real pairs are not merely different representatives of the same projective point. Infinitely many affine real points also suffice to defeat a bound on all projective real points.

For nonreduced determinant polynomials, raw gradients need not recover the reduced curve's dual. The submitted code and documents correctly restrict the source specialization to the proved smooth homogeneous pencil and avoid asserting universal correctness of this shortcut for arbitrary repeated factors. They also avoid assuming that the dual curve and algebraic boundary agree for every matrix.

## Numerical range and genuine algebraic boundary

`numericalRange` uses the actual Hermitian quadratic form

\[
\sum_i\overline{v_i}(Av)_i
\]

on vectors with `Σ Complex.normSq(vᵢ)=1`. `unit_condition_iff` proves equivalence with the ordinary Hermitian unit equation `Σ conjugate(vᵢ)vᵢ=1`. The definition therefore uses the Euclidean unit condition, without relying on a function type's supremum norm.

The actual matrix quadratic form is proved equal to `2 conjugate(v₀)v₁`. The first inclusion in the disk follows from the unit condition and the squared norm inequality. For every complex disk point ζ, `disk_quadratic_witness` constructs

\[
s=\sqrt{1-|\zeta|^2},\qquad
 a=\sqrt{(1+s)/2}>0,\qquad b=\zeta/(2a),
\]

and proves both `|a|²+|b|²=1` and `2 conjugate(a)b=ζ`. Thus the reverse inclusion has an actual unit-vector witness for every point, with positivity addressing division. `numericalRange_witness_eq` proves equality with the closed complex unit ball, and `frontier_numericalRange_witness` uses the genuine topological frontier theorem to identify its unit sphere.

`algebraicBoundary` is not defined as the frontier alone. It takes real coordinate pairs whose associated complex points lie in the frontier and then takes their real Zariski closure. `realCoordinatePoint_mem_sphere` computes this coordinate set as the unit circle. `circle_eq_zeroLocus` identifies the circle with the zero locus of the real polynomial `X₀²+X₁²−1`; the proved general zero-locus closure identity then fixes it. Consequently the actual real algebraic boundary is the circle. Its equality to the previously computed real dual chart is a theorem specific to the witness. This fully supplies the source's parenthetical boundary interpretation without conflating real and complex closure.

## Infinitude and exact final claims

`circleParam` is the rational map

\[
t\longmapsto\left(\frac{1-t^2}{1+t^2},\frac{2t}{1+t^2}\right).
\]

Membership in the circle is proved, denominators are positive, and `circleParam_inverse` gives `t=y/(1+x)` on the image. This proves injectivity on all real parameters. The resulting infinite image establishes actual set infinitude, transported to both curve constructions by their proved equalities.

The count is `Set.encard`, so infinitude gives infinity rather than the zero value of a finite-only cardinal function on infinite sets. Theorems explicitly exclude every finite natural bound on each curve. `conjecture978_disproof` and `dualPointBoundClaim_false` specialize this to the proposed dimension-two expression; `universal_algebraicBoundary_bound_false` negates the all-dimension statement. `witness_certificate` combines the characteristic polynomial, homogeneity, projective smoothness, boundary infinitude and equality of the two real curves. The quantifiers and coercions in the printed types match these meanings.

I read the full final report and checked all displayed object identities, the unit-vector construction, the closure argument and the cardinality reasoning. They agree with the proof. The additional observation that (1,0) and (−1,0) are distinct circle points is mathematically immediate from the proved circle identity; the formal disproof itself uses the stronger infinitude result. The report, README, VERIFICATION and proposed PR body consistently describe the literal source scope and the smooth-specialization boundary.

## Execution evidence and trust boundary

The separate execution agent's record reports a fresh project directory without project build outputs, a successful default build in 8.448 seconds, and warnings-as-errors replays of all six Lean files with exit code zero. The run finished at `2026-10-04T21:10:19.734164+00:00`. I inspected the command/result records and actual build output; I did not execute this build myself.

I read the full actual `axioms.txt`: all 20 definitions and all 50 theorem types and transitive axiom dependencies are present, matching the complete 70-declaration source inventory. There are no named instances, private or unnamed proof declarations. Every displayed theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. The independent lexical scan reports no admitted proofs, custom axioms, `native_decide`, execution shortcuts, or kernel-trust changes, consistent with my complete source reading.

Lean 4.19.0 is pinned to compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Mathlib v4.19.0 resolves to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The execution evidence checks all nine exact dependency revisions and clean tracked sources before and after the build, rechecks the compiler, and records unchanged source/configuration and audit inventory. My recomputation confirms that all nine source/configuration identities match both the frozen manifest and the original/copied identities in the execution record. No auxiliary mathematical program, numerical oracle, or unverified simulation is needed.

## PDF and eligibility evidence

`pdf.json` records successful final-source compilation in the built-in editor and Tectonic 0.17.0 export of a four-page, 69,389-byte PDF. Its source and PDF hashes match my recomputation. The export reports no warning or box diagnostics, consistent with my inspection of the recorded compiler diagnostics.

The report author personally inspected all four complete final rendered pages and reported PASS. The coordinating agent separately inspected the same four final pages and reported PASS, with their page identities recorded. They report no clipping, overlap, broken mathematical glyphs, or layout defects. I reviewed and hash-bound that evidence, but did not personally view the PDF images and do not claim those visual checks as my own.

I read the initial eligibility record and final refresh. The separate corpus agent's all-state PR snapshot completed at `2026-10-04T21:07:25.319554+00:00`, covering 570 PRs through PR574; the complete recorded refresh including direct discussion checks completed at `2026-10-04T21:07:55.381298+00:00`. Main, source, guides and unsolved metadata are unchanged. The five new PRs were classified as unrelated; the broad Chinese PR5/511 discussions were directly fetched again and matched the previously inspected bytes. No prior or competing submission was found within the recorded scope. I did not independently repeat those searches. Indexed-search lag, inaccessible work, and later submissions remain outside the snapshot guarantee.

Both complete current contribution guides were read during this review process. Their hashes are listed separately below. The required semantic scope and recorded validation are satisfied for the identified inputs. Packaging, future changes, maintainer review and acceptance are separate from this signoff.

## Exact reviewed input identities

I recomputed all 21 hashes immediately before finalizing this review. Paths are intended submission-relative paths. The table excludes this review itself and the later package manifest.

| Submission-relative input | SHA256 |
| --- | --- |
| `README.md` | `b272794a02dd79078033dc3d58da47c32068b090a9d6ef29b7c35c57b99696a6` |
| `VERIFICATION.md` | `c5ee80ca3a5cc5ccfd445dababc01bc07eb280cbea52200744105023de914436` |
| `conjecture.md` | `557ca674a08a7668f155d2f24328c3f83dbf2ea3780c3f5925396d8557120ea8` |
| `lean/Check.lean` | `26f568645629c12f47ec41eb6db841c1928ee8932c80ac5785ba1551da76a78b` |
| `lean/Conjecture978.lean` | `ad6451d360443f1ab7f847bd455c18640dfcb37cf3ad50c60f4d4e8e6f8daaa6` |
| `lean/Conjecture978/Boundary.lean` | `6ce6305dc1bf664ba45aef1d7929a219275d094fea2a340fd9d12f94ee6a192d` |
| `lean/Conjecture978/DualCurve.lean` | `8477f12ddcd824eb1b0ffd270afd993670062c5e39da47466408dec612397ea8` |
| `lean/Conjecture978/NumericalRange.lean` | `850c01ba06a9fc30d8843e74c9cbe895ff810b2347944b48ec021df0890b5bba` |
| `lean/Conjecture978/Pencil.lean` | `0e898f9552e9ed8b63382125db4965f748c995fd29e49d7005ed56cff7950532` |
| `lean/lake-manifest.json` | `7db95ab4e82070da47d81ecc01cada3a24cacd461b7c8a4b4d2cce85d3d9ff96` |
| `lean/lakefile.toml` | `86b4473ea2f0a0546cb730d30e7548b8900bf34d0b5d39aede68058396213922` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `main.pdf` | `06c852069416ec5fd48f0603810cca0b41646e43c88c142b12a7b20de6b04b13` |
| `main.tex` | `6ab3fc6fac1dcbf8643ce1dcef02a910587b927536a1cf54ed130096b443f477` |
| `verification/axioms.txt` | `8fb98a7b14b8c04d5d58c36e9f9113801f0a12757c968d976e887f2640d975c7` |
| `verification/build.txt` | `899af1eedc170570cff972b8b672e30d024acb41253884f7bd9a42adf0f2d07a` |
| `verification/eligibility.json` | `f6c4f3db3cf1caf290d7b75fbbbe258cbe74fc375f3381b3b13d295171910ce1` |
| `verification/pdf.json` | `31c612468329e47d008479a32669bf113448b91f783c20cdb3baa9e87b908805` |
| `verification/prepublication.json` | `de67793250c9409b31b7420c44e356a0162d34985b6f615159c1ba4b25cc56cc` |
| `verification/report.txt` | `ccc4806e5f44c658935aa24907bd1fffc95f44fe74e6f6a6f35f396180f19c0b` |
| `verification/strict-replay.json` | `8b484586d475a00b0d6f7d3032c9339c8e0e4c44850e30a31262150aecf07c1f` |

Current upstream contribution guides, read in full and separate from the 21 submission inputs:

- `README.md`: `cd54d17f51e08212ee9557ef74568f6f2c388279ac74339dc4a3bab7c283f27e`.
- `README.zh-CN.md`: `ffedf1385079b9741fce4176c7aa1662720c29391116b34e5e78ba154b4fa244`.

The guide identities belong to recorded upstream main `fe1d06d431b0591b65d759c60035b1d2e293a819`.
