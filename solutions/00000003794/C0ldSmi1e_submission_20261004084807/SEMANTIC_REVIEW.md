# Internal semantic review: conjecture 00000003794

**Verdict: PASS for the unrestricted solution-count assertion explicitly identified in the report. No correction to the reviewed mathematical source or report is required.**

This is an internal, independent source and mathematical-correspondence review dated 4 October 2026. It is not an official competition review, an acceptance decision, or a claim that the reviewer personally reran the compiler or inspected the rendered PDF. The reviewer read every submitted proof module and the report, compared them with the exact bilingual conjecture, inspected the relevant Mathlib definitions, and checked the separate compilation and axiom-audit records against independently calculated source hashes. Maintainers retain responsibility for interpreting and accepting the submission.

## 1. Exact statement and scope

The English and Chinese source were both read in full. The source's first substantive clause places an upper bound of 2^n on the number of LCP solutions. Neither version states a P-matrix domain hypothesis, a nonsingularity hypothesis, or a restriction to finite or isolated solution sets. The subsequent phrase about the tightness of the bound and the strictness of P-matrices is not a precise mathematical definition. The report quotes the English source, preserves the exact bilingual source separately, and expressly identifies the unrestricted bound as the clause being refuted.

This interpretation is faithful to the explicit first clause. It is not a claim that every possible intended repair of the poorly specified final phrase is false. The counterexample has determinant zero and is not a P-matrix. It does not refute a statement whose quantifiers are newly restricted to P-matrices, to isolated solutions, or to LCPs with finite solution sets. The report discloses all three scope limitations. No such restriction has silently been removed from an explicit hypothesis in the source, and no invented formal definition of “P-matrix tightness” is used.

The source refers to complementarity on cones. The nonnegative orthant is an actual convex cone and gives the standard real LCP instance; refuting a claimed universal count in this instance is sufficient. Counting actual solutions differs from counting complementarity patterns. The proof and report consistently count actual real vectors, not supports, basis choices, connected components, or isolated solutions.

## 2. Fidelity of the definitions

`nonnegativeOrthant n` is defined as Mathlib's `ConvexCone.positive ℝ (Fin n → ℝ)`. The imported definition has carrier `Set.Ici 0`; the order on the function space is pointwise. Consequently the proved equivalence with `∀ i, 0 ≤ x i` is the actual nonnegative orthant, not an arbitrary predicate named after a cone.

`LCPSolutions M q` ranges over all real vectors indexed by `Fin n` and requires all three standard conditions:

1. `x` belongs to the orthant.
2. The actual residual `M.mulVec x + q` belongs to the orthant.
3. `dotProduct x (M.mulVec x + q) = 0`.

The imported `Matrix.mulVec` is row-by-column matrix-vector multiplication, and `dotProduct` is the finite sum of entrywise products. The code proves the coordinatewise complementarity equivalence for every dimension and all real matrices and vectors. Its nonnegative-sum argument correctly uses nonnegativity of both vectors before inferring that every product vanishes. No feasibility or complementarity condition is omitted, and `q` is unrestricted in the definition and universal bound.

The primary definition was checked against X. Chen and S. Xiang, *Sparse solutions of linear complementarity problems*, Mathematical Programming 159 (2016), 539–556, §1, p.540. It uses exactly these conditions and discusses the possibility of infinite solution sets. [Author-hosted article](https://www.polyu.edu.hk/ama/staff/xjchen/Chen-Xiang2016MP.pdf).

## 3. Counterexample and all-solution classification

The code's matrix is exactly the real 2-by-2 matrix with rows `(1,-1)` and `(-1,1)`. `diagonalVector t` is exactly `(t,t)`.

- `counterMatrix_mulVec` proves, for every real vector `x`, that the product is `(x 0 - x 1, x 1 - x 0)`.
- `counterMatrix_mul_diagonal` proves that every diagonal vector is in its kernel.
- `diagonalVector_mem` verifies every LCP condition for each real `t ≥ 0` with the actual offset `q = 0`.
- `counterSolutions_iff` proves both directions of the complete solution-set characterization. In the forward direction, the two residual inequalities imply `x 0 = x 1`, and primal feasibility gives the nonnegative parameter. It is legitimate that complementarity is not needed for this direction: feasibility is already strong enough. The reverse direction invokes the fully checked solution-membership theorem.

Thus the set is exactly `{(t,t) : t ∈ ℝ, t ≥ 0}`, rather than an assumed ray or merely a ray-like surrogate.

The matrix-strength claims are also actual theorems. Nonzeroness follows from its `(0,0)` entry, the determinant is computed to be zero, and its Hermitian property is checked entrywise. Over the reals this is ordinary symmetry. The quadratic-form identity is proved for every real vector, with Mathlib's actual star and dot product:

`dotProduct (star x) (counterMatrix.mulVec x) = (x 0 - x 1)^2`.

`counterMatrix_posSemidef` combines symmetry with this nonnegative square and establishes Mathlib's `Matrix.PosSemidef`, whose definition is Hermitian symmetry together with a nonnegative quadratic form for every vector. Positivity is not asserted only on the cone or only on the displayed solutions. These stronger properties are supplementary; the disproof does not assume that arbitrary LCP matrices are positive semidefinite.

## 4. Cardinality and quantified negation

The construction `solutionSequence k = diagonalVector (k : ℝ)` has domain all natural numbers. Membership follows from nonnegativity of natural casts. Injectivity follows by evaluating equality at coordinate zero and using injectivity of the natural-to-real cast. `Set.infinite_of_injective_forall_mem` then proves infinitude of the actual solution set. This argument uses no finite experiment or unsupported passage from arbitrarily many examples to infinitude.

`Set.encard` is Mathlib's cardinality in the extended natural numbers `ℕ∞`; infinite sets have value `⊤`. This is the appropriate representation for the claimed finite upper bound. The proof avoids the incorrect use of natural-valued `Nat.card` or `Set.ncard`, whose value on an infinite set is zero. Collapsing all infinite cardinalities to `⊤` loses no information relevant to comparison with the finite number 2^n.

The code proves the solution set has `encard = ⊤`, exceeds every finite natural bound, and does not have `encard ≤ 2^2`. It also constructs an injective map from `Fin 5` into the genuine solution subtype. The latter is an additional concrete five-solution witness, not an assumption used to define the solution set.

The predicate `SolutionCountBound` quantifies over every positive natural dimension, every real square matrix of that dimension, and every real offset vector. Its right-hand side is `(2 : ℕ∞)^n`. The final theorem specializes this unrestricted predicate to dimension two, the actual displayed matrix, and the zero vector, then contradicts the proved failure of the four-solution bound. It has no outstanding matrix, cone, cardinality, identification, or existence hypotheses. The final theorem negates the explicit first clause; it does not formalize or separately negate the source's unspecified tightness phrase. Failure of that necessary first clause suffices for the reported disproof.

## 5. Report, context, and trust boundary

The final reviewed report includes the matrix, offset, exact ray, injection, five concrete solutions, symmetry, quadratic identity, and zero determinant. Its formal-correspondence section matches the implemented definitions and theorem statements. The displayed quantification explicitly takes `n ∈ ℕ` with `n > 0`, matching Lean.

The observation that points with `t > 0` are strictly complementary is correct: every primal coordinate is positive and every residual coordinate is zero, so their coordinatewise sum is positive. It is an elementary prose observation, not a separately named formal theorem or a premise needed by the proof. Likewise, the P-matrix exclusion follows in prose from the formally proved zero determinant and the standard definition requiring every principal minor to be positive. The report does not falsely claim to have formalized general P-matrix theory.

The Rohn citation was read at the original journal source: J. Rohn, *Description of all solutions of a linear complementarity problem*, Electronic Journal of Linear Algebra 18 (2009), 246–252. Proposition 2.4 assumes all complementary matrices are nonsingular for the finite 2^n bound; Proposition 2.5 gives conditions producing infinitely many solutions. Its alternative positive/negative-part formulation is equivalent to the usual LCP. The report uses these results as explanatory context, not as unformalized premises. [Journal article](https://journals.uwyo.edu/index.php/ela/article/download/619/619/).

Every theorem in the two proof modules was read, including the 23 theorem statements covered by `Check.lean`. The audit file prints all six submitted definitions and checks all 23 theorem types and transitive axiom lists. The reviewed source contains no `sorry`, `admit`, user-declared axiom, `native_decide`, custom elaborator, unchecked external result, or replacement of a mathematical object by a success predicate. Tactics operate on the actual equalities and inequalities described above.

The independently produced records in `strict-replay.json`, `build.txt`, and `axioms.txt` were inspected. They record a fresh build in `/private/tmp/tlmc3794-independent`, successful strict replay of all three Lean files with warnings treated as errors, six definition prints, and all 23 axiom audits containing only `propext`, `Classical.choice`, and `Quot.sound`. All six proof/configuration hashes in that record match hashes independently recomputed for this review. The record also reports the exact Lean commit, matching pinned dependency revisions, and clean dependency tracked files before and after the build. This reviewer did not rerun that build; the evidence is separate from the independent source review.

The inspected pins are Lean 4.19.0, Lean commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; the manifest pins all transitive dependencies. Rendered-PDF and final package-manifest checks belong to the packaging workflow and are not claimed as personally performed by this reviewer.

An intermediate eligibility-directory checksum manifest contained an old checksum for the subsequently finalized `strict-replay.json`. This was reported to the packaging agent. That temporary manifest is not the final submission manifest and is not included in this semantic PASS; the packaging agent confirmed that a fresh manifest will be computed over the submitted files. The exact verification-record hashes read here are recorded below.

## 6. Reviewed files and SHA-256 identity

The three Lean modules and three configuration files were read from `/private/tmp/tlmc3794-proof`. The report was read from `/private/tmp/tlmc3794-package/main.tex`. The bilingual statement was read from `/Users/daniel/The-Last-Math-Competition/conjectures/00000003794.md`; its bytes also match `/private/tmp/tlmc3794-verification/conjecture.md` and the source identity recorded for upstream revision `0862407ef50dda4f7376342ca3e79368dce942d2`.

The report was reread after its second-page wording was shortened and `n ∈ ℕ` was made explicit. Those edits preserve the mathematical claims and the disclosed scope. The hash below is for that final reviewed version, not the earlier draft.

| Reviewed file | SHA-256 |
| --- | --- |
| `Conjecture3794/Problem.lean` | `c855d1cb4f594faa71d62dc2c958cc7a52ffb7a680cd4a84e6216537cff6f3b4` |
| `Conjecture3794.lean` | `4d56153d30c2f6c5726e7757d48274cd514fb3a3637ab05dca44712706ca7efb` |
| `Check.lean` | `c1a7df99c938726344f637418ce6e00a8a1387a5de175af03488185b4669ebf4` |
| `lakefile.toml` | `d66453f57a54c0eb83c1d2c8de7ef735e80328a2f57d2b25ce51245809aafab3` |
| `lake-manifest.json` | `ccf737330cc56f95cfef4f0efda291f14dd742659b94f844051ea5a12e35b501` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `main.tex` | `f9d1477f8d3576dc8e912b879b7546a5f4b347819e6d8c026439adcb40aff601` |
| `conjectures/00000003794.md` | `6084481811395579aadf1e178f0c488228fad349b98d5d4ada8f60799e5a4fca` |

The separate verification evidence inspected had these hashes:

| Evidence file | SHA-256 |
| --- | --- |
| `strict-replay.json` | `781590f2123a116c277879a3fdb11d095a333c244576325ffd4bdb613c0f10ca` |
| `build.txt` | `abe1d213fe931ea69b59cfb8994a2bb6c79bce269f908d38cf3844641d877679` |
| `axioms.txt` | `349ad9d8304330e034b652fca4b938ac6a25d44b10fcd789b92ab6d958f79bd2` |
| `eligibility.json` | `ad014bedcb82dc869f6282af5a0292e52b2253ffdec5b8cdf2b83242f33f0f29` |

**Remaining mathematical corrections: none.** The semantic verdict applies to the precise unrestricted clause and the exact file identities above. It neither preempts a maintainer's interpretation of the ambiguous tightness wording nor establishes official acceptance.
