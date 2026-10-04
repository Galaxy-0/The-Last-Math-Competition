# Independent internal semantic review — conjecture 00000000367

**Verdict: PASS.** The reviewed Lean statements give faithful counterexamples to the necessary lower-bound clause in both language versions. No unresolved mathematical or semantic correction was identified. This is an internal, independently performed source review, not official reviewer approval, maintainer acceptance, or a claim that a pull request has been merged.

## Reviewed scope and original claim

I read all six Lean files, all three configuration files, the entire final LaTeX report, the exact bilingual conjecture, and the relevant rules in both current guides at upstream commit `4cc82278ba1e5becc4d20b1e2a68dede094e2b8d`. I also inspected the relevant underlying Mathlib definitions and lemmas for linear recurrences, characteristic polynomials, finite multiplicative order, nearest-integer rounding, infimum distance, and exponential-versus-power limits. The final report includes the corrected, precise sentence identifying recurrence, minimality, distance and limiting claims as the kernel-checked content. I also read the final package README and VERIFICATION documents; their mathematical coverage, module inventory, reproduction commands and division of review responsibilities agree with the reviewed sources and execution evidence.

The source asserts that the nearest-integer distance of the general term of a nondegenerate linear recurrence exceeds `n^(-C)` for an explicit exponent determined by characteristic-root modulus gaps. Neither language imposes an integer-coefficient restriction, excludes integral terms, requires irreducibility, or specifies exceptional indices. The formal target deliberately permits an arbitrary eventual threshold and any real exponent. Failure even with those permissions refutes the printed lower-bound claim. A formula assigning an exponent from root gaps cannot exist for a witness having no such exponent at all; no artificial definition of that unspecified formula is introduced.

The standard meaning of nondegeneracy was checked against D’Costa, Ouaknine and Worrell, *Nonnegativity Problems for Matrix Semigroups*, STACS 2024, section 3, p. 27:3: [author-hosted primary paper](https://people.mpi-sws.org/~joel/publications/matrix-nonnegativity24.pdf). The paper permits LRS over a field, uses the minimal-order characteristic polynomial, and excludes root-of-unity quotients of distinct characteristic roots. Its discussion explicitly includes rational sequences. This is a definition reference only; no result from that paper is an unformalized step in the disproof.

## Actual recurrence and root semantics

`recurrence r` is Mathlib's actual `LinearRecurrence ℝ` with order two and coefficient vector `![-2*r, 2+r]`. Under Mathlib's `IsSolution` definition this means `u(n+2) = -2*r*u(n) + (2+r)*u(n+1)`. `sequence_isSolution` proves this identity for the actual sequence `2^n+r^n` at every natural index. There is no substitute recurrence predicate or assigned characteristic-root table.

`recurrence_charPoly` computes the actual Mathlib polynomial as `(X-C 2)*(X-C r)`. Mapping it to complex coefficients is explicit. `recurrence_complex_root_iff` identifies **every** complex root and both displayed roots. `Nondegenerate` quantifies over the full complex root set, requires the roots nonzero, and excludes `IsOfFinOrder (a/b)` for every distinct pair. Mathlib's finite-order predicate means a positive power equals one. The proof uses the necessary unit-norm property of such elements, not a claim based merely on distinct real values. Positivity and `r≠2` make the quotient norm argument valid.

Minimality is a proved property against **all** real homogeneous linear recurrences satisfied by the sequence. Order zero is ruled out by the nonzero initial value; order one forces `(r-2)^2=0`. Thus the main and supplemental examples have true order two even over the reals, and consequently also cannot have lower-order recurrences over the rationals or integers. No unused characteristic root has been added to manufacture nondegeneracy. Although the custom nondegeneracy predicate explicitly includes nonzero roots, both witnesses satisfy that stronger requirement, so it introduces no loophole in the counterexample.

For `r=1/3`, the coefficient vector is proved equal to rational data `(-2/3,7/3)` embedded in the reals. The sequence is separately proved rational-valued. For `r=3`, its coefficients are proved equal to integer data `(-6,5)`, and its terms are actual casts of `2^n+3^n` from the integers. This covers both the ordinary field-valued convention and a restriction to monic integral recurrences with integer initial data.

## Distance to integers and all-index arguments

`distanceToIntegers x` is `Metric.infDist x (Set.range (Int.cast : ℤ → ℝ))`, using the entire integer set. `distanceToIntegers_eq_round` proves equality to `|x-round x|` in both directions: the rounded integer supplies a member for one inequality, and the nearest-integer theorem supplies the lower bound against every integer for the other. Nonemptiness of the integer range is explicitly provided. There is no reliance on the zero value of infimum distance to an empty set.

For every `n≥1`, the proof establishes `(1/3)^n≤1/3`, rounds that remainder to zero, uses compatibility with integer translation, and obtains exact distance `(1/3)^n`. Positivity proves actual nonintegrality against every integer, rather than only inequality with the chosen nearest integer. The positive-index condition correctly excludes `n=0`, whose term is the integer two. Growth to positive infinity is also proved by comparison with `2^n`, so the principal example is not just a decaying sequence.

`polynomial_mul_third_pow_tendsto` applies the actual real exponential-versus-power limit with positive rate `log 3`, then composes with natural-number coercion tending to infinity. Its exponent is an arbitrary real `C`. The subsequent eventual comparison uses positivity of `n^C` on a positive tail and the real inverse-power identity. It therefore proves the strict reverse inequality on an entire tail, not merely for selected exponents or finitely many samples.

`HasPolynomialLowerBound` has exactly the relevant existential quantifiers: some real `C`, some natural threshold `N`, and the printed strict lower inequality at every positive index beyond `N`. The main contradiction intersects the reverse-inequality tail with both `n≥N` and `n≥1`. The integer alternative chooses `N+1`, proves the power positive, and contradicts the zero distance. `conjecture_false` and `conjecture_false_integer_example` are genuine negations of the universal assertion and discharge all actual solution, positive-order, minimality and nondegeneracy hypotheses with the constructed witnesses.

## Report correspondence and limits

The report's initial values, characteristic factorizations, determinants `25/9` and `1`, root quotients, and root modulus gap `5/3` are correct. Its minimality argument agrees with the more general Lean proof. The exact distance, nonintegrality, unbounded growth and full limiting contradiction agree with the formal theorem statements. The displayed determinant and gap arithmetic are explanatory specializations; the final report does not overstate that each displayed numeral has a separately named theorem.

The logical bridge uses the source as written and the cited standard meaning of nondegeneracy. It does not assert that unrelated, stronger conjectures with additional restrictions have been refuted. In particular, the rational example and the integral example address two clear conventions separately; the rational example is not claimed to have monic integer recurrence coefficients. No auxiliary numerical computation is used as mathematical evidence.

I reviewed the LaTeX source for mathematical correspondence. I did not independently render or visually inspect the PDF in this semantic-review task. I inspected `pdf.json` and the final TeX log: they record successful native compilation and Tectonic export, two pages, and a full visual inspection of both pages by the coordinating agent. The log has no warnings or overfull/underfull boxes. I recomputed the actual TeX and PDF hashes and confirmed both match that record. Visual layout findings are attributed to that separate inspection, not my own execution. No proof or report source was edited by this reviewer.

## Execution evidence inspected

I read the completed independent records `strict-replay.json`, `build.txt` and `axioms.txt`, finished at `2026-10-04T18:07:10.290499+00:00`. The separate execution agent performed the fresh build in `/private/tmp/tlmc367-independent`; I did not rerun that build. The records show a successful full build and six direct source replays with warnings treated as errors, using Lean 4.19.0 commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. All nine dependency revisions match the pinned manifest and have clean tracked sources before and after execution. Dependency caches were reused; the submitted project outputs were built afresh.

I read the actual emitted seven definition printouts, all 35 theorem types, and all 35 axiom lists. I independently reparsed the theorem inventory from `Check.lean` against the emitted axiom lists: all names agree, and the only axioms are `propext`, `Classical.choice` and `Quot.sound`. The scan records contain no proof-bypass hits. I independently recomputed every one of the nine source/configuration hashes in both the original and the fresh copy; all agree with the execution record and remain unchanged. The final theorem outputs carry no unexpected parameters or assumed witness properties.

The eligibility record examined here marks the conjecture unsolved and reports no matching submission among 541 all-state PRs through PR545, nor in the checked solution-path histories. The short-ID search hit PR367 concerns a different conjecture. I additionally read the final refreshed prepublication record, checked through `2026-10-04T18:12:14.150236+00:00` at upstream commit `45e2f961f922bc86e3797967254eb513ac180edc`. Although main advanced, the exact conjecture, both entire guides (including their rules and leaderboards), and the entire metadata file are unchanged from the reviewed revision. The snapshot covers 543 all-state PRs through PR547, still marks conjecture367 unsolved, and finds no candidate submission or current/historical solution path. Prior raw evidence is preserved; this eligibility update does not change any mathematical source, report or execution identity. These are bounded, timestamped screening results, not a guarantee against later submissions. I have not independently audited staged Git bytes or a final package-wide hash manifest; those repository-scope checks remain separate operational responsibilities. The supporting documents describe those packaging checks, rather than supplying an additional mathematical assumption.

## Exact reviewed identities

SHA-256 hashes below identify the reviewed files. Lean/configuration paths are relative to the reviewed project root `/private/tmp/tlmc367-proof`; report, source, guides and records are identified separately.

| File | SHA-256 |
|---|---|
| `Conjecture367/Definitions.lean` | `21961da49f15983b3844bd1d38fb3dd1ef7e94b3341b8204653f37e0fd70c939` |
| `Conjecture367/Recurrence.lean` | `c37690828302a36fa3dcf32560b18483364e01854fa0390b3d6fa6ca84cb12ba` |
| `Conjecture367/Distance.lean` | `127acd430b7ca5634ffb66e9f4948db613f6c7253364e2f819f4b8d64d53882b` |
| `Conjecture367/Asymptotics.lean` | `99db7e6acb0701147020a90c0cbbe9a9be0e0660506a8eacbff572d5a298cc91` |
| `Conjecture367.lean` | `4da4e7d0f7e7b7535c37620e9885bd0085339a5d23ad25fa58ea92027821b420` |
| `Check.lean` | `6a61075f924ecf0a848385c822024d64c4ffa5d5642326f2d85c1405ac28704f` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `lakefile.toml` | `41c91436a380339543f8e5f90735901a074da6aa195865f13959cbe76d1a6028` |
| `lake-manifest.json` | `40e77959e02f718e712f3a3c529fb9f97c8ee94f3d4d543261e1a853ec7aeda1` |
| Report `main.tex` | `0707dd41a71a2f4bc7f873b1abb8b421c7ec9c004a17bfe950a37031929099e0` |
| Exact bilingual `conjecture.md` | `4a1200a058785f8ddefb4b5b61c09c068eccb5c2fbcad99962d4abdcf0589b01` |
| Upstream English guide | `f7df38cc270f58a323726aaa98535a26a447a59b801a89dca371460e2f852186` |
| Upstream Chinese guide | `2b044eeb742eb45a4607e55edd82471e975f8c01e376ba5313c128fcf0d301ae` |
| Eligibility record | `40ee7e6b0541bcf1b22bc82f0852641ac0776d04b589033c2c37346f51cd712d` |
| Execution `strict-replay.json` | `dfab240a8a6c4c363f1a04d98e8556fbc11f6d8d1c4451e60f91a93746159f78` |
| Execution `build.txt` | `d7c45080042990e6c08d9edff5c53708a1dad969569ebb783a326127b1057157` |
| Execution `axioms.txt` | `4b68ecae345473c997d4583768d53f16e9f5c6153d029fc008b5e665a39ccddb` |
| Package README.md | `2530cb040a27b6996b52613b9e83e7bab34225a1d6b68f25ffd743b025102cb9` |
| Package VERIFICATION.md | `3575d79dae20dc0400d4eddaf35b19186496e0c01cbe286fbea81cc2b089ec2c` |
| Report PDF (identity only) | `c30ec444fb9f7d480d685ebefb1ec6c79d1b7b1cbd41acdc245e9190a7255708` |
| PDF evidence pdf.json | `316e95c5332743559a6a68978b119b834614f16815a59256ad335d5ba9eb4298` |
| TeX log report.txt | `0db44e6d87a0fdfb26fd889b12d2b78dfb67df972164c2188791be6ade482f89` |
| Final prepublication record | `b566c978dfe808b8c7cb4a98439227a628d433f374bb12de4b5a195cb81b4785` |
