# Independent internal semantic review — conjecture 00000000574

**Verdict: PASS. The reviewed sources faithfully disprove the explicit strictly-alternating-sign clause using the actual parallel-thickened uniform matroid U(3,4). No mathematical or semantic correction is required.** This is an independent internal author-side review, not an official competition review or maintainer acceptance.

## Review scope and source interpretation

I read all seven frozen Lean files, including the root import and Check file, all three configurations, the complete final LaTeX report, README and VERIFICATION document, the exact bilingual conjecture, and both complete contribution guides. I examined the separately produced execution, emitted-output, PDF and final eligibility records and independently reconciled their identities. Source correctness was assessed separately from successful compilation.

Both source languages explicitly assert strict alternation of the KL coefficients. Refuting this necessary clause suffices to refute the conjunction; the submission does not invent a definition for the unspecified hypergeometric terms. It uses the ordinary matroid KL polynomial, not a negative-variable substitution. Its coefficients 1 and 2 are adjacent and nonzero, so their equal sign contradicts alternation independently of starting sign, coefficient-reading direction, or a convention for omitting zero coefficients.

The ordinary definition was checked against the author-hosted [Elias–Proudfoot–Wakefield paper](https://pages.uoregon.edu/njp/kl.pdf): Section 2.1 and Theorem 2.2 specify the Möbius characteristic polynomial, rank-zero value, strict half-rank degree bound and recurrence. The introduction describes the matroid interpretation of flat intervals; Example 4.7 independently confirms the rank-three uniform formula. The code uses the equivalent standard ranked-flat definition directly and proves the required existence and uniqueness for this matroid. It does not assert a global KL implementation or postulate an external formula.

## Actual matroid and complete flat lattice

`uniform` constructs an actual Mathlib `Matroid` through `IndepMatroid.ofFinite`. The independent sets are precisely the subsets with cardinality at most r; downward closure and augmentation are proved. The finite ambient type discharges the finiteness needed by set cardinalities. The proofs derive the actual ground set, closure, flat characterization and extended-natural rank rather than assigning these as unrelated data.

`thickened34` is the actual comap of `uniform (Fin 4) 3` along the first-coordinate map on `Fin 4 × Fin 2`. Its actual independence condition requires at most three represented classes and injectivity on the independent set. Its actual rank is `min 3` of the number of represented classes, and its total rank is three. The code proves looplessness, two-element class cardinality, singleton closure equal to its class, and a genuine two-element circuit for the two copies of each original point. Thus this is a parallel extension of the intended uniform matroid, not a direct sum, an assigned rank formula, or a disconnected vector table.

The copy-count ambiguity in the source is addressed without changing the obstruction. The witness has one added copy per element, two total copies per class, or four individual parallel additions. The general `comapFlatOrderIso` is proved for surjective maps, and `comapFlatOrderIso_eRk` proves preservation of actual ranks. The report accurately limits the generic formal statement to that flat/rank fact and uses the particular eight-element witness for the final polynomial.

`uniformFlatOrderIso` and its composition `thickenedFlatOrderIso` establish an order isomorphism from the finite presentation to **all** actual `Matroid.IsFlat` subsets. The inverse maps and both inverse laws prove completeness, not just membership of twelve nominated sets. The order is actual inclusion. The flats are empty, four classes, six pairs of classes and the whole ground set. The actual extended-natural ranks agree with the presentation's ranks 0, 1, 2, 3. Actual rank finiteness is proved, so `eRk.toNat` does not conceal infinity. Empty and full endpoints are identified with the actual empty set and actual ground set. This closes the finite-poset-to-matroid bridge.

## Möbius function and full KL characterization

The explicit `mobius` function is zero off the order relation, has the correct diagonal values, and satisfies both incidence recurrences on every pair. Its incidence-algebra element is proved to be Mathlib's `IncidenceAlgebra.mu` by the zeta inverse identity. Consequently the characteristic polynomials are genuine complete Möbius sums with actual interval rank differences. The whole-lattice value is proved to be `X^3 - 4*X^2 + 6*X - 3`.

`SmallDegree d p` sets every coefficient with `d ≤ 2*i` to zero. This is exactly strict support below half the rank; it allows the zero polynomial and excludes the even-rank midpoint. Diagonal intervals are handled separately with value 1, while strict rank monotonicity makes every strict interval's rank difference positive. The derived support bound justifies using `Polynomial.reflect d` as rank-d reflection. I checked the underlying Mathlib implementation during the core review: it reflects exponents at d, not at the polynomial's own degree; the coefficients above d vanish here.

The recurrence is imposed on **every comparable interval**, including both endpoints, with the correct product `characteristic a c * P c b`. The candidate family is 1 on proper intervals and `1+2X` on the sole rank-three interval. Its diagonal values, strict degree bounds and full recurrence are proved. The finite coefficient computation covers indices 0 through 4, and proved degree bounds on both sides show all higher coefficients vanish; it is therefore a full polynomial equality, not a finite numerical sample. These finite checks use ordinary kernel-checked Lean proofs.

`klFamily_unique` compares arbitrary competing families by strong induction on the actual rank difference. Removing the lower-endpoint summand isolates the unknown interval value; every remaining upper interval has smaller rank. Low-degree coefficient separation for the resulting skew-reflection identity proves equality. The proof correctly establishes uniqueness only for comparable pairs. Incomparable values are left unconstrained and never used; neither code nor final documentation claims uniqueness of an arbitrary total family function.

## Transport and final logical contradiction

The same proved order isomorphism transports the complete interval sums. `actualMobius` satisfies both recurrences over all actual flat intervals. `actualCharacteristic` is defined as a sum over the actual flat subtype using actual matroid rank, and its equality to the computed presentation is proved. `actualCandidate_isKL` transports every defining condition, not just the value of a polynomial.

`actualKL_existsUnique` proves there is exactly one polynomial occurring as the bottom-to-top value of any certified family on the actual matroid's flats. The transported candidate supplies existence, so this is not a conditional or vacuous characterization. `klPolynomial` is selected from that proved existence; `klPolynomial_spec` exposes the full certificate. Only afterward does generic uniqueness identify its value as `1+2X`. The final answer is therefore derived from the invariant's axioms, not defined by prescribing the answer.

`AdjacentSignsAlternate` is a necessary condition for strict alternation: each adjacent pair that is nonzero must have negative product. Allowing zeros in this weaker predicate cannot weaken the counterexample, since coefficients zero and one are proved to equal 1 and 2. `conjecture_false` negates that necessary instance for the actual witness without residual hypotheses. It does not purport to negate a newly invented hypergeometric formula. The instance is enough to contradict the source's universal sign assertion.

The report's rank-one/rank-two interval calculations, characteristic polynomial, rank-three equation and uniqueness argument agree with the code. The full three-page source was read; the README and VERIFICATION document accurately describe its scope and reproduction steps. No auxiliary mathematical numerical program is needed.

## Execution, identity and PDF evidence

A separate verification agent performed a fresh project build in `/private/tmp/tlmc574-independent`, copying only seven Lean files and three configurations. I inspected those execution records; I did not rerun compilation as part of this semantic review. The build and all seven direct source replays with warnings treated as errors exited zero. Lean is 4.19.0 at exact commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, checked before and after. All nine dependency revisions match their manifest pins and their tracked sources remained clean. Mathlib is pinned at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The execution reused a pinned dependency cache rather than rebuilding all dependency sources.

I independently recomputed all ten source/config hashes and matched them against the frozen bytes, fresh-copy bytes, and both recorded identities. I also independently reparsed the actual Check output: all 30 definition/abbreviation/structure printouts, all 80 types, and all 80 axiom lists match the requested names exactly. This comprises 75 named theorems and five named instances. The only transitive axioms are `propext`, `Classical.choice` and `Quot.sound`. The actual output also equals the Check replay output embedded in the JSON. There is no admitted proof, custom axiom, native decision proof or kernel bypass. The scan's one raw match is the English verb “admit” in a comment; the code-token scan is empty.

I checked the final TeX/PDF hashes against `pdf.json` and inspected the preserved TeX log, which has no warning or overfull/underfull box entry. Native/Tectonic compilation and visual inspection of all three rendered PDF pages were performed by the coordinating agent, not by this reviewer. Their recorded scope is complete final-page inspection, and the compilation/rendering records report success. My own report review is of the full source and its correspondence with the proof.

## Eligibility and review limits

Both complete guides and the exact bilingual source match final upstream `fe1d06d431b0591b65d759c60035b1d2e293a819`. The final eligibility refresh through 2026-10-04 19:06:07 UTC retains unsolved metadata, covers 546 PRs through #550, and reports no ID match, relevant competitor, or current/historical solution path. Three keyword matches, PRs 69, 371 and 476, are explicitly classified as unrelated Coxeter/Hecke problems; the searches are not falsely described as having no keyword results. No previous-submission error account is indicated by the reviewed records.

These are time-bounded, search-scoped eligibility findings. This review does not reperform the remote search, guarantee absence of inaccessible or future submissions, or approve a final staged diff. Final personal-folder-only staging, publication and official maintainer acceptance are separate tasks. The reviewed material addresses the guides' mathematical, source/report and execution requirements; this document does not authorize changes to an official review folder, metadata or leaderboard.

## Exact reviewed identities

All hashes are SHA-256 of the final reviewed bytes. `lean/` paths below come from `/private/tmp/tlmc574-proof`; report/document paths from `/private/tmp/tlmc574-package`; the eligibility and verification prefixes identify files in the corresponding `/private/tmp/tlmc574-*` evidence directories.

| Reviewed file | SHA-256 |
|---|---|
| `lean/Conjecture574/FlatDefs.lean` | `9d2dc2ef031b8eeb214092485beb9507175f494a6ba0d28131146a38d0385ca0` |
| `lean/Conjecture574/Matroid.lean` | `93fc9af6919663e681a9db25206d9365f2ca5240d4625d9a55bece273f5cd517` |
| `lean/Conjecture574/KLCore.lean` | `ab56918e284a2d32023868c98ca507ac9c08d18e1dfdd7992e7a4b20b79d93e6` |
| `lean/Conjecture574/Lattice.lean` | `488c172089b6603b220bf66fb87ece957e013329ad08c694a655c40193a63161` |
| `lean/Conjecture574/ActualKL.lean` | `7db26357c627c1fdee68cef5525e683c4972dc8792faefc605baf633f9d1ef06` |
| `lean/Conjecture574.lean` | `b450eced35ed49e7d7a10ab18becb74c9702981645ff2af1f087729fda6ea537` |
| `lean/Check.lean` | `9782ecd02c757fd130779259685d9c93901765a658f07ddd2c643da78fccb2ec` |
| `lean/lakefile.toml` | `a89cfbc423f97c2b5770d03b1e614678a612beaa86be6c29d6bcd708b5fff0e7` |
| `lean/lake-manifest.json` | `1625883b5dde2c85aa09bee7f923bd4f4d484f9355c3b49b331fc4d7d404ba89` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `main.tex` | `dc00ca6fdb3910c1a681a0ae80d8a5abdfcfcbc97b8124335a88bc19d0fc309f` |
| `main.pdf` | `610aa8535dece1b2381e83397d278cfab976395d911e459e30a2fd753cb6ff41` |
| `README.md` | `7d87d4f5075a641cd3fb5d455e83bfc43912f18aaa68e07561b4fc03f229f80c` |
| `VERIFICATION.md` | `4bf333d221cb403869c8c54a4e0c17d8627056504408182a533169dca3387954` |
| `eligibility/conjecture.md` | `2c200bd4207bd543fa48a329f6e8ac777bb7de5926220a2e7041477a77749203` |
| `eligibility/upstream-README.md` | `cd54d17f51e08212ee9557ef74568f6f2c388279ac74339dc4a3bab7c283f27e` |
| `eligibility/upstream-README.zh-CN.md` | `ffedf1385079b9741fce4176c7aa1662720c29391116b34e5e78ba154b4fa244` |
| `eligibility/eligibility.json` | `440ffa773926918e5a343682bf5c30a1fea9025ff1c4c52c2edf9e623656f320` |
| `verification/strict-replay.json` | `97460e6e65146fe03ec7bdf996e1dc93f2833c98f3cb6b96aa92fbdd677ce1aa` |
| `verification/build.txt` | `29daed892be64d76e617a4bb66c4da28fb5ef990862971add11d55ad53f3e8ea` |
| `verification/axioms.txt` | `4a9706536977d22dd29dd206cbab0919624415e439ce94cdff0e059e8cab708e` |
| `verification/pdf.json` | `897908523b92b936c78cc303d46aac64b70ddfcbe49f5633ece127e42099f944` |
| `verification/report.txt` | `bb8d146fbe1786c6146a53d9e91b1e68c9fbeff893d394143c639c1590153d9f` |
| `verification/prepublication.json` | `2cb4fca62482e833db931a33e599885a6131a552926658ee1bc2124c20adc3a8` |
