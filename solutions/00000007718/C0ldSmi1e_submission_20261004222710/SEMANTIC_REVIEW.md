# Independent internal semantic review — conjecture 00000007718

**Verdict: PASS for the explicit positive-minimum refutation and the stronger family conclusions, with the scope stated below. No correction is required in the reviewed mathematical source or report.**

This is independent internal scrutiny by the `alternative_candidate` agent, not an official competition review or maintainer acceptance. I participated in candidate scouting and semantic preassessment, but authored none of the submitted Lean proof, LaTeX report, README, or verification documentation. I read all four implementation modules, `Check.lean`, all three configuration files, both language versions of the conjecture, both complete contribution guides, the entire final report and documentation, and the execution/PDF/eligibility records. I inspected the four complete final rendered PDF pages. I changed none of those inputs.

The fresh Lean build and strict replays were performed by a separate execution agent. I inspected their actual recorded output and independently reparsed the emitted definitions, theorem types, and axiom lists; I did not rerun that build. The distinctions between source review, separately performed execution, document compilation, visual inspection, eligibility searches, and official acceptance are maintained throughout this review.

## 1. Meaning of the claim and the exact logical refutation

Both English and Chinese explicitly assert that the smallest possible positive second-to-Perron eigenvalue ratio at r=3 is `(3−sqrt 5)/2`. A minimum entails that every positive ratio in the claimed class is at least that number. The formal theorem `conjecture_00000007718_false` negates this necessary universal lower-bound consequence on a certified subclass of primitive three-letter geometric substitutions. The subclass restrictions strengthen the witness hypotheses; they do not weaken a universal assertion being refuted.

The source does not separately define r. The report transparently uses three-letter/alphabet size and 3×3 matrix size, and also proves actual matrix rank three. This is an explicit convention, not a hidden interpretation as ambient geometric dimension or algebraic degree of the Perron number. No aperiodicity, unimodularity, characteristic-polynomial irreducibility, or bound on substitution length occurs in either source language.

The report correctly leaves the trace-error and algebraic-degree conjuncts unresolved separately. The false minimum clause suffices to refute the conjunction. Neither Lean nor the report invents a definition for the source's underdescribed trace formula. The final theorem is not represented as a formalization of every other conjunct: its precise necessary-consequence type is printed and explained.

For conventions, I checked the primary research sources cited by the report: Berlinkov–Solomyak, [*Singular substitutions of constant length*](https://arxiv.org/pdf/1705.00899), introduction and §2.1, for actual word-count incidence matrices, positive-power primitivity and ordering matrix eigenvalues by modulus; and Solomyak, [*Eigenfunctions for substitution tiling systems*](https://arxiv.org/pdf/math/0512602), §§3.1–3.2, for colored prototiles and expanding geometric subdivision rules. Equal supports of differently colored prototiles are permitted. Aperiodicity is a separate restriction, not part of primitivity. These references support the semantic interpretation; no cited mathematical result replaces a required Lean calculation.

## 2. Actual objects and all mathematical bridges

### Words, counting and primitivity

`Letter` is the actual finite type `Fin 3`. `substitution m` builds finite words with `List.replicate` and concatenation. `incidenceCounts σ i j` is literally `List.count i (σ j)`, and `incidenceMatrix` is its complexification. The proofs establish that these actual counts equal the displayed symmetric matrix

```
[[m+2, m,   m+1],
 [m,   m+3, m  ],
 [m+1, m,   m+2]].
```

The matrix is not disconnected from the words or assigned an invariant by definition. Its entries, common word length `3*m+3`, and nonempty images are proved. The transposed convention gives the same matrix by a separate symmetry theorem.

`wordMap` is genuine concatenation by `List.flatMap`, and `iterateWord` uses actual `Function.iterate`. `PrimitiveSubstitution` requires one positive iterate in which every letter occurs in every single-letter image, with a common iterate for all letters. For every m≥1 the proof supplies iterate one using strict positivity of all actual counts. The usual positive-matrix-power certificate is proved separately at power one. There are no empty-word, empty-alphabet, or vacuous-domain witnesses.

### Genuine geometric substitution rule

`prototileSupport` is the real closed interval `[0,1]` for each distinct letter color. `expandedPrototileSupport q` is the actual image under `x ↦ q*x`. The tile indexed by i in the actual substituted word has support `[i,i+1]` and color `w.get i`. `wordTileColors_eq` reconstructs the original word exactly; the subsequent counting theorem connects its geometric colors back to the incidence entries.

The implementation uses actual topological interiors, proves they are the corresponding open intervals, and proves pairwise disjointness. Coverage of `[0,L]` handles both the floor-index case `x<L` and the right endpoint `x=L`; the empty-length case is excluded where needed. Each support is proved to be a translate of the prototile with its actual word color. `UnitIntervalSubstitution` requires these assertions and expansion `q>1`; the family supplies q=3m+3. The indexed intervals are genuine translated compact interval tiles, not merely a prescribed count table.

This certifies the finite geometric tile-substitution rule. It does not formalize an infinite fixed tiling, hull, invariant measure, pattern-frequency theorem, aperiodicity, or finite-local-complexity theorem. The report and documentation explicitly state this scope. Those constructions are unnecessary for the independent matrix-ratio minimum clause, whose quantifier is over primitive substitutions. No claim of their kernel verification is made.

### Complete complex spectrum, multiplicity, order and rank

The matrix is the same complexified word-count matrix throughout. `incidence_charpoly` computes Mathlib's actual determinant-defined characteristic polynomial. `incidence_resolvent_det` independently computes `det(zI−M)` for every complex z. `incidence_mem_spectrum_iff` uses Mathlib's actual algebra spectrum and the equivalence between matrix invertibility and nonzero determinant. I also inspected the relevant pinned Mathlib definitions and lemmas; this is the standard finite-dimensional complex spectrum, not an assigned eigenvalue list or a dynamical-action spectrum.

The resulting complete characteristic factorization is `(X−(3m+3))(X−3)(X−1)`, and the complete spectrum is exactly those three values. For m≥1, q=3m+3>3>1>0. The factorization together with strict inequalities establishes simple roots and removes multiplicity or tie ambiguity. `perron_isGreatest` identifies the greatest actual spectral modulus q. `second_isGreatest` identifies 3 as the greatest modulus after removing q. Removal of a set element is valid here because the Perron root is simple. There are no omitted complex roots.

The actual all-ones vector is shown to satisfy the eigenvector equation, and its real coordinates are strictly positive. The determinant is `3*q ≠ 0`; `incidence_rank` consequently proves Mathlib matrix rank three. The name `perronValue` alone would not establish its role, but the complete spectrum, strict domination, and positive eigenvector prove that role here.

### Actual admissible ratios and the universal conclusion

`OrderedSpectralData` requires strict positivity/order, the full characteristic polynomial, and the two greatest-modulus assertions about the actual spectrum. `AdmissibleRatio` existentially quantifies a genuine substitution and geometric/spectral data, requiring word primitivity, nonempty images, the geometric rule, rank three and the ordered spectral certificate. It is a mathematically legitimate subclass of the source class. Its ratio `s/p` is the source ratio `|λ₂|/λ₁` because s and p are proved positive and are the relevant ordered moduli. The proofs supply every hypothesis for every family member with m≥1.

`spectralRatio_eq` proves the exact identity `3/(3m+3)=1/(m+1)`. The decisive witness m=2 therefore has actual words `aaaabbccc`, `aabbbbbcc`, `aaabbcccc`, incidence matrix `[[4,2,3],[2,5,2],[3,2,4]]`, complete spectrum 9,3,1, and ratio 1/3. The strict comparison with `(3−sqrt 5)/2` follows from the actual square-root identity and nonnegativity; no numerical approximation is used.

The final contradiction applies a universal lower bound to this fully certified, positive admissible ratio. It is not merely the isolated false inequality `c≤1/3`. The stronger theorem quantifies over every real ε>0 and uses the Archimedean property to choose a natural m≥1 with `0<ratio_m<ε`. Its subsequent conclusions rule out every positive universal lower bound and every least positive admissible ratio. Since the witnessed subclass already has arbitrarily small positive ratios, the broader source class cannot have a positive lower bound or least positive value either.

## 3. Report and PDF correspondence

I read all of `main.tex`, `README.md` and `VERIFICATION.md`, and viewed each of the four complete final page images after checking their hashes against `verification/pdf.json`. The mathematical displays, literal words, incidence matrix, spectrum, strict inequality, quantified lower-bound statement, stronger proposition, theorem correspondence, commands and references agree with the Lean source. No clipped text, overlap, missing mathematical glyph, or illegible page transition was found. The fourth page contains the stated scope and reproduction instructions rather than additional unverified mathematical claims.

The record reports successful native LaTeX compilation and a successful Tectonic 0.17.0 export with no warning/box diagnostics. I inspected the export log and final artifact identities. The PDF is four pages and 67,894 bytes. I did not compile or export it myself. The source's quoted English conjecture agrees with the bundled exact bilingual file. The documents consistently distinguish local scrutiny from maintainer acceptance.

## 4. Execution-record fidelity and trust checks

The separately performed execution used a fresh project-output directory, with only the five Lean files and three configuration files copied and cached dependencies shared. The build log actually lists all four implementation modules and successful default completion. All five recorded direct replays use `-DwarningAsError=true` and exit zero. `Check.lean` is replayed explicitly even though it is not a default library module.

I independently parsed `verification/axioms.txt`, rather than accepting only summary counts. It contains exactly the requested 21 definition/abbreviation printouts, all 43 theorem types, and all 43 corresponding transitive axiom lists, in exact inventory order. The embedded Check output in `strict-replay.json` is byte-identical to this file. Every list uses only `propext`, `Classical.choice`, and `Quot.sound`, or a subset. The source inventory has no additional named instances or private/anonymous proof declarations. The record's lexical scan has no raw or code proof-bypass hits; my full source read found no admitted proof, custom axiom or execution shortcut.

The recorded compiler is Lean 4.19.0 at commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all nine locked dependencies match their revisions and have clean tracked files both before and after execution. All eight copied/source identities remain unchanged. These are inspected execution records, not a claim that this semantic reviewer performed a second build. The record completed at `2026-10-04T22:15:28.295423+00:00`.

## 5. Rules, eligibility and limits

I read both complete contribution guides. Their current bytes agree with the final prepublication copies and the previously read copies. The English guide SHA-256 is `cd54d17f51e08212ee9557ef74568f6f2c388279ac74339dc4a3bab7c283f27e`; the Chinese guide SHA-256 is `ffedf1385079b9741fce4176c7aa1662720c29391116b34e5e78ba154b4fa244`. These guide hashes are supplementary and are not additional entries in the 20-input table below.

I inspected the initial eligibility and final prepublication records, including their source/rule identities, unsolved metadata, query scopes, topic classifications, historical-path results and reuse comparisons. The final snapshot is checked through `2026-10-04T22:17:50.191243+00:00`, at unchanged main `fe1d06d431b0591b65d759c60035b1d2e293a819`, with 587 all-state PRs through PR591. It reports no target submission, no current/history solution path and no blocker. All 13 previously classified broad topic leads remain unchanged, with 39 fresh response-array comparisons retaining two known unrelated comments. The closest substitution/Perron leads concern other conjectures. This review assesses those recorded findings and their consistency; it does not claim independently to have rerun every remote search or read every remote PR body. Eligibility remains timestamped and subject to later changes.

Only the personal solution package is intended for publication. The bundled conjecture is the exact official source. This review did not inspect a future staged Git diff or final all-files package manifest; those assembly checks remain the coordinator's responsibility. This document is an internal semantic review, not a repository maintainer review, merge decision, or claim of official acceptance.

## 6. Exact reviewed inputs

All 20 entries below were independently hashed before review and rechecked after writing this review. They match `/private/tmp/tlmc7718-review-inputs.json` exactly; no reviewed input was modified. Names are the manifest-relative package names. The review itself is a new artifact and is not one of its own inputs.

| Manifest-relative name | SHA-256 |
| --- | --- |
| `lean/Conjecture7718/Substitution.lean` | `6c49b67e44b22af1a6a8e428ad1278a551bba0719b3e68b80f18237ed0296cd8` |
| `lean/Conjecture7718/Tiling.lean` | `2aeb6d5894b35209701264619df9e80cda785161058e899475836a23c0dabf41` |
| `lean/Conjecture7718/Spectrum.lean` | `5a58456c04605acf19ad4af374f774efcff09721ec4a5a4b00b12a03c65603c6` |
| `lean/Conjecture7718.lean` | `8b810dc00bdf3f3740e18bceca899f5ddaad2b8a0a79108efa55430bb7558857` |
| `lean/Check.lean` | `417b68fee198b487e8936b98a2ef02137c858913805db2fbf9c49221de9bb38f` |
| `lean/lakefile.toml` | `fd8a99266a1ecc51a16d7fa79e683889d7a5e7e6df8109cfff1496d9cff1b3e0` |
| `lean/lake-manifest.json` | `781674693be1bf96bd27a7f4ecc0e44db0878908d554b6f504ba1b4b30be9b43` |
| `lean/lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `conjecture.md` | `946f0ae013e5ad15673ccf5adf3a35a83f1258d409f1ef88bd07a72f5b78e5e9` |
| `main.tex` | `a80a1ba11afd92dab6310de5b6a8d21405c3352fdcc05c8e6511454d87dd71aa` |
| `main.pdf` | `7d98006f2344e5e9ff3601e2fd9c7c49f9c4ab43a220214816075bbd227168c4` |
| `README.md` | `b5b9520efddf1ca22555742c17801bc3485dbb1a3353413d67d9d0d35ce9e9d7` |
| `VERIFICATION.md` | `483ef5ccad896190ca952951803f498abde4f8d9d12c06228263332d7639ee8c` |
| `verification/strict-replay.json` | `7a892775377a0e65467719b9918208f38c9fd98ae151655de57785392ebc754f` |
| `verification/build.txt` | `9379648ccd7494ceed47a4c80061c0854e1fac67d43ce8003a46ca645fe0cad8` |
| `verification/axioms.txt` | `a4ac934eb54526e33ca576a565c110ad5e92fd790cd7bc42ef36a6bc1a498d7f` |
| `verification/pdf.json` | `3795d454675d85b234bc974ff18ac79b02c229a0d22c94dd7c84df6e324a7a39` |
| `verification/report.txt` | `8ec3d96e1c23b16dfd1ab52c0a9adf44f631d5869fe96cf690bd6b97150b0882` |
| `verification/prepublication.json` | `29bb2b6c2675cca5428f03796cc9df95a536e007c0939bd2b0d1909eb5f0afd2` |
| `verification/eligibility.json` | `d70e8d72b7f6a3b67aae03330376ec68783f0062648fafee8535bd1402c85e56` |

Final conclusion: the reviewed Lean theorem and report faithfully disprove the explicit positive-minimum clause under the stated three-letter/matrix-size convention. The stronger family conclusions are also established. No unresolved mathematical or recorded-execution blocker was found within this review scope.
