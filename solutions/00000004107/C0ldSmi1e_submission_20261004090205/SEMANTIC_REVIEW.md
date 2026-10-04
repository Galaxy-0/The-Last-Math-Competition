# Internal semantic review: conjecture 00000004107

**Verdict: PASS. No mathematical correction to the reviewed proof or report is required.**

This is an internal independent source review dated 4 October 2026. It is not an official competition review, a maintainer acceptance decision, or a claim that this reviewer personally performed the separate compiler runs or rendered-PDF inspection. The reviewer read all five Lean sources, all three project configuration files, the complete bilingual conjecture, and the LaTeX report; inspected the relevant Mathlib definitions; and compared independently calculated file hashes with the completed independent-build records.

## 1. Source statement and precise scope

Both language versions assert universal strict sign alternation for the coefficients of the characteristic polynomial of a subspace arrangement. Neither restricts the members to hyperplanes or to subspaces of one common dimension. The source's further assertion about the dimension spectrum is a separate conjunct. The submission refutes the first clause and does not invent a definition of “dimension spectrum” or claim a separate formal result about that additional assertion.

The witness is a finite central arrangement of two distinct proper nonzero real subspaces, with neither contained in the other: a coordinate plane and the transverse coordinate axis in real three-dimensional space. It therefore remains an admissible arrangement under usual conventions excluding repetitions, redundant contained members, the zero subspace as an arrangement member, or the entire ambient space as an arrangement member. The origin and ambient space appear legitimately as intersections, not as members of the input arrangement.

The line is not a hyperplane of the three-dimensional ambient space. The report explicitly discloses this and does not claim to refute a theorem restricted to hyperplane arrangements. A restriction to hyperplanes or to equal-dimensional members would change the source's stated domain.

The standard definition was checked in A. Björner and T. Ekedahl, *Subspace Arrangements over Finite Fields: Cohomological and Enumerative Aspects*, §2 and §3, equation (3.1), PDF pp.3–5. Those sections introduce the intersection poset over a general field, order it by reverse inclusion, include the ambient space, and define the characteristic polynomial as the sum of Möbius values times powers indexed by the actual subspace dimensions. Real central linear arrangements are a special case of that definition. [Primary paper](https://arxiv.org/pdf/math/9612217).

## 2. Geometry is represented by actual subspaces

`V` is the real coordinate space `Fin 3 → ℝ`. `U` and `W` are genuine `Submodule ℝ V` values with proved closure properties and carriers respectively `x 2 = 0` and `x 0 = 0 ∧ x 1 = 0`. Their membership theorems expose exactly those conditions.

`planeEquiv` and `axisEquiv` are explicit real linear equivalences from the actual submodule types to `Fin 2 → ℝ` and `ℝ`. Their inverse maps insert the missing zero coordinates, and the code proves both inverse laws and linearity. Consequently the dimension computations use actual `Module.finrank`, giving dimensions two and one. The ambient and zero submodules have finranks three and zero. The spaces involved are finite-dimensional submodules of a finite-dimensional real coordinate space, so there is no misuse of the natural-valued finrank convention for infinite-dimensional spaces.

`U_inf_W` proves that an element of the intersection has all three coordinates zero. Its reversed form is also proved. The coordinate vectors `(1,0,0)` and `(0,0,1)` witness the two failures of containment. Nonzeroness and properness follow without assumptions about a prescribed dimension table. All four eventual intersection subspaces are genuinely distinct.

## 3. Complete intersection poset and its order

The generic `IntersectionPoset A` is directly the order dual of the subtype

`{S : Submodule ℝ (Fin n → ℝ) // ∃ s : Finset (Fin m), s.inf A = S}`.

This is the family of actual finite intersections of the actual indexed subspaces. It is not a four-element poset merely labeled with geometric names. Since the input family is finite, finite index sets represent all its subfamilies. In the submodule lattice, infimum is intersection and the empty infimum is the whole ambient space.

`intersectionPoint_surjective` follows from the subtype's existential membership condition. It establishes that every intersection has a finite-subfamily representative. Finiteness is then obtained through this real surjection from `Finset (Fin m)`, and the locally finite order is derived from the resulting finite type. Equal intersections are equal subtype elements regardless of how many subfamilies produce them; the sum does not overcount subfamily representations.

The order is inherited from the order dual of the actual submodule order. `intersection_le_iff` states precisely that `S ≤ T` means `T.val ≤ S.val`. Thus it reverses ordinary containment. `ambient` is the empty intersection; `ambient_val` identifies it with the top submodule, and `ambient_le` proves it is least in the reversed poset. No order relation or finiteness property is assumed from the desired answer.

For the concrete family `![U,W]`, the three named nonambient points are intersections of `{0}`, `{1}`, and `{0,1}`. Their underlying submodules are proved to be `U`, `W`, and bottom. `finTwo_subsets` proves that these three subsets and the empty subset exhaust all subfamilies. Combined with the generic surjection, `concretePoset_cases` and `concretePoset_univ` prove completeness of the four-point list. Equality is equality of the underlying submodules. The code uses the actual intersection subtype throughout, so no unproved order-isomorphism or transport from an unrelated finite model is required.

## 4. Genuine Möbius computation and characteristic polynomial

`characteristicPolynomial A` is defined for every finite indexed real arrangement by the finite sum

`∑ S : IntersectionPoset A, C (IncidenceAlgebra.mu ℤ (ambient A) S) * X ^ Module.finrank ℝ S.val`.

The coefficients lie in the integers, as do the standard poset Möbius values. Exponents are dimensions of the actual submodules. In particular, they are not ranks of the abstract diamond-shaped poset; confusing these would give a different polynomial. The implementation uses the correct geometric dimensions.

Mathlib's `IncidenceAlgebra.mu` was inspected in `Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean`. It is the actual incidence-algebra Möbius function defined recursively through order intervals. `mu_self` and `mu_eq_neg_sum_Ico_of_ne` implement the diagonal value one and the negative sum over the half-open interval. The submission invokes these lemmas rather than supplying a handcrafted coefficient function named “Möbius.”

The three interval theorems are proved on the actual reversed intersection poset:

- From ambient to plane, excluding the plane endpoint, the interval is the ambient singleton.
- From ambient to axis, excluding the axis endpoint, it is again that singleton.
- From ambient to origin, excluding the origin endpoint, it contains exactly ambient, plane, and axis.

These give Möbius values `1,-1,-1,1` at ambient, plane, axis, and origin. Together with finranks `3,2,1,0` and the proved complete enumeration, `characteristicPolynomial_arrangement` derives the identity `X^3 - X^2 - X + 1`. The proof unfolds the genuine invariant and evaluates its sum. The polynomial is not merely postulated or substituted for an unformalized arrangement invariant.

No separate topological construction of the complement is needed for this computation: the standard characteristic polynomial at issue is defined by the intersection poset, exactly as in the cited definition. The proof makes no cohomological or topological identification requiring an additional unformalized bridge.

## 5. Sign obstruction and all quantifiers

`StrictSignAlternation p` requires the product of every adjacent pair of coefficients, from degree zero through the leading degree, to be strictly negative. `WeakSignAlternation p` weakens this to nonpositivity. The latter is explicitly a necessary adjacent-sign condition; with zeros present it need not characterize every alternative convention for reading only nonzero coefficients. That distinction cannot affect this witness.

The root module proves that coefficients at degrees zero through three are respectively `1,-1,-1,1`. The polynomial identity excludes any higher nonzero coefficients. Thus all coefficients between the constant and leading terms are nonzero. In particular the adjacent degree-one and degree-two coefficients are negative, with positive product. Reading the coefficient sequence backwards, deleting zero coefficients, allowing zero coefficients in a weak convention, or fixing the leading sign cannot eliminate this pair.

The general negative-pair lemma proves that the tested index really lies below `p.natDegree`: the second negative coefficient is nonzero, so its index is at most the degree. It does not derive a contradiction from an out-of-range coefficient or a vacuous degree bound. The strict-to-weak implication and the positive product of two negative integers then give both concrete failure theorems.

`ConjectureClaim` quantifies over all natural ambient dimensions `n`, all finite family sizes `m`, and all functions `A : Fin m → Submodule ℝ (Fin n → ℝ)`. This is a representation of finite real subspace arrangements; repeated members cause no multiplicity in the intersection subtype. The final `conjecture4107_disproof` specializes to `n=3`, `m=2`, and the actual plane-axis family. The witness has positive dimension, a nonempty family, and distinct proper nonzero incomparable members, so the argument does not exploit empty families, zero ambient dimension, repetitions, or redundancy even if one imposes those usual admissibility conventions.

The final theorem has no unproved geometric, order, dimension, polynomial, or sign hypotheses. It negates the universal first clause. A counterexample over the reals is sufficient whether the source is read as referring to real arrangements or more broadly to arrangements over general fields. No claim about all fields or about the unspecified second conjunct is needed.

## 6. Report correspondence and verification evidence

The report's subspaces, four-point intersection list, ordering, dimensions, Möbius values, polynomial, and sign obstruction all agree with the reviewed code. Its statement of scope correctly distinguishes subspace arrangements from hyperplane arrangements. Its reference supports the definition actually implemented; the cited paper's deeper cohomological results are not premises of this proof.

All 47 theorem declarations in the proof modules are represented by theorem-type and transitive-axiom checks in `Check.lean`. The 17 printed definitions/abbreviations include the actual subspaces, linear equivalences, generic poset, characteristic polynomial, concrete family and points, sign predicates, and final claim. The submitted source has no `sorry`, `admit`, user-declared axiom, `native_decide`, custom elaborator, unchecked external computation, or artificial success predicate. The ordinary `decide` used to enumerate four finite index subsets is kernel-checked and is not `native_decide`.

The completed independent records in `strict-replay.json`, `build.txt`, and `axioms.txt` were inspected. They report a fresh project build in `/private/tmp/tlmc4107-independent` and successful strict replay of all five Lean sources with warnings treated as errors. The printed definition bodies and theorem types agree with the source reviewed here. All 47 axiom lists contain only members of `{propext, Classical.choice, Quot.sound}`. The record reports 17 printed definitions, no proof-bypass scan hits, matching dependency revisions, and clean dependency tracked files before and after the build. All eight proof/configuration hashes in both the source and independent-copy records match hashes independently computed during this review.

The project pins Lean 4.19.0, Lean commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; the manifest also pins the transitive dependencies. This review inspected the separate build evidence rather than rerunning compilation. PDF rendering, final package manifest verification, and official acceptance remain distinct from this source-level semantic verdict.

## 7. Exact reviewed file identities

Proof and configuration files were read from `/private/tmp/tlmc4107-proof`. The report was read from `/private/tmp/tlmc4107-package/main.tex`. The bilingual source was read from `/Users/daniel/The-Last-Math-Competition/conjectures/00000004107.md`; its bytes match `/private/tmp/tlmc4107-verification/conjecture.md`. The review applies to the following exact SHA-256 identities.

| Reviewed file | SHA-256 |
| --- | --- |
| `Conjecture4107/Geometry.lean` | `e24affd7c39b65c63c9564d7aa31996f85626f4ec5749b043874dcde74fa3e16` |
| `Conjecture4107/Arrangement.lean` | `3e7a892ace8c79db9a6b0bf7369d76f3ab97370caea350643e1d0c782dadbaec` |
| `Conjecture4107/Signs.lean` | `bc604112985479165a002e83f1f6c6a9b3e39c0b87689b105cbe99dd21ec42c6` |
| `Conjecture4107.lean` | `d4bb44bbe7bddd25383497c17f75864a486484cbd2cfc6c94e8d2371e8f8df22` |
| `Check.lean` | `26dfab52d5223e4cfceed2b093ef06b9ecb44474b5faeb0a74465151ab719a8c` |
| `lakefile.toml` | `eec7aa3e6b93100bfb5693efb77543b93065e7255701275b5ceb6b39a3e58e20` |
| `lake-manifest.json` | `217c00b63467adfbfe9d8f3a223f74f0144a783c9360179bb5c9993cfb6b9959` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `main.tex` | `474654ce6a83d8414a41548c1c97128a7f0f8d61564215aa69c0dd43f54fcee4` |
| `conjectures/00000004107.md` | `9e96fc1047404a87bf9591799cbf44a24e6026d94c5f38a3e41249e9cab25465` |

Separate verification records inspected:

| Evidence file | SHA-256 |
| --- | --- |
| `strict-replay.json` | `5935150d10724321d01f090e59100d31cfb63838fd5d0dfe9cc3be56168291b4` |
| `build.txt` | `83684e1a83ea0bd5afface99eda6c14fa9ec9070703f784b319179e35d5237db` |
| `axioms.txt` | `2e8ace582cd7d4d56fdd8561fe32e4eb2b3fc4c8c5c69ced8ecd1e82492d5ed7` |

**Outstanding semantic corrections: none.** This PASS records internal mathematical and source correspondence for the exact files above; it does not establish maintainer acceptance.
