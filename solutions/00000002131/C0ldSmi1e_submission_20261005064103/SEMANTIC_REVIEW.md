# Independent semantic review — conjecture 00000002131

**Verdict: PASS.** The frozen Lean project proves a counterexample to the displayed universal Stanley–Wilf direct-sum multiplicativity assertion in both language versions of the source. The report correctly describes that result. No correction to the submitted mathematics is requested. This is an independent internal review, not maintainer acceptance or a publication-eligibility certification.

## Scope, identity, and reading

Reviewer: the separate nonauthor `review_2131` agent. The review concerns only conjecture 00000002131 and the exact frozen package identified below. I did not modify its inputs or any repository files, open a PR, or post externally.

| Item | SHA-256 |
|---|---|
| Frozen 36-file manifest `/private/tmp/tlmc2131-review-inputs.json` | `bee4f579c5c53c0bcc2fb2240a3401b6717f0146f1468eb02a783925e1d79b26` |
| Exact bilingual `conjecture.md` | `221a85de07555772cc81c7f5c563456208ef1247b8bd1d56aa1774cb22e68230` |
| Mathematical source `Conjecture2131.lean` | `07b8245887ade2b63041ed870b7242d437f2d68ea23c32f439b74d857a2d149e` |
| `main.tex` | `7927711ef5711bda4c270d564dfa781747f89e09717e44ca09532eae79190123` |
| Submitted `main.pdf` | `540add081b1541a381beed1b38673fe5620c26c09a414cadfe67680564f1b798` |
| English contribution guide | `84cd9992c3b4027d90044109df969e22390051df4a5f7f21ca81138e5f717795` |
| Chinese contribution guide | `167c69fba1d5592feb55117da9a0151b0355ff6b2a0fb773115f367e58c59b47` |

I read all 36 frozen inputs in full: both complete guides, the exact bilingual statement, all mathematical/configuration/inspection sources, the full LaTeX and both PDF pages, author notes, the semantic preassessment, eligibility record, all logs and all JSON records. For JSON fields duplicating full transcripts or inventories, I parsed the entire file, verified exact equality with the separately read transcript/inventory, and read all remaining fields. The PDF was independently extracted, rendered, visually inspected, and compared with a fresh export; the two supplied page images were also visually inspected. `review-evidence/all-input-reading.json` records each input and reading method.

Every file and the manifest matched its supplied hash before review and again after all review operations. `review-evidence/hashes-before.json` and `hashes-after.json` are identical. The five source/configuration copies in the fresh project also remained byte-identical.

No prior solution or PR mathematical content was opened. Scope disclosure: a team-agent inventory call, made while checking whether an additional independent reviewer could be delegated, incidentally returned completed summaries for unrelated tasks. I did not open their files, pursue their mathematics, or use those results in this review. A second-reviewer spawn was unavailable because the team limit had been reached. The conclusions below come from the 2131 source, the frozen candidate, and my own reproduction and scrutiny.

## Statement and permitted domain

The English and Chinese statements both explicitly assert

\[
L(\pi_1\oplus\pi_2)=L(\pi_1)L(\pi_2).
\]

Neither language imposes a length-at-least-two restriction, excludes the one-element pattern, or restricts either pattern by shape or avoidance class. Under the ordinary finite nonempty permutation-pattern domain, length one is permitted. The candidate uses two actual one-element permutations, not an empty pattern or a repeated-value word. The report makes this convention prominent and expressly limits its conclusion to the source as stated. An amended conjecture excluding one-element inputs would require another argument; this review does not certify such an amendment.

The further “complete characterization” clause gives no characterized property or separate equivalence. The report does not assign it an invented predicate. Since the source explicitly asserts the displayed equality, refuting that necessary assertion refutes its conjunction with any further clause retaining it. The final `not_source_conjunction (Extension : Prop)` expresses exactly that elementary implication. It does not purport to disprove the unspecified extension independently. This is a sufficient negative settlement of the written source, not a claim of a positive classification theorem.

## Mathematical and formal correspondence

I checked definitions and actual compiled theorem types, not merely declaration names or author descriptions.

1. **Objects and containment.** `Permutation n` is `Equiv.Perm (Fin n)`, so every object is a bijection of the full finite ordered index set. `Contains p s` selects an arbitrary strictly increasing map of positions and preserves every strict comparison of values in both directions. There is no adjacency condition. `Avoids` is precisely negation of this classical containment predicate. `avoidanceCount p n` is the cardinality of the entire avoiding subtype. No weighting, normalization, restricted family, or unproved alternative count is substituted.

2. **Direct sum.** `directSum` transports the genuine blockwise equivalence through `finSumFinEquiv`. Its left/right equations give values `p(i)` and `k + q(j)` in the two blocks. The value equations and position/value separation lemmas confirm the ordinary direct sum rather than skew sum or an operation on avoidance classes. `increasing_sum_increasing` proves the identity needed at the witness: `1 ⊕ 1 = 12`.

3. **Length-one count.** `contains_one` selects position zero in every size `n+1` permutation. Strict monotonicity and the comparison equivalence on `Fin 1` are vacuous for distinct indices; the proof handles equality correctly. `avoidanceCount_one` shows the entire avoiding subtype is empty, hence its cardinality is zero for every positive size. This is a symbolic statement over all sizes, not an observed finite table.

4. **Length-two count and uniqueness.** `contains_two_iff` proves both directions of the increasing-pair test. In its reverse direction the map explicitly selects the two ordered positions. `avoids_two_iff_strictAnti` uses injectivity to rule out equal values; therefore absence of an increasing pair is strict decrease. `decreasing` is the actual reverse permutation. Its strict antitonicity is proved. `avoids_two_iff_decreasing` then uses equality of ranges of strictly antitone maps, together with both permutations' surjectivity, to establish uniqueness. `avoidanceCount_two` proves the full subtype has cardinality exactly one for every natural size, including zero. This supplies all sizes required by the limit.

5. **Roots and convergence.** In `rootCount`, the count is coerced to `Real` and the reciprocal exponent is real division. `rootSequence` uses `n+1`, avoiding the artificial zero index. `rootSequence_at_positive_index` accounts for every positive source index; `sw_iff_unshifted` proves the usual eventual shift equivalence. The auxiliary totalized value at index zero is one and is explicitly isolated. `SW p x` is actual `Filter.Tendsto` to the real neighborhood filter, with neither a limsup replacement nor a freely assigned growth constant. The zero-root proof verifies the exponent is nonzero, using positivity, before applying `Real.zero_rpow`.

6. **Actual limits and contradiction.** The two positive-index root sequences are identically zero and one, respectively. Their genuine convergence is proved by constant-sequence convergence. `sw_one_directSum_one` supplies the third limit, and `nonmultiplicative_witness` packages the actual values 0, 0, 1 and their inequality. `sw_unique` uses uniqueness of real limits. Thus the disproof does not exploit a nonexistent limit or an arbitrary totalized value.

7. **Exact universal negation.** `UniversalMultiplicativity` quantifies over every positive pair of lengths and every pair of actual permutations, and requires actual limits `x,y,z` satisfying `z=x*y`. The proof of `not_universalMultiplicativity` specializes to the permitted length-one pair, identifies any asserted limits with 0, 0, 1 by uniqueness, and contradicts `1=0*0`. There are no hypotheses on the final negation and no assumed global limit assignment.

8. **Function notation.** `NumericalMultiplicativity L` has the source's literal equality form. `universal_iff_numerical_of_verified_limits` proves equivalence with the relational assertion only when `L` is verified to give genuine limits on every permitted nonempty pattern. Both directions are proved. The main counterexample does not assume the existence of that global function or use this hypothesis to manufacture values. General Stanley–Wilf existence for unrelated patterns is unnecessary to refute this particular universal equality.

The complete report agrees with these definitions, counts, limits, domain qualifications, and final theorem. Its combinatorial uniqueness explanation is valid by finite bijectivity. Its statements about proof scope and the qualitative extension are accurate. No mathematical numerical computation, enumeration, approximation, asymptotic estimate, or outside computational result is needed by this proof.

## Own fresh reproduction

I created `/private/tmp/tlmc2131-semantic/fresh-proof` from only these frozen inputs: `Conjecture2131.lean`, `Check.lean`, `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`. The directory had no candidate build outputs. Its `.lake/packages` is a link to the approved shared package directory `/private/tmp/tlmc310-proof/.lake/packages`; no candidate `.olean`, `.ilean`, native object, cache, or compiled library was copied.

I inspected the full supplied verifier, adapted only its fresh destination/evidence-output paths in `review-evidence/replay-verifier.py`, and ran it. I independently checked its results and added a separate inspection harness and transitive dependency traversal. The fresh default `lake build` succeeded. Direct source and `Check.lean` replays both succeeded with `-DwarningAsError=true`. The author's exact `AuthorAudit.lean` was independently replayed against this fresh project; it succeeded and its entire output was byte-identical to the frozen author audit log.

The compiler was Lean 4.19.0, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, before and after. All nine actual dependency revisions matched the frozen manifest, and all tracked sources were clean before, after the build, and after the extended audits:

| Package | Actual pinned revision |
|---|---|
| mathlib | `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| plausible | `77e08eddc486491d7b9e470926b3dbe50319451a` |
| LeanSearchClient | `25078369972d295301f5a1e53c3e5850cf6d9d4c` |
| importGraph | `e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b` |
| proofwidgets | `c4919189477c3221e6a204008998b0d724f49904` |
| aesop | `5d50b08dedd7d69b3d9b3176e0d58a23af228884` |
| Qq | `fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02` |
| batteries | `f5d04a9c4973d401c8c92500711518f7c656f034` |
| Cli | `02dbd02bc00ec4916e99b04b2245b30200e200d0` |

The full execution records are under `review-evidence/replayed-verifier/`; the final environment observation is `review-evidence/final-environment.json`. This is a fresh build of the submitted project using approved shared dependencies, not a claim to have rebuilt every dependency from source.

## Exhaustive compiled and trust audit

Source inspection finds exactly 40 authored declarations: 12 definitions/abbreviations and 28 theorems, with no anonymous or private authored declarations. `Check.lean` prints all 12 definitions and all 28 theorem types and axiom lists. The author audit additionally prints the axiom dependencies of every authored declaration.

My separate `ReviewerAudit.lean` enumerates **every constant by actual originating module**, not by name prefix. It independently found exactly **55 constants**, including all 40 authored declarations and all 15 generated declarations. Their names, full types, kinds, safety flags, and `collectAxioms` results exactly match the frozen exhaustive inventory. No declaration was silently excluded. Full types, proof/definition bodies, direct dependencies, and transitive safety traversal results are preserved in `reviewer-audit.log` and `reviewer-audit.json`.

The 15 generated declarations consist of five reflexive equation theorems, three extracted arithmetic proof theorems from `omega`, and seven compiler runtime definitions:

- `decreasing._cstage1`, `decreasing._cstage2`;
- `directSum._cstage1`, `directSum._cstage2`;
- `increasing._cstage1`, `increasing._cstage2`;
- `increasing._closed_1._cstage2`.

All seven names here are under `Conjecture2131`. Their compiler-unsafe flags were retained and reported. Their classification was checked against the complete authored source, fresh generation by the pinned compiler, actual types, and bodies. The stage-one bodies implement the corresponding ordinary definitions. The stage-two bodies have erased `_obj` types and runtime placeholders such as `_neutral` and `_rarg`; these placeholders are not kernel logical constants. The five equation theorem bodies are reflexivity; the three extracted arithmetic theorems are ordinary checked arithmetic proof terms.

All 55 `collectAxioms` results contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`. That observation alone is not treated as a proof of runtime safety: the axiom collector skips absent runtime placeholders. I therefore separately traversed **types and logical values through the checked environment**, including theorem bodies, for every authored declaration. Every one of the 40 authored closures has **zero unsafe constants, zero partial constants, and zero missing constants**. In particular, none depends directly or transitively on any of the seven unsafe runtime definitions or their placeholders. The unsafe runtime records remain in the inventory; they are not mathematical premises or proof shortcuts.

There are no authored axioms, admitted proofs, `native_decide`, unsafe/partial declarations, custom elaborators, injected theorem constructors, or kernel-checking bypasses. The supplied lexical scan has no hits; this agrees with full manual source inspection and the complete axiom/safety audits. The inspection harness itself uses metaprogramming only to read and print already compiled declarations and prove no submitted theorem. Its initial printing-branch type error was corrected in the inspection copy, and the successful complete replay is saved; the candidate was never changed.

## PDF reproduction and visual review

I read all of `main.tex`, extracted the complete original PDF text independently, and visually inspected both complete final pages. The displayed statement, lemma, proof, root formula, contradiction, and reproduction instructions are readable and agree with the source. There is no clipping, overlap, missing symbol, blank or orphaned page, or unreadable mathematical expression.

I inspected and replayed the supplied exporter using the existing Tectonic binary, changing only output locations and removing the copied claim that my export had invoked the native compiler. The exact LaTeX was exported into `review-evidence/pdf-reexport/`. The export succeeded with no warning or box diagnostic. I independently rendered the original PDF and the new export with Poppler. Both have exactly two pages. Full extracted text is identical, and every pixel on both 1237×1600 rendered pages is identical to the corresponding original render and supplied image.

The independent PDF SHA-256 is `ffd12da5105fe7d65458f776b1b96dc92d6f634e153579d116525014ccc64fec`; it is **not byte-identical** to the submitted PDF. I investigated the discrepancy, rather than rejecting or ignoring it. A raw metadata-stripping comparison initially remained unequal because the timestamp is in a compressed object stream. A decoded comparison of all 117 PDF objects establishes that only the creation timestamp and document ID differ; the timestamp also changes its containing compressed stream. All other object dictionaries, page-content streams, fonts, resources, and decoded streams are identical. Evidence is in `pdf-evidence/comparison.json` and `canonical-object-comparison.json`. No material source/render mismatch exists. I did not independently repeat the app's native compilation; its supplied success record is distinguished from my actual Tectonic reproduction.

## Auxiliary coverage, limitations, and conclusion

All supplied auxiliary inspection/export sources were inspected and executed against fresh or scratch copies: the Python verifier, its generated Lean environment inventory, the separate author audit, and the PDF exporter. My additional safety and PDF-object inspectors also ran successfully. Their absolute scratch paths are execution evidence, not mathematical prerequisites. The full source and reproduction logs are retained in `review-evidence/`. There is no required numerical computation left untested.

The supplied initial eligibility record was read, but this review does not independently refresh remote eligibility, inspect prior PR mathematics, or authorize publication. The coordinator must retain its separate current-eligibility/publication process. Similarly, the report's reference to a separate semantic review is satisfied by this completed review only when this report is packaged with the frozen material.

**PASS for the exact frozen package and the source as written.** The actual permitted witness has limits 0, 0, and 1; the verified direct sum is the two-element increasing permutation; the formal theorem negates the corresponding universal equality without extra hypotheses. The qualitative extension is handled only by valid conjunction logic. No unresolved mathematical, formal, auxiliary-computation, report-correspondence, or PDF-rendering concern remains within this review's scope.
