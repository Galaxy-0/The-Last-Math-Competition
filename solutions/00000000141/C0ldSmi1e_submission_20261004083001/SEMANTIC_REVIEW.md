# Independent semantic review: conjecture 00000000141

**Verdict: PASS — no mathematical or semantic blocker found in the frozen Lean sources and final report.**

This is an internal independent source review, not an official maintainer review or acceptance. This reviewer read the proof and relevant Mathlib definitions independently, but did not rerun the compiler or inspect the rendered PDF. The separate fresh-build and strict-replay records were inspected and their source hashes compared with the audited files. Final PDF and publication checks belong to the parent workflow.

## Materials and identities

Read in full:

- Both languages of `conjectures/00000000141.md`.
- `/private/tmp/tlmc141-proof/Conjecture141/Counting.lean`.
- `/private/tmp/tlmc141-proof/Conjecture141/Growth.lean`.
- `/private/tmp/tlmc141-proof/Conjecture141.lean`.
- `/private/tmp/tlmc141-proof/Check.lean`.
- The project's `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`.
- `/private/tmp/tlmc141-package/main.tex`.

All corresponding source/configuration/report files were compared byte for byte with the submission at:

`/Users/daniel/.codex/worktrees/conjecture-420/The-Last-Math-Competition/solutions/00000000141/C0ldSmi1e_submission_20261004083001`

Every compared file matched, including the bilingual `conjecture.md` copy. SHA-256 hashes follow; Lean/configuration paths are relative to the submission's `lean/` directory.

| File | SHA-256 |
|---|---|
| `Conjecture141/Counting.lean` | `583f8da02bb698efdcb1b533ff83df07c09d9af021f4ce720902daba8eae5439` |
| `Conjecture141/Growth.lean` | `68aa1fd7cf49134dd36da6472d216f19fdd765edae9e5442c6bd6d90b73d5f44` |
| `Conjecture141.lean` | `aefe20572266f672797224fc129b98eb08ee1a1df6a363a28d4ec732cf7b4108` |
| `Check.lean` | `61ce488e56878264a6d859e0f29498327f9d9697a965558513c30db79e6f2520` |
| `lakefile.toml` | `1137be0fd1fc7fcb670550f464e8567764f9249b3c51e3dc0cc986a7fc25a43e` |
| `lake-manifest.json` | `d5b2e1b59533b0c4158a639152ea019dda603bae69ccc2784fc638ead54797f6` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| Submission `main.tex` | `696a333851427d2fa12f9a09c4b56a7b95da980fecf0f8a9e8f6bb6ffc75fc4a` |
| Submission `conjecture.md` | `fa4a7a53fb5a1bd9f705405fd1ccb6f6291e77203b1819e0bcc224c694c0e03d` |

The final report differs from the initially read report, hash `e9e4b270dc5ffc33a5fff0945cb90dc48509782f348d554d965db21a419517dc`, only in two reviewed edits: it now asserts positivity of the classical displayed expression for integers k ≥ 2, instead of all positive integers, and shortens the heading “Exact expression and asymptotic relation.” to “Exact asymptotic relation.” Reversing exactly those replacements restores the initial hash. An intermediate line-breaking `\allowbreak{}` was subsequently removed; reversing all three latest replacements restores the intermediate hash `6682b58d7401c661695c45e0c65c378e3edb66fc5afdbf04c8df26dc62cc9272`.

The positivity wording correction is valid and preferable: the classical formula has log(1) in a denominator, whereas the formal function is totalized by Lean. Only eventual positivity is needed, and the proof already operates at sufficiently large indices. No Lean source or mathematical conclusion changed.

## 1. Correct object and fixed-point convention

Both language versions explicitly count permutations of n elements with all cycle lengths prime. The count is over labeled permutations themselves, not their conjugacy classes, prime partitions, or a quantity divided by n!. The later generating-function phrase does not change the object explicitly identified as N(n).

`PrimeCycles σ` requires every part of the actual Mathlib permutation partition `σ.partition.parts` to be prime. The Mathlib definition was inspected: this multiset is `σ.cycleType` plus one copy of 1 for every fixed point. Thus fixed points are correctly excluded by the prime condition. The implementation does not make the common mistake of checking only `cycleType`, which omits singleton cycles.

`N n` is the actual finite cardinality of the full subtype of permutations on `Fin n` satisfying `PrimeCycles`. There is no surrogate counting sequence, normalization, conjugacy quotient, or restriction to involutions in its definition. The empty permutation at n = 0 presents no issue for the eventual argument.

## 2. Explicit injection and relabeling

`crossMatching σ` is an actual equivalence on the sum of two copies of the label type. It sends `inl i` to `inr (σ i)` and `inr j` to `inl (σ.symm j)`. Its inverse is the same map, and both inverse laws are proved. Its application formulas, involution property, absence of fixed points, and injectivity in σ are proved for arbitrary label types.

The injectivity proof is faithful: applying equal cross-matchings to `inl i` recovers equal values σ i and τ i for every i. It does not rely on counting a larger or differently labeled object.

`doubleFinEquiv n` is the actual equivalence from `Fin n ⊕ Fin n` to `Fin (2*n)`, using `finSumFinEquiv` and a proved equality of the finite cardinal indices. `matchingPermutation` conjugates the cross-matching through this equivalence. Mathlib's `permCongr` definition and application formula were inspected; they perform exactly this relabeling. Absence of fixed points, the square-equals-identity property, and injectivity are all established after the transport.

For an arbitrary fixed-point-free involution, the proof first establishes full support. Rewriting the actual partition with full support removes precisely the fixed-point 1-parts. Every remaining cycle length k divides the order of the permutation, which divides two; Mathlib's cycle-type theorem also gives k ≥ 2. Therefore k = 2 and is prime. No assertion that order equals two is needed for an empty label type.

`matchingEmbedding n` is an actual injection into the subtype defining N(2*n), with the prime-cycle proof carried in its codomain. `Fintype.card_le_of_injective`, together with Mathlib's `Fintype.card_perm`, yields the unconditional theorem `n.factorial ≤ N (2*n)` for every natural n. The usual exact count of all fixed-point-free involutions is neither assumed nor needed.

## 3. Displayed expression and exact constant

`proposedCount c n` is exactly

`c * (n : ℝ)^(-1/2) * exp(2 * sqrt((n : ℝ) / log(n : ℝ)))`,

with real powers and the natural logarithm. Parentheses and casts agree with the source formula. The source constant is exactly `(4*pi)^(-1/2) * exp(-1/2)` and is proved strictly positive. There is no floating approximation or silently changed exponent.

`proposedCount_pos` establishes positivity at all positive natural n for positive c. The classical displayed expression is only needed at sufficiently large n, where log n ≥ 1; the proof does not derive its contradiction from Lean's totalized logarithm or division at n = 0 or 1. The eventual nonvanishing needed for asymptotic equivalence is separately proved.

## 4. Infinite factorial growth and simultaneous eventual bounds

`proposedCount_le_exp` proves the actual inequality `proposedCount c n ≤ c*exp(n)` from c ≥ 0, n ≥ 4, and log n ≥ 1. The proof bounds n/log n by n, its square root by sqrt n, and 2 sqrt n by n, and bounds the negative real power by one. All multiplication and exponential monotonicity steps have the required sign hypotheses.

`factorial_eventually_gt_geometric` proves, for every fixed pair of real numbers a and c, the eventual strict inequality `c*a^n < n!`. It uses Mathlib's proved `Real.summable_pow_div_factorial`, whose statement and proof were inspected. The terms of the summable real exponential series tend to zero. Multiplication by c preserves this limit, so the terms are eventually below one; positivity of n! then justifies clearing the denominator. This is a proof at infinity, not finite numerical evidence or an assumed Stirling estimate.

The main growth theorem temporarily accepts an arbitrary natural-valued count with the factorial lower bound. That hypothesis is then discharged for the actual N in the root module; no unproved growth hypothesis survives into the final theorem.

Under a purported ratio limit of one, the proof establishes that the even-index map n ↦ 2*n tends to infinity. Casting to ℝ preserves this, and the logarithm also tends to infinity. It obtains all four eventual conditions on the same natural parameter:

1. 2*n ≥ 4;
2. log(2*n) ≥ 1;
3. count(2*n)/proposedCount(c,2*n) < 2;
4. `2*c*(exp 2)^n < n!`.

Their intersection is an eventual set in the nontrivial atTop filter, so it contains a common sufficiently large n. The positive denominator justifies the ratio inequality. The proved bound on the model and the identity `exp(2*n) = (exp 2)^n` give

`n! ≤ count(2*n) < 2*proposedCount(c,2*n) ≤ 2*c*(exp 2)^n < n!`.

This is the claimed contradiction. The proof controls arbitrarily large indices and correctly handles the even subsequence; it is not an isolated finite counterexample to an asymptotic assertion.

## 5. Actual asymptotic-equivalence bridge and conclusion

`ConjectureClaim` uses Mathlib's genuine `Asymptotics.IsEquivalent` relation at `Filter.atTop`, with the actual real-cast N and exact source constant. Mathlib defines this relation by the difference being little-o of the comparison function.

The inspected `isEquivalent_iff_tendsto_one` theorem equates this relation to the quotient tending to one under eventual nonvanishing of the denominator. The root proof provides precisely that nonvanishing from positivity for n ≥ 1. It then invokes the independently established failure of the quotient limit.

`count_not_asymptotic` rules out every positive c, and `conjecture141_disproof` explicitly specializes it to the positive printed constant. The final theorem has no additional assumptions and directly negates the primary assertion of the source. Once that assertion fails, no formalization of the later capacity-integral phrase is required to disprove the conjunction.

## 6. Report correspondence

The report follows the same proof: the labeled cross-matching injection, full-cycle convention, factorial lower bound, coarse exponential upper bound, eventual factorial domination from the exponential series, cofinal even subsequence, and actual asymptotic-equivalence bridge. The stronger quantification over all positive constants is accurately stated.

Its elementary ratio-test explanation of the factorial lemma is mathematically sound, including negative a and C and the zero case. Mathlib's imported summability result supplies this infinite analytic ingredient in the formal proof. The report does not substitute a finite calculation for it.

The report correctly identifies `partition.parts` as including fixed points and describes the actual subtype cardinality, rather than only naming a numerically convenient sequence. It does not claim the exact full asymptotic of N, the exact total matching count, or a separate disproof of the capacity-integral statement. No numerical auxiliary program is needed.

## 7. Configuration, verification evidence, and scope limits

Lean 4.19.0 is pinned. The manifest pins Mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0) and records exact revisions for all listed dependencies. The root build target imports both supporting modules.

`Check.lean` prints nine central definitions and checks all nineteen theorem types and their transitive axiom dependencies. A source scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, unsafe declaration, or weakened checking option.

The separate `strict-replay.json` records a fresh-copy build and successful direct strict replay of all four Lean files, all nineteen expected axiom audits, and only `propext`, `Classical.choice`, and `Quot.sound`. The source hashes in that record match every currently audited Lean and configuration file. These are inspected build-agent records, not compiler runs performed by this semantic reviewer.

The inspected eligibility record identifies unsolved metadata at upstream revision `0862407ef50dda4f7376342ca3e79368dce942d2`, with an empty prior solution history and no exact-ID or comment-search match. The short-ID search result numbered PR141 is explicitly about conjecture 58, so it is not a competing submission for conjecture 141. This supports the report's statement that no prior or competing submission was identified. This semantic reviewer did not independently repeat the remote searches.

No mathematical changes are requested. Preserve these audited identities, or obtain a delta review for later source/report changes. PDF rendering, final README command checks, package bookkeeping, and publication remain outside this source audit.
