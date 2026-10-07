# Solution Review — Conjecture 00000000027 (PR 720)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005145551`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (EN+CN): r₃(N) = N·exp(−O(√log N)) for the maximal size of an AP-free subset of [N]. `conjecture.md` byte-identical to the official file.
- LaTeX: independent rebuild exits 0; shipped PDF matches in content; only spacing/glyph extraction artifacts.
- Lean build: exit 0, 8708 jobs, zero errors/warnings.
- Forbidden content: none.
- Axioms: my independent `CheckJ6.lean` over all 9 theorems: exactly `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: `verification/` logs verified (one CRLF manifest artifact, content identical).
- Sanity check: r₃(N) ≤ N and Behrend's N·exp(−4√log N) ≤ r₃(N) are classical; the derived g(N) = log(N/r₃(N)) ∈ [0, 4√log N] is then exact.

## Semantic audit
This is a PROOF, and the central review question is whether the reading trivializes the conjecture. It does not. "r₃(N) = N·exp(−O(√log N))" — with the standard meaning of O inside a formula — asserts exactly: there is a function g with g(N) = O(√log N) and r₃(N) = N·exp(−g(N)) (for large N). Since 1 ≤ r₃(N) ≤ N always, this statement is equivalent to Behrend's lower bound r₃(N) ≥ N·exp(−C√log N), which is a genuine theorem (Behrend 1946). The submission's main theorem has precisely this quantifier structure, proved for all N ≥ 1 with explicit constant 4 and g = log(N/r₃(N)) ≥ 0.

The formalization of the objects is careful: `r3 N` is defined from scratch as the maximum cardinality of subsets of `Icc 1 N` avoiding non-trivial 3-term APs (`∃ a d, 0 < d ∧ …`), proved equal to Mathlib's `addRothNumber (Icc 1 N)` and then to `rothNumberNat N` via `addRothNumber_Ico`, so the [N] = {1..N} vs {0..N−1} convention is settled rather than assumed; `not_hasThreeAP_iff` connects the explicit predicate to Mathlib's `ThreeAPFree`. `behrend_r3` transports Mathlib's `Behrend.roth_lower_bound` (a real Mathlib theorem by Dillies–Mehta). No hypothesis is strengthened and no conclusion weakened: the final `conjecture_27` is ∃ g, (g =O[atTop] √log N) ∧ (∀ N ≥ 1, 0 ≤ g N ∧ g N ≤ 4√log N) ∧ (∀ N ≥ 1, r₃ N = N·exp(−g N)).

Crucially, the submission is honest about scope: the tex states explicitly that the matching upper bound r₃(N) ≤ N·exp(−c√log N) (the Θ-version, which is the genuinely open problem — Kelley–Meka/Bloom–Sisask bounds are far weaker) is NOT claimed, and that the one-sided −O(·) notation does not assert it. Nothing is overclaimed; the proven statement is the conjecture as written, no more and no less.

## Issues found
- None. (A reviewer might prefer the two-sided reading under which the conjecture is open; but the written text uses one-sided Big-O, and the submission proves exactly that, while documenting the stronger reading it does not claim. This is the correct conduct.)

## Verdict
APPROVED. A faithful proof of the conjecture as literally stated, reducing it (via a clean identification of r₃(N) with Mathlib's rothNumberNat) to Mathlib's formalized Behrend bound, with explicit constants and full disclosure of the unclaimed stronger statement.
