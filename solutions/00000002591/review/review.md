# Solution Review — Conjecture 00000002591 (PR 665)

**Submission:** Jackmeson1 — `solutions/00000002591/Jackmeson1_submission_20261005091932`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture 00000002591 read in full (official bilingual English+Chinese text, ground truth). Shipped `conjecture.md` is **byte-identical** to `conjectures/00000002591.md` (`diff` clean).
- LaTeX: read the entire `proof.tex` (169 lines). Rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch dir from the shipped source; build succeeded. Shipped vs rebuilt PDF text compared with pypdf (whitespace- then glyph-normalized, including underscore handling in `\texttt` identifiers): **exactly identical**, 5335 normalized chars.
- Lean: `lake build` succeeded from clean with Lean `leanprover/lean4:v4.33.1`, Mathlib v4.33.1 rev `0df444a360` (prebuilt pool `poolM10`); 8708 jobs, **zero errors, zero warnings**.
- Axioms: fresh `lake env lean Check.lean` on the shipped project printed `[propext, Classical.choice, Quot.sound]` — only the three standard axioms — for the decisive theorem `not_superpolynomial` and all supporting theorems (`card_cuts_lt`, `card_cuts_le`, `exists_proper_not_cut`, `E_eq_zero`, `antichain2_attains`, `no_three_of_cuts`, `E_two_pos`). No `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` anywhere in the submission.
- Aux code: `verification/axioms.txt` and `verification/build.txt` match my fresh runs exactly. `verification/SHA256SUMS.txt` has stale entries for `conjecture.md` and `lean/Conjecture2591/Basic.lean` (final edit after checksumming; the PR is a single commit, so the shipped file is the only version, and it is the one I built and audited). Not blocking.
- Metadata: `metadata.csv` lists 00000002591 with `proven=false, disproven=false` (unsolved) — consistent.

## Semantic audit

The official conjecture asserts a size law for Dedekind–MacNeille completions: |DM(P)| ≤ 2^{|P|}, "with the upper bound attained by unbounded dense antichains"; that "the isomorphism types of P attaining the bound are superpolynomial in number"; and a minimal-generator characterization by three-chain cross products. The submission proves that for finite posets the bound is attained by nothing: |DM(P)| < 2^{|P|} whenever |P| ≥ 3, so the count E(n) of isomorphism types of n-element posets attaining the bound is 0 for every n ≥ 3, whence "superpolynomial in number" is false under both its readings (eventually above every n^k; above C·n^k infinitely often for every k, C, i.e. not O(n^k) for any k). Since the conjecture is a conjunction, this falsifies it. Clause (iv) (three-chain cross products) is admittedly vague; the report declines to formalize it and correctly observes that refuting clause (iii) suffices.

The formalization is faithful to the conjecture's own objects. DM(P) is Mathlib's `DedekindCut P = Concept P P (· ≤ ·)`: pairs (A, B) with `upperBounds A = B` and `lowerBounds B = A` — exactly the pair form of MacNeille cuts, so |DM(P)| is `Nat.card (DedekindCut P)`; the cut is determined by its left set (`Concept.extent_injective`), giving |DM(P)| ≤ 2^{|P|} by injection into the power set (formalized as `card_cuts_le`, with the `Fintype` scope stated in the report). The core argument is elementary and complete: if every singleton {x} were a left set, then {x} = lowerBounds(upperBounds {x}) = Iic x, so every element is minimal and P is an antichain; then any two-element set has no upper bound, so its closure is lowerBounds(∅) = P, which for |P| ≥ 3 differs from the two-element set — so some singleton or pair is not a left set and strictness follows (`no_three_of_cuts`, `exists_proper_not_cut`, `card_cuts_lt`). The counting definitions (`Attaining n`, `Iso`, `E n = Nat.card (Quot Iso)`) are exact counts of isomorphism types, and non-vacuity is proved: the two-element antichain has all four subsets as left sets, so E(2) > 0 (`antichain2_attains`, `E_two_pos`). No hypothesis is strengthened and no definition trivialized.

I independently brute-forced all partial orders on 3 and 4 labeled points (19 and 219 posets, matching the known counts) and counted cuts as sets s with lowerBounds(upperBounds s) = s: zero posets attain 2^n at n = 3 or 4, the two-element antichain attains 4 = 2^2, and antichains have exactly n + 2 cuts — all matching the Lean theorems and the report's prose. The report's scope statements are accurate: its title says "finite", clause (ii) is refuted for finite antichains (any antichain with n ≥ 3 has n + 2 < 2^n cuts, a special case of `card_cuts_lt`), and the infinite case is discussed in prose without being claimed. E(n) = 0 for all n ≥ 3 kills superpolynomiality under every reasonable reading.

## Issues found

None blocking. Stale entries in `verification/SHA256SUMS.txt` (`conjecture.md`, `lean/Conjecture2591/Basic.lean`); the shipped files are the ones built and audited here.

## Verdict

APPROVED. A correct, fully machine-checked disproof: no finite poset with at least three elements has 2^{|P|} Dedekind–MacNeille cuts, so the number of isomorphism types attaining the conjectured 2^{|P|} bound is zero for every n ≥ 3 and the "superpolynomial in number" clause (with the claimed antichain attainment) is maximally false. Formalization faithful (real MacNeille cuts, exact counting, non-vacuity at n = 2), build clean, axioms only the standard three, and the brute-force cross-check agrees everywhere.
