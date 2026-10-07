# Solution Review — Conjecture 00000002158 (PR 651)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005075251`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — "the chromatic threshold for C₅-free graphs is 1/5" plus a non-mathematical balancing clause; `conjecture.md` is byte-identical to `conjectures/00000002158.md`.
- Change scope: only the submission folder was added.
- LaTeX: independently rebuilt (exit 0); shipped/rebuilt text matches up to glyph extraction artifacts.
- Lean build: `lake build` exit 0, zero errors, zero warnings.
- Forbidden content: none executable; no `sorry`, no `native_decide`, no axiom declarations.
- Axioms: independent run — `chromaticThreshold_cycle5_ne`, `chromaticThresholdInd_cycle5`, and `one_sixth_admissible` all use only `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs reproduce; SHA-256 manifest stale (see Issues).
- Semantic audit: pass (below).
- Independent arithmetic check: private-neighbourhood counting, the |S| ≤ 11 bound, the 22-colouring, and the induced threshold = 1 all re-derived by hand.

## Semantic audit
The threshold definition in Lean is exactly the Allen–Böttcher–Griffiths–Kohayakawa–Morris definition quoted in the report: `admissible H = {d | 0 < d ∧ ∃ K, ∀ n G, H.Free G → d*n ≤ G.minDegree → G.Colorable K}`, `chromaticThreshold = sInf (admissible H)`. This matches the source's "minimum-degree/|V| threshold keeping bounded chromatic number for H-free graphs"; "H-free" is Mathlib's `Free` (no non-induced subgraph copy), the standard reading; the strict χ < C is encoded as Colorable K with K = C−1, which defines the same admissible set; the `DecidableRel` binder covers all finite graphs classically; and the infimum is taken over a set that is nonempty (1/6 is in it) and bounded below by 0.

The disproof is an elementary but genuine upper bound. The counting lemma `card_mul_minDegree_le` (|T|·δ ≤ n + 2|T|(|T|−1) for a good T) is proved via pairwise-disjoint private neighbourhoods P(s) = N(s) ∖ ⋃_{t≠s} N(t) — disjointness and δ ≤ |P(s)| + 2(|T|−1) both check out by hand. A maximal good set S with |S| ≥ 12 would give 2n ≤ 12δ ≤ n + 264, so n ≤ 264; for n > 264 this bounds |S| ≤ 11. Maximality gives every outside vertex a witness s with ≥ 3 common neighbours, and the C₅-forcing lemma (u ∼ u′, both ≠ s, ≥ 3 common neighbours with s ⟹ C₅ ⊆ G) rules out same-colour adjacent outside pairs. The colouring {true,false}×S uses ≤ 22 colours; graphs with n ≤ 264 are n-coloured, so 1/6 is admissible with K = 264, giving threshold ≤ 1/6 < 1/5 and ≠ 1/5. The bound is not tight (the true threshold is 0 by deeper results), but a strict upper bound below 1/5 is exactly what refutes the equality.

The induced reading is handled with equal care and refutes it too: complete graphs contain no induced C₅, have δ = n−1 ≥ dn for any d < 1 and χ = n unbounded, while d = 1 is admissible vacuously, so the induced threshold is exactly 1 ≠ 1/5 (`chromaticThresholdInd_cycle5`). Other threshold notions (e.g. the homomorphism threshold, where 1/5 does appear for {C₃,C₅}-free graphs) are explicitly not addressed, and the source's own definition is the bounded-chromatic-number one, so the two formalized readings are the faithful ones.

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale (hash of `conjecture.md` does not match the shipped file; the shipped copy is byte-identical to the official source).

## Verdict
APPROVED. The numerical claim 1/5 is refuted faithfully under both natural readings of "H-free"; builds, axioms, PDF and source correspondence all verified.
