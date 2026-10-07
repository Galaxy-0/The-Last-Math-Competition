# Solution Review — Conjecture 00000006420 (PR 650)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005074728`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — existence of two sets with the same isoperimetric deficit but different asymmetry, realized by an explicit two-circle union; `conjecture.md` is byte-identical to `conjectures/00000006420.md`.
- Change scope: only the submission folder was added.
- LaTeX: independently rebuilt (exit 0); shipped/rebuilt text matches up to glyph extraction artifacts.
- Lean build: `lake build` exit 0, zero errors, zero warnings.
- Forbidden content: none executable; no `sorry`, no `native_decide`, no axiom declarations.
- Axioms: independent run — `separation`, `conjecture6420`, `normalisations`, `perimeter_axiomatic` all use only `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs reproduce; SHA-256 manifest stale (see Issues).
- Semantic audit: pass (below).
- Independent arithmetic check: every containment and distance estimate re-derived by hand (7/5 ≤ √2, 13/10 ≤ √2, 1/10 + 9/10 = 1, 10 > 2 + 2√2, area bookkeeping 2π − π/50).

## Semantic audit
The conjecture is an existence statement with an explicit-construction clause, and the submission proves it, not disproves it. The terms are given their standard quantitative-isoperimetric-inequality meanings, with sources: perimeter P(E) = ℋ¹(∂E), deficit δ(E) = P(E)/P(B_E) − 1 with B_E the equal-area disk, asymmetry α(E) = inf_x |E △ B̄(x, r_E)|/|E| (Fraenkel asymmetry). "Two-circle union" as a union of two closed disks is the right reading (circles as curves have zero area, so their deficit is undefined). These readings are faithful; nothing is trivialized.

Both witnesses are genuine two-disk unions: E_near = D₀ ∪ D_{5/2}, E_far = D₀ ∪ D₁₀ with disjoint closed unit disks. The equal-deficit part is fully computed, not assumed: the boundary of a disjoint union of closed sets is the union of the boundaries (proved in Lean), ℋ¹ is translation invariant and scales by √2 under dilation, so both sets have perimeter 2L and comparison perimeter √2·L with 0 < L < ∞ (bounds L ≤ 2π via the 1-Lipschitz parametrization e^{iθ} and 2 ≤ L via the Lipschitz projection onto [−1,1]), giving δ = 2L/(√2 L) − 1 = √2 − 1 for both. The value L never needs to be known to be 2π.

The asymmetry separation is proved by genuine estimates. For E_far: a radius-√2 disk cannot meet both unit disks (distance 10 > 2 + 2√2), so one disk lies wholly in E ∖ B and B ∖ D₀ ⊆ B ∖ E disjointly, giving |E △ B| ≥ π + (2π − π) = 2π and α ≥ 1. For E_near: the comparison disk B₀ = B̄((2/5,0), √2) contains D₀ (7/5 ≤ √2) and a radius-1/10 disk inside D_{5/2} (1/10 + 9/10 = 1; 1/10 + 6/5 = 13/10 ≤ √2), so |E △ B₀| ≤ 2(2π − |K|) = 2π − π/50 and α ≤ 1 − 1/100. I verified each inequality by hand; all are correct, and α(E_near) ≠ α(E_far) follows. `conjecture6420` in Lean is exactly the existential statement with explicit centres and radii — the witnesses are the actual sets, not an abstract surrogate. `perimeter_axiomatic` additionally shows any translation-invariant perimeter additive on disjoint compact sets (properties the De Giorgi perimeter has) takes the same value on both witnesses, so the separation survives alternative deficit conventions; the report transparently marks which parts of that identification are not formalized.

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale (hashes of `conjecture.md` and the main Lean file do not match the shipped files; the shipped `conjecture.md` is byte-identical to the official source and the shipped Lean file builds cleanly with clean axioms).

## Verdict
APPROVED. A correct, fully formalized existence proof with explicit, non-degenerate witnesses; all audited checks reproduce.
