# Solution Review — Conjecture 00000001673 (PR 655)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005080635`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — ind(C₆) = (√3−1)/2, extremal configuration the balanced triangular-prism blow-up uniquely, stabilizer justification; `conjecture.md` is byte-identical to `conjectures/00000001673.md`.
- Change scope: only the submission folder was added.
- LaTeX: independently rebuilt (exit 0); shipped/rebuilt text matches up to glyph extraction artifacts.
- Lean build: `lake build` exit 0, zero errors, zero warnings.
- Forbidden content: none executable; finite C₆ facts are kernel `decide` on `Fin 6`, which is fine.
- Axioms: independent run — `C1673.not_conjecture` uses only `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs reproduce; SHA-256 manifest stale (see Issues).
- Semantic audit: pass (below).
- Independent arithmetic check: pair lemma, local bound, double counting, 2/7 < (√3−1)/2, 5/324 lower bound — all re-derived by hand.

## Semantic audit
The value clause is refuted in every asymptotic reading. An induced copy of C₆ is a `SimpleGraph.Embedding` `cycleGraph 6 ↪g G` (injective, adjacency-reflecting), so `InducesC6 G s` is exactly "G[S] ≅ C₆"; `c6Density` is #inducing 6-sets / C(n,6); `maxC6Density n` is the supremum over all graphs on n labelled vertices (a finite, nonempty set, hence a max); `indC6` is the limsup. The uniform bound is a genuine double counting argument, not a finite counterexample: (a) if b∖{x} and b∖{y} both induce C₆, then in the two 6-copies a third vertex w has degree 2 in each, so [w~x] = [w~y] (`pair_twins`); (b) three simultaneous deletions would make the twin-free property of C₆ contradict (a) (`erase_count_le_two`); (c) counting (S,T) pairs with S inducing and T a 7-superset gives c(n−6) ≤ 2·C(n,7), hence 7c ≤ 2·C(n,6) and d(G) ≤ 2/7 for all n ≥ 7 (`count_mul_le`, `c6Density_le`). Since 2/7 < (√3−1)/2 (equivalent to 121/49 < 3, proved by `Real.lt_sqrt`), the limsup, the liminf, any limit of M(n), and the limsup along any graph sequence all differ from (√3−1)/2. The n = 6 exception (M(6) = 1 for C₆ itself) is correctly excluded from every asymptotic statement.

The extremal clause is refuted as well. A blow-up of the prism along p has, within each fibre, twins; the twin-freeness of C₆ forces p∘f injective for any induced embedding, hence bijective onto the six prism vertices, and then the prism triangle (0,0),(1,0),(2,0) pulls back to a triangle of C₆ — impossible (`prism_blowup_no_C6` proves `IsEmpty (cycleGraph 6 ↪g prism.comap p)`). So every prism blow-up has induced-C₆ density 0, while balanced blow-ups of C₆ itself give m⁶ inducing transversals at n = 6m, density ≥ 720/6⁶ = 5/324 (`c6Count_blowup_ge`, `c6Density_blowup_ge`), so ind(C₆) ≥ 5/324 > 0: the claimed extremal family cannot be extremal, and no sequence of prism blow-ups approaches ind(C₆). The stabilizer clause presupposes the extremal clause and needs no separate treatment.

I checked the pair lemma, local bound, double counting identity 7·C(n,7) = (n−6)·C(n,6), (√3−1)/2 > 2/7, and 5/324 = 6!/6⁶ by hand; all are correct, and the Lean formalization tracks the report step for step.

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale (hashes of `conjecture.md` and the main Lean file do not match the shipped files; the shipped `conjecture.md` is byte-identical to the official source and the shipped Lean file builds cleanly with clean axioms).

## Verdict
APPROVED. A self-contained, correct and faithfully formalized disproof of both the value clause and the extremal clause; every audited check reproduces.
