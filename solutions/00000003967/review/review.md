# Solution Review — Conjecture 00000003967 (PR 326)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261003112932`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0, Mathlib v4.33.1)
- [x] No `sorry`, no `native_decide`, no extra axioms (`#print axioms` exactly `[propext, Classical.choice, Quot.sound]`)
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Clause 1: the graphs attaining the Graham bound π(G) = 2^d (d = diameter) are exactly the (d−1)-subdivision classes of paths. Clause 2: every 2-connected graph satisfies π(G) ≤ 2^d (1 − c/log d) for some constant c > 0.

## What the submission proves
The 4-cycle C₄ refutes both: diameter 2, π(C₄) = 4 = 2², not a path (4 edges vs 3 for P₄; any subdivision of a path is a path), and 2-connected, while 4 > 4(1 − c/log 2) for every c > 0. Lean: faithful pebbling definitions (move = 2 pebbles from u, 1 on adjacent v; solvability via `Relation.ReflTransGen`; π = least universal t); `π(C₄) ≤ 4` by a depth-bounded search with a proven soundness lemma and an exhaustive `decide` over all distributions summing to 4 and all targets; `π(C₄) ≥ 4` by the standard weight potential Ψ = 4p(0) + 2p(1) + p(2) + 2p(3), non-increasing along moves (all 8 edge directions checked), with the all-on-vertex-2 distribution of t ≤ 3 pebbles unable to reach the opposite vertex; `diam_C4` by genuine ediam bounds on Mathlib's `cycleGraph 4`; `conjecture_00000003967_false : ¬ Claim1 ∧ ¬ Claim2`.

## Verification notes
`lake build` exit 0; axiom audit clean. The reviewer verified π(C₄) = 4 independently (4 pebbles always reach any target on C₄; 3 on the opposite vertex never reach 0, matching the weight argument). The (d−1)-subdivision reading is addressed in the report: subdivisions of paths are paths, so the "is a path" formalization covers it; C₄ fails both readings. Claim 2 is formalized with d ≥ 2 so that log d > 0, which only weakens it. LaTeX consistent; PDF present.

## Verdict
APPROVED — merged into main.
