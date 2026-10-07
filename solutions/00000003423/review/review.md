# Solution Review — Conjecture 00000003423 (PR 703)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005130435`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read; copy check.** Read `conjectures/00000003423.md` in full (bilingual). Shipped `conjecture.md` is byte-identical to it (`diff` clean).
- **LaTeX rebuild + PDF comparison.** Fresh `latexmk -pdf` build: exit 0, 3 pages matching the shipped PDF. Extraction differences are only glyph/font-substitution artifacts in math mode; rendered pages are content-identical (checked visually page by page). Cosmetic.
- **Lean build.** `lake build` from scratch: zero errors, 8708 jobs, exit 0 (toolchain `leanprover/lean4:v4.33.1`, Mathlib v4.33.1, pool rev 0df444a360). Incremental rebuild of the extracted tree confirms shipped sources match the built state.
- **Axioms.** No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. Independent scratch check covers more than the shipped `axioms.txt`: `not_edge_monotone_hittingTime`, `not_edge_monotone_maxHittingTime`, `adding_edge_increases_hittingTime`, `harmonic_le_zero`, `hittingTime_spec` — all `[propext, Classical.choice, Quot.sound]`, only the standard three.
- **Aux code.** `Axioms.lean` reproduces `verification/axioms.txt`. Note: `verification/SHA256SUMS.txt` has two stale entries (`conjecture.md`, `lean/Conjecture3423/Basic.lean`) that do not match the shipped files; both verified correct independently.
- **Metadata.** `metadata.csv` lists 00000003423 as unsolved (proven = false, disproven = false); no competing solution folder on main.

## Semantic audit

The conjecture is a conjunction: (1) the maximal hitting time of the complete graph is n−1, and (2) "adding edges decreases hitting time submodularly". The submission addresses the right target: it refutes clause (2), which falsifies the conjunction, and correctly identifies clause (1) as true (prose remark; on K_n every pairwise hitting time is n−1) without needing to formalize it. The refutation is stated at the right strength: the decisive theorems `not_edge_monotone_hittingTime` and `not_edge_monotone_maxHittingTime` are the negations of "for all connected G ≤ G', hitting times (resp. maximal hitting time) never increase" — the exact monotone core that any "decreases submodularly" claim would imply — in both the pairwise and the maximal reading of "hitting time", with the narrower readings (commute times, stationary averages) explicitly declared out of scope.

The formalization is faithful and, moreover, contains a genuine piece of mathematics, not just a computation: hitting time H_G(·→b) is defined as the value of the unique solution of the first-step system h(b) = 0, h(v) = 1 + (1/deg v)Σ_{u∼v} h(u), and existence plus uniqueness of this system on every finite connected graph is proved in general (`harmonic_le_zero` maximum principle, `isHittingTimeVec_unique`, `exists_isHittingTimeVec` via injectivity-implies-surjectivity). The graphs are Mathlib `SimpleGraph`s: `pathGraph 5` and its sup with `SimpleGraph.edge 0 2`, with connectedness of the supergraph inherited by monotonicity — the conjecture's own objects.

The mathematics is correct and I verified it independently: solving the first-step system exactly (rational Gaussian elimination) for P₅ reproduces the shipped 5×5 table (row target 4: 0, 7, 12, 15, 16; H(0→4) = 16), and for P₅ + {0,2} with target 4 it reproduces (18, 18, 16, 9, 0), so H(0→4) = 18 and the maximal hitting time rises from 16 to at least 18. The explicit Lean vectors `hP5` and `hChord` are checked against the system by `decide`-based enumeration of the neighbor sets, so the Lean proof is a complete verification of the counterexample, and the intuition (from 0 the walk must reach 2 before going deep; the chord lets it jump back, trapping it in {0,1,2} more often) is sound. Adding an edge can indeed increase hitting times — the claimed universal decrease is false.

The submission also fixes the defect of the earlier closed PR #224 (whose counterexample was prose-only): here the graphs, the hitting-time system, and the increase 16 → 18 are all in Lean.

## Issues found

- Non-blocking: `verification/SHA256SUMS.txt` lists two hashes that do not match the shipped `conjecture.md` and `lean/Conjecture3423/Basic.lean` (stale checksums; both files verified correct independently). The other 12 entries check out.

## Verdict

APPROVED. The submission refutes the second clause of the conjecture — hence the conjecture itself — with a fully formalized, faithful counterexample on real graphs, backed by a general existence/uniqueness theorem for the hitting-time system; the quantifier structure of the refuted statements matches the claim, the arithmetic was independently reproduced exactly, and the build is clean with only the standard three axioms.
