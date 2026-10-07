# Solution Review — Conjecture 00000000421 (PR 735)

**Submission:** Jackmeson1 — `solutions/00000000421/Jackmeson1_submission_20261005191649`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (bilingual, `conjectures/00000000421.md`): growth-tree statistic a(T) = number of addable outer-corner cells; expectation of a(T) on a uniformly random tableau converges to 2 with rate 1/log n. Shipped `conjecture.md` is **byte-identical** to the official file (diff clean).
- **LaTeX rebuild**: `latexmk -pdf -interaction=nonstopmode` in a scratch dir succeeds (3 pages, same as shipped). pypdf text comparison of shipped vs rebuilt PDF: content matches; differences are extraction artifacts of the shipped PDF's font map (`|` extracted as `j`, `→` as `!`, `≥` as a private-use glyph, kerning splits such as "T rivedi", missing interword spaces). Cosmetic only.
- **lake build**: fresh build succeeds with **zero errors and zero warnings** (8708 jobs, Lean v4.33.1, Mathlib v4.33.1 rev 0df444a360 from poolM05; 41–61 s for Basic.lean), reproducing `verification/build.txt`.
- **Axioms**: `lake env lean Axioms.lean` run fresh: `C421.disproof` depends only on `[propext, Classical.choice, Quot.sound]`, matching `verification/axioms.txt`. Grep for `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/declared `axiom`: only benign English mentions in docs.
- **Aux code**: no scripts shipped; `verification/` claims (build success, axiom output) reproduced exactly. The tex Remark mentions a numeric check "for n ≤ 22" whose script is not shipped; I reproduced that check independently (see semantic audit).
- **Metadata**: `metadata.csv` lists 00000000421 as unsolved; no solution folder for this ID on `main`.

## Semantic audit

The conjecture states that the expectation of a(T) — the number of outer-corner (addable) cells of the tableau's shape — on a uniformly random tableau of size n converges to 2, with convergence rate 1/log n. The submission reads "uniformly random tableau" as the uniform measure on standard Young tableaux with n cells (the literal reading), formalizes SYT faithfully (injective placement of entries 1..n on a lower set with strictly increasing rows and columns — exactly the standard definition), and also covers the alternative uniform measure on Young diagrams with n cells. The Plancherel reading (where the limit 2 is actually true) is explicitly flagged as not covered; since the conjecture's own text says "uniform", the chosen reading is the faithful one, and the tex notes the counting argument refutes Plancherel on paper as well.

The decisive theorem `C421.disproof` proves: for every prime p ≥ 3, `7/3 ≤ E_SYT p` and `7/3 ≤ E_shape p`; consequently neither expectation tends to 2, and no constant C satisfies |E n − 2| ≤ C/log n eventually (7/3 > 2 while C/log n → 0, and there are arbitrarily large primes). This is the exact negation of the conjecture's two clauses under the stated reading, with a clean quantifier match. The proof is a genuine argument about the conjecture's own objects: every nonempty Young diagram has the two addable cells (0, rowLen 0) and (colLen 0, 0); a non-rectangular diagram has a third addable cell (k, rowLen k) at the first short row; a diagram with a prime number p of cells that is a rectangle must be a single row or column; a single row or column carries at most one standard tableau; and the hook tableau of shape (p−1, 1) exists and is neither. Averaging a ≥ 3 − [row-or-col shape] over the finite set of tableaux, with at most two exceptional objects among at least three, gives E ≥ 7/3.

I verified the mathematics independently by brute-force enumeration of all SYT for n ≤ 8: the counts reproduce the involution numbers t_n (1, 2, 4, 10, 26, 76, 232, 764), the identity E_SYT(n) = t_{n+1}/t_n stated in the (non-load-bearing) Remark holds exactly, E_SYT(3) = 2.5 and E_SYT(5) = 76/26 ≥ 7/3, and in fact E_SYT(n) → ∞, so the conjecture's limit 2 is far off under this reading. The refutation is sound and, if anything, conservative.

## Issues found

- `verification/SHA256SUMS.txt` is stale: its entries for `conjecture.md` (and `lean/Conjecture421/Basic.lean`) are pre-final-commit hashes and do not match the shipped files. Non-blocking: the shipped `conjecture.md` is byte-identical to the official file, and the build and axiom claims were re-verified fresh on the shipped source.
- The tex Remark cites a numeric-check script ("for n ≤ 22") that is not included in the submission. Non-blocking: the remark is explicitly marked "not used, not formalized", and I reproduced the numerics independently.
- Minor tex/Lean mismatch in boundary wording: the tex proof of the corner lemma discusses the empty-diagram edge case that the Lean `two_le_a` avoids by hypothesis. Cosmetic.

## Verdict

APPROVED. The submission formalizes exactly the conjectured objects under the literal reading of "uniformly random tableau", proves the precise negation of both the limit and the rate clause by an elementary, verifiable averaging argument, builds cleanly with only the three standard axioms, and reports honestly which readings it does not cover. The stale checksum file and the missing (non-load-bearing) numerics script are quality blemishes, not correctness or faithfulness concerns.
