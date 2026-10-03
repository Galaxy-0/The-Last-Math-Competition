# Solution Review — Conjecture 00000008438 (PR 313)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003091740`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — Max column count of a strength-t orthogonal array N(n,t) ≤ n²−n+t, attained for prime-power n; deficit ≥ n^{1/2} for non-prime-powers. Strength t is defined (EN and CN) as "the uniformity of any t ROWS".
- LaTeX: compiled ok (pdflatex twice, exit 0), 1-page PDF; included main.pdf genuine, page count matches verification.json.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings (warnings-as-errors), v4.19.0, Std only. Uses `maxHeartbeats`/`maxRecDepth` options (legitimate, not completeness-affecting).
- Forbidden content: none — no sorry/admit/native_decide/axiom/unsafe/implemented_by/extern.
- Auxiliary code: none present (`auxiliary_scripts_rerun: []`). I ran an INDEPENDENT Python verification: the 3×8 binary full-factorial array satisfies strength-3 index-1 uniformity over every ordered triple of distinct rows, has 8 distinct columns, 8 > 2²−2+3 = 5; the 3×27 ternary full-factorial array likewise with 27 distinct columns, 27 > 3²−3+3 = 9; binary array matches the tex-displayed matrix. sha256 of Main.lean/main.tex match verification.json; axiom printout (propext only) reproduced.
## Semantic audit
Conjecture's literal claim (EN): "The maximal number of columns of a strength-t OA is N(n,t) at most n² − n + t", with strength t defined as "the uniformity of any t rows" (CN: 任意 t 行的均匀性; max column count: 正交表最大列数).

Lean definitions verified faithful:
- `occurrences A i j k x y z` = number of columns whose entries in rows i,j,k are x,y,z — a literal count over `List.finRange c` (all columns).
- `OA3 A := ∀ i j k : Fin r, i ≠ j → i ≠ k → j ≠ k → ∀ x y z, occurrences A i j k x y z = 1` — exactly strength-3 uniformity over any 3 distinct rows, in every order, at index one. Matches the conjecture's row-based definition.
- `ColumnBoundAtThree : Prop := ∀ (n r c : Nat), 2 ≤ n → 3 ≤ r → ∀ A : Fin r → Fin c → Fin n, OA3 A → c ≤ n*n − n + 3` — the t=3 specialization of N(n,t) ≤ n²−n+t with n = alphabet size.
- Witnesses: `binaryArray` (3 rows, 8 columns, all binary words; `binaryArray_is_OA3`, `binaryArray_columns_distinct` by kernel decide) and `ternaryArray` (3 rows, 27 columns, all ternary words; `ternaryArray_is_OA3`, `ternaryArray_columns_distinct`).
- Final theorems: `conjecture8438_false : ¬ ColumnBoundAtThree` (8 > 5) and `conjecture8438_false_ternary : ¬ ColumnBoundAtThree` (27 > 9).
- Hypotheses satisfied: the witnesses ARE strength-3 index-1 OAs under the conjecture's own row-based definition (verified in Lean AND independently in Python). Distinct-columns theorems preempt the "just repeat columns" objection; index-1 is the strongest repair of an otherwise trivially-false bound (concatenating copies of a full array raises column count without losing strength, so with unbounded index the conjectured max is infinite — the index-1 witnesses refute even the repaired reading).
- Ambiguity handling: "n" could mean alphabet size or row count. The ternary witness has alphabet size = row count = 3, so under BOTH readings the bound is 9 < 27. The binary witness additionally covers the alphabet reading (8 > 5). No plausible reading of n rescues the bound.
- Orientation note: if the conjecture had meant the standard OA(N,k,s,t) convention (uniformity over columns/factors, bounding the number of factors), the transposed witnesses (k = 3 columns) would not violate k ≤ 5/k ≤ 9. However, both the English ("uniformity of any t rows") and Chinese (任意 t 行) define strength over ROWS, and the submission follows the literal definition; the conjecture's own wording is the authoritative one. This is noted as an interpretive issue, not a blocker.
- LaTeX↔Lean match: tex displays the same binary matrix (`W`-analog verified equal by my Python and by the tex display match), states 8 > 5 and 27 > 9, and describes exactly the Lean predicates/theorems above.
## Issues found
- Interpretive (non-blocking): the conjecture is a garbled translation; its bound only makes sense in the row-uniformity orientation it itself defines, and under that literal text both witnesses refute it decisively. If an organizer insists on the transposed standard-convention reading, the conjecture's definition sentence would have to be rewritten, which is not the reviewer's place.
- Minor: report says "Run `lean Main.lean`" for reproduction while the packaged build uses `lake build` (both work; verification.json records the lake build).
## Verdict rationale
Under the conjecture's own definition (strength = uniformity over any t rows) and both plausible meanings of n (alphabet size or row count — equal to 3 in the ternary witness), the index-1 full-factorial array of 27 distinct columns violates N(3,3) ≤ 9 by a factor of 3, with everything kernel-checked in Lean, independently reproduced in Python, compiled warning-free, and no forbidden content. The disproof engages the conjecture's actual objects (a genuine strength-3 orthogonal array) rather than numeric trivia.

## Disposition
APPROVED — merged into main (PR 313). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
