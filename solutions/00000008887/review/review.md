# Solution Review — Conjecture 00000008887 (PR 368)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — Snort/Col coloring-game conjecture; third clause: "the arithmetic of the duality is the reversal snort equals minus col (a reversal law)"; fourth: "the exceptions to reversal are asymmetric graphs (an exception law)".
- LaTeX: recompiled twice in /tmp/tlmc-review2/scratch/pr-368, exit 0, zero errors; shipped main.pdf real 1-page PDF, SHA-256 matches VALIDATION.json; content matches tex.
- Lean build: fresh `rm -rf .lake && lake build` exit 0; only `#print axioms` infos — [propext, Quot.sound] only; Lean 4.19.0, Std only, `-DwarningAsError=true`.
- Forbidden content: grep for sorry/admit/native_decide/`axiom `/unsafe/implemented_by/extern/skipKernelTC: no matches.
- Auxiliary code: none shipped (none needed); my independent python3 game-tree search over the complete K2 state space (9 colorings, exhaustive legal moves per standard rules) confirms: Snort(K2) outcomes (Left-first, Right-first) = (True, True) i.e. first-player win; Col(K2) = (False, False) i.e. second-player win = value 0; −Col(K2) also (False, False); hence Snort(K2) ≠ −Col(K2). All VALIDATION.json hashes match; conjecture.md identical to official bilingual statement.
## Semantic audit
Conjecture literal claim attacked: Snort = −Col (reversal law). Final theorem:
```lean
theorem conjecture8887_counterexample :
    ¬ EqualValue (boardGame true) emptyBoard (negative (boardGame false)) emptyBoard
```
where `EqualValue G s H t := ∀ U [BEq U] [LawfulBEq U] (K : Game U) (u) (p), wins (sumGame G K) p (s,u) = wins (sumGame H K) p (t,u)` — the standard observational equality of short partizan game values (equal outcome of disjunctive sums with every finite context, either player to move). Faithfulness of objects: `Game` is a finite normal-play partizan game with complete state list, all Left/Right moves (`move : Bool → S → S → Bool`), and a strictly decreasing height; `wins` is a well-founded recursive predicate (player to move with no move loses — normal play) bridged to a computable evaluator by `wins_eq_fuel` (fuel must exceed the position height; used with fuel 3 > height 2), so the `decide` computations are not truncations. The board is the full 9-coloring space of K2 (`every_board_present`, `every_coloring_represented`); `legal snort p b v` encodes exactly the standard rules — Snort: no adjacent vertex may bear the opponent's color (adjacent opposite colors forbidden); Col: no adjacent vertex may bear the player's own color (adjacent equal colors forbidden) — matching the cited Definition 1.4 of Games of No Chance 6. `every_move_is_a_legal_placement` and `all_moves_decrease` tie moves to placements; `negative` swaps the two players' move relations (standard negation); `sumGame` is the disjunctive sum. The refutation instantiates the zero-game context: `zero_context_separates` proves wins(Snort(K2)+0, Left) = true and wins(−Col(K2)+0, Left) = false — different outcome classes (N vs P), which separates the values under ANY reading of value equality (any notion implying equal bare outcomes). `symmetric_graph` additionally proves K2 has a nonidentity adjacency-preserving involution, so the conjecture's own exception clause ("exceptions are asymmetric graphs") cannot cover this counterexample; the asymmetric-exception law is thereby also false. I independently re-derived all outcomes by exhaustive python3 game search. Not vacuous: real Snort, real Col, real negation, real K2 with its automorphism — the conjecture's actual objects are present.
## Issues found
- none blocking. (Observation: only the zero context is needed and used; EqualValue's stronger universal quantification makes the refutation harder, not easier.)
## Verdict rationale
Fresh warning-free build with only standard axioms, recompiling real PDF, faithful rule encodings verified against complete state spaces with a proved fuel bridge, and a decisive outcome-class separation (first-player win vs second-player win) between Snort(K2) and −Col(K2) on a symmetric graph. The literal reversal clause of the bilingual conjecture is genuinely falsified, and the asymmetric-graph exception cannot apply.

## Disposition
APPROVED — merged into main (PR 368). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
