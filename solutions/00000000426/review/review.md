# Solution Review — Conjecture 00000000426 (PR 344)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — there exist CSP triples (X, C, X(q)) where C has prime order p and X(q) = 1 at all p-th roots of unity.
- LaTeX: compiled (pdflatex twice, exit 0, 1 page); shipped main.pdf is a real PDF v1.5, text matches recompiled output (3042 vs 3030 chars; diffs are pdftotext spacing/kerning artifacts only, verified line-by-line).
- Lean build: exit 0, fresh (`rm -rf .lake && lake build`), Lean 4.19.0, `import Std`, no Mathlib. Only output = four `#print axioms` info lines. No warnings.
- Forbidden content: none (grep for sorry/admit/native_decide/axiom/unsafe/implemented_by/extern/skipKernelTC: zero matches). Axiom lists: [propext, Quot.sound] / [propext] / none — all standard, no sorryAx, no custom axioms.
- Auxiliary code: no Python/JS shipped. verification/lean-axioms.log, lake-build.log match my fresh-build output exactly. Independent python3 re-check of the instance (C_2 = xor on Bool acting on 2 positions by rotation; X = {00}; both rotations fix the word; roots {1,-1}; polynomial identically 1) passes.
## Semantic audit
Conjecture (literal): "There exist CSP instances where the rotation group has prime order p and X(q) takes the value 1 at all p-th roots of unity (a separation of trivial sieving from nontrivial counting)." This PR claims a PROOF, so the Lean must establish the statement.

Key Lean signatures (lean/Main.lean, namespace Conjecture426):
- `abbrev C := Bool`, `def groupMul (a b : C) : C := Bool.xor a b`, `theorem group_laws` (assoc, identity, self-inverse), `theorem group_cyclic`, `theorem group_enumeration` (Nodup, complete, length = 2), `def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p`, `theorem group_order_prime : Prime groupElements.length` — a real cyclic group of prime order 2.
- `def rotate (g : C) (w : Word) : Word := fun i => w (groupMul i g)` with `rotate_identity`, `rotate_composition` — an actual rotation action on binary words (faithful on positions: `rotation_on_positions_nontrivial`).
- `def X : List Word := [zeroWord]` with `action_closed`, `X_complete`, `X_no_duplicates`; `def equalWord` + `theorem equalWord_correct` (Boolean test ≡ function equality); `def fixedCount (g : C)` + `theorem fixed_count (g : C) : fixedCount g = 1` — genuine fixed-point counting.
- `def polynomial : List Nat := [1]` (nonneg integer coefficients) with Horner `evaluate` over an `EvaluationAlgebra R` structure; `theorem polynomial_one_at_every_point {R} (A : EvaluationAlgebra R) (q : R) : evaluate A q polynomial = A.one` — X(q) = 1 at EVERY point of every algebra obeying the elementary laws, hence at all complex p-th roots of unity (ℂ admits such an instance); no finite-root sampling.
- `def root (g : C) : Int := if g then -1 else 1` + `roots_are_primitive_and_faithful` (root true ≠ 1, square = 1, multiplicative, injective) — the second roots of unity as a concrete group.
- `def CyclicSieving (A) (omega) : Prop := ∀ g, evaluate A (omega g) polynomial = A.fromNat (fixedCount g)` — the CSP defining equality for every group element; `theorem cyclic_sieving_for_every_evaluation` proves it.
- `theorem conjecture426 : Prime groupElements.length ∧ groupElements.length = 2 ∧ X.length = 1 ∧ CyclicSieving intAlgebra root ∧ (∀ q : Int, evaluate intAlgebra q polynomial = 1)`.
- `theorem identity_forces_singleton ... : cardinality = 1` — proves the parenthetical "nontrivial counting" reading is impossible: 1 is a p-th root of unity, so X(1)=|X|=1 is forced.

Fidelity check: the CSP framework matches Reiner–Stanton–White (fixed-point count = polynomial evaluation at a root of unity of the element's order); the submission cites RSW and honestly discloses that the action on X is nonfaithful (CSP does not require faithfulness — correct). The instance is degenerate (|X|=1), but that degeneracy is mathematically forced by the literal statement, and the author proves this forcing rather than hiding it. Not vacuous: a real prime-order cyclic group, real rotation action, real fixed counts, real polynomial, real root map, CSP equality for all g — all the conjecture's objects are present and the existence claim is established. Under the alternative "primitive roots only" reading the conjecture would still be true (e.g. X(q)=1+[p]_q), so no reading makes the submission's theorem false; the literal-reading proof follows the #996 adjudication bar.
## Issues found
- Interpretation call (disclosed by author, and I concur): "all p-th roots of unity" is read to include q=1, which forces |X|=1; the parenthetical "separation from nontrivial counting" is unachievable under the literal text. The submission proves the explicit existence assertion as written.
- ℂ is not available in plain Std; coverage of complex roots is via the universal evaluation theorem (valid over every algebra with the stated laws). Mathematically airtight; flagged for transparency.
## Verdict rationale
The Lean genuinely instantiates the CSP framework and establishes the conjecture's literal existence claim for p = 2, with the degenerate reading proved unavoidable rather than smuggled in. Build is clean, axioms standard, no forbidden constructs, and the report's scope discussion is accurate. Under the competition's literal-bilingual-statement rule this is a valid proof.

## Disposition
APPROVED — merged into main (PR 344). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
