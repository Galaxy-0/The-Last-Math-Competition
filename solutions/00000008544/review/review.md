# Solution Review — Conjecture 00000008544 (PR 316)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003091740`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — chain product lattice = Cartesian product of total-order chains; Sperner number = max multinomial coefficient AND the maximal antichain is unique (the middle layer).
- LaTeX: compiled ok (pdflatex run twice, exit 0 both, 0 errors); included main.pdf is a real PDF (v1.5, 31874 bytes), 1 page, text matches main.tex; verification.json records pages=1.
- Lean build: fresh build after `rm -rf .lake`, exit 0, no warnings (lakefile sets `-DwarningAsError=true`); axiom printout identical to lean-verification.txt.
- Forbidden content: none — only grep hit is "external" inside a doc comment (line 45); no sorry/admit/native_decide/axiom/unsafe/implemented_by/extern.
- Auxiliary code: none shipped (verification.json `auxiliary_scripts_rerun: []`); nothing to run — nothing claimed to have run.
## Semantic audit
Conjecture literal claim (English): "The Sperner number of a chain product lattice is the maximum multinomial coefficient; and the maximal antichain is unique, namely the middle layer." The disproof refutes the uniqueness clause, which is one conjunct of the asserted conjunction — logically sufficient.

Lean definitions all faithful: `Below x y` is the coordinatewise order on `(Fin 2)^3` via `cube`/`unCube`, explicitly checked inverse maps (`cube_left_inverse`, `cube_right_inverse`); `factors_are_total_chains` and `product_is_partial_order` verify the chain-product hypotheses. `Antichain s := ∀ x y, member s x → member s y → Below x y → x = y` is genuine. `MaximumAntichain s := Antichain s ∧ ∀ a, Antichain a → cardinality a ≤ cardinality s` is "maximum" (largest size), matching SOURCE.md's interpretation note. Completeness of the subset enumeration is proved, not assumed: `every_subset_encoded (p : Element → Bool) : member (encode p) = p`.

Final theorems:
- `sharp_upper_bound : ∀ a : Subset, Antichain a → cardinality a ≤ 3` — kernel `decide` over all 256 encoded subsets.
- `rankOne_maximum : MaximumAntichain rankOne` (mask 22 = elements {1,2,4} = weight-1 layer) and `rankTwo_maximum : MaximumAntichain rankTwo` (mask 104 = {3,5,6} = weight-2 layer), `two_maximum_antichains_differ : rankOne ≠ rankTwo`.
- `conjecture8544_false : ¬ UniqueMaximumAntichain` where `UniqueMaximumAntichain := ∀ a b, MaximumAntichain a → MaximumAntichain b → a = b`.

(i) Definitions faithful (checked above). (ii) Hypotheses: $C_2^3$ is a Cartesian product of total-order chains — verified in Lean. (iii) The theorem directly negates the uniqueness clause for a genuine chain product; in $B_3$ both middle layers have size 3 = width, so "the middle layer" is not unique — the conjecture's uniqueness claim fails in the most literal way. (iv) Not vacuous: antichains, the width bound, and the chain-product structure are all present and proved; this is exactly the opposite of the rejected PR #286-288 pattern. LaTeX matches Lean: same sets {100,010,001}/{110,101,011}, same masks 22/104, same sizes and width 3, same 3-chain partition argument reproduced independently by `sharp_upper_bound`.
## Issues found
- Non-blocking: the Sperner-number = max-multinomial clause is not separately verified; the report states this explicitly. Refuting one conjunct of a conjunction suffices.
- Non-blocking: "maximal" could be read inclusion-wise; the counterexample works under both readings (both layers are also inclusion-maximal antichains), and SOURCE.md pins the "maximum" reading.
## Verdict rationale
The submission exhibits a genuine chain product ($C_2^3$) with two distinct maximum antichains, proved exhaustively in Lean by kernel `decide` over all subsets, with the chain-product hypotheses (bijective encoding, coordinatewise order, partial-order laws, factor totality) explicitly verified. Everything compiles and runs; the only axioms are standard (`propext`, `Quot.sound`). This genuinely refutes the uniqueness clause of the conjecture as stated.

## Disposition
APPROVED — merged into main (PR 316). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
