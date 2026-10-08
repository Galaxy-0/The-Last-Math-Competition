# Verification and independent semantic review

Date: 2026-10-08 Asia/Shanghai (2026-10-07 UTC).

## Result

For the actual quotient PSL₂(F₅)=SL₂(F₅)/{I,−I}, eight explicit proper subgroups cover exactly 888 of 3600 ordered pairs. Therefore the generating probability is at most 113/150, strictly less than the conjectured 19/25 at q=5. Only the universal lower-bound clause is refuted; no claim is made about an eventual large-q amendment or the separate asymptotic assertion.

## Formal semantic audit

The full final source and mathematical report were reviewed separately from their author. The independent reviewer found no mathematical or semantic flaw.

- `slElements` enumerates all 120 determinant-one matrices with residue entries 0,…,4. `groupElements` enumerates the 60 canonical sign representatives without duplicates.
- `normalize_fibers` proves that normalization fibers are exactly the equivalence classes {M,−M}. `quotient_certificate` additionally checks normalization range, inverse compatibility and multiplication compatibility; every canonical representative is a determinant-one matrix fixed by normalization.
- `rawMul_assoc` proves genuine modular matrix associativity symbolically for arbitrary natural-number entries, using modular arithmetic and distributivity. It is not assumed and is not replaced by a finite guessed multiplication table.
- `mul_assoc` derives associativity on canonical representatives from the proved raw identity, finite raw-product closure and quotient multiplication compatibility. The reviewer checked that there is no circular dependency or weakened associativity statement.
- `matrix_group_axioms` proves closure, identity, inverse and associative laws on the concrete model.
- Each of the eight listed sets is a duplicate-free subset of this group, contains identity, is closed under products/inverses and omits the actual group element (0,1,4,3).
- `Generated` is genuine inductive group-word closure. `generated_stays` proves that every such word stays in a certified subgroup containing the generators. The same missing witness therefore rules out generation.
- `orderedPairs_nodup` ensures actual distinct pairs are counted, not an unexplained weighted list. `generatingCount` counts exactly the pairs satisfying `Generates`, using classical decidability.
- `possible_count` kernel-checks that 2712 pairs escape all eight exclusions. `generating_count_bound` proves the actual generating count is at most 2712.
- `conjecture1184_false` refutes the exact cross-multiplied inequality 19·60²≤25·generatingCount, the specialization of the conjecture at q=5.

## Actual checks

1. A fresh submission directory without prior `.lake` artifacts passed `lake build` under official Lean 4.31.0 in approximately 140 seconds.
2. `lake env lean -DwarningAsError=true Counterexample.lean` also exited 0 on the same final source in approximately 140 seconds, with no warnings.
3. Main theorem axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. Group-law and quotient theorems: exactly `propext`, `Quot.sound`.
4. Source scan and full review found no sorry, admit, custom axiom, native_decide, unsafe declaration or implementation override.
5. The independent Python checker reconstructs all determinant-one matrices and sign classes using its own arithmetic, checks representative fibers and quotient operations, all group laws, subgroup closure and properness, and verifies exactly 888 excluded pairs. Its separate exact generation count 2280/3600 is supplemental and is not presented as the Lean theorem.
6. The subgroup-code table in the report was parsed and compared against every tuple in the Lean source; all eight rows agree.
7. The final LaTeX report compiled in two passes. Both final PDF pages were rendered and visually inspected. No clipping, overlap, missing glyphs or unresolved reference was found.

The independent review was a separate AI review process, not an official competition reviewer. No acceptance claim is made.

## Formalization boundary

The project formalizes this concrete residue-matrix quotient and its group laws, not a general library classification of finite groups of Lie type. Identifying PSL₂(F₅) as type A₁ uses the standard definition of that named group. No classification theorem or A₅ isomorphism is a premise. Probability is represented by the exact generating-pair count divided by the nonzero group-order square, with the final inequality cross-multiplied over natural numbers.

## Reproduction

Use the pinned official toolchain, `lake build`, and `lake env lean -DwarningAsError=true Counterexample.lean`. There are no external Lean packages. `check_independent.py` uses only the Python standard library.

`build-pdf.sh` assumes a normal LaTeX installation. This cloud image required TEXINPUTS, TFMFONTS, T1FONTS and TEXFONTMAPS to point at the corresponding standard `/usr/share/texlive/texmf-dist` trees, and TEXFORMATS to point at an existing locally generated pdfLaTeX format. The source explicitly enables PDF output. No mathematical result depends on that formatting configuration.

## Eligibility

At the recorded check, upstream main was `6dc8261ea302809ca633aa6c0c903aa8acfacf1f`; metadata marked 00000001184 unsolved. Its solution directory returned 404. All-state PR searches for the padded identifier, unpadded identifier, Dixon and pair-generation returned zero. Responses are retained in `eligibility.json`; recheck immediately before publication.
