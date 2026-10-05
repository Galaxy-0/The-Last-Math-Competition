# Solution Review — Conjecture 00000001141 (PR 580)

**Submission:** jilint777 — `jilint777_submission_20261004190201`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read (`conjectures/00000001141.md`): the claim is that `Kdim Z(u(slₙ)) = n−1` (from the p-centres of the sl₂-sections) and that for every reductive `g` the centre of `u(g)` is spanned by the Weyl-invariant p-centre polynomial ring with dimension equal to the rank.
- LaTeX report independently rebuilt with `latexmk -pdf`: clean build; extracted text identical to the shipped `report.pdf` after normalizing itemize-bullet glyph extraction (same length, no content differences).
- Lean: fresh `lake build` on `leanprover/lean4:v4.19.0` succeeds, zero errors/warnings; build log identical to the one embedded in `verification.txt`.
- `#print axioms` (Main.lean lines 1068–1076): only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`/`native_decide`/`axiom`/`unsafe`/`implemented_by`/`extern`/`admit` anywhere in the project.
- `verify.py` rerun: 50 PASS, 0 FAIL, output identical to `verification.txt` (when run from the submission directory it also PASSes the check that the six Lean operator tables equal the left/right multiplication tables obtained independently by word rewriting).
- Independent recomputation (reviewer's own code, different method): built `u(sl₂)/F₃` by normal-ordering rewriting; verified the relations and associativity (left/right multiplication commutation); computed `dim Z = 4` with basis containing exactly `1` and `h+h²+ef` (= the report's `z₂`) and `e²hf²+2e²h²f²` (= `2·z₄`), confirming the submission's tables and the structure `Z ≅ F₃ × F₃[x,y]/(x,y)²`.

## Semantic audit
The conjecture's first clause is `Kdim Z(u(slₙ)) = n−1`. The submission's refutation is the standard and correct observation that `u(g) = U(g)/(x^p − x^[p])` has dimension `p^(dim g)` (Jacobson's PBW theorem), so its centre is a finite-dimensional commutative algebra; any prime quotient of it is a finite-dimensional domain, hence a field (multiply-by-x is injective, thus surjective), so every prime is maximal and there are no strict chains of primes: the Krull dimension is `0 ≠ n−1` for every `n ≥ 2`, every prime `p`. The true statement the conjecture garbles — `Kdim Z(U(slₙ)) = n−1` in characteristic 0 (Harish-Chandra/Chevalley) — is correctly identified in the report, as is the char-p fact `Kdim Z(U(slₙ)) = n²−1`; the report handles these alternative readings honestly.

The Lean formalization instantiates this at `n = 2`, `p = 3`. It builds from scratch the field `F₃`, the space `V = F₃²⁷` with PBW basis `e^a h^b f^c`, six sparse operator tables, and the generated algebra `A ⊆ End(V)`. The decisive theorems are all machine-checked: `relations` (the six defining relations of `u(sl₂)` hold in `A`, by `decide` over all basis vectors), `ev_bijective` (evaluation at `1` is a bijection `A → V`, so `|A| = 3²⁷`), a general `CRing` library with `IsIdeal`/`IsPrime`/`HasChain`/`KrullDimIs`, a formalized pigeonhole argument giving `primes_incomparable` and `finite_krullDim_zero`, the explicit prime `P₀ = ker χ` (the counit) for non-vacuity, and `krullDim_center : KrullDimIs 0`, hence `conjecture_00000001141_false : ¬ KrullDimIs (2−1)`. The definitions are faithful: `KrullDimIs d` is exactly "supremum of lengths of chains of prime ideals equals d", `ZU`/`ZRing` is exactly the centre with its commutative ring structure, and `Clause n := ZRing.KrullDimIs (n−1)` matches the official text's "the Krull dimension of the center of u(slₙ) is n−1" read at `n = 2`.

The one step not formalized — `A ≅ u(sl₂)` — is correctly argued in the report: the relations give a surjection `u(sl₂) → A` by the universal property, PBW spanning (Prop. 5, proved elementarily in the report via the commutation formulas of Lemma 4, which I checked) gives `dim u ≤ 27`, and `ev_bijective` gives `|A| = 3²⁷`, so the surjection is an isomorphism. The submission states this limitation explicitly. Moreover the disproof does not depend on the model: the general finite-dimensional argument (Theorem 3) is self-contained, and I re-verified the concrete numerics independently (dim Z = 4, the centre basis, and hence the two maximal primes and `Kdim = 0`).

The second clause ("dimension always equal to the rank") is also refuted: in `u(g)` the p-centre generators `x^p − x^[p]` vanish, so the p-centre spans only scalars, while Lean proves `casimir_central` and `casimir_not_scalar` (`center_not_rank_dim`: Z is not a one-dimensional `F₃`-span), so `dim Z(u(sl₂)) ≥ 2 > 1 = rank sl₂` (in fact `= 4`, per verify.py and my recomputation).

## Issues found
None blocking. The `A ≅ u(sl₂)` bridge rests on the report's (correct, standard) PBW argument rather than being formalized; the submission discloses this, and the fully formal parts (relations, cardinality, finite-ring Krull dimension zero) plus two independent recomputations leave no doubt.

## Verdict
APPROVED. The mathematical content is right, the Lean development genuinely proves Krull dimension 0 for the centre of a concrete, certified model of `u(sl₂)/F₃` with only the three standard axioms, the quantifier structure (the conjecture asserts equality for all `n`; refuting `n = 2` refutes it) matches the official bilingual text, and every auxiliary artifact (verify.py, verification.txt, PDF) reproduces exactly.
