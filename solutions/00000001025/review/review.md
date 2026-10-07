# Solution Review — Conjecture 00000001025 (PR 678)

**Submission:** Jackmeson1 — `solutions/00000001025/Jackmeson1_submission_20261005111009`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (English + Chinese); `conjecture.md` byte-identical to the official file.
- **LaTeX report:** read in full; independently rebuilt with `latexmk` — exit 0.
- **PDF match:** normalized text of shipped vs. rebuilt PDFs differs only in math-glyph extraction artifacts (∈→2, ∪{∞} vs [f1g], ⊆, ≠, ligatures). Content identical.
- **Lean build:** `lake build` succeeded (8708 jobs, zero errors, zero warnings); the one `set_option maxHeartbeats 2000000` is a benign timeout bump for finite `decide +kernel` computations.
- **Axioms:** independent scratch `Check.lean` for `conjecture_1025_false`, `card_aut_ge`, `card_comm_le`: all exactly `[propext, Classical.choice, Quot.sound]`. All finite computations use `decide +kernel`, not `native_decide`.
- **Cheating scan:** clean.
- **Auxiliary code:** the referenced Python check (`check()` in the "attempt file") is not shipped; I reimplemented it independently in Python (GF(2^11) via x^11+x^2+1, generator polynomial ∏_{j∈N}(x−ζ^j) for ζ a primitive 23rd root of unity, parity extension, Gaussian elimination): the resulting 4096-word extended code equals W (dim 12, all generators of W are codewords). The claimed identification is verified.
- **Semantic audit:** pass (see below).
- **Sources:** the Wikipedia quotations (Binary Golay construction of W from quadratic non-residues; QR-code generator polynomial and extension; M24 consistency) match the cited pages; only the submission folder is added; metadata marks the conjecture unsolved.

## Semantic audit

The conjecture asserts that the only exception to "Aut(extended q-ary QR code) is a semidirect product of PSL(2,q) with commutative automorphisms" is q = 7. The submission exhibits a second exception: the extended binary QR code of length 23 (the extended Golay code), whose automorphism group is not such a semidirect product in either factor order. Both assignments of the letter q are covered: (R1) q = prime length 23 ≠ 7 with N = PSL(2, ZMod 23); (R2) q = alphabet size 2 ≠ 7 with N = PSL(2, ZMod 2). Since binary codes have trivial scalar/field automorphism ambiguities, the permutation automorphism group is the standard notion, and "commutative automorphisms" is covered by letting A range over all commutative groups.

The counting argument is airtight. Lower bound: a Lean-certified stabilizer chain (∞,0,1,2,3,4) with explicitly word-certified permutations moving each base point to 24, 23, 22, 21, 20, 16 distinct points gives |Aut W| ≥ 24·23·22·21·20·16 = 81,607,680 (orbit–stabilizer injection, formalized). Upper bound for a hypothetical decomposition: Mathlib's `SemidirectProduct.card` gives |Aut W| = |N|·|A|; |N| ≤ |SL(2,23)| ≤ 12144 via the injective (A,u) ↦ diag(u,1)A trick and `Matrix.card_GL_field`; the commutative factor A embeds in Sym(24), and a commutative subgroup of S_n has order ≤ 3^{n/3} — proved by a clean induction (the stabilizer of a point in a commutative group fixes its orbit pointwise; |A| ≤ |O|·|A_x|; k³ ≤ 3^k) giving |A|³ ≤ 3^24, i.e. |A| ≤ 3^8 = 6561. Then |Aut W| ≤ 12144·6561 = 79,676,784 < 81,607,680, a contradiction. Both factor orders (N normal via `inr`, A normal via `inl`) are handled.

The identification W = extended binary QR code is the one step not done in Lean; the report says so explicitly and supports it by the Wikipedia construction (which defines G24 as exactly this span of translates of the non-residues plus the all-ones word) and by a Python check. My independent reproduction confirms it: over GF(2^11) with a primitive 23rd root of unity ζ, the cyclic code with generator ∏_{j∈N}(x−ζ^j) (degree 11, dimension 12) extended by a parity bit equals W as a set of 4096 words (equivalently, the idempotent 1_N generates it and all-ones is a codeword). Equivalence-class invariance of automorphism groups makes this sufficient for the conjecture's "the" extended QR code. Consistency: M24 has order 244,823,040 ≥ 81,607,680.

Sanity check: |PSL(2,23)| = 23·(23²−1)/2 = 6072 ≤ 12144 ✓; PSL(2,2) ≅ S3 has order 6 ≤ 12144 ✓; the classical theory (QR codes exceptional at length 8, and M24 for length 24) is fully consistent with 23/2 being an exception other than 7.

## Issues found

- The W ≅ extended-QR identification rests on cited sources plus a Python check rather than Lean; it is transparently disclosed, and my independent recomputation confirms it exactly (with the non-residue generator and any primitive 23rd root of unity; the residue generator gives the companion code).
- The Lean statements record the common bound |N| ≤ 12144 for both PSL(2,23) and PSL(2,2); this is weaker than exact orders but sufficient and non-misleading.

## Verdict

APPROVED. A complete, machine-checked counting disproof with both readings of q covered; the single extra-Lean identification was independently verified by me; build and axiom audit are clean.
