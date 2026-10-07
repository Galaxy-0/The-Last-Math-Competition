# Solution Review — Conjecture 00000001756 (PR 711)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005133548`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (EN+CN): d(n) = #{λ ⊢ n : hook(λ) pairwise coprime} (explicit formula); a submatrix of that order selectable from irreducible-character rows sorted by dimension. `conjecture.md` byte-identical to the official file.
- LaTeX: independent rebuild exits 0 (4 pages); content matches; extraction artifacts only.
- Lean build: exit 0, 8708 jobs, zero errors/warnings.
- Forbidden content: none.
- Axioms: my independent `CheckJ6.lean` over all 40 theorems: exactly `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs verified (CRLF manifest artifacts only, including proof.tex — content verified).
- Sanity check: all six 2×2 minors and three 3×3 minors of [[1,1,1],[1,−1,1],[2,0,−1]] computed — unimodular orders {1,2}, 3×3 determinants ±6; hook lengths (3,2,1), (3,1,1), (3,2,1) all pairwise coprime. Exactly as proven.

## Semantic audit
This is the most ambitious of the twelve packages: since Mathlib has no S₃ character table, the submission constructs the representation theory from scratch inside `FDRep ℂ (Equiv.Perm (Fin 3))`. The three representations (trivial, sign, standard — the latter via explicit integer matrices in the basis f_j = e_j − e₂ of the sum-zero plane) are proven multiplicative homomorphisms, their characters are χ = 1, sgn, fix−1, each is `Simple` by Mathlib's `FDRep.simple_iff_char_is_norm_one` (the norm-1 sums are `decide`-checked over the six permutations), they are pairwise non-isomorphic (distinct characters), and — the key completeness step — any further irreducible would be orthogonal to all three, giving the linear system a+3b+2c = 0, a−3b+2c = 0, 2a−2c = 0 on the three class values, hence χ ≡ 0, contradicting norm 1. The abstraction `IsCharTable` (rows = complete irredundant irreducible list, columns = complete irredundant class list, any order) is the right notion, and `IsCharTable.reindex` proves every character table of S₃ is the integer table with rows and columns permuted.

On this foundation: `unimodular_two` exhibits the −1 minor (rows {χ₀, χ₂}, columns {(01), (012)}), `det_full_submatrix` shows every 3×3 submatrix has determinant ±6 (det = 6 with sign changes from row/column permutations), so `unimodular_le_two` caps the order at 2, and `maxUnimodularOrder_of_isCharTable` transfers this to every table in any order via `isUnimodularOrder_reindex` (integer determinants equal ±1 iff their complex casts do). On the other side, `hookCount_three` computes the right-hand side on Mathlib `Nat.Partition` objects with Ferrers diagrams and cell-wise hook lengths (arm + leg + 1): all three partitions of 3 satisfy the strongest pairwise-coprimality reading, so the count is 3 under every reading of "hook(λ) coprime", as the tex's remark explains. The main theorem `conjecture_1756_false` is then the exact failure d(3) = 2 ≠ 3 = hookCount 3, and `conjecture_1756_false_any_table` extends it to every character table — covering the "sorted by dimension" selection clause, which cannot help since no 3×3 submatrix of any table is unimodular.

The provenance note (Ferrers construction adapted with credit from the accepted C0ldSmi1e solution of conjecture 428, GPL-3.0) and the comparison with the rejected PR #214 (whose refutation was only prose) are candid and accurate.

## Issues found
- None blocking.

## Verdict
APPROVED. A complete and correct refutation at n = 3, built on genuine Lean representation theory (irreducibility, orthogonality, completeness, and a reindexing theorem over all character tables), with the hook side computed from Mathlib partition objects; build, axioms and numerics all check out.
