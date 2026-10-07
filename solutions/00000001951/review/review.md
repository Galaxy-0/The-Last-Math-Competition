# Solution Review — Conjecture 00000001951 (PR 658)

**Submission:** Jackmeson1 — `solutions/00000001951/Jackmeson1_submission_20261005082650`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

| Check | Result |
|---|---|
| Official conjecture read (EN+ZH); submission `conjecture.md` diffed against `conjectures/00000001951.md` | pass (byte-identical) |
| Extraction integrity | pass (all 15 files match `refs/remotes/pr/658` git blob hashes) |
| `proof.tex` read in full; PDF rebuilt with `latexmk -pdf` | pass |
| Shipped vs rebuilt PDF compared | pass (4 pages both; text identical modulo glyph-extraction artifacts (`·`, `≠`); rendered pages visually identical, ~1% anti-aliasing/hinting pixel noise) |
| `lake build` | pass (Build completed successfully, 8708 jobs, zero errors) |
| Cheating grep (`sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, `axiom`) | pass (clean) |
| `#print axioms` on all decisive theorems (independent `Check.lean`, all 6: `smallest_index_ne`, `not_all_index_ge`, `sInf_properIndices`, `exists_normal_index_two`, `K_index`, `outDet_surjective`) | pass (only `propext`, `Classical.choice`, `Quot.sound`) |
| Auxiliary code (`verification/axioms.txt`, `build.txt`, `SHA256SUMS.txt`) | pass (axiom and build outputs reproduced exactly; see issue below on the sums manifest) |
| Faithfulness | pass (genuine `Out(F_n) = MulAut (FreeGroup (Fin n)) / (MulAut.conj).range`; explicit exponent-sum abelianization; no toy instantiation, no assumed hypothesis) |
| Semantic audit | pass (see below) |
| Independent mathematical sanity check | pass (determinant character argument is textbook-correct) |

## Semantic audit

The official conjecture (both language versions) is the conjunction, for every n >= 3, of
(a) Out(F_n) fails the congruence subgroup property (with the parenthetical that its smallest-index
proper subgroup is an automorphism kernel), and
(b) the smallest index of a proper subgroup of Out(F_n) equals 2^n * C(n,2).

The submission is a **disproof**: it establishes `C1951.smallest_index_ne : 3 ≤ n → sInf (properIndices n) ≠ 2^n * n.choose 2`, the exact negation of clause (b) in the conjecture's own quantifier range, which negates the conjunction. The counterexample satisfies all stated hypotheses:

- `Out n := MulAut (F n) ⧸ Inn n` with `F n := FreeGroup (Fin n)` and `Inn n := (MulAut.conj).range` — the conjecture's own object, not a surrogate.
- The determinant character `outDet : Out n →* Z^x` is well defined because `Inn_le_ker` shows inner automorphisms have `det(mat φ) = 1`; `outDet_surjective` for `1 ≤ n` is witnessed by `flip ⟨0, hn⟩` (invert the first generator), with `det_flip : det (mat (flip i₀)) = -1`.
- `K_index : (K n).index = 2` (kernel of a surjective map to `Z^x`, `Fintype.card_units_int`), so `exists_normal_index_two` gives a proper normal subgroup of index 2; `sInf_properIndices` shows the minimum over proper finite-index subgroups is exactly 2 (index 0 excluded via `FiniteIndex`, index 1 excluded via properness).
- `two_lt : 2 ≤ n → 2 < 2^n * n.choose 2`, so for every n >= 3 the conjectured value 2^n*C(n,2) (24 at n=3) is not the minimum.

The reading "proper subgroup" as proper finite-index subgroup is innocuous: the exhibited index-2 subgroup exists under either reading and the minimum of 2 dominates any reading that admits infinite index. The exhibit is normal, so the "proper normal subgroup" reading is refuted as well. The submission explicitly does not address the CSP clause (a) — correct and sufficient, since one false conjunct falsifies the conjecture.

## Issues found

1. Minor hygiene (non-blocking): `verification/SHA256SUMS.txt` lists stale checksums for `conjecture.md` and `lean/Conjecture1951/Basic.lean` (the shipped final versions of these two files postdate the manifest). The actual files match the PR head byte-for-byte and build cleanly; all other manifest entries verify. Does not affect correctness.

## Verdict

**APPROVED.** Correct, faithful, fully machine-checked disproof of the stated minimum-index clause (and hence of the conjecture as written), with a transparent statement of scope.
