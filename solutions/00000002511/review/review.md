# Solution Review — Conjecture 00000002511 (PR 765)

**Submission:** Jackmeson1 — `solutions/00000002511/Jackmeson1_submission_20261005214132`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (`conjectures/00000002511.md`, English + Chinese); shipped `conjecture.md` copy is **byte-identical** to it (`diff` clean).
- **LaTeX**: entire `proof.tex` (171 lines) read; `latexmk -pdf` rebuild in a scratch dir succeeds. Rebuilt PDF text vs shipped PDF text (pypdf, whitespace-normalized): content matches; differences are glyph-extraction artifacts only (OT1 braces read as `f`/`g`, `|` as `j`, ⊗/⊙/≥/∈/→ as control chars or wrong glyphs, ∑/∏ as `P`/`Q`, one hyphenation break) — cosmetic.
- **lake build**: succeeds with **zero errors, zero warnings** on Lean 4.33.1, Mathlib v4.33.1 (rev `0df444a360`, prebuilt pool), 8708 jobs.
- **Axioms**: independent scratch `Check.lean` audit of `C2511.symmetric_tensors_are_forms`, `C2511.symToForm_bijective`, `C2511.symToForm_symProd`, `C2511.eval_toPoly`, `C2511.finrank_symTensors` — each reports exactly `[propext, Classical.choice, Quot.sound]`.
- **No cheating**: grep for `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, declared `axiom`: only hits are the `#print axioms` audit lines in `Axioms.lean`.
- **Aux code**: `verification/axioms.txt` and `verification/build.txt` claims reproduce exactly on a fresh build. SHA256SUMS.txt mismatches (`conjecture.md`, `lean/Conjecture2511/Basic.lean`, `proof.tex`) are CRLF-vs-LF line-ending artifacts of the Windows authoring environment; content is identical.
- **Metadata**: `metadata.csv` lists 00000002511 with `proven=false`, `completed_by_ai=false` — unsolved before this PR.

## Semantic audit

The conjecture states that the symmetric version of tensors corresponds to homogeneous polynomials: symmetric tensors are forms, and the dictionary closes under homogeneous polynomials. This is the classical dictionary Sym^d(V) ≅ (homogeneous polynomials of degree d on V) — here over a field of characteristic 0, the standard setting of the result (Comon–Golub–Lim–Mourrain, cited), where the correspondence holds and is multiplicative.

The decisive theorem `C2511.symmetric_tensors_are_forms` proves, for a char-0 field `K`, any `K`-vector space `V` with finite basis `b`, and all degrees `d, e`: (1) every symmetric d-tensor maps under the dictionary `toPoly b d` to a form in `MvPolynomial.homogeneousSubmodule ι K d`; (2) the restricted dictionary `symToForm b d` is a linear bijection, giving the isomorphism `symEquiv b d : Sym^d V ≃ₗ K[X]_d` (with the finrank corollary `finrank_symTensors`); (3) the symmetric product `T ⊙ U = symz(T ⊗ U)` (averaging symmetrization) is sent to the product of the two forms; (4) conversely, `(symEquiv b (d+e)).symm (p*q)` equals the symmetric product of the preimages of `p` and `q`. The `eval_toPoly` theorem gives the dictionary its intrinsic meaning: evaluating the polynomial of T at the coordinates of a functional φ yields T(φ,…,φ) — guarding against a dual-space misreading.

The formalization uses the conjecture's own objects: `TPow K V d` is the genuine iterated tensor product (`PiTensorProduct` over `Fin d`), permutations act by `PiTensorProduct.reindex` of the factors, symmetric tensors are the fixed points of all of `S_d`, and forms are Mathlib's `MvPolynomial.homogeneousSubmodule`. This is no toy surrogate. The proof is correct: coordinates of a symmetric tensor are constant on content fibres (`exists_perm_of_content_eq` glues fibre bijections via `Equiv.ofFiberEquiv`), so the coefficient of X^α in the image is |F_α|·(common coordinate), which is nonzero exactly because char K = 0 makes the fibre cardinality invertible — injectivity (`toPoly_eq_zero`); conversely the normalized orbit sum over each nonempty fibre maps to the monomial X^α (`exists_sym_monomial`), and the degree-d monomials span the forms (`homogeneousSubmodule_eq_finsupp_supported`) — surjectivity. The multiplicative part is proved by reducing to pure tensors, where the product of linear forms splits via `Fin.prod_univ_add`, and symmetrization does not change the image (`toPoly_symz`, using d!·(d!)⁻¹ = 1 in char 0). I checked the characteristic-0 necessity myself: without it, in degree p and dimension ≥ 2, the orbit sum with p−1 copies of b₁ and one copy of b₂ maps to p·X₁^(p−1)X₂ = 0 while being nonzero — so the char-0 hypothesis is the right standard setting and is disclosed, not smuggled (the package claims nothing in other characteristics). The vague closing clause "the dictionary closes under homogeneous polynomials" is read as closure under products of forms, in both directions — a reasonable and explicitly declared reading; the averaging normalization of ⊙ is likewise declared. Quantifier structure is clean (all degrees, all symmetric tensors, both product directions); no conclusion is weakened.

## Issues found

None blocking. (The explicit dimension formula C(n+d−1, d) and positive characteristic are honestly declared out of scope; neither is part of the stated conjecture.)

## Verdict

APPROVED. The submission proves the full symmetric-tensors/forms dictionary — homogeneity, linear isomorphism, and multiplicative closure in both directions — on the genuine objects (tensor powers, permutation action, homogeneous polynomials) in the standard characteristic-zero setting, from scratch, with a clean build, standard axioms only, and a report that matches the Lean development exactly.
