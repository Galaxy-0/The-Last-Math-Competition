# Solution Review — Conjecture 00000008197 (PR 614)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261004234258`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-05

## Verification

The official bilingual statement, full LaTeX, all PDF pages, and all Lean/source and audit files were reviewed. Only the declared submission folder was added. Base metadata marks 00000008197 unsolved and no prior solution existed; the included conjecture text is byte-identical to the official source. The PDF was independently rebuilt twice with `xelatex`; both passes exited 0, both versions have three pages, and extracted text is identical after whitespace normalization. The Lean 4.33.1/Mathlib `0df444a…` project was independently linked and built; `lake build`, direct warning-as-error checks, and the axiom audit all exited 0. The main theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. No executable forbidden shortcut or kernel bypass is present.

An independent enumeration through genus 8 reproduced the numerical-semigroup totals, the two genus-2 gap sets, least nonsymmetric genus 2, both symmetry criteria, and the reported uniform symmetric shares. The source checksum manifest has stale hashes only for `conjecture.md` and `proof.tex`; actual contents were independently verified and rebuilt, so this is non-blocking.

## Disproof

Under the literal numerical-semigroup reading, `{0}∪{n≥3}` has gaps `{1,2}`, genus 2, and Frobenius number 2. It is nonsymmetric because the gap 1 reflects to itself. Since every genus-0 or genus-1 numerical semigroup is symmetric, nonsymmetric semigroups first occur in genus 2, contradicting the claimed least genus 3.

Under the proper-Weierstrass-point reading, every genus-2 numerical semigroup has gaps `{1,2}` or `{1,3}`. The non-ordinary possibility is necessarily `{1,3}`, i.e. `<2,5>`, and is symmetric. Thus every probability distribution on proper-point semigroups puts mass 1 on symmetric semigroups, whereas the exact claimed concentration at genus 2 is `1-2^{-2}=3/4`. This contradiction is non-vacuous and covers every distribution induced by random curves.

**Disposition: APPROVED.**
