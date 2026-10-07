# Solution Review — Conjecture 00000009994 (PR 822)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261006164343`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture read in full (bilingual) from `conjectures/00000009994.md`; shipped `conjecture.md` is byte-identical to it (`diff` clean). The Chinese Definition line is garbled; the submission reads the conjecture through the English Definition line, which is the right call.
- LaTeX: full `.tex` read; `latexmk -pdf -interaction=nonstopmode` rebuild in a scratch dir succeeds with 0 errors. Shipped vs rebuilt PDF text compared with pypdf: identical word-for-word; all differences are glyph-mapping extraction artifacts (≤, →, ∈, {, }, ⊥, ·, −, ≥, ∞ extracted as control characters or stand-in glyphs by the author's TeX; ligature forms in the shipped file). Cosmetic.
- Lean build: `lake build` from scratch against the prebuilt pool, 0 errors, 0 warnings (Lean 4.33.1, Mathlib v4.33.1, rev 0df444a360 pinned identically by `lake-manifest.json`).
- Axioms: `#print axioms` re-run independently for `conjecture_9994_false`, `headline`, `family`, `pd_last`, `loewyLength_eq_two` — all report exactly `propext, Classical.choice, Quot.sound`. Grep for `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/`axiom`: only audit prose hits.
- Aux code: `Axioms.lean` output matches shipped `verification/axioms.txt` exactly; `verification/build.txt` is a consistent fresh-build log (author's Windows machine, same 8708-job graph). All 14 entries of `verification/SHA256SUMS.txt` reproduce over the shipped files; the four "mismatches" are pure CRLF/LF line-ending artifacts (CRLF-normalized hashes match exactly).
- Metadata: `metadata.csv` lists 00000009994 as `proven=false, disproven=false` (unsolved); no competing solution folder.

## Semantic audit

The conjecture asserts that the finitistic dimension of a finite-dimensional algebra is controlled by twice the Loewy length, with the doubling coefficient optimal, attained by subalgebras of exterior algebras, and the bound independent of quiver size. Its testable core is the bound clause: findim(A) ≤ 2·LL(A) for every finite-dimensional k-algebra A, or more weakly findim(A) ≤ f(LL(A)) for some f.

The submission proves the negation of this clause, under four readings (standard/literal findim × exact/functional bound), with one explicit family: Λ_{m+1}, the radical-square-zero algebra of the linear quiver with m+1 vertices, formalized genuinely as `TrivSqZeroExt (Fin (m+1) → k) (Fin m → k)` with the twisted arrow bimodule. Lean proves with Mathlib's `Ring.jacobson` and `Ideal.mem_jacobson_iff` that J = {a : a.fst = 0}, J² = 0, J ≠ 0, so `loewyLength = 2`. The simples S_j and indecomposable projectives P_{i+1} = Λe_{i+1} are constructed with explicit retracts into Λ (projectivity), the sequences 0 → S_i → P_{i+1} → S_{i+1} → 0 are proven short exact, and S_{i+1} is proven non-projective by the arrow obstruction (a section s with s(1) = (1,t) forces α_i·s(1) = (0,1) ≠ 0 = s(α_i·1)). Mathlib's `hasProjectiveDimensionLT_X₃_iff` then gives pd S_j = j by induction; since S_m is one-dimensional and has pd m, `finitisticDimension ≥ m`. The headline instance m = 5 gives findim(Λ_6) ≥ 5 > 4 = 2·LL(Λ_6), and m = f(2)+1 refutes every function-of-LL bound, hence also every c·LL + d bound.

The formalization is faithful. The decisive theorem quantifies over exactly the conjecture's objects: genuine finite-dimensional algebras (`Module.Finite k A` hypothesis in `DoublingBound`/`LoewyControlled`), the standard little finitistic dimension (supremum of Mathlib's `projectiveDimension` over finite-dimensional modules of finite projective dimension), and the actual Jacobson radical with subspace powers for the Loewy length. The counterexample is not a toy surrogate: it is the canonical representation-theoretic family showing findim is unbounded at fixed Loewy length (pd S_j = j for the linear quiver kQ/J² is classical). Refuting one conjunct of a conjunction is a valid refutation; leaving optimality and exterior-algebra attainment abstracted as `Rest` is logically sound.

The mathematics is correct, and I verified it independently of the Lean proof: numerically over ℚ for Λ_6 (associativity of the multiplication; J² = 0; the Jacobson criterion in both directions — z = 1 − yx for x ∈ M, and the coordinate obstruction for vertex-supported x; linearity and exactness of every sequence in the chain; the non-splitting obstruction at every level). Dimension shifting then forces pd S_5 = 5 > 4. This matches the known fact that the finitistic dimension of a radical-square-zero algebra equals the maximal path length, which is unbounded while LL = 2 — so the conjecture's first clause (and its "independent of quiver size" rider) is genuinely false.

## Issues found

None blocking. Non-blocking notes:
- `verification/SHA256SUMS.txt` was computed over CRLF versions of `conjecture.md` and `proof.tex`; the shipped files are the LF-normalized archive renders. Content is otherwise byte-identical (CRLF-normalized hashes match).

## Verdict

APPROVED. A complete, faithful, machine-checked disproof of the conjecture's central clause: an explicit two-parameter-free family of finite-dimensional algebras with Loewy length 2 and arbitrarily large finitistic dimension, refuting both the exact doubling bound and every bound depending only on the Loewy length, over every field, under both readings of the Definition line. Build clean, axioms clean, LaTeX/PDF consistent, shipped conjecture copy verbatim.
