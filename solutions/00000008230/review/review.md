# Solution Review — Conjecture 00000008230 (PR 382)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004030302`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — four conjuncts about Adams operations ψ^k on characters: spectral support scaled by k; fixed class functions have k-regular-class basis; dim Fix(ψ^k) = #k-regular classes; composition law with Stiefel sign correction.
- LaTeX: compiled (pdflatex twice, exit 0 both passes); shipped report.pdf is a real PDF (v1.5), extracted text matches report.tex (including the boxed 2 ≠ 3 statement).
- Lean build: exit 0, "[1388/1389] Built Main", "Build completed successfully.", zero warnings/errors; axiom audit: `'Adams8230.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- Forbidden content: none. Only grep hit is VERIFICATION.md:52 English prose ("No additional axioms, incomplete proofs, `sorryAx`, or `native_decide` occur..."). No tactic-level `sorry`/`admit`, no `native_decide`, no `axiom` declarations, no `unsafe`/`extern`/`implemented_by`/`skipKernelTC`. Finite group facts use kernel-checked `decide`.
- Auxiliary code: none claimed ("The proof needs no auxiliary numerical program"). I independently recomputed with my own Python/numpy code: for C₃, dim Fix(ψ²) on class functions = 2 (nullity of the squaring-permutation matrix minus I) while #2-regular classes (order coprime to 2) = 3 → not equal; also cross-checked on the representation ring R(C₃) (ψ² permutes irreps (0)(1 2), fixed dim 2), and noted k = 3 gives 1 = 1 (equality holds there), confirming k = 2 is a genuine discriminating case, not a fluke.
## Semantic audit
Conjecture (EN): "the dimension of the fixed subspace equals the number of k-regular classes (a regular count law)"; (CN: "不动的维数（不动子空间的维数）= k-正则类数（正则计数律）"), within "class functions fixed by ψ^k". The submission refutes exactly this conjunct for G = C₃, k = 2; refuting one conjunct of the conjunctive claim refutes the conjecture, and the README/report state this scope honestly.

Lean encodings (all genuine Mathlib objects):
- `abbrev G := Multiplicative (ZMod 3)` with derived `Fintype`; `theorem cube_one (g : G) : g ^ 3 = 1` and `square_eq_one_iff` by kernel `decide`.
- `def adams (k : ℕ) (f : G → ℂ) (g : G) : ℂ := f (g ^ k)` — the literal ψ^k(f)(g) = f(g^k).
- `def IsClassFunction (f : G → ℂ) : Prop := ∀ x g, f (x * g * x⁻¹) = f g` with `every_function_is_class` (abelian group) — matches the conjecture's "class functions" domain.
- `def RegularElement (g : G) : Prop := Nat.Coprime (orderOf g) 2` — standard k-regularity (order coprime to k), using Mathlib `orderOf`; `all_regular` proved since order divides 3.
- `def RegularClass (c : ConjClasses G) : Prop := ∃ g, ConjClasses.mk g = c ∧ RegularElement g` — genuine conjugacy-class quotient; `regular_class_count : Fintype.card {c // RegularClass c} = 3` via `ConjClasses.mkEquiv` (abelian) + `decide`.
- `def fixedClassFunctions : Submodule ℂ (G → ℂ)` with carrier `{f | IsClassFunction f ∧ adams 2 f = f}`; submodule axioms proved.
- `noncomputable def coordinates : fixedClassFunctions ≃ₗ[ℂ] (ℂ × ℂ)` — f ↦ (f 1, f a) with explicit inverse (u,v) ↦ (u,v,v); `left_inv`, `right_inv`, `map_add'`, `map_smul'` all proved (third-group-element case uses the fixed-point equation f(a²) = f(a)).
- `theorem fixed_dimension : Module.finrank ℂ fixedClassFunctions = 2` via `coordinates.finrank_eq`.
- Final: `theorem counterexample : Module.finrank ℂ fixedClassFunctions ≠ Fintype.card {c : ConjClasses G // RegularClass c}` — i.e. 2 ≠ 3.

(i) Faithful: yes — ψ^k, class functions, conjugacy classes, element orders, and k-regularity are all standard Mathlib notions; nothing supplied as unproved data. (ii) Hypotheses: C₃ is a legitimate finite group, k = 2 a legitimate Adams index. (iii) 2 ≠ 3 contradicts the regular count law under the standard (Brauer-style coprime-order) reading of k-regular; robustness check — under the alternative reading "classes fixed by the k-power map" the count is 1, still ≠ 2, so the disproof survives the ambiguity. (iv) Non-vacuous: both sides are computed quantities of constructed objects. This is not a numeric-facts-only proof: the dimension comes from a proved linear equivalence, the class count from a proved bijection plus kernel `decide`.
## Issues found
none blocking
## Verdict rationale
The "dimension of the fixed subspace = number of k-regular classes" conjunct is genuinely false for C₃ at k = 2 (dim 2 vs 3 classes, since squaring fuses the two non-identity classes' values), and the submission proves both sides in Lean from faithful Mathlib definitions with only standard axioms. My independent computation confirms the numbers and that k = 2 is a discriminating case (k = 3 would satisfy the equality). Scope (refuting one conjunct of a conjunction) is legitimate and clearly disclosed.

## Disposition
APPROVED — merged into main (PR 382). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
