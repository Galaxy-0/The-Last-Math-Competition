# Solution Review — Conjecture 00000001672 (PR 629)

**Submission:** AlyciaBHZ — `solutions/00000001672/AlyciaBHZ_submission_20261005101836`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

| Check | Result |
|---|---|
| Official conjecture read (`conjectures/00000001672.md`, bilingual) | pass |
| LaTeX report read in full; rebuilt with `latexmk -pdf` | pass |
| Shipped vs rebuilt PDF text (pypdf, glyph-normalized) | pass |
| `lake build` (Lean v4.33.0, Mathlib db584cd6d4, prebuilt pool) | pass |
| Axiom audit (`#print axioms`, scratch checks; allowed set only) | pass |
| `verify.py` executed; output matches shipped `verification.txt` | pass |
| No `sorry`/`native_decide`/`admit`/`extern`/`unsafe`/`axiom` | pass |
| Faithfulness gate (conjecture's own objects, no surrogate) | pass |
| Semantic audit (exact quantifiers/objects) | pass |

Build facts: `lake build` exits 0 with no errors; the only reported axioms are
`propext`, `Classical.choice`, `Quot.sound` for this PR the theorems depend on no axioms at all (core-Lean `decide` proofs); the Lean source
SHA-256 in `verification.txt` matches the shipped source; the rebuilt PDF has the
same page count as the shipped one and identical extracted text modulo
ligature/smart-quote glyph-extraction artifacts introduced by font subsetting.

## Semantic audit

Decisive theorems: conjecture_inconsistent and formula_range_excludes_77 quantify over arbitrary cr:Nat->Nat->Nat, so they refute the literal conjunctive statement for the actual crossing number by pure instantiation; the arithmetic 81!=77 is decided by the kernel. Counterexample parameters (7,7) satisfy all stated hypotheses (min(7,7)=7<=7). The report distinguishes headline/restatement/parenthetical readings and does not overclaim the bare-iff reading.

## Issues found

None blocking. Minor observations: (1) the deep mathematical content (Woodall's computation) is cited, not formalized - appropriate since the literal statement is refuted without it; (2) the '77' versus 81 slip makes the statement false as written, and the submission documents that replacing 77 by 81 would repair only the headline, not settle the range clause.

## Verdict

**APPROVED** — disproof.

The official statement is internally inconsistent as written: it asserts both cr(K_{7,7})=77 and that the Zarankiewicz formula holds for min(m,n)<=7, but the formula evaluates to floor(7/2)*floor(6/2)*floor(7/2)*floor(6/2)=81. The Lean file (import-free, kernel-only 'decide' proofs, zero axioms) proves for every function cr the negation of the conjunction, the positive-parameter variant, that the range clause forces cr(7,7)!=77, and that the bare-iff reading is abstractly satisfiable (honestly not claimed as refuted). The isolated headline is additionally refuted by the cited Woodall (1993) computer-assisted theorem cr(K_{7,7})=81 (fact-checked by the reviewer: MathWorld confirms Woodall settled K_{7,7}=81 and the smallest unsettled cases are K_{7,11} and K_{9,9}); the submission transparently marks this citation as not formalized. Faithful to the conjecture's own objects; no surrogate; no overclaiming.
