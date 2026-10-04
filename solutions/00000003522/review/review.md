# Solution Review — Conjecture 00000003522 (PR 453)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004114409`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read; `SOURCE.md` is byte-identical to the official file.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded, producing the same one-page semantic report as the shipped PDF after ligature/line-break extraction normalization; no TeX warnings.
- Lean: official pinned dependencies were linked, then fresh `lake build` and direct `lake env lean -DwarningAsError=true Main.lean` succeeded under Lean 4.19.0/Mathlib `c44e0c8e...`.
- Axioms: all nine printed results depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external implementation, or kernel bypass occurs.
- Auxiliary programs: none supplied or needed; both universal cancellation laws and the explicit ordinal counterexample are formalized directly.
- Base metadata marks the conjecture unsolved.

## Semantic audit
If `β<γ`, the defining lower-set property of Hessenberg natural addition gives `α#β<α#γ`; symmetry gives strict monotonicity in the first argument as well. Hence fixing either argument yields an injective map, so
`α#β=α#γ ↔ β=γ` and `β#α=γ#α ↔ β=γ`.
The converse directions follow by substitution. This proves cancellation for arbitrary ordinals.

For the contrasting ordinary operation, `0+ω=ω` and, by continuity at the limit, `1+ω=ω`, although `0≠1`; therefore ordinary ordinal addition is not right-cancellative. The submission correctly retains the true ordinary left-cancellation direction rather than claiming both directions fail.

The Lean file uses Mathlib's genuine `Ordinal.{u}` and `Ordinal.nadd`, with arbitrary universe `u`. It derives strict monotonicity from `Ordinal.lt_nadd_iff`, proves both cancellation equivalences, constructs the actual ordinal `ω` counterexample, negates universal ordinary right cancellation, proves ordinary left cancellation, and shows natural addition distinguishes the same witness. The final theorem combines exactly the source's natural cancellation assertion and ordinary-addition contrast, with no problem-specific hypothesis.

## Issues found
None blocking.

## Verdict
APPROVED. The standard theorem is correctly proved for all ordinals, the contrasting ordinary-addition counterexample is explicit, and all independent build and axiom checks pass.
