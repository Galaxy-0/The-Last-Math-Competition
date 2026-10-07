# Solution Review — Conjecture 00000001209 (PR 624)

**Submission:** AlyciaBHZ — `solutions/00000001209/AlyciaBHZ_submission_20261005101836`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

| Check | Result |
|---|---|
| Official conjecture read (`conjectures/00000001209.md`, bilingual) | pass |
| LaTeX report read in full; rebuilt with `latexmk -pdf` | pass |
| Shipped vs rebuilt PDF text (pypdf, glyph-normalized) | pass |
| `lake build` (Lean v4.33.0, Mathlib db584cd6d4, prebuilt pool) | pass |
| Axiom audit (`#print axioms`, scratch checks; allowed set only) | pass |
| `verify.py` executed; output matches shipped `verification.txt` | pass |
| No `sorry`/`native_decide`/`admit`/`extern`/`unsafe`/`axiom` | pass |
| Faithfulness gate (conjecture's own objects, no surrogate) | pass |
| Semantic audit (exact quantifiers/objects) | pass |

Build facts: `lake build` exits 0 with no errors; the only reported axioms are
`propext`, `Classical.choice`, `Quot.sound` for this PR every audited theorem depends only on `propext`, `Classical.choice`, `Quot.sound`; the Lean source
SHA-256 in `verification.txt` matches the shipped source; the rebuilt PDF has the
same page count as the shipped one and identical extracted text modulo
ligature/smart-quote glyph-extraction artifacts introduced by font subsetting.

## Semantic audit

Decisive theorems: universal_refutation (negation of the forall-t first-coordinate asymptotic) and universal_le_refutation for the non-strict convention. 'Asymptotic' is formalized as the necessary coordinatewise ratio condition; refuting it at a single t refutes the universal assertion. The game formalization is the conjecture's own object, defined from scratch (Move, well-founded isP, decidable checker, sorted enumeration). verify.py independently confirms the game recursion on [0,100]^2, the mex/Beatty formulas, and the limit ratio 0.8740... != 1.

## Issues found

None blocking. Minor: t is formalized over natural numbers while the conjecture says t>=1 (possibly real); integer counterexamples refute the universal claim over reals a fortiori, and the report's Fraenkel discussion covers the general-t behavior.

## Verdict

**APPROVED** — disproof.

Under Fraenkel's standard t-Wythoff game (remove from one heap, or from both with |k-l|<t), the conjecture's universal claim 'for every t>=1 the n-th P-position is asymptotic to (phi*n, phi*n+t*n)' fails already at t=2: the submission proves the EXACT characterization of the recursively defined P-positions of the t=2 game as {(floor(n*sqrt2), floor(n*sqrt2)+2n)} (n>=0) - via Rayleigh-Beatty complementarity, no-move-between-candidates, and reachability, all machine-checked from the raw move relation, not assumed from Fraenkel - hence the n-th smaller heap equals floor(n*sqrt2) with a_n/n -> sqrt2, and a_n/(phi*n) -> sqrt2/phi != 1, refuting the necessary first-coordinate condition (nthLower is defined via Nat.nth directly from the game's P-predicate, not from a Beatty ansatz). The non-strict convention |k-l|<=t is handled by a proved exact parameter shift (MoveLE t = Move (t+1)), refuting that reading already at t=1. The report honestly scopes what the 'explicit linear correction coefficient' wording can and cannot save and cites Fraenkel's general alpha_t formula as context. Both counterexample parameters (t=2, resp. t=1) lie in the conjectured range t>=1.
