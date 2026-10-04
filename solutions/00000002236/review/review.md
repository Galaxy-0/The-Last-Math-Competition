# Solution Review — Conjecture 00000002236 (PR 490)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004152700`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — a fixed coprime degree-two pair has unbounded composite-orbit gcds.
- Eligibility: base metadata is unsolved; PR adds only its own correctly named directory.
- LaTeX: independent build exit 0, one A4 page, no substantive warnings; shipped/fresh content matches.
- Lean: official shared pinned dependencies linked; `lake build` exit 0 (`[2793/2794] Built Main`) and direct warnings-as-errors elaboration exit 0.
- Axioms: only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none.
- Auxiliary computation: none needed.

## Semantic audit

`f=X²` and `g=X²−1` are coprime via `f−g=1`, with both degrees 2. Iterating `f` gives `X^{2^k}`. Since `g∘g=X²(X²−2)`, the even iterates `q_k=g^{∘2k}` satisfy `q_{k+1}=q_k²(q_k²−2)`, from which induction proves `X^{2^k} | q_k`. Hence the polynomial gcd of `f^{∘k}` and `g^{∘2k}` is monic `f^{∘k}` and has degree `2^k`, unbounded. Evaluation at 2 gives the exact integer gcd `2^{2^k}`, also unbounded. Lean formalizes actual composition, coprimality, recurrence, divisibility, polynomial and integer gcds, and every-bound unboundedness, so both plausible readings of the official claim fail.

## Verdict

APPROVED — the counterexample is elementary, exact, fully formalized, and independently reproducible.
