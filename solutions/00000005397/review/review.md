# Solution Review — Conjecture 00000005397 (PR 415)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004054258`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results

- Conjecture read: yes — the conjecture asserts that a two-dimensional torus-translation orbit is dense iff the two frequency components are linearly independent over `Q`; the submission refutes the sufficiency direction with the actual frequency family `(sqrt2,1)`.
- Eligibility: base metadata records `proven=false`, `disproven=false`, no prior solver; PR inventory adds only the properly named submission directory.
- LaTeX: independently rebuilt with `latexmk -pdf -interaction=nonstopmode -halt-on-error`; exit 0, two US Letter pages, no errors or overfull/undefined-reference warnings. Shipped and fresh PDFs have identical page counts/dimensions and matching complete text content; both pages rendered and inspected.
- Lean: independently rebuilt from the fresh copied project with Lean 4.19.0 and pinned Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; `lake build` exit 0 and “Build completed successfully”; `lake env lean Main.lean -DwarningAsError=true` exit 0.
- Axioms: all printed principal theorems, including `counterexample`, depend only on `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: none. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `implemented_by`, `extern`, or kernel-check bypass appears in source.
- Auxiliary programs: none shipped; no unverified computational output is relied upon.

## Semantic audit

The conjecture's density criterion is false for the ordinary fixed-map torus translation. Take `T=(R/Z)^2`, frequency vector `alpha=(sqrt2,1)`, and increment `theta=([sqrt2],[1])=([sqrt2],0)`. The real components are `Q`-linearly independent: `a*sqrt2+b=0` with rational `a,b` forces `a=0` (otherwise `sqrt2=-b/a` would be rational) and then `b=0`. But `[1]=0` in `R/Z`, so every integer iterate `x+n*theta` has second coordinate exactly `x_2`. The entire orbit lies in the closed proper fiber `F_x={y:y_2=x_2}`, while `(x_1,x_2+[1/2])` lies outside it because `[1/2]!=0`. Hence no orbit is dense, contradicting independence-to-density. The forward orbit is a subset of the full integer orbit, so its density would imply the impossible density of the latter.

The Lean proof formalizes the actual objects: Mathlib `AddCircle (1:R)` and its product two-torus; the real family `(sqrt2,1)` with actual `LinearIndependent Q`; the corresponding circle increment; actual translation/inverse/integer orbit and forward iterates; continuity and inverse identities; a closed proper coordinate fiber; and `Dense` negations for every starting point. `theta_from_frequency` prevents any substitution of unrelated objects, `theta_second` proves the integer-period identity, and `half_nonzero` proves the fiber is genuinely proper. The final theorem combines independence, continuity, and non-density of every integer and forward orbit. No conclusion is assumed and no theorem is vacuous.

The report and Lean statement correspond exactly. It honestly limits the claim to the standard fixed-map/discrete-orbit reading and explicitly says that the remaining closure-count and unique-ergodicity conjuncts are not separately claimed. Since a single valid counterexample already refutes the conjecture's biconditional density criterion, this scope is sufficient.

## Issues found

- Non-blocking interpretation disclosure: the original does not explicitly distinguish discrete and continuous time. The submission openly uses and states the standard fixed-translation-map convention and does not claim the continuous-flow theorem.

## Verdict

APPROVED — the counterexample is mathematically decisive, the report and PDF are independently reproducible, and the complete Lean formalization passes warnings-as-errors with only the standard permitted axioms.
