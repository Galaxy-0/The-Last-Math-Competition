# Solution Review — Conjecture 00000002311 (PR 522)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004170613`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — it states the lower bound \(c/|\Omega|\) with \(c=1/2\) and says tightness of this corrected constant is verified by Frobenius groups.
- Change scope: only the allowed submission directory was added. Base metadata marks the problem unsolved and no prior solution existed.
- LaTeX: independently rebuilt with `latexmk -pdf -interaction=nonstopmode -halt-on-error` (exit 0; four pages; no errors or unresolved warnings). Shipped/fresh text agrees up to font/line-break extraction artifacts; all four shipped pages were split and rasterized.
- Lean build: Lean 4.19.0 / Lake 5.0.0, Mathlib exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`; exact official dependencies linked via the supplied script and Main compiled independently. `lake build` exit 0 (`[1016/1017] Built Main`); direct warning-as-error Lean check exit 0. All fifteen audited theorems use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`; broad hits are prose-only. The finite \(S_3\) checks use ordinary kernel `decide`.
- Auxiliary code: none is supplied or needed.
## Semantic audit
The formal derangement set is \(\{g:\forall x,gx\ne x\}\) for an actual Mathlib group action, and the proportion is the exact rational quotient of cardinalities. Transitivity is `MulAction.IsPretransitive`; actions are not assumed faithful, so the theorem includes every transitive permutation group.

The Cameron–Cohen proof is complete. Burnside's lemma on \(\Omega\) gives \(\sum_g \mathrm{fix}(g)=|G|\). On \(\Omega\times\Omega\), fixed pairs are counted by \(\mathrm{fix}(g)^2\), and for degree \(n\ge2\) the diagonal and an off-diagonal pair give at least two orbits, so \(\sum_g\mathrm{fix}(g)^2\ge2|G|\). Pointwise \((f-1)(f-n)\le n\mathbf 1_{f=0}\); summing yields \(n|D|\ge|G|\), hence \(\delta(G)\ge1/n\). This is stronger than \(c=1/2\) and holds for every finite transitive action of degree at least two.

For a Frobenius action (transitive, degree at least two, nonidentity elements fixing at most one point, and a nonidentity point stabilizer), the identity contributes \(n\) fixed points; each nonidentity non-derangement contributes one, and derangements contribute none. The Burnside identity gives \(|D|=n-1\). Lean proves this and derives \(\delta=(n-1)/|G|\).

Consequently \(c=1/2\) is not tight under three natural readings: \(c=1\) improves the universal bound; no Frobenius group can equal \((1/2)/n\) because every transitive group has \(\delta\ge1/n\); and no Frobenius family approaches it, since choosing \(\varepsilon=1/2\) still gives the universal \(1/n\) lower bound. Lean formalizes all three readings and negates their disjunction. Conversely \(S_3\) on three points is proved Frobenius and has \(\delta=1/3=1/n\), establishing tightness of \(c=1\). Degree one is explicitly excluded as degenerate; that exclusion is conservative because the submitted refutation works entirely for \(n\ge2\).
## Issues found
none blocking
## Verdict rationale
The inequality with \(1/2\) is true but weaker than the universal Cameron–Cohen \(1/n\) bound. Therefore the asserted tightness of \(1/2\) is false, including all three natural formulations involving improvement, attainment, and approximation by Frobenius groups. The corrected constant \(1\) is attained by \(S_3\). The formalization carries actual groups, actions, derangements, Burnside counting, tightness quantifiers, and the example.

## Disposition
APPROVED — ready to merge (PR 522). Independent fresh rebuild, direct warning-as-error Lean check, axiom audit, PDF rebuild/comparison, source inspection, forbidden-pattern scan, and semantic audit all passed.
