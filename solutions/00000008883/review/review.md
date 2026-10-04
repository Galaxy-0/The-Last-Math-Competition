# Solution Review — Conjecture 00000008883 (PR 408)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004051017`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Conjecture/status:** read the full bilingual conjecture. Base metadata marks `00000008883` neither proven nor disproven. The PR changes only its own submission directory.
- **Report/PDF:** read the full LaTeX report and both pages of the shipped PDF. Recompiled twice in a fresh directory; both passes exited 0. The rebuilt and shipped PDFs have the same two-page content; raw textual differences are only Tectonic/TeX ligature and spacing extraction artifacts.
- **Lean:** fresh Lean 4.19.0 project using pinned Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Full `lake build` exited 0 and built `Main`; direct `lake env lean Main.lean -DwarningAsError=true` exited 0.
- **Forbidden content:** no `sorry`, `admit`, `native_decide`, custom axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- **Axioms:** all principal theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- **Auxiliary computation:** none is used or required.

## What the submission proves

For every finite-edge blue/red Hackenbush graph, restrict its arbitrary vertex set to the finite union of the endpoint images. Isolated vertices have no effect on play or value, while every edge, endpoint, color, and relevant ground flag is retained. Enumerating this finite incident support and the finite edge set gives endpoint maps `Fin e → Fin v`, two Boolean colors, and incident ground flags. For fixed `v,e` only finitely many descriptions exist; the dependent union over all `v,e` is countable.

Lean formalizes both the graph model and the exhaustive reduction. `Graph V E` has genuine independent edge identities, so loops and parallel edges are allowed. `support`, `source_in_support`, and `target_in_support` handle arbitrary `V`; `normalize`, `normalization_preserves_incidence`, and `exhaustive_finite_edge_representation` produce a finite description under actual vertex/edge equivalences while preserving endpoint, color, and ground data.

The reals are uncountable. Consequently no function from finite descriptions to the reals is surjective. `no_partial_value_assignment` extends this to any subtype of descriptions that happen to have real values, and `no_functional_realization_covers_all_reals` extends it to any deterministic realization relation.

## Why this disproves the official conjecture

The conjecture explicitly asserts that **all real surreals are realizable by finite edge graphs**. Distinct reals are distinct real surreals, so that clause would realize every ordinary real. A finite Hackenbush graph has one value, and relabeling or deleting isolated vertices cannot change the legal-move tree or game value. Therefore a purported finite-graph realization would induce a deterministic real-valued relation on the exhaustive countable normalized descriptions. The formal theorem rules out such coverage of all reals.

This cardinality obstruction requires no formula for Hackenbush values and no analysis of the separate “infinite Hackenbush” clause. It is valid for all finite sizes and even includes overgeneral graph features such as loops, parallel edges, disconnected components, and arbitrary grounding. Since one asserted conjunct is impossible, the full conjunction is false.

## Verification

Independent full build and direct checking succeeded. The initial local Mathlib cache helper had a platform-executable failure, but after unpacking the official cache, `lake build` completed successfully. No author log was relied upon for the verdict.

**Disposition: APPROVED.** The formal theorem and ordinary countability argument decisively refute the finite-realization clause of conjecture `00000008883`.
