# Solution Review — Conjecture 00000008486 (PR 414)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004052950`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- Full bilingual conjecture read. Base metadata marks the ID unsolved; the PR adds only its own solution directory.
- Full report and both shipped PDF pages read. Fresh two-pass `pdflatex` compilation exited 0; both pages rendered. Rebuilt/shipped differences are compiler text-extraction artifacts.
- Full Lean 4.19.0/Mathlib build at pinned revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`: `lake build` exited 0 at `[2216/2217] Built Main`; direct warning-as-error Lean check exited 0.
- No forbidden proof shortcut. All five principal theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- No auxiliary computation is needed.

## Counterexample

Let `Ω={0,1}` with the discrete topology, `T=id`, and `f(0)=0`, `f(1)=1`. The maximum set is the fixed orbit `{1}`, whose uniform measure is `δ1`.

For the conjecture's exact density `exp(-f/t)` relative to counting measure,

`Z_t=1+e^{-1/t}`,
`μ_t = (1/(1+e^{-1/t}))δ0 + (e^{-1/t}/(1+e^{-1/t}))δ1`.

As `t↓0`, `e^{-1/t}→0`, so `μ_t` converges weakly to `δ0`, not `δ1`. The two Dirac measures differ, and the weak probability topology is Hausdorff, so the asserted unique maximum-orbit limit is false.

Lean constructs the actual compact system, continuous dynamics/observable, maximum orbit, probability measures, exact Gibbs point masses, Bochner integrals, and genuine Mathlib weak convergence. It proves convergence to `δ0` and nonconvergence to `δ1`.

**Disposition: APPROVED.**
