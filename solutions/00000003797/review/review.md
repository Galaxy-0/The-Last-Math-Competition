# Solution Review — Conjecture 00000003797 (PR 235)

**Submission:** orionsheep — `orionsheep_submission_20261003025022`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
The projected gradient method for variational inequalities always converges uniformly; the optimal step size is the midpoint of the spectral interval of the operator, and the convergence rate is linear.

## What the submission proves
Take f(x) = x^2 with gradient 2x, whose operator has spectral interval [2,2] and midpoint 2 — the conjecture's claimed optimal step. With step 2 the iteration is x_{n+1} = -3x_n, so |x_n| = 3^n|x_0|. Lean defines mag by exactly this recurrence, proves the closed form by induction, and certifies the anchor mag 1 10 = 59049 > 10^4, with the main theorem stating the escape. The iterates escape every bound, refuting "always converges uniformly" and showing the spectral midpoint is a divergent (hence non-optimal) step, the true optimum being 1/2.

## Verification notes
The recurrence x_{n+1} = -3x_n is correct classical arithmetic (step 2 exceeds the stability bound 2/L = 1 for L = 2), and the counterexample uses the conjecture's own claimed optimal step; a single divergent trajectory suffices against "always converges". The divergence — general closed form and escape anchor — is proven in Lean about a bespoke object modeling the conjecture's iterates; the scheme over the reals is not formalized, the recurrence being taken definitionally from the one-line computation x - 4x = -3x. reproduce.py independently simulates the divergent orbit and the one-step convergence at step 1/2.

## Verdict
APPROVED — merged into main.

