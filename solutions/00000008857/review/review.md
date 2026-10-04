# Solution Review — Conjecture 00000008857 (PR 440)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004095058`  
**Reviewer:** independent competition audit  
**Date:** 2026-10-04

## Checklist

- [x] Only the permitted submission directory was added
- [x] Full LaTeX source and PDF read; independent LaTeX build passed
- [x] Full Lean project independently built with pinned dependencies
- [x] Direct warning-as-error Lean check passed
- [x] No `sorry`, `admit`, `native_decide`, extra axiom, unsafe implementation, external binding, or kernel bypass
- [x] Axiom audit shows only `propext`, `Classical.choice`, and `Quot.sound`
- [x] Formal model is non-vacuous and matches the official monotone-game/Nash statement

## Conjecture and counterexample

The official conjecture says that the Nash equilibrium set of every monotone game is nonempty (and then has the stated closed/convex/containment properties). Take two players with strategy sets \(\mathbb R\) and costs

\[
c_i(x_0,x_1)=e^{x_i}.
\]

The strategy domains are nonempty closed convex sets, the costs are positive and smooth, and each own-action cost \(a\mapsto e^a\) is strictly convex. Its actual pseudogradient is

\[
F(x)=(e^{x_0},e^{x_1}).
\]

Since the exponential is increasing,

\[
\langle F(x)-F(y),x-y\rangle
=\sum_i (e^{x_i}-e^{y_i})(x_i-y_i)\ge0,
\]

so the game is monotone.

There is nevertheless no Nash equilibrium. At every profile \(x\), player \(i\) can choose \(a=x_i-1\), and

\[
c_i(x^{i\leftarrow(x_i-1)})=e^{x_i-1}<e^{x_i}=c_i(x).
\]

Thus every profile admits a strict profitable deviation and the equilibrium set is empty, contradicting universal nonemptiness.

## Formal verification

The Lean project uses the actual `EuclideanSpace ℝ (Fin 2)` profile space and standard inner product. `changeAction` changes only the selected coordinate. `IsNash` quantifies over both players and every real alternative action, not merely a finite table.

Lean proves unrestricted strategy geometry, positivity, smoothness, unilateral differentiability and strict convexity, coordinatewise derivative identification, Hilbert-space monotonicity, the strict profitable deviation, and equality of the full Nash set with `\u2205`. The packaged theorem proves both that the game is monotone and that no Nash profile exists.

Independent `lake build` and `lake env lean Main.lean -DwarningAsError=true` commands exited 0. All principal theorem audits report exactly the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Verdict

APPROVED — this is a correct, non-vacuous disproof of Conjecture 00000008857.
