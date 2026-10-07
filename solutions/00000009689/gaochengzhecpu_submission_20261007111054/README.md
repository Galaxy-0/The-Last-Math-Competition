# Conjecture 00000009689: an algebraic auxiliary value cannot add transcendence degree

For every complex x and algebraic complex j, the field Q(x,j) has transcendence degree at most one over Q. The conjecture's joint-degree claim already fails for one positive squarefree parameter, where it prescribes 1+1=2. The proof uses d=1 and x=exp(pi), but the obstruction holds for every d and every algebraic auxiliary value.

## Files and reproduction

- `main.tex`, `main.pdf`: full disproof and formal correspondence.
- `SOURCE.md`: the unchanged bilingual conjecture, byte for byte.
- `lean/`: portable project pinned to Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `verification/`: actual build logs, theorem-axiom output, hashes, source provenance, and reviews.

Inside `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. On a new machine, `lake exe cache get` retrieves official dependency artifacts. All dependency commits are pinned; the submitted configuration contains no local paths. Run `tectonic main.tex` from the submission directory to reproduce the PDF. No auxiliary numerical computation is required for this field-theoretic argument.

## Formalization and scope

The proof uses actual `IsAlgebraic`, `Algebra.trdeg`, and `IntermediateField.adjoin`. The algebraicity of j gives degree zero for Q(j)/Q. A genuine polynomial evaluation map bounds the transcendence degree of Q(j)[x] by one; the algebraic passage to Q(j)(x) preserves the bound. The tower formula and a proved equality of iterated adjoining with Q(x,j) yield the conclusion.

`gelfondValue` uses `Complex.exp`, `Real.pi`, and `Real.sqrt`. The final theorem rules out every assignment of algebraic auxiliary values satisfying the source's claimed singleton degree; positive squarefree d=1 is verified explicitly. The source itself calls the corresponding CM j values algebraic. The generic theorem therefore applies to those values without computing them. No modular j function is defined, replaced by an artificial function, or assumed through a custom axiom. The separate algebraic independence assertion is not addressed.

Fresh builds reuse only the official, unmodified dependency cache at the pinned commits and compile the submission in a new directory without its previous build artifacts. The audit excludes proof gaps, custom axioms, and native computation shortcuts. The built-in LaTeX compiler is attempted and its result recorded; the existing Tectonic installation exports the PDF and every page is inspected. Author self-review and parent-agent review are separate; no external independent review is claimed.
