# Conjecture 00000006953: variance-proportional allocation is not optimal

For two equally weighted strata with values ±1 and ±2, the variances are 1 and 4. With five equally costly independent observations, allocation (1,4) is exactly proportional to these variances. Its unbiased stratified mean has variance 1/2. Allocation (2,3) uses the same five observations and has smaller variance 11/24.

## Files and reproduction

- `main.tex`, `main.pdf`: complete mathematical counterexample and Lean correspondence.
- `SOURCE.md`: exact original bilingual source bytes.
- `lean/`: portable Lean 4.19.0 project with all dependency commits pinned.
- `verify.py`: exact rational enumeration of all 32 outcomes, independently of Lean.
- `verification/`: actual fresh build, hashes, axiom output, provenance, and review records.

Inside `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`; official artifacts may be obtained on a new machine with `lake exe cache get`. The project has no local dependency paths. From the submission directory, run `python verify.py` and `tectonic main.tex`.

## Actual probability objects and formal scope

The sample space is the full product of five copies of `Fin 2`. `μ` is the actual measure `(1/32) • Measure.count`, and `mass_one` proves it is a probability measure. `joint_outcome_mass` verifies every specified five-coordinate outcome has probability `(1/2)^5`, the independent fair-bit distribution.

The `estimator n` function computes the equally weighted sum of the two stratum sample means, using n samples from ±1 and 5-n samples from ±2. `Admissible` requires n>0 and n<5. `Optimal` compares actual `ProbabilityTheory.variance` among every such allocation. `integral_as_sum` and `variance_as_sum` connect Mathlib integrals and variances to exact finite sums.

The proof computes both stratum means and variances, the variance-proportional allocation ratio, the unbiasedness of each competing estimator, and the exact actual variances 1/2 and 11/24. The final theorem refutes optimality of allocation (1,4). No moment, variance, or optimum is stipulated numerically in a definition.

Equal weights and costs remove ambiguity from those factors. Both allocations are positive and have identical total count five; the proportional allocation is integral. The result needs no asymptotics, simulation, or finite-population correction. It concerns the source's proposed variance-proportional allocation, not a different standard-deviation-proportional rule.

Fresh validation builds the submitted Lean source without its own compiled artifacts, reusing only unmodified, official, commit-pinned dependency artifacts. Axiom checks allow only the standard three axioms. The built-in LaTeX editor/compiler is attempted with its outcome recorded; the existing Tectonic installation exports the PDF and every page is visually inspected. Author self-review and parent adversarial review are separate; no external independent review is claimed.
