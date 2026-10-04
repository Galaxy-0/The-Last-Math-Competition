# Solution Review — Conjecture 00000000308 (PR 423)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004063225`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The merge base was `0862407ef50dda4f7376342ca3e79368dce942d2`, relative to the supplied clean base `4cc82278ba1e5becc4d20b1e2a68dede094e2b8d`. The three-dot diff adds only files beneath the correctly named personal folder `solutions/00000000308/C0ldSmi1e_submission_20261004063225/`. The base metadata row marks conjecture 00000000308 neither proven nor disproven. The submitted `conjecture.md` is byte-identical to `conjectures/00000000308.md`.
- **LaTeX and PDF.** I read the complete three-page report and every submitted source/configuration file. A fresh `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` succeeded (exit 0; 3 pages). I extracted text from both the shipped PDF and the independently built PDF with `pypdf`, rendered all fresh pages with Ghostscript, and checked the title, abstract, definition/scope, both proofs, formal-correspondence section, reproduction section, and references. The text differences were only engine/spacing/ligature extraction differences; the mathematical content and section sequence match. No auxiliary computation is claimed or needed.
- **Lean.** In a fresh copied project, after force-unpacking the official pinned Mathlib cache, `lake build` completed successfully (exit 0), building `Definitions`, `RealBound`, `ComplexBound`, and `Conjecture308`. Direct replay with warnings as errors succeeded for `Definitions.lean`, `RealBound.lean`, `ComplexBound.lean`, `Conjecture308.lean`, and `Check.lean` (all exit 0). `Check.lean` printed the actual definitions, theorem types, and eight central axiom audits. Every audit reports exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** The submitted Lean/config files contain no `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, `implemented_by`, `extern`, `skipKernelTC`, kernel-trust override, or incomplete proof. The only occurrences of the word “axioms” are the legitimate `#print axioms` audit commands and prose. Toolchain and dependency revisions are pinned; no dependency source is bundled as submission proof code.
- **Author evidence.** The supplied build/axiom/hash records agree with my independent replay. They were treated as evidence only; the verdict relies on the fresh build and semantic audit.

## Semantic audit

The official claim is: “The intersection of Bad(ℂ) with any real line is empty; and the complement of Bad(ℂ) has full measure on every line, with convergence rates controlled by the lattice density of the Gaussian integers.” The submission explicitly interprets Bad(ℂ) by the standard Gaussian-rational criterion: there exists `c > 0` such that `|z-p/q| ≥ c/|q|²` for every `p,q ∈ ℤ[i]`, `q ≠ 0`, with complex division and modulus. This is the usual notion of complex bad approximability. No coprimality restriction or finite denominator cutoff is imposed.

Lean's `BadC` is exactly that set: it quantifies over Mathlib's actual `GaussianInt` numerator and denominator, casts both into `ℂ`, uses complex division, and bounds `c / ‖q‖²` by the complex norm of the error. Thus a Gaussian denominator with either coordinate zero is not excluded.

The real estimate is valid for every nonzero integer `m` and integer `n`. Let `r=|m√2-n|` and `s=|m√2+n|`. Since `2m²-n²` is a nonzero integer, `rs=|2m²-n²| ≥ 1`; also `|m| ≥ 1`. If `r ≥ 1`, then `|m|r ≥ 1 ≥ 1/4`. If `r < 1`, then `s ≤ 2|m|√2+r < 3|m|+1 ≤ 4|m|`, so `1 ≤ rs ≤ 4|m|r`, again giving `1/4 ≤ |m|r`. This is precisely formalized in `real_sqrt_two_bound`, with no size restriction on `m` or `n`.

For arbitrary nonzero `q=u+iv` and `p=a+ib`, at least one integer coordinate `u,v` is nonzero. The corresponding coordinate of `q√2-p` is `u√2-a` or `v√2-b`, and its absolute value is at most `|q|·|q√2-p|`. Applying the real bound to that coordinate gives `1/4 ≤ |q|·|q√2-p|`; after multiplying by the identity `q√2-p=q(√2-p/q)` and dividing by `|q|²`, this yields `1/4|q|² ≤ |√2-p/q|` for every Gaussian numerator and nonzero Gaussian denominator. Lean proves this unrestricted transfer in `ComplexBound.lean` and therefore establishes `√2 ∈ BadC` with `c=1/4`.

The line is nondegenerate: Lean defines `realLine a v = {a+t v : t ∈ ℝ}` and disproves the universal claim only under `v ≠ 0`. The real axis is `realLine 0 1`; `√2` is an explicit member. Consequently `BadC ∩ realLine(0,1)` is nonempty, directly negating the universal empty-intersection clause. This is not a vacuity trick: the witness genuinely satisfies both the full all-denominator bad-approximation predicate and the nonzero-direction real-line membership.

Since the conjecture is a conjunction, refuting its first clause refutes the whole statement. The submission does not overclaim resolution of the measure or convergence-rate clauses.

## Verdict rationale

The fresh LaTeX and Lean builds succeed; all central Lean results use only the three standard foundational axioms; the source is free of proof escapes; and the formal theorem faithfully refutes the literal universal empty-intersection assertion using a mathematically sound, unrestricted Gaussian-rational counterexample. I also spot-checked the conjugate-product arithmetic exactly and sampled Gaussian numerators/denominators numerically, consistent with the formal bound.

## Disposition

APPROVED — ready for merge (PR 423). This review records independent verification; no merge action was taken by this reviewer.
