# Solution Review — Conjecture 00000006480 (PR 434)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004092136`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** The official bilingual statement is existential and asks for two same-covariance processes with different extremal distributions, explicitly non-Gaussian and with different joint laws. The final Lean witness theorem supplies every required property for concrete finite processes.
- **Repository structure.** PR head `d819b464...`, from clean base `4cc82278...`, adds only the correctly named submission folder. The copied conjecture is byte-identical to the official source; base metadata has no prior solve. All submitted hashes independently match.
- **LaTeX/PDF.** Read the full report and both shipped PDF pages. Independently compiled `main.tex` twice; both passes exited 0. The fresh and shipped PDFs have equivalent two-page content; Ghostscript rendered the shipped PDF successfully.
- **Lean.** Used `/tmp/link_shared_mathlib.sh` and independently built the pinned Lean 4.19/Mathlib project: `lake build` exit 0. Strictly replayed Processes, Gaussian, final, and Check files with `-DwarningAsError=true`: all four exit 0. All 42 audited declarations use only standard permitted axioms; Check output matches shipped axiom evidence byte-for-byte.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, additional axiom, unsafe implementation, `extern`, `implemented_by`, or kernel-check bypass.
- **Auxiliary code.** None needed; all probability calculations are exact Lean theorems on actual measures.

## Semantic audit

Let `A,B,C` be independent fair signs and define `X=(A,B,C)` and `Y=(A,B,AB)`. Every coordinate is a fair sign, and the relevant cross-products all have mean zero, so both covariance matrices are `I₃`. The joint vector `(-1,-1,-1)` has probability `1/8` for `X` and zero for `Y`, proving different joint laws. `max X=-1` only on the all-negative outcome, while `max Y=1` always, so their maximum laws differ. Both first-coordinate marginals have an atom of mass `1/2`; a real Gaussian law is either atomless or a Dirac mass, so neither process is Gaussian.

Lean constructs these on the actual uniform measure on `Fin 8`, computes covariance via centered integrals, defines joint and extreme laws as pushforwards, proves full maximum laws, proves both non-Gaussian under all real linear combinations (including zero variance), and combines these in `conjecture_true : ExplicitWitnessClaim`. The witness theorem is non-vacuous and matches the official existential claim exactly.

## Issues found

None blocking.

## Verdict rationale

The explicit pair satisfies equal covariance, different joint law, different extremal law, and non-Gaussianity, proving every requested conjunct. Independent builds, strict replays, PDF reconstruction, hash checks, and semantic review all pass.

## Disposition

**APPROVED**
