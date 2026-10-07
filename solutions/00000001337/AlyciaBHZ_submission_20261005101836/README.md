# TLMC 00000001337: the iterated Möbius mean converges to 6/π²

Under the specified convention μ_out(−1) = μ_out(1) = 1 and μ_out(0) = 0, the actual composition μ_out(μ(n)) is the squarefree indicator. We prove, for **every real x ≥ 0**,

\[
\left|\sum_{n=1}^{\lfloor x\rfloor}\mu_{\mathrm{out}}(\mu(n))
       -\frac{6}{\pi^2}x\right|\leq3\sqrt{x}.
\]

For x > 0 the normalized error is at most 3/√x. Thus the requested real-endpoint mean converges to **6/π² > 0**, and cannot converge to zero. The conjecture's phrase “diverges to a limit” is read as convergence to a nonzero limit; literal nonconvergence is incompatible with the proved behavior.

The proof counts squarefree integers using the Möbius divisor identity, controls the floor errors by √x, bounds the reciprocal-square tail by 2√x, and identifies the coefficient using the Basel sum and Möbius inversion. The Lean source defines the literal outer convention and composition first, and proves their equality with the indicator rather than assuming it.

## Contents

- `lean4/MobiusMean.lean`: one complete source file, including the supporting count proof and the main theorems `MobiusMean.mean_tendsto`, `MobiusMean.count_error`, `MobiusMean.mean_error`, `MobiusMean.limit_ne_zero`, and `MobiusMean.not_tendsto_zero`.
- `lean4/lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: pinned Lean/Mathlib v4.33.0 project; library and package name `MobiusMean`.
- `report.tex`, `report.pdf`: self-contained mathematical proof, interpretation discussion, formal statements, provenance, and axiom audit.
- `verification.txt`: successful compiler output and axiom audit and independent Python output.
- `verify.py`: standard-library sanity checks of the composition, finite counting identity, and error bounds.
- `LICENSE.trureturing`: upstream Apache-2.0 license; the immutable vendored revision is documented below.

## Build and reproduce

In a fresh environment with Lean installed:

```sh
cd lean4
lake exe cache get && lake build
cd ..
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Mathlib is pinned to tag `v4.33.0`, commit `db584cd6d46c92f209a44c0f1c829460d327499d`. The recorded Lean compilation completed with exit status 0. Every printed axiom audit is exactly `[propext, Classical.choice, Quot.sound]`; there are no added axioms or unproved goals.

The report and source retain the interpretation boundary: the conclusion is convergence to a nonzero limit, and the numerical checks supplement the universal Lean proof.

## Attribution and vendoring

Submitted by AlyciaBHZ on behalf of the Omega Institute (trureturing project, https://github.com/the-omega-institute/trureturing).

The complete supporting squarefree coprime count proof is adapted from the Apache-2.0 trureturing file `D5/S3/Weil/Mertens/CoprimeSquarefreeDensity.lean`, with only `C`, `e` from `CoprimeMobiusCertificateError.lean` and `sum_one_div_sq_le` from `Third.lean` inlined. The upstream revision is `1be30b25c4fe6cd46397090ca09b5696eb62ea78`. The source retains an attribution header; the upstream license is included. Namespaces were renamed, all trureturing imports removed, and the resulting proof compiles using only Mathlib. The literal composition, identification of 6/π², mean limit, and nonzero-limit conclusions are supplied in this submission.
