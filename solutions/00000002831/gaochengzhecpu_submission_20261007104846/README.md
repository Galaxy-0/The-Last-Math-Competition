# Conjecture 00000002831: The stochastic HMM image need not be algebraic

A one-hidden-state, two-symbol HMM realizes every (t,1-t) with 0<=t<=1. Any family of polynomial equations vanishing there also vanishes at (2,-1), which is not an observed probability distribution. Thus the image is not a real algebraic set.

## Scope and formalization

The source says image, not Zariski closure. The proof uses actual normalized, nonnegative stochastic parameters and observed probabilities, actual polynomial substitution, and infinitude of the real interval. It addresses the stochastic image itself; its algebraic closure and the invariant-degree clause are not refuted. No numerical calculation is needed.

See `main.tex` / `main.pdf` for the complete mathematical argument and theorem correspondence. `SOURCE.md` is the unchanged bilingual source.

## Reproduction

Inside `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. Lean is pinned to 4.19.0 and Mathlib to c44e0c8ee63ca166450922a373c7409c5d26b00b. The public-Git manifest pins all transitive dependencies and contains no local paths. A new machine can run `lake exe cache get` to obtain official dependency artifacts. From the submission directory run `tectonic main.tex` to export the PDF.

No auxiliary numerical computation is needed.

The submitted project is rebuilt in a fresh directory without its own previous artifacts, reusing only verified official dependency artifacts. Build logs, printed axiom dependencies and source hashes are in `verification/`. The author checks every final PDF page. Separate author self-review and delegated-agent adversarial review records are included; no external independent review is claimed.
