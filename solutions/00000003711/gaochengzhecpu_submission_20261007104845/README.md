# Conjecture 00000003711: Triangle resistance sums are not its spanning-tree count

Actual K3 has three spanning trees. Its resistance quadratic forms sum to 2 over unordered pairs and 4 over ordered pairs. All four Moore-Penrose equations and the uniqueness of terminal voltage drops under Kirchhoff's law are formalized.

## Scope and formalization

The graph is connected and all edge conductances are one. Both standard pair-sum conventions fail. The individual resistance formula remains valid. The spanning-tree count is obtained from actual IsTree subgraphs via a finite-mask equivalence; it is not assigned by definition. The supplemental Python program performs exact rational matrix arithmetic and graph enumeration.

See `main.tex` / `main.pdf` for the complete mathematical argument and theorem correspondence. `SOURCE.md` is the unchanged bilingual source.

## Reproduction

Inside `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. Lean is pinned to 4.19.0 and Mathlib to c44e0c8ee63ca166450922a373c7409c5d26b00b. The public-Git manifest pins all transitive dependencies and contains no local paths. A new machine can run `lake exe cache get` to obtain official dependency artifacts. From the submission directory run `tectonic main.tex` to export the PDF.

Run `python verify.py` for the supplemental exact computation.

The submitted project is rebuilt in a fresh directory without its own previous artifacts, reusing only verified official dependency artifacts. Build logs, printed axiom dependencies and source hashes are in `verification/`. The author checks every final PDF page. Separate author self-review and delegated-agent adversarial review records are included; no external independent review is claimed.
