# Proof of conjecture 00000001227

For every finite simple undirected graph and every specified start, the first player wins normal-play vertex geography if and only if every maximum-cardinality matching saturates the start.

The report explicitly states the conventional finite game rules omitted by the short source. It covers disconnected graphs and isolated starts, assumes no perfect matching, and acknowledges that the criterion is a known theorem. It makes no claim about unspecified infinite play or a new historical extension.

`main.tex` and `main.pdf` contain the full proof and formalization correspondence. `conjecture.md` is the byte-identical bilingual source. `lean/` contains the complete pinned Lean project. `auxiliary/` contains the independently written exhaustive finite sanity check. `VERIFICATION.md` and `verification/` preserve the execution evidence; `SEMANTIC_REVIEW.md` records independent internal scrutiny, which is distinct from maintainer acceptance.

With Lean 4.19.0 available, from `lean/` run:

```sh
lake build
lake env lean -DwarningAsError=true Check.lean
lake env lean -DwarningAsError=true ../verification/environment-inventory.lean
```

The first dependency setup needs network access; the manifest pins all nine dependencies, including Mathlib v4.19.0. The library build treats warnings as errors. `Check.lean` prints every authored definition and each theorem's type and axiom dependencies. The extra inspection harness enumerates every constant from the submitted modules; it creates no proof.

From the submission directory, using Python 3 and only its standard library:

```sh
python3 auxiliary/check_vertex_geography.py --max-n 6
```

This compares independently enumerated matchings and legal game trees on all 33,868 labelled graphs and 202,013 starts through six vertices. It is supplementary finite evidence; the Lean proof establishes the theorem for all finite sizes.

Compile `main.tex` with a standard LaTeX engine or Tectonic. The submitted PDF was exported with Tectonic 0.17.0, also compiled in the native document editor, and all three pages were visually inspected.

`verification/SHA256SUMS.json` pins every submitted file other than that manifest itself. All changes in this contribution belong to this personal submission folder.
