# Disproof of conjecture 00000000464

For `G_k = C_(2^(k+2))`, every graph is connected and 2-regular, its order tends to infinity, and its actual spanning-tree count is `2^(k+2)`. The largest prime factor stays at 2. Hence every positive logarithmic lower bound fails eventually.

Both original language versions permit degree 2. This disproves the deterministic lower-bound clause, and therefore the stated conjunction. It does not settle a modified restriction to degree at least 3 or separately resolve the random-graph distribution clause.

## Files

- `main.tex` and `main.pdf`: complete mathematical report and its compiled PDF.
- `conjecture.md`: exact original bilingual statement.
- `lean/`: complete Lean project, dependency manifest, and axiom audit.
- `SEMANTIC_REVIEW.md`: internal correspondence review, distinct from maintainer review.
- `verification/`: build and audit output, reproduction notes, and file hashes.

## Reproduce the proof

Install the toolchain in `lean/lean-toolchain` (Lean 4.19.0), enter `lean/`, and run:

```sh
lake exe cache get
lake build
for source in CycleFacts.lean CycleTrees.lean NumberTheory.lean Conjecture464.lean Check.lean
do
  lake env lean -DwarningAsError=true "$source" || exit 1
done
```

The cache download is an optional acceleration. An ordinary `lake build` can build the pinned dependencies from source. If the native cache executable has a platform-specific loading failure, use:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
lake build
```

The committed manifest pins Mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0) and records its dependencies. Preserve this manifest when reproducing the recorded results.

`Check.lean` prints the definitions of spanning trees, their count, and largest prime factor; the full concluding theorem type; and the axiom dependencies of eleven central results. All eleven depend only on `propext`, `Classical.choice`, and `Quot.sound`.

No auxiliary numerical computation is part of the proof. The count is established by an arbitrary-order bijection, not an assumed formula or a finite experiment. Every positive real constant and every finite starting index are covered by the final theorem.

## Formal source map

| File | Main contribution |
|---|---|
| `CycleFacts.lean` | Any single-edge deletion from a cycle of order at least 3 is connected. |
| `CycleTrees.lean` | Actual spanning trees are in bijection with cycle edges; their number is the order. |
| `NumberTheory.lean` | Power-of-two orders are unbounded, their largest prime factor is 2, and logarithmic bounds diverge. |
| `Conjecture464.lean` | The actual connected 2-regular family and `conjecture464_counterexample`. |

## Reproduce the report

Compile `main.tex` with a standard LaTeX installation, for example `latexmk -pdf main.tex` or `tectonic main.tex`. The checked-in PDF was exported from this exact source with Tectonic 0.17.0. The source also compiled successfully in the desktop LaTeX editor.

All changes belong to this personal submission folder. These checks establish local verification; acceptance remains the competition maintainers' decision.
