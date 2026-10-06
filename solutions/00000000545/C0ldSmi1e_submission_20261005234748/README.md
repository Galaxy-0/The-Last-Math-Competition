# Disproof of conjecture 00000000545

Every finite complete graph has an entirely quadratic Markov basis for its standard edge-ring toric ideal. In particular, `K_6` contradicts the proposed cutoff `n ≤ 5`. The proof works over every nontrivial commutative coefficient ring, hence over every field.

`ORIGINAL.md` preserves the exact English and Chinese conjecture. `report.tex` and `report.pdf` give the complete mathematical argument. The formal conclusion is `CompleteGraph.conjecture545_false_positive` in `lean/Conjecture545.lean`, which negates the stated equivalence for positive integers `n`.

## Mathematical scope

The graph has every unordered pair of distinct vertices as an edge. Its parametrization sends the edge variable `y_{ij}` to `x_i*x_j`; the toric ideal is the kernel of that actual polynomial map. The finite basis consists of all nonzero differences of two degree-two edge monomials with the same labeled vertex degrees.

The proof establishes connectivity for **all** nonnegative edge-multiplicity fibers, then proves that these quadratic binomials generate the **entire** polynomial kernel. It does not rely on bounded fiber enumeration, a lattice-spanning proxy, or a simple-graph restriction. Nonzero generators and exact degree two are proved explicitly. No minimality or literature novelty is asserted.

## Reproduce the verification

Install Lean through Elan and have Git and Python 3 available. From this submission directory:

```sh
cd lean
lake exe cache get
lake build
cd ..
python3 verify.py
```

The checked-in toolchain selects Lean 4.19.0. `lake-manifest.json` and `pinned-dependencies.json` bind Mathlib v4.19.0 and all eight transitive Git dependencies to exact revisions. `lake exe cache get` downloads the standard library build cache; it is not part of the proof. Local verification reused those pinned, unmodified dependency checkouts and cache while rebuilding the authored modules from source.

`verify.py` uses only Python's standard library. It verifies the frozen proof/configuration hashes and original source, checks all nine dependency revisions and tracked trees, builds the complete project, and replays all five Lean modules with warnings treated as errors. It reads the actual compiled declaration inventory from `Audit.lean`, including generated and private declarations, and checks every complete axiom list against the recorded inventory. It then rechecks the dependencies and input hashes. By default, complete command/output records are written to a new temporary directory; `--output NEW_DIRECTORY` selects another new directory.

The 93 mathematical declarations have no axiom dependencies beyond `propext`, `Quot.sound`, and `Classical.choice`. There are no admitted proofs, `native_decide`, custom axioms, or unsafe proof declarations. `Check.lean` independently instantiates the disproof and parametrization at `K_6` over an arbitrary field. The argument requires no auxiliary numerical computation or finite experiment.

## Files and evidence

| File | Purpose |
| --- | --- |
| `lean/Connectivity.lean` | Arbitrary-multiplicity connectivity by quadratic switches |
| `lean/IdealBridge.lean` | Full polynomial-kernel argument over any commutative ring |
| `lean/Conjecture545.lean` | Graph-ring definitions, finite quadratic basis, and exact disproof |
| `lean/Check.lean` | Arbitrary-field and `K_6` interface checks |
| `lean/Audit.lean` | Compiled declaration and axiom-dependency inventory |
| `verify.py` | Portable verification entry point |
| `verification/author/` | Frozen author identities and successful execution records |
| `verification/root/` | Independent clean build, strict replay, full compiled inventory, and historical tooling records |
| `verification/package-replay/` | Actual execution of `verify.py` from this submission package |
| `verification/independent-semantic-review.json` | Independent, non-author audit of every mathematical bridge |

The verification records describe local checks, not maintainer acceptance. Historical command records retain the absolute paths used at execution time; use the portable `verify.py` entry point to reproduce the current proof. The author's frozen report records an earlier checkpoint before document creation. A complete final report/PDF review and source-to-PDF identity record accompany the finished package.

To regenerate the PDF, run `tectonic report.tex` or compile the standalone source with a standard LaTeX installation. No external mathematical computations are required to build the report.
