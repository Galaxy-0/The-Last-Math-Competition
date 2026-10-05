# Disproof of conjecture 00000001066

For every prime `p`, no finite subset of `F_p` has cardinality exactly `sqrt(p)`: its natural-number cardinality would square to the prime. The proof therefore refutes the conjecture's exact-attainment clause, and hence its written conjunction. Both universal-prime and existential-prime attainment readings are formalized and disproved.

This is the literal, unrounded real square root. No claim is made about rounded or asymptotic Sidon extrema, or about the upper-bound clause by itself. Ordered Sidon differences exclude diagonal pairs. The report explains the English/Chinese interpretation, and `conjecture.md` preserves the exact bilingual source.

## Reproduce the Lean verification

Use Lean 4.19.0, as pinned by `lean/lean-toolchain`. The manifest pins Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b` and all eight supporting packages.

From this submission folder:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture1066.lean
lake env lean -DwarningAsError=true Check.lean
lake env lean -DwarningAsError=true ../verification/environment-inventory.lean
```

The default build target is the actual proof module. `Check.lean` prints all five definitions, all seven theorem types, and all seven transitive axiom lists. The separate environment-inspection harness prints every constant whose compiled module of origin is `Conjecture1066`, including its type, safety flags, and axioms. It inspects existing declarations and proves no submitted theorem.

Expected results: successful build and strict replays; twelve compiled-origin constants (five definitions, seven theorems); only `propext`, `Classical.choice`, and `Quot.sound` as theorem axioms; no custom axioms, admissions, `native_decide`, unsafe or partial proof declarations. The final results are `Conjecture1066.universal_conjecture_false` and `Conjecture1066.existential_prime_conjecture_false`.

No auxiliary search or numerical program is needed for this proof, and none was used. The arithmetic is exact inside Lean; ordinary `decide` is used only for the numeral proposition `2 ≤ 2`.

## Report and audit records

`main.tex` is standalone. Rebuild it with a normal LaTeX installation, for example:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The supplied PDF was compiled from the exact source with the desktop compiler and exported with Tectonic 0.17.0; both final pages were rendered and visually inspected. A different TeX engine can produce different PDF bytes while preserving the content.

`verification.txt` summarizes the completed local checks. `verification/strict-replay.json` contains execution commands, timings, dependency identities, source hashes, and all trust checks. The other records contain the build transcript, complete type/axiom and environment audits, PDF diagnostics/text/renders, and eligibility records. Historical local paths identify the checked files; the commands above reproduce the proof from this package without those paths. `verification/independent-verify.py` is the exact coordinator inspection runner and records its original scratch/cache locations; it is not a mathematical dependency or a portable one-command installer.

`SEMANTIC_REVIEW.md` records the independent final review against the exact frozen input manifest. `verification/SHA256SUMS.json` covers every other packaged file. Local verification and independent agent review are distinct from repository maintainer acceptance.
