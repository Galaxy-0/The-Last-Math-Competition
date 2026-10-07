# TLMC 00000001672: inconsistency of the statement as written

The Zarankiewicz product at `(7,7)` is `3 * 3 * 3 * 3 = 81`, not `77`. The headline `cr(K_{7,7}) = 77` and the asserted restatement that the formula holds for `min(m,n) <= 7` cannot both be true. Lean proves this for every function `cr : Nat -> Nat -> Nat`, together with the positive-parameter variant and the false parenthetical numerical claim.

**Scope:** Lean formally refutes the jointly asserted statement for every function `cr`, without computing crossing numbers. Separately, Woodall's computer-assisted theorem proves `cr(K_{7,7}) = 81` and `cr(K_{7,9}) = 144`, so the isolated headline `cr(K_{7,7}) = 77` is false as well. This published theorem is cited, **not formalized** here. The description of `K_{7,7}` as the smallest open instance is also false: the smallest unsettled cases are `K_{7,11}` and `K_{9,9}`. A supplementary Lean theorem shows that a bare equivalence between the abstract headline and the full range can have both sides false; it is not a crossing-number model.

Reference: D. R. Woodall, “Cyclic-order graphs and Zarankiewicz's crossing-number conjecture,” *Journal of Graph Theory* **17** (1993), 657–671, https://doi.org/10.1002/jgt.3190170602.

Contents:

- `report.tex`, `report.pdf`: complete proof, verbatim statement, scope discussion, Lean correspondence, citations, and axiom audit.
- `lean4/ZarankiewiczConsistency.lean`: one proof file, with seven theorems and final `#print axioms` commands.
- `lean4/lean-toolchain`, `lean4/lakefile.toml`, `lean4/lake-manifest.json`: standalone project pinned to Lean and Mathlib `v4.33.0`.
- `verify.py`: independent exact arithmetic check using only Python's standard library.
- `verification.txt`: successful compiler output, axiom audit, and Python check output.

Build a fresh project:

```sh
cd lean4
lake exe cache get && lake build
```

Reproduce the supplementary check and PDF from the submission directory:

```sh
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The proof uses core Lean only; the project also pins Mathlib for reproducibility. The final compiler audit reports no axioms for all seven theorems. No `sorry`, `admit`, `native_decide`, or added axiom declarations occur in the proof source. No code is vendored from trureturing or the example submissions.

Submitted by AlyciaBHZ on behalf of the Omega Institute (trureturing project, https://github.com/the-omega-institute/trureturing).
