# Conjecture 00000006542 — counterexample

The actual Ihara Euler product of the triangle is `(1-u^3)^(-2)`.
It has an order-two pole at `u=1`, while `1` is not an eigenvalue of
the triangle's actual adjacency action on arbitrary complex vectors.
This refutes the explicit English/Chinese pole-reciprocal claim.

The source does not exclude cycle graphs or require degree at least 3.
The standard Ihara definition used here permits connected graphs of
fundamental-group rank at least 1 without degree-one vertices.

## Files

- `SOURCE.md`: original English and Chinese statement.
- `main.tex`: mathematical proof and detailed semantic map to Lean.
- `lean/Main.lean`: arbitrary-length primitive walk classification;
  quotient by rotation; complete Euler product; pole certificate;
  actual adjacency operator and absence of eigenvalue 1.
- `verify.py`: independent finite walk and exact polynomial checks for
  this conjecture only; not a substitute for the unbounded Lean proof.
- `RESULT.json`, `lake-build.log`, `lean-axioms.log`: actual validation
  commands, results and source hashes.

## Reproduce

With the bundled Lean 4.19.0 `bin` directory on PATH:

```text
cd lean
lake build
lake env lean -DwarningAsError=true Main.lean
```

Run `python verify.py` in this problem directory for the auxiliary checks.
Only `Std` is used. No `sorry`, `admit`, `native_decide`, or custom axioms.
The generic scalar proof applies in particular to the usual complex field;
the integer scalar instance is not a restriction on allowed eigenvectors.

Local work only. This round has no authorization to publish or upload.
