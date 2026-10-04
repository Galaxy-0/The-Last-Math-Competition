# Disproof of conjecture 00000008849

On the real Hilbert line, take A(x)=B(x)={1} and the identity coupling M. Both actual graphs are maximal monotone, but A(x)+MB(y)={2} for all inputs. Therefore neither independent solution pairs nor the displayed shared-input inclusion can have a solution.

The proof refutes the universal existence clause in both original language versions. Constant maximal monotone maps are allowed without a zero-existence hypothesis. No result about the other algorithmic or classification clauses is asserted.

Files: report.tex and the two-page report.pdf give the full proof and mathematical correspondence. lean/Main.lean verifies graph maximality under inclusion, the standard Hilbert inner product, actual continuous linear identity coupling and positivity, genuine coupled-value sets, and nonexistence.

## Reproduction

Install Lean 4.19.0 through elan. In lean/, run:

```text
lake update
lake exe cache get
lake build
lake env lean Main.lean -DwarningAsError=true
```

The Git dependency and manifest pin Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. No local dependency paths are committed. The ignored .lake directory may be regenerated normally.

Compile report.tex with a standard LaTeX engine or Tectonic. No auxiliary numerical code is needed.
