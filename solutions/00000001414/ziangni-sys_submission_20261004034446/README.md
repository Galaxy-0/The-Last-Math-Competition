# Conjecture 00000001414: the displayed rational cannot be a group order

This submission disproves the explicit equality |K10(Z)| = B12/(2·6!) in both source languages, understood as a finite group order. It does not compute any algebraic K-group, or refute an unspecified denominator-clearing/numerator-extraction operation. Absolute-value and explicitly parenthetical-denominator readings are also proved nonintegral.

Files: `report.tex`, `report.pdf`, reproducible `lean/` project, and `verification/` evidence. There is no auxiliary numerical code.

Build with Lean 4.19.0: `cd lean` then `lake build`; check the full source and audits with `lake env lean -DwarningAsError=true Main.lean`. Lake fetches Mathlib at the pinned public Git revision. Local cache junctions used during preparation are ignored and unnecessary for reproduction.

`Main.lean` computes actual Mathlib Bernoulli numbers from their recurrence, evaluates all three fractions exactly, proves no natural number equals any of them, and applies the obstruction to every finite group cardinality. The final existential finite-group formula is negated. Only standard logical axioms occur in the audited dependencies.

Compile the report with `tectonic report.tex`. See verification/README.md for the completed checks and exact scope.
