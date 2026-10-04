# Disproof of conjecture 00000003380

The complex algebra M_2(C) x M_2(C) is noncommutative. Exchanging its two
components is an algebra automorphism preserving the usual adjoint, but
it moves the central idempotent (I,0). Every inner automorphism fixes that
element. Hence the conjectured universal innerness assertion is false.

## Reproduction

With Lean 4.19.0 and the supplied public-Git, commit-pinned dependencies:

```text
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

The cache command is optional if dependencies have already been built.
Compile main.tex with Tectonic or a compatible LaTeX installation.
No supplementary numerical program is needed.

## Scope and artifacts

The exact bilingual source is in SOURCE.md. The paper main.tex/main.pdf
contains the complete proof and its precise formalization boundary.
The Lean project defines actual complex matrices, their product algebra,
a genuine complex algebra equivalence, and innerness by all actual units.
It proves noncommutativity, the central idempotent obstruction, and the
negation of the universal innerness assertion. Adjoint preservation is
also proved. A normed C*-algebra API is not used or claimed.

The unit implementing an inner automorphism must be an element of the
algebra itself; an implementer in a larger ambient algebra is irrelevant.
The source imposes no simplicity or factor condition. The proof does not
claim to refute variants with additional hypotheses or define the
unspecified measure-of-innerness phrase.

The verification directory records an adversarial self-review and a
distinct delegated agent's internal review, plus
actual fresh compilation and direct Lean logs, standard axiom audits,
source provenance, and final PDF inspection. No external independent
review is claimed. No custom axiom, sorry, admit or native_decide is used.
