# Proof of conjecture 00000002226

For a nonzero commutative ring R and n >= 1, the matrix ring M_n(R) has
the McCoy property if and only if n = 1. For n = 1 this is McCoy's
theorem for the commutative ring R. For n >= 2 the polynomials
f = (I - E22) + E12 x and g = E21 - E11 x satisfy f g = 0, while no
nonzero constant matrix annihilates f on the right; a mirrored pair
handles the left property. So M_n(R) is neither right nor left McCoy.

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

SOURCE.md contains the exact bilingual source. main.tex/main.pdf contain
the complete proof. The Lean project defines the right, left and
two-sided McCoy properties for an arbitrary ring and Mathlib's
polynomial ring, proves them for commutative rings from Mathlib's McCoy
theorem, transfers them to M_1(R) along an explicit ring isomorphism,
and refutes both one-sided properties for matrices of size at least two
over any nonzero ring. The main theorem is the stated equivalence for
Matrix (Fin n) (Fin n) R; the one-sided equivalences are also proved.

The result assumes R nonzero and n >= 1, the usual conventions for a
matrix ring. If R = 0 or n = 0, then M_n(R) is the zero ring, which is
McCoy vacuously; the Lean file records this as a separate lemma. A
reader who admits the zero ring should read the result as: the
equivalence holds exactly for nonzero R.

The verification directory contains an adversarial self-review, the
actual fresh compilation, direct Lean and standard axiom logs, source
provenance, and final PDF inspection. This problem was developed and
reviewed by a single AI agent; no independent review is claimed. No
custom axiom, sorry, admit or native_decide is used.
