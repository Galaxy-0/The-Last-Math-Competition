# Disproof of conjecture 00000002305

The Frobenius group G = C31 : C5 of order 155, realised as the affine
maps x -> 2^k x + a of Z/31Z, has exactly 11 conjugacy classes. The
stabiliser H of 0 is a maximal subgroup of index 31. Since 11 < 31/2,
the bound k(G) >= (1/2) [G:H] for maximal H fails. It fails for every
constant c > 11/31.

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
the complete proof. The Lean project builds the group on pairs
(a, k) in ZMod 31 x ZMod 5, proves the group axioms and a faithful
affine action, and uses Mathlib's Subgroup, Subgroup.index, IsCoatom
(maximal subgroup) and ConjClasses (conjugacy classes). The class
number is proved to be exactly 11, and the final theorem negates the
bound quantified over every finite group and every maximal subgroup.

The source is read as a statement about every finite group and every
maximal subgroup. The example does not address a reading in which H is
only some maximal subgroup: the normal subgroup of order 31 has index 5.
The source does not define epsilon(G); the corollary records the range
of constants for which this example fails. No claim is made about the
tightness clause.

The verification directory contains an adversarial self-review, the
actual fresh compilation, direct Lean and standard axiom logs, source
provenance, and final PDF inspection. This problem was developed and
reviewed by a single AI agent; no independent review is claimed. No
custom axiom, sorry, admit or native_decide is used.
