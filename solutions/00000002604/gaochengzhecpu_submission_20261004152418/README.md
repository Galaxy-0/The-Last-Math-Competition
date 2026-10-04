# Disproof of conjecture 00000002604

The distributive lattices L1 = C4 x C2 and L2 = (C3 x C3) minus the
point (2,0) have eight elements each and the same layer-count vector
(1,2,2,2,1), counted from the bottom or from the top (so also the same
number of coatoms). They are not isomorphic: (1,1) in L2 has two
incomparable elements below it and two incomparable elements above it,
and no element of L1 has this property. So finite distributive lattices
with equal layer-count vectors need not be isomorphic.

## Earlier submission

Pull request 48 (earthking11) used an equivalent example, the ideal
lattices of two four-element posets. It was merged on 2026-10-01 and
removed by the organisers in re-audit commit 541cf4f on 2026-10-03
because non-isomorphism was never established. Its Lean theorem
`perms.all (fun p => IsIsoPerm leP leQ p) = false` states only that not
every bijection is an isomorphism; it does not state that no bijection
is one. That file also never formed the lattices or a statement about
lattice isomorphism. The mathematics of that submission was correct.
This submission proves `IsEmpty (L1 ≃o L2)` for Mathlib distributive
lattices and negates the universal claim. main.tex has the full account.

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
the complete proof. In Lean, L1 is Fin 4 x Fin 2 with Mathlib's product
order and DistribLattice instance; L2 is a subtype of Fin 3 x Fin 3
proved closed under sup and inf, with the induced DistribLattice
instance. Rank and corank functions are defined through Mathlib's
covering relation and proved for both lattices. The final theorem
negates: any two finite bounded distributive lattices whose corank
functions have equal layer counts are order isomorphic. The same is
proved for rank functions.

The English source says layer-count vector; the Chinese source counts
layers from the coatoms. Both readings are covered. The disproof
concerns the first clause; no claim is made about the Kruskal-Katona
clause. The identification of L1 and L2 with ideal lattices of posets
is a remark in the paper and is not formalised.

The verification directory contains an adversarial self-review, the
actual fresh compilation, direct Lean and standard axiom logs, source
provenance, and final PDF inspection. This problem was developed and
reviewed by a single AI agent; no independent review is claimed. No
custom axiom, sorry, admit or native_decide is used.
