# Disproof of conjecture 00000004289

Every free abelian group is flat as an integer module. Thus, if every subgroup
of cardinality strictly below kappa is free, every such subgroup is flat.
No almost-free but not flat-free group exists at any threshold or carrier size.
The asserted least separation cardinal aleph omega therefore does not exist.

The project uses actual abelian groups, all additive subgroups, canonical
integer-module structures, standard basis freeness and tensor flatness, and
genuine cardinalities. The almost-free definition retains the whole group's
non-free requirement. Threshold and carrier cardinality are independently
quantified, so the disproof covers the source's unstated relation between them.
The separate aleph-one implication is true and is proved explicitly.

This disproves the necessary existence/minimum component of the compound
conjecture. It does not claim a formalization of coded ZFC derivability,
independence, or a Shelah black-box construction. These limits are stated in
the report and detailed correspondence record.

## Reproduce

Use the pinned Lean 4.19.0 toolchain and Mathlib v4.19.0 manifest in `lean/`.
From that directory, with the dependencies available:

```sh
lake build
lake env lean -DwarningAsError=true Conjecture4289.lean
lake env lean -DwarningAsError=true Check.lean
```

The explicit default target is `Conjecture4289`. The final theorem is
`Conjecture4289.conjecture4289_disproof`, negating the least-cardinal assertion.
The stronger `no_separation_exists` excludes actual existence for any threshold
and carrier cardinality. All statements are universe-polymorphic.

`Check.lean` prints all five definitions and all nine theorem types and axiom
dependencies. The exhaustive compiled-module audit additionally records every
generated constant. No external mathematical computation is required. The
source contains no admitted proofs, `native_decide`, custom axioms, unsafe
declarations or partial definitions.

## Materials

`main.tex` and `main.pdf` contain the complete report. `conjecture.md` is the
byte-identical bilingual source. `verification.txt` records the fresh build,
strict replays, exhaustive compiled-module inventory, dependency pins, PDF
checks and eligibility. The detailed author mapping is in
`verification/formal-correspondence.txt`; independent internal scrutiny is in
`SEMANTIC_REVIEW.md`. `verification/SHA256SUMS.json` covers every other file.

Inspection/export scripts and records under `verification/` preserve the exact
local audit. Their absolute scratch paths describe that run and are not needed
by the mathematical project. Local validation and independent internal review
do not establish maintainer acceptance.
