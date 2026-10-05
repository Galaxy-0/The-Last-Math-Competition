# Disproof of conjecture 00000002131

Let both input patterns be the one-element permutation. Its avoidance count is
zero at every positive size, so its Stanley-Wilf limit is 0. The direct sum is
the increasing two-element pattern. Exactly one permutation of every size avoids
it: the decreasing permutation. Its limit is 1, contradicting multiplicativity.

The statement does not exclude length-one patterns. This convention is explicit
in the report and formal domain. The project refutes the displayed universal
formula on actual permutations, actual classical avoidance cardinalities, and
genuine real limits. It does not assign an invented meaning to the unspecified
"complete characterization" clause or claim to settle an amended domain that
excludes the chosen inputs.

## Reproduce

Use the pinned Lean 4.19.0 toolchain and Mathlib v4.19.0 manifest in `lean/`.
From that directory, with the dependencies available:

```sh
lake build
lake env lean -DwarningAsError=true Conjecture2131.lean
lake env lean -DwarningAsError=true Check.lean
```

The explicit default target is `Conjecture2131`. The main theorem is
`Conjecture2131.not_universalMultiplicativity`. The theorem
`nonmultiplicative_witness` proves the actual three limits and their inequality.
The numerical-function formulation is connected by
`universal_iff_numerical_of_verified_limits`; its hypothesis requires verified
real limits, and is not needed or assumed by the main counterexample.
`not_source_conjunction` records the logical consequence for any additional
clause without pretending to define that clause.

`Check.lean` prints all 12 definitions/abbreviations and all 28 theorem types
and axiom dependencies. The exhaustive compiled-module inventory also records
all generated constants. No external numerical computation is required. The
authored source contains no admitted proofs, `native_decide`, custom axioms,
unsafe declarations, partial definitions, or elaboration bypasses.

## Materials

`main.tex` and `main.pdf` give the complete report. `conjecture.md` is the exact
bilingual source. `verification.txt` records the independent build, strict source
replays, exhaustive declaration inventory, pins, PDF review, and eligibility.
`verification/formal-correspondence.txt` gives the author derivation and detailed
mapping. `SEMANTIC_REVIEW.md` records separate independent internal scrutiny.
`verification/SHA256SUMS.json` covers every other submission file.

Inspection/export scripts and records under `verification/` preserve the exact
local audits, including the separate author's inspection script and outputs.
Their absolute scratch paths describe those runs and are not required by the
mathematical project. Compiler-generated runtime constants are distinguished
from authored logical declarations in the exhaustive audit; none is silently
excluded. Local verification and internal review do not mean maintainer acceptance.
