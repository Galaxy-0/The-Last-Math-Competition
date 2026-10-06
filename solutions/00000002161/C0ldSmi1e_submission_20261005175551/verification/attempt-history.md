# Inspection attempt history

The frozen mathematical sources did not change during independent verification.
The first clean build and all three strict source replays succeeded. The expanded
inspection then stopped because its runtime classification recognized only
`_cstage1` and `_cstage2` definitions, and not six unsafe compiler-generated axiom
stubs. Its original records are retained in `inspection-initial-attempt/`.

The six entries were two eager-lambda-lifting artifacts and four function
specializations. Their origin was checked independently against Lean 4.19.0:

- https://github.com/leanprover/lean4/blob/v4.19.0/src/library/compiler/eager_lambda_lifting.cpp#L224-L231
- https://github.com/leanprover/lean4/blob/v4.19.0/src/library/compiler/specialize.cpp#L906-L920

The final inspector has an exact six-name allowlist, checks their unsafe axiom
kind and expected properties, retains every artifact in the inventory, and
requires every logical declaration's transitive dependency closure to exclude
all unsafe, partial, or missing declarations. Every logical axiom dependency
must remain among `propext`, `Classical.choice`, and `Quot.sound`.

The corrected inspector was run in a second fresh project directory and passed.
The independent semantic reviewer separately built and inspected the same frozen
source, reaching the same counts and logical-trust result. The source changes
were exclusively to the external inspection tool; no proof was weakened to pass
an audit. Compiler runtime records are not mathematical assumptions.
