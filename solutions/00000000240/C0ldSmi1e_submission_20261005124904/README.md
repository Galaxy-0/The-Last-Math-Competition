# Disproof of the equality clause of conjecture 00000000240

The four-dimensional origin-symmetric convex body

`K = [-1,1] × {x in R^3 : |x_1| + |x_2| + |x_3| <= 1}`

has Lebesgue volume `8/3`, while its actual polar has volume `4`. Its Mahler volume is therefore `32/3 = 4^4/4!`. Nevertheless, K has 12 extreme points, whereas the four-dimensional cube has 16 and the cross-polytope has 8. It is a linear image of neither: a linear map onto a full-dimensional body must be invertible, and invertible maps preserve extreme points bijectively.

This disproves the necessary equality classification shared by both language versions. It does not claim to disprove or settle the general Mahler lower-bound inequality. The final Lean statements explicitly refute both dimension-four conjunctions; that instance suffices to refute the all-dimension assertion.

- `main.tex` and `main.pdf`: matching four-page mathematical report.
- `conjecture.md`: exact bilingual source.
- `lean/`: complete Lean 4.19.0 / Mathlib v4.19.0 project with all dependency revisions pinned.
- `reproduce.py`: independent exact rational facet, duality and volume checks.
- `VERIFICATION.md`: reproduction commands, verification coverage and limitations.
- `SEMANTIC_REVIEW.json` and `SEMANTIC_REVIEW.txt`: separate nonauthor review.
- `verification/`: input identities, execution evidence, complete declaration audit and report checks.

The main witness theorem is `Mahler240.counterexample`. The final negations are `Mahler240.conjecture_00000000240_english_false` and `Mahler240.conjecture_00000000240_chinese_false`.

This is an AI-produced submission. The mathematical author began in a fresh context containing only this candidate's exact source, repository guides and pinned library infrastructure. A separate fresh nonauthor reviewed the mathematics, definitions, report and executable checks. The coordinator added only two compiler annotations to the author's proof. Local verification is distinct from acceptance by repository maintainers.
