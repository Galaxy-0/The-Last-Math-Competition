# Independent semantic review: 00000000426

Verdict: **PASS for the literal existential statement, with an essential scope note.**

Read the complete current Lean file and both source-language statements.
The manuscript was not yet present at review time. This is a core/source
review, not a PDF or manuscript-finalization review.

The objects are genuine two-position Boolean words, acted on by the actual
cyclic rotation group C2 (group laws, generator order, and complete group
enumeration are proved). The ambient position action is nontrivial; its
restriction to the singleton all-zero word is trivial, which standard CSP
does allow. `equalWord_correct` verifies equality of functions through both
positions, and `fixedCount` therefore counts genuine fixed words. The
polynomial is the actual coefficient list [1]. Evaluation is Horner
evaluation, and `polynomial_one_at_every_point` is universal over every
evaluation algebra satisfying elementary ring laws. Thus it is sufficient
for evaluation at complex roots as well, despite the concrete final example
also being instantiated over integers. No finite complex-root enumeration
or unjustified numerical surrogate is being used.

The scope note is unavoidable: the parenthetical phrase "nontrivial
counting" cannot mean cardinality greater than one, because CSP at the
identity gives |X|=X(1)=1. The theorem `identity_forces_singleton` proves
exactly this. A final paper may claim the literal requested existence but
must not claim the parenthetical nontrivial-counting interpretation.

Primary definition checked: Reiner--Stanton--White (2004),
https://sites.math.washington.edu/~billey/classes/561.fall.2021/past.articles/reiner.stanton.white.pdf .
The defining equality is fixed points versus evaluation; no faithfulness
requirement excludes this example.

## Independent execution

Command (working directory: the reviewed `lean` directory):
`tools/lean-4.19.0-windows/bin/lean.exe -DwarningAsError=true Main.lean`

Independently executed by reviewer on 2026-10-03: exit 0. The printed
dependency lists contain only standard logical axioms (at most `propext`
and `Quot.sound`); no custom axiom, `sorry`, `admit`, or `native_decide`.
No author file was edited. No GitHub operation was performed.

## Reviewed file fingerprints

- `round4/root/00000000426/lean/Main.lean`: `e00700c286d4efb05052492448c3fd67b32fa2d1624834bef20d54dddf777a3d`
- `round4/root/00000000426/SOURCE.md`: `168decdd1f3c5ef914961af5ec1dc138a9f93aefff4f31f96d3815fb53e6cfef`

## Manuscript addendum

The complete current main.tex was subsequently read. PASS: it accurately presents the same mathematics and retains the essential scope limitation above. No change to the mathematical verdict. Reviewed main.tex SHA-256: 34968f3b120d8aea3bad0d03f3ea65627541ec53d473bcf1889922044db6ded6.

