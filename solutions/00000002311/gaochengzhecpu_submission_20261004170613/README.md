# Disproof of conjecture 00000002311

The source asserts that the proportion of fixed-point-free elements
(derangements) of a transitive group on Omega is at least c/|Omega| with
c = 1/2, and that this constant is tight, as verified by Frobenius
groups. The inequality is true, but the tightness clause is false: for
every finite transitive group of degree n >= 2 the proportion is at
least 1/n (Cameron-Cohen). So no transitive group, Frobenius or not,
attains or approaches (1/2)/n. The tight constant is 1, and it is
attained by the Frobenius group S3 on three points (proportion 1/3).
Every Frobenius group of degree n has exactly n - 1 derangements.

## Earlier submission

Pull request 190 (orionsheep) addressed the same tightness clause with
the Frobenius group AGL(1,7): 6 derangements among 42 elements, so the
realised constant is 1. It was closed without merging on 2026-10-03.
The computation was correct. The reviewer named two errors. First, the
Lean file used Lean core only and its decisive theorem was
`theorem not_half_tight : ¬ (6 = 3)`; no group, action, derangement
proportion or tightness statement occurred. Second, one Frobenius group
with constant 1 does not show that no other Frobenius group does
better; this needs a general fact, which that submission gave only in
prose and only for the groups C_p : C_m. This submission proves the
general fact for all transitive groups and for all Frobenius groups,
with Mathlib's groups and actions. main.tex has the full account.

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
the complete proof. In Lean, `derangements G Ω` and
`derangementProportion G Ω` are defined for a Mathlib `MulAction`.
`cameron_cohen` proves |G| <= |Omega| * |derangements| for every finite
group acting transitively (`MulAction.IsPretransitive`) on a finite set
with at least two points, using Mathlib's Burnside lemma on Omega and on
Omega x Omega. `frobenius_card_derangements` proves that a Frobenius
action of degree n has n - 1 derangements. `s3_isFrobenius` and
`s3_proportion` treat `Equiv.Perm (Fin 3)` on `Fin 3`. The propositions
`LowerBound c`, `CannotBeImproved c`, `AttainedByFrobenius c` and
`ApproachedByFrobenius c` state the bound and three readings of
tightness; `conjecture_false` negates the conjunction of the bound with
c = 1/2 and the disjunction of the three readings, and
`corrected_statement` proves all of them for c = 1.

This is a disproof of the source's statement as a whole, through its
tightness clause. The bound itself is true and is proved in a stronger
form. "The corrected constant" is read as the stated constant c = 1/2.
The degree is assumed to be at least two; for degree one there are no
derangements and the bound fails, which is not used. Actions are not
assumed faithful. The Frobenius property is defined in the file by the
permutation-group condition (transitive, degree at least two, no
non-identity element fixes two points, some non-identity element fixes
a point), because Mathlib has no such notion. The characterisation of
equality (sharply 2-transitive groups) and the divisibility of n - 1 by
the stabiliser order are remarks and are not formalised. The
Boston-Shalev conjecture itself is not addressed.

The verification directory contains an adversarial self-review, the
actual fresh compilation, direct Lean and standard axiom logs, and
source provenance. This problem was developed by a delegated AI agent
with a self-review; the coordinating agent reviews it separately. No
independent or external review is claimed. No custom axiom, sorry, admit
or native_decide is used.
