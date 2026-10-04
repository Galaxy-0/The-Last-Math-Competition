# Disproof of conjecture 00000003842

The source claims that the number of hypoplactic classes of words of
length at most l over an n-letter alphabet equals the number of plane
partitions in a 2 x n x l box. Over two letters there are 7 classes of
length at most 2 (4 of length exactly 2), but the 2 x 2 x 2 box
contains 20 plane partitions. The identity also fails for every l >= 1
when n = 1 (l + 1 classes, at least l + 2 plane partitions) and for
every n >= 1 when l = 1 (n + 1 classes, at least n + 2 plane
partitions). Both the English reading (length at most l) and the
Chinese reading (length exactly l) are refuted.

## Earlier submission

Pull request 280 (orionsheep) proposed the instance n = 2, l = 2 and
was closed without merging on 2026-10-03. The reviewer's reason: its
main Lean theorem was the conjunction 2 + 4 = 6, 6 >= 6,
17280 / 864 = 20, 20 > 6, with no hypoplactic class and no plane
partition defined in Lean, and the hand-entered word count omitted the
empty word (7 words, not 6). The Lean file of that submission was read:
the objects occur only in comments. The mathematical idea was right.
This submission defines the hypoplactic congruence on Mathlib's free
monoid, the sets of classes of a given length and plane partitions in a
box, proves the exact counts 4, 7 and 20, and negates the identity
quantified over all n and l. main.tex has the full account.

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
the complete proof. In Lean, the hypoplactic congruence is Mathlib's
conGen of the two Knuth relations and the two quartic hypoplactic
relations on FreeMonoid of a linearly ordered alphabet, and the
hypoplactic monoid is the quotient monoid. classesOfLength and
classesUpToLength are the sets of its elements represented by a word of
length exactly l, respectively at most l. PlanePartition a b c is the
type of a x b arrays with entries in {0, ..., c} that are weakly
decreasing along rows and columns. The final theorems
conjecture_false_upTo and conjecture_false_exact negate the identity
for all n and l in the two readings.

Lean proves: equivalent words have equal length; distinct equivalent
words have length at least 3; the number of classes of length l <= 2 is
n^l; over one letter there is one class of each length; the 2 x 2 x 2
box has exactly 20 plane partitions; the 2 x 1 x l box (l >= 1) has at
least l + 2 and the 2 x n x 1 box (n >= 1) at least n + 2.

Not formalised: the exact binomial values of the last two counts,
MacMahon's formula, the symmetry of the plane-partition count in the
three sides, the quasi-ribbon formula and the table in the remark of
the paper, and the equivalence of the presentation used here with the
definition of the hypoplactic monoid by quasi-ribbon tableaux. The
counterexamples use only that every defining relation preserves length
and has length at least 3.

The verification directory contains an adversarial self-review, the
actual fresh compilation, direct Lean and standard axiom logs, source
provenance, and final PDF inspection. This problem was developed by a
delegated AI agent with a self-review; the coordinating agent reviews
it separately. No independent or external review is claimed. No custom
axiom, sorry, admit or native_decide is used.
