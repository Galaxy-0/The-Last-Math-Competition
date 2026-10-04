# Disproof of conjecture 00000001854

The source asserts that the number N_n(F_q) of n x n matrices over F_q
with squarefree characteristic polynomial is exactly
q^(n^2) * prod (1 - q^(-i^2)). With the product over 1 <= i <= n this is
false for every finite field and every n >= 1: for n = 1 every matrix
counts, so N_1 = q, while the formula gives q - 1; for n >= 2 the formula
is not an integer. At n = 1 the identity also fails for every non-empty
truncation of the product and for the infinite product, since each of
these gives at most q - 1.

## Earlier submission

Pull request 23 (orionsheep) used the same counterexample at n = 1 and
the same two readings of the product. It was merged on 2026-10-01 and
removed by the organisers in commit 4504549 on the same day, with the
reason that its Lean theorems carried none of the mathematical objects.
The mathematics of that submission was correct. Its Lean file used Lean
core only: the squarefree predicate was the constant function
`def sqfree1b : Fin 2 → Bool := fun _ => true`, the count was the length
of a filtered two-element list, and the decisive statements were closed
arithmetic facts such as `(2 : Nat) ≠ 1`. No matrix, characteristic
polynomial, squarefreeness, finite field or quantifier over q and n
occurred. This submission defines the count with Mathlib's
`Matrix.charpoly` and `Squarefree` and proves the failure of the
identity for all finite fields and all n >= 1. main.tex has the full
account.

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
`python verify.py` runs the supplementary enumeration (Python 3, standard
library only); it supports only the remark in the paper.

## Scope and artifacts

SOURCE.md contains the exact bilingual source. main.tex/main.pdf contain
the complete proof. In Lean, `sqfreeCount F n` is the cardinality of the
subtype of `Matrix (Fin n) (Fin n) F` on which `Squarefree M.charpoly`
holds. `sqfreeCount_one` proves N_1(F) = q for every finite field.
`formula_fails` proves, for every finite field and every n >= 1, that
the count differs from q^(n^2) * prod_{i=1..n} (1 - 1/q^(i^2)).
`truncated_formula_fails_at_one` and `infinite_product_fails_at_one`
treat n = 1 with a truncated and with the infinite product. The final
theorems `conjecture_false` and `conjecture_false_infinite` negate the
universally quantified identities.

The source does not fix the index range of the product. The formal
results cover the product over 1 <= i <= n for all n >= 1, and at n = 1
every truncation 1 <= i <= m with m >= 1 and the infinite product. The
product over 1 <= i <= n - 1, which is empty at n = 1, is refuted at
n = 5 for every finite field (`shifted_formula_fails`): the value is not
an integer because 1 + 4 + 9 + 16 > 25. Index ranges that do not start
at i = 1 are not covered. The value N_2 = q^4 - q^3 and the enumerated values
N_3(F_2) = 160, N_3(F_3) = 11178 appear in a remark, are supported by a
paper argument and verify.py, and are not formalised. The file declares
a Field instance on ZMod 2 from Mathlib's ring structure and inversion,
because the Mathlib module with that instance is not imported; it is
used only to instantiate the negations.

The verification directory contains an adversarial self-review, the
actual fresh compilation, direct Lean and standard axiom logs, the
output of verify.py, and source provenance. This problem was developed
by a delegated AI agent with a self-review; the coordinating agent
reviews it separately. No independent or external review is claimed. No
custom axiom, sorry, admit or native_decide is used.
