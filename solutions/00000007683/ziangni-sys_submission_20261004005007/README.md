# Conjecture 00000007683: a flat maximum at n = 3

**Result: disproof of the stated conjecture.**

The defining product gives

\[
[3]_q! = 1\,(1+q)(1+q+q^2) = 1+2q+2q^2+q^3.
\]

The coefficients at degrees 1 and 2 are both 2 and both global maxima.
Thus the coefficient sequence has an actual flat peak inside its support,
contradicting the assertion that it is flat-free for every fixed n.
This does not dispute log-concavity: the sequence `(1, 2, 2, 1)` is log-concave.
No claim about the other asymptotic clauses is needed for this disproof.

## Materials and verification

- `main.tex` and `main.pdf`: complete argument and formalization correspondence.
- `SOURCE.md`: both original language versions and their source commit.
- `lean/Main.lean`: self-contained formal proof using only Lean's `Std` library.
- `verify.py`: independent exact polynomial convolution and exhaustive
  inversion-count check of the six permutations of three elements.
- `lean-verification.txt`: compilation output and printed axiom dependencies.

From this submission directory:

```sh
cd lean
lake build
lake env lean -DwarningAsError=true Main.lean
cd ..
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The Lean toolchain is pinned to **4.19.0**. No Mathlib download is required.
All proof checks use the Lean kernel; there are no admitted proofs, native
decision procedures, or added axioms. The final theorems
`conjecture_flatFree_false` and `conjecture_false` have **no axiom dependencies**.
The polynomial evaluation and full-support maximum lemmas use only standard
Lean logical axioms as recorded in the build output.

`FlatFree` excludes equal adjacent coefficients within the finite coefficient
list. To make the meaning of the counterexample explicit, `flat_maximum`
additionally proves that the equal entries are global maxima; it does not
rely on the zero coefficients outside the support. `conjecture_false` treats
the remaining clauses as an arbitrary proposition: conjoining anything with
the refuted necessary clause is false. It does not substitute a new definition
for the remaining clauses or claim to verify them.

## Submission attribution

Submitted by **ziangni-sys**, with the mathematical argument, formal proof,
report, and auxiliary verification prepared using **OpenAI Codex**.
The directory timestamp is UTC. This is a solver submission for independent
review, not a claim of organizer acceptance.
