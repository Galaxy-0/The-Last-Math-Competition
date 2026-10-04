# Disproof of conjecture 00000009611

The source claims that the minimal size of a nonnegative integer matrix
realising a Perron number as the entropy of a mixing subshift of finite
type is a function f(d) of its algebraic degree d, and that f(d) = d
exactly when the minimal polynomial is sign-alternating.

Let x be the real root of X^3 - X - 1 and y the real root of
X^3 + X^2 - 3X - 4 in [9/5, 2]. Both are Perron numbers of degree 3.
x is the Perron eigenvalue of the primitive 3 x 3 matrix
[[0,1,0],[0,0,1],[1,1,0]], and no smaller size is possible, so its
minimal size is 3. y is the Perron eigenvalue of the primitive 4 x 4
matrix [[0,0,1,2],[1,0,2,0],[0,1,0,0],[1,0,0,0]]. A 3 x 3 nonnegative
integer matrix with eigenvalue y would have characteristic polynomial
X^3 + X^2 - 3X - 4 and trace -1, which is impossible, so the minimal
size of y is 4. Hence no function of the degree gives the minimal size.
Also the minimal polynomial of x has two adjacent coefficients equal to
-1, so it is not sign-alternating although minimal size and degree
agree.

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
the complete proof. The Lean project uses Mathlib's Matrix, minpoly,
Matrix.charpoly and Polynomial. It defines primitive matrices, Perron
eigenvalues (an eigenvalue with a positive eigenvector), realisability
in a given size, the minimal size, the algebraic degree and Perron
numbers. It proves that a Perron eigenvalue bounds every complex
eigenvalue in modulus and that the logarithmic growth rate of the
number of paths, that is the entropy, is the logarithm of the Perron
eigenvalue. It proves irreducibility of both cubics over Q, the
existence of the two real roots, that both roots are Perron numbers of
degree 3, and that their minimal sizes are 3 and 4.

The final theorem `conjecture_false` negates: there is a function f
with minimal size f(degree) for every Perron number.
`conjecture_false_realized` negates the same statement quantified over
all numbers realised by some primitive matrix. `sign_criterion_false`
negates: for every Perron number, minimal size equals degree if and
only if no two adjacent coefficients of the minimal polynomial have the
same strict sign.

Not formalised: Lind's theorem (not used), the Perron-Frobenius
existence theorem (not used; realisability is defined by a positive
eigenvector, and the lower bounds hold for every real eigenvalue of
every nonnegative integer matrix), the equivalence of primitivity with
mixing, and the three remarks of the paper (the 0-1 matrix reading and
the converse direction of the sign criterion). The source does not
define "sign-alternating"; the paper states the reading used.

The verification directory contains an adversarial self-review, the
actual fresh compilation, direct Lean and standard axiom logs, source
provenance, and final PDF inspection. This problem was developed by a
delegated AI agent with a self-review; the coordinating agent reviews
it separately. No independent or external review is claimed. No custom
axiom, sorry, admit or native_decide is used.
