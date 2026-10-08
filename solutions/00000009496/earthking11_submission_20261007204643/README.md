# Conjecture 00000009496: Chevalley–Warning divisibility

The conjecture's mathematical assertion is the Chevalley–Warning theorem for
systems of polynomial equations over a prime field. Let (p) be prime and
let (f_i\in\mathbb F_p[X_1,\ldots,X_n]), for (i=1,\ldots,r). If
\(\sum_i\deg f_i<n\), then the number of their common zeroes in
\(\mathbb F_p^n\) is divisible by \(p\).

`solution.tex` gives a complete elementary proof. `solution.pdf` is its
rendered report. `lean/Main.lean` states the general finite-field theorem,
which includes the prime-field assertion by taking the field to be `ZMod p`,
the variable type `Fin n`, and the equation index type `Fin r`. Its subtype
cardinal counts the actual common zeroes. The proof uses Mathlib's fully
proved Chevalley–Warning theorem
`char_dvd_card_solutions_of_fintype_sum_lt`; it does not assume the desired
divisibility or replace the zero set by a number.

The official statement is terse. We interpret its phrase about the
"combination" as the standard degree-sum hypothesis. No claim about an
unspecified stronger divisibility is made.

## Reproduce

From `lean/`, run `lake build`. The project pins Lean v4.33.1 and Mathlib
revision `0df444a360eaa60ab8c11dca51a86af692955474` in its Lake
configuration and manifest. The `#print axioms` commands at the end of
`Main.lean` audit both the final theorem and its Mathlib dependency.

To regenerate the PDF, run `tectonic solution.tex` from this submission
directory. The local `.lake/` build directory is intentionally excluded.
