# Disproof of conjecture 00000007737

This submission disproves the asserted formula for the lower endpoint of the
support of the two-fold free multiplicative convolution of the uniform law on
`[0,1]`.

It is a submission for [The Last Math Competition](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition).

At `k = 2`, the asserted formula equals `16 / exp 2 > 1`. However,
if `0 ≤ a,b ≤ 1`, then `0 ≤ sqrt(a) * b * sqrt(a) ≤ 1`, so every scalar
spectral probability law of this product has nonempty support in `[0,1]`.
This includes the free product realization of the two uniform laws.

The Lean theorem `conjecture_00000007737_endpoint_false` proves this stronger
operator statement using Mathlib's C*-algebras, continuous functional calculus,
measure support, and real exponential. It also checks substitution into the
original formula. The free-product construction and its identification with
free multiplicative convolution are explained in the report; the Lean project
does not define the free-convolution operation itself.

With Lean/Elan installed, run in this directory:

```sh
lake exe cache get
lake build
```

The toolchain and Mathlib are pinned to `v4.33.1`; transitive revisions are
recorded in `lake-manifest.json`. The source prints the final theorems' axiom
dependencies, which are only `propext`, `Classical.choice`, and `Quot.sound`.
No proof placeholders, additional axioms, or native evaluation are used.

Compile `proof.tex` with `tectonic proof.tex` (tested with Tectonic 0.17.0), or
with `pdflatex proof.tex` twice. The PDF is generated from this LaTeX source.

Only the lower-endpoint clause is refuted; that suffices to disprove the
conjunction. The density and Stieltjes-transform clauses are not needed.
