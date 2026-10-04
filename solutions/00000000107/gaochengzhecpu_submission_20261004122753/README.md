# Conjecture 00000000107: disproved

The source quantifies over **every fixed nonzero integer** constant. Choose that constant to be `2`. At every even degree `n>=2`, the polynomial `X^n-X-2` has rational root `-1`, and its actual Galois group over the rationals has order at most `(n-1)! < n!`. It therefore cannot be abstractly isomorphic to `S_n`.

For every degree threshold `N`, the degree `2*(N+1)` is an explicit counterexample at this same fixed integer. Thus the conjecture fails in its eventual sense, not merely at a finite collection of exceptional degrees.

## Reuse and independence

This is the **same constant-2 obstruction** also used for the prime-parameter Conjecture 00000000095. The construction and general Galois-group lemmas are reused transparently; this is not claimed to be a different mathematical construction. Conjecture 107 has its own integer-parameter quantifier, formalized here with a constant of type `Int` and the hypothesis that it is nonzero.

This package is self-contained and has no dependency on the submission or PR for 95. All needed proof source is included in its own `Main.lean`, and only public pinned Mathlib dependencies are required. The final theorem is specifically the negation of the statement for **all nonzero integers**, not a renamed prime-parameter theorem.

## Contents

- `main.tex`, `main.pdf`: full proof, explicit reuse statement, and formalization correspondence.
- `SOURCE.md`: byte-exact bilingual conjecture.
- `lean/Main.lean`: actual rational polynomials, splitting-field automorphism groups, degree/factorization lemmas, cardinality bounds, and the final integer-parameter negation.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`: portable pinned project.
- `verify.py`: six exact arithmetic sample checks, supplementary to the generic proof.
- `verification/BUILD.json` and adjacent logs: fresh build, direct Lean, axiom audit, dependency identities, Python output, PDF compilation/rendering, and source hashes.
- `verification/SELF_REVIEW.md`: authoring-agent adversarial review.

## Reproduce

With Lean installed through elan, run from `lean/`:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

The project pins Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All transitive Git dependencies have locked revisions. Optional `lake exe cache get` fetches official Mathlib build artifacts on a fresh machine instead of rebuilding the dependencies.

From the submission directory:

```text
python verify.py
tectonic main.tex
```

The Python script uses only exact standard-library integer arithmetic. It checks degrees 2, 4, 6, 8, 10, and 20: evaluation at `-1`, multiplication of an explicit quotient by `X+1`, quotient degree, and the strict factorial comparison. It does not compute exact Galois groups or infer an infinite theorem from the samples.

## Formalization and scope

`trinomial (p : Int) (d : Nat)` is the rational polynomial `X^d-X-C(p)`. `Polynomial.Gal` is Mathlib's actual group of rational algebra automorphisms of its splitting field. `FullSymmetricGalois p d` asserts an actual multiplicative equivalence to `Equiv.Perm (Fin d)`.

The general factorial bound uses the faithful action on the actual root set. The linear-factor step uses the injective Galois restriction map for a product and triviality of the group of a rational linear factor. No irreducibility assumption on the quotient is required.

`even_degree_gal_card_bound` proves the group order is at most `(d-1)!`. `even_degree_not_full_symmetric` rules out the actual abstract group equivalence. `arbitrarily_large_counterexamples` supplies the explicit even degree beyond every threshold.

`EventualFullSymmetricForEveryNonzeroInteger` quantifies over `p : Int` with `p != 0`. Its negation is the final theorem `conjecture107_false`. This is the exact integer-parameter version requested by the source. The paper's failure-of-density-one observation is an elementary consequence of the even-degree family; a separate asymptotic-density formalization is not claimed. Neither odd degrees nor a corrected statement excluding the parameter 2 are resolved here.

## Validation and review

The exact source SHA-256 is `8b18dde7c2a62ce62f2851febb2d3ce07191849865a8905d7c16d80d95d15766`.

`BUILD.json` records the final fresh-build evidence. The submission's own Lean artifacts are not reused. Existing artifacts from unmodified official dependencies at pinned Git commits may be reused. The printed theorem dependencies are only `propext`, `Classical.choice`, and `Quot.sound`; the proof contains no holes or custom axioms.

The native LaTeX editor was requested, and native compilation was attempted. Its `Unable to find standard directories for platform` failure is recorded in `native-compiler.json`. The delivered PDF is generated using the existing Tectonic installation and checked through Poppler-rendered images of every final page.

The completed evidence records a successful fresh `lake build`, direct Lean with warnings treated as errors, eight standard-axiom audits, all six exact auxiliary checks, and warning-free Tectonic export. Both final PDF pages were visually inspected, and `pdf_visual_review` is `PASS`.

Authoring-agent self-review is complete. Parent review and a final upstream source/duplicate check are required before publication. This agent performed no GitHub writes.
