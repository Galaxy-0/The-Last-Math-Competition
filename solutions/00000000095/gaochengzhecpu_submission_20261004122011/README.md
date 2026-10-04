# Conjecture 00000000095: disproved

For the fixed prime `p=2`, the polynomial `f_d = X^d-X-2` has the rational root `-1` at every even degree `d>=2`. Its Galois group over the rationals has order at most `(d-1)!`, strictly smaller than `d!`. Thus it cannot be isomorphic to `S_d`, even as an abstract group.

This is an unbounded counterexample family at one fixed prime. For every threshold `N`, the degree `2*(N+1)` is an explicit counterexample. The submission therefore refutes the usual eventual meaning of "for every fixed prime p, as d tends to infinity," rather than relying on a single exceptional small degree. Both source languages include the prime 2 and all sufficiently large degrees without parity restrictions.

## Files

- `main.tex`, `main.pdf`: complete proof, source interpretation, and formalization correspondence.
- `SOURCE.md`: byte-exact original bilingual statement.
- `lean/Main.lean`: actual rational polynomials, splitting-field automorphism groups, faithful root actions, factorization, cardinality bounds, and asymptotic negation.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`: portable pinned Lean project using public Git dependencies.
- `verify.py`: supplementary exact arithmetic checks for six even degrees.
- `verification/BUILD.json` and adjacent logs: actual fresh builds, theorem axioms, dependency identities, auxiliary results, and PDF export/render checks.
- `verification/SELF_REVIEW.md`: authoring-agent adversarial review.

## Reproduction

From `lean/`, with Lean available through elan:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

The project pins Lean 4.19.0 and Mathlib at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Every transitive Git dependency is locked in the manifest. On a new machine, `lake exe cache get` may fetch official dependency artifacts instead of compiling Mathlib from source.

From the submission directory:

```text
python verify.py
tectonic main.tex
```

The Python script uses only the standard library and exact integers. It checks the rational root, expands the explicit quotient times `X+1`, verifies degrees, and compares factorials at degrees 2, 4, 6, 8, 10, and 20. It does not claim to compute exact Galois groups. The group-theoretic order bound and infinite family are formally proved in Lean.

## Formalization

`trinomial p d` is the actual element `X^d-X-C(p)` of `Polynomial Q`. `Polynomial.Gal` is Mathlib's actual group of rational algebra automorphisms of its splitting field. `FullSymmetricGalois p d` means an actual multiplicative equivalence from this group to the permutation group on `Fin d`.

The general lemma `gal_card_le_factorial_degree` uses Mathlib's faithful root action and the bound on the number of distinct roots. `gal_card_linear_mul_le` uses the injective restriction map for a polynomial product and triviality of the Galois group of a rational linear factor. These lemmas justify the full abstract-group order argument, rather than treating reducibility alone as the formal conclusion.

The theorem `even_degree_gal_card_bound` gives `(d-1)!` for every even `d>=2`. `even_degree_not_full_symmetric` rules out the actual group isomorphism by cardinality. `arbitrarily_large_counterexamples` supplies a counterexample for every threshold. `conjecture95_false` negates the quantified eventual claim for every fixed prime, using the verified primality of 2.

No irreducibility assumption for the quotient is required. Its set of distinct roots has cardinality at most its degree, which suffices even without proving separability as a separate step. The paper explains equality of splitting fields; the formal proof obtains the needed inequality through Mathlib's restriction injection instead.

The paper's density-one observation follows from failure at every even degree. The formal theorem states the stronger pointwise family and explicit unboundedness; it does not introduce a separate asymptotic density formalization. This submission makes no claim about odd degrees or a conjecture restricted to odd primes.

## Source, validation, and review

The source SHA-256 is `43762b1ff9723495c1dd89a5506982c33d61fda7a28aed5c519ce56b71b1d3cc`.

The final clean-build status, source hashes, standard-axiom audit, and PDF checks are in `verification/BUILD.json`. Dependencies are unmodified official sources at pinned commits; their existing artifacts may be reused, but the submitted Main module is built in a fresh directory. Printed theorem axioms contain only `propext`, `Classical.choice`, and `Quot.sound`.

The native source editor was requested and native compilation was attempted; it returned `Unable to find standard directories for platform`. That platform error is recorded in `verification/native-compiler.json`. PDF export uses the existing Tectonic installation, followed by Poppler rendering and direct inspection of every final page.

The final evidence records a successful fresh `lake build`, direct Lean with warnings treated as errors, all six exact auxiliary checks, and warning-free Tectonic export. Both final PDF pages were rendered and visually inspected; `pdf_visual_review` is `PASS`.

Authoring-agent self-review is complete. Parent review and the final upstream source/duplicate check must precede publication. This agent performed no GitHub writes.
