# Conjecture 00000009978: finite termination is false

The actual formal power series ring `R = Q[[X]]` is a commutative fully bounded Noetherian ring. Its Jacobson radical is `J = (X)`, and for every natural number `N`, `J^N = (X^N)` contains the nonzero series `X^N`. Therefore no finite intersection of the initial radical powers is zero. The powers are strictly descending at every stage, although their infinite intersection is zero.

This refutes the explicit finite-termination conjunct of the original statement. It does not refute the zero infinite-intersection property or make a claim about Artinian rings. No interpretation of the source's unspecified exponential decay constant is needed.

## Delivered files

- `main.tex`, `main.pdf`: the complete proof, scope, and formalization correspondence, in two pages.
- `SOURCE.md`: the exact upstream source bytes, with no additions or normalized whitespace.
- `lean/Main.lean`: actual power-series ring, standard commutative FBN condition, actual Jacobson radical, all finite stages, strict descent, and zero infinite intersection.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`: public Git dependency URLs and pinned versions.
- `verification/SOURCE_PROVENANCE.md`: upstream blob/hash and the standard FBN definition reference.
- `verification/BUILD.json` and adjacent logs: actual build and artifact evidence.
- `verification/SELF_REVIEW.md`: authoring-agent adversarial self-review.

## Reproduce

Using elan, run from `lean/`:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

Lean is pinned to 4.19.0 and Mathlib to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Every transitive dependency is recorded in the Lake manifest. No local filesystem paths occur as submitted dependency sources. A new machine can optionally download the official Mathlib cache with `lake exe cache get` rather than rebuilding dependencies.

From the submission directory, reproduce the PDF with:

```text
tectonic main.tex
```

There is deliberately no finite-range numerical verifier. The result for every natural `N` is proved directly in Lean; no checked prefix of the sequence stands in for that theorem.

## Actual verification

- Fresh-directory `lake build`: passed.
- Direct Lean with `-DwarningAsError=true`: passed.
- Twelve printed axiom-dependency lists contain only `propext`, `Classical.choice`, and `Quot.sound`; no proof gaps, custom axioms, opaque declarations, or `native_decide` occur.
- The proof source was built afresh. Only unchanged official dependency artifacts at pinned Git commits were reused.
- Final Tectonic compilation: passed, two pages, no warnings.
- Both final Poppler page images were visually inspected and passed.
- Later changes were confined to TeX layout. The final PDF refresh checked that all Lean source/configuration hashes still matched the successful clean build, and recorded the final TeX/PDF hashes separately.
- Native editor opening was requested, and its compiler was actually invoked. It failed on the platform-directory issue recorded in `verification/native-compiler.json`; the final PDF comes from Tectonic.

## Formalization correspondence

`Ring` is Mathlib's untruncated `PowerSeries Q`, not polynomials modulo a cutoff. `radical` is `Ideal.jacobson` of the zero ideal, and is identified with `(X)` using the actual local-ring and power-series API.

`CommFBN` records Noetherianity plus the standard requirement on essential ideals in all prime quotients. This is the FBN condition specialized to commutative rings: left, right, and two-sided ideals coincide. `comm_noetherian_fbn` proves the condition, and `ideal_right_mul_closed` explicitly verifies right-multiplication closure of the ideals used. This is sufficient for the exhibited commutative ring; no library of arbitrary noncommutative FBN rings is claimed.

`prefixIntersection N` is the actual ideal intersection indexed by `Fin (N+1)`. It equals `J^N`. Nonvanishing and strict descent use the degree-`N` coefficient of the genuine series `X^N`; the infinite intersection theorem uses all coefficients. The formal statement quantifies over every natural stage without a finite search bound.

The standard FBN definition is verified against S. Caenepeel and T. Guedenon, *Fully bounded noetherian rings and Frobenius extensions*, arXiv:math/0503686v3, Introduction, page 1: https://arxiv.org/pdf/math/0503686v3 . The membership of the witness in the commutative specialization is also proved in Lean.

Review status: authoring-agent self-review complete; parent review and current duplicate recheck precede publication. This agent performed no GitHub writes and did not modify the earlier 00000007860 package.
