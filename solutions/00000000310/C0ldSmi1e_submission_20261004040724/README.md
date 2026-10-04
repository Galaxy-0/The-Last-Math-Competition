# Disproof of conjecture 00000000310

**Result:** the set defined in the conjecture is empty. Its Hausdorff dimension is zero, so the asserted dimension two is false.

For any point of the Euclidean plane, choose a perpendicular unit direction. The projection is zero, whose distance to the integers is zero. It cannot exceed a positive constant divided by a positive denominator. This excludes every point, even when the constant may depend on the direction.

## Exact formal scope

`lean/Conjecture310.lean` uses Mathlib's `EuclideanSpace ℝ (Fin 2)`, Euclidean norm and inner product, `Metric.infDist` to the range of the integer-to-real cast, and actual Hausdorff dimension `dimH`.

The quantified definition permits a separate positive constant for each unit direction and requires the bound for all positive natural denominators. This is the weaker reading of the source's word "uniformly"; a common positive constant would also be impossible.

The principal theorems prove:

- Every point has a perpendicular unit direction.
- In that direction, the nearest-integer distance is zero for every real multiplier.
- The stated set is empty.
- Its Hausdorff dimension is zero and is not two.
- Its intersection with every set is empty and has dimension zero.

The final theorem directly negates the conjecture's dimension assertion. The separate absolute-winning game is not formalized: a false dimension conjunct already disproves the full stated conjecture. The mathematical obstruction also persists for eventual-denominator or infinitely-many-denominator interpretations, as explained in the report.

## Contents

- `main.tex`, `main.pdf`: complete argument and formalization correspondence.
- `conjecture.md`: exact bilingual source at upstream commit `6ad05f1490626b518d19ad5c5603419f7a021d30`.
- `lean/`: complete pinned Lean project and theorem axiom audit.
- `verification.txt`: compiler, fresh project build, source replay, and axiom-audit results.
- `SEMANTIC_REVIEW.md`: internal independent-agent source review, distinct from the competition's official review.

## Reproduce

Install Lean `leanprover/lean4:v4.19.0` using your usual Lean toolchain manager. The Lake manifest pins Mathlib v4.19.0 to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, together with its dependencies.

From this directory:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture310.lean
lake env lean Check.lean
```

If the compiled cache downloader encounters a platform loader error, the equivalent interpreter invocation is:

```sh
lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
```

Every theorem printed by `Check.lean` depends only on `propext`, `Classical.choice`, and `Quot.sound`, Mathlib's standard logical foundations. The submitted proof has no admitted steps, custom axioms, or native evaluation tactics.

From the submission directory, compile the report with:

```sh
tectonic main.tex
```

No auxiliary numerical computation is needed for the proof.

## Provenance

Prepared by **C0ldSmi1e** with Codex assistance. A separate agent checked the mathematical and formal definitions against both language versions; a clean copy of the packaged project was rebuilt and its proof source replayed. The competition maintainers' review and acceptance remain separate from these checks.
