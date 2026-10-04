# Delegated internal adversarial review: 00000003380

Verdict: PASS

Reviewer: a delegated agent distinct from the authoring parent agent. This is an internal review within the same assistant workflow, not an external independent mathematical referee report.

## Material actually inspected

- Both language versions in `SOURCE.md`, checked byte-for-byte against the current local raw upstream snapshot.
- The complete submitted `lean/Main.lean` and the mathematical argument and scope statements in `main.tex`.
- `verification/BUILD.json`, `lake-build.log`, and `lean-axioms.log`.
- Hash equality of the current Lean source/configuration files with the fresh-build record.

Reviewed Lean source SHA-256: `a48bc9317b670b896def7fb74caee1fb0ab2140c109ac1c116404d9ed4f8cf7c`.

Reviewed source-statement SHA-256: `321decc752e84b934fc2ebcfa45b2e69172d784ac3dd0fdc6751a93bb3ce4aca`.

## Adversarial findings

1. **The algebra is in the stated domain.** The actual object is `M_2(C) × M_2(C)` with its library product algebra structure. The source makes no central-simplicity, factor, or trivial-center assumption. The submitted noncommuting pair is computed using actual matrix multiplication, so the example is noncommutative for the required reason. Its decomposability is permitted by the printed claim.

2. **The automorphism fixes the base field.** `exchange` is an actual `AlgEquiv` over `C`, constructed from `RingEquiv.prodComm` with scalar compatibility checked by reduction. Thus it is a bijective, unital, additive and multiplicative complex-linear automorphism. This is stronger than merely exchanging a set or constructing a semilinear map. The adjoint-preservation statement uses the actual matrix conjugate transpose.

3. **Every internal implementer is excluded.** `IsInner` has the quantifier order `exists u : Bˣ, forall a : B, ...`, with `u` and its actual inverse in the same algebra. The proof tests the purported implementer at a fixed central idempotent and does not restrict the unit group to diagonal, scalar, unitary, connected, or preselected matrices.

4. **The central obstruction is proved, not postulated.** The element `(I,0)` commutes with every algebra element and is idempotent. Associativity, that commutation identity, and the unit inverse laws show that conjugation by every internal unit fixes it. Exchange sends it to `(0,I)`, and inequivalence is checked at the first component's `(0,0)` matrix entry over `C`. The contradiction therefore rules out all units at once.

5. **Ambient implementation does not invalidate the conclusion.** Embedding the product algebra as block-diagonal matrices in `M_4(C)` allows a block-swap matrix to normalize it, but that matrix is not a unit of the block-diagonal product algebra. The formal quantifier is over `Aˣ`, precisely the required internal units. The manuscript explicitly makes this distinction.

6. **The source's unitary wording does not rescue its universal clause.** A unitary implementer is in particular an invertible internal implementer. Excluding all units therefore also excludes unitary implementations, irrespective of any further connected-component restriction. A general C*-norm or connected-unitary-group theorem is not claimed as formalized or required here.

7. **The final theorem addresses a necessary clause of the conjecture.** It negates the universal statement for noncommutative complex algebras and their complex algebra automorphisms. An explicit counterexample in this subclass suffices to refute the unrestricted algebra assertion. No proposed meaning of the unspecified innerness-measure clause is needed. The proof does not challenge results with additional central-simple hypotheses.

## Verification boundary

The supplied fresh-build and direct-Lean logs both report success, and all nine printed theorem dependencies are among `propext`, `Classical.choice`, and `Quot.sound`. Current submitted Lean hashes match those logs' build record. I did not rerun the already successful Lean build, change the proof source, or claim a second fresh build.

The author is performing the final PDF layout repair and all-page visual review. This delegated verdict concerns source correspondence, mathematical correctness, formalization adequacy, and the inspected Lean evidence; it does not assert that I reviewed the final rendered PDF. No blocking mathematical or formalization issue was found.
