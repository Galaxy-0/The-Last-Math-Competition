# Proof of conjecture 00000005960

Two nonconstant random real symmetric 2×2 matrices have the same complete eigenvalue spectrum `(1, 3)` and different eigenvector-statistic laws. Both are drawn from the explicit continuous rational family `M(t) = Q(t) diag(1,3) Q(t)ᵀ`, where `Q(t)` is an actual orthogonal rotation for every real parameter. The family is injective on `[0,1]`.

The statistic is intrinsically defined as the squared Euclidean norm of the actual orthogonal projection of the first coordinate vector onto the actual eigenvalue-1 eigenspace. We prove that it equals the squared first coordinate of **every** normalized eigenvector for that eigenvalue. Its two laws are the fair distribution on `{0,1}` and the point mass at `9/25`. Thus the distinction does not depend on eigenvector signs or an assigned formula for a statistic.

## Contents

- `conjecture.md`: exact bilingual source.
- `main.tex` and `main.pdf`: complete mathematical proof.
- `lean/`: Lean 4.19.0 / Mathlib v4.19.0 project with manifest-pinned dependency revisions.
- `VERIFICATION.md` and `verification/`: reproduction evidence and exact file hashes.
- `SEMANTIC_REVIEW.md`: independent mathematical and statement-fidelity scrutiny.

## Reproduce the formal proof

From this submission's `lean` directory, using the pinned toolchain:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture5960/Family.lean
lake env lean -DwarningAsError=true Conjecture5960/Eigenvectors.lean
lake env lean -DwarningAsError=true Conjecture5960/Ensembles.lean
lake env lean -DwarningAsError=true Conjecture5960.lean
lake env lean -DwarningAsError=true Check.lean
```

The default target builds the complete final proof. `Check.lean` prints all 21 named definitions/abbreviations, checks all 78 theorem types plus two named instances, and prints all 80 axiom dependencies. The two instances equip the actual matrix type with its ordinary coordinate Borel measurable structure; they are included in the audit.

The report uses standard LaTeX packages. Its matching three-page PDF was exported with Tectonic 0.17.0. No numerical sampling, simulation, or external computational result is needed.

## Source correspondence

`Family.lean` constructs actual real matrices and Euclidean vectors. It proves both orthogonality identities, symmetry, the actual characteristic polynomial `(X−1)(X−3)`, the full real spectrum `{1,3}`, the corresponding operator spectrum, unit eigenvectors, continuity, and a two-vector decomposition for every real parameter.

`Eigenvectors.lean` identifies the entire actual eigenvalue-1 eigenspace, derives its actual orthogonal projection, and proves the intrinsic statistic formula and its equality with the squared first coordinate of every unit eigenvector. It also proves interval injectivity of the matrix family.

`Ensembles.lean` uses a genuine fair probability mass function on `Fin 2`. It proves that both matrix laws are non-Dirac, both characteristic-polynomial and spectrum laws agree, and the eigenvector-statistic laws differ. Exact measure-pushforward identities connect the probability mass functions to the matrix-valued and real-valued random variables on the common finite probability space. Measurability of these finite-domain maps is proved; no global measurability assumption about eigenvector selection is used.

The main module supplies explicit parameter maps placing both ensembles inside the same family. `conjecture_5960` proves the full existential statement in the strengthened form `ParametricSeparation`: continuous interval-injective parametrization, unchanged complete spectrum at all real parameters, two non-Dirac ensembles, and unequal intrinsic-statistic measure pushforwards.

The claim is existential and imposes no Wigner, independent-entry, or asymptotic restriction. We make no global injectivity claim for the all-real parameter formula. The report cites Knowles–Yin, [arXiv:1102.0057, Remark 1.8](https://arxiv.org/abs/1102.0057), only as context for squared-coordinate eigenvector observables; no random-matrix universality theorem is assumed.

The supplied execution and semantic reviews are local verification. Maintainer acceptance is a separate decision.
