# Disproof of conjecture 00000000283

The ordinary partial products of the Kepler–Bouwkamp cosine product do not converge at the conjectured cubic rate. For the actual positive infinite product `K` and the actual source-indexed partial products `S_N = ∏_{k=3}^N cos(π/k)`, the Lean project proves

`S_N - K ≥ 2 K / (N+1)^2` for every natural `N ≥ 3`.

It then proves that for every real constant `C` and every cutoff `N₀`, some `N ≥ max(N₀,3)` satisfies `|S_N-K| > C/N^3`. Thus the error is not `O(N⁻³)` in Mathlib's standard definition. This refutes an explicit conjunct in both source languages, and hence the combined conjecture. It does not decide whether the constant is transcendental or whether the stated Gamma-function reduction is valid. The lower bound is not asserted to be the sharp convergence rate.

## Contents and reproduction

The submission includes the exact bilingual `conjecture.md`, the complete report `main.tex` and matching `main.pdf`, the pinned Lean project, and execution and semantic-review records. From `lean/`, with the pinned toolchain available:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture283/Factors.lean
lake env lean -DwarningAsError=true Conjecture283/Prefixes.lean
lake env lean -DwarningAsError=true Conjecture283/Rate.lean
lake env lean -DwarningAsError=true Conjecture283.lean
lake env lean -DwarningAsError=true Check.lean
```

Lean 4.19.0 and Mathlib v4.19.0 are pinned; the manifest fixes all nine dependency revisions. The default build imports every proof module. `Check.lean` prints all five definitions, checks all 25 theorem types, and prints every theorem's transitive axiom dependencies. There are no unnamed or private proof declarations. The report uses standard LaTeX packages. Its matching PDF is exported with Tectonic 0.17.0.

## Correspondence with the conjecture

- `Factors.lean` defines the real cosine factors `a_n = cos(π/(n+3))`, their finite prefixes, and the genuine infinite product using `tprod`. Quadratic cosine estimates prove summability of `a_n-1` and then of `log(a_n)`. The equality with the exponential of that logarithm sum proves positivity. `hasProd_factor` and `tendsto_prefix` establish actual product convergence; convergence is not merely assumed from the totalized `tprod` definition.
- `Prefixes.lean` defines the source partial products over `Finset.Icc 3 N`. It proves the exact identity `S_(n+2) = P_n`, convergence of `S_N` to `K`, and decreasing positive prefixes. The first omitted factor yields the displayed lower error bound.
- `Rate.lean` proves the unrestricted constant-and-cutoff counterexample and negates the genuine `Asymptotics.IsBigO` relation at infinity. `CubicConvergence` names that necessary rate clause; the top-level `conjecture_283` proves its negation.

All estimates concern the actual cosine product, with no accelerated approximation, numerical oracle, assigned limit, or assumed rate. No auxiliary numerical computation is needed. The report cites Chamberland and Straub, [On gamma quotients and infinite products](https://arxiv.org/abs/1309.3455), §4.1, for background only; the disproof is established by the Lean project.

`VERIFICATION.md` describes the recorded checks. `SEMANTIC_REVIEW.md` is an independent internal review, and `verification/SHA256SUMS.json` covers the submitted files except itself. These records distinguish local validation from maintainer acceptance.
