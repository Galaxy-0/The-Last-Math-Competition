# TLMC 00000007701: irrational areas in a literal cut-and-project scheme

The conjecture's literal dimensions are preserved: physical space `R`, internal space `R²`, and a rank-three lattice in `R × R²`. Set `alpha = sqrt(2)` and `beta = sqrt(3)`, and take

```text
Gamma = {(k + alpha*m + beta*n, (m - k*alpha, n - k*beta)) : k,m,n in Z}.
```

The generators are `(1,-alpha,-beta)`, `(alpha,1,0)`, and `(beta,0,1)`. Their determinant is `6`. Rational independence of `1,sqrt(2),sqrt(3)` gives injectivity of the physical projection and density of the internal projection. The lattice density is `1/6`.

For each positive integer `q`, the internal window

```text
W_q = [0, fract(-q*sqrt(2))) × [0,1)
```

has irrational Lebesgue area `a_q = fract(-q*sqrt(2))`. Its model set consists of the selected points

```text
t_k = 6*k + sqrt(2)*fract(-k*sqrt(2)) + sqrt(3)*fract(-k*sqrt(3)),
selected when fract(-k*sqrt(2)) < a_q.
```

Each point lies in `[6*k,6*(k+1))`. Consequently the actual model-set count on `[6*K,6*(K+N))` equals a circle Birkhoff sum, with discrepancy at most `q` from `N*a_q`. Sandwiching each interval between inner and outer aligned blocks gives, for every real `x <= y`,

```text
abs(#(Lambda(W_q) intersect [x,y)) - (a_q/6)*(y-x)) <= q + 2.
```

Thus these are bounded remainder windows for the literal scheme. Their areas are outside `(1/2) Z` and form a dense subset of `(0,1)`, refuting both the half-integer clause and discreteness. This suffices to refute the conjecture's conjunction.

## Formal and human proofs

The headline Lean theorem is **`literal_volume_clause_false`**:

```text
¬ (∀ W : Set (R × R), IsPhysicalBRS (sqrt 2) (sqrt 3) W →
     ∃ k : Z, (volume W).toReal = k / 2)
```

`IsPhysicalBRS` requires measurability, finite actual model-set intersections, and a uniform counting-discrepancy bound for every real half-open interval. `literal_window_discrepancy` proves the bound `q + 2` by sandwiching the interval between aligned blocks and using monotonicity of finite-set cardinality; `literal_window_isPhysicalBRS` establishes membership for every `q >= 1`. No part of this all-interval argument is left as a human bridge. `literal_physical_brs_areas_dense` proves that areas of windows in this physical BRS class meet every open subinterval of `(0,1)`. `literal_area_spectrum_not_discrete` formally proves `¬ IsDiscrete literalAreaSpectrum` for the full area spectrum of this physical BRS class.

Lean also proves canonical-parameter uniqueness, exact equality of each aligned model-set intersection with a finite set, the counting reduction, and its discrepancy bound. `literal_block_counterexamples` proves irrational area and exclusion from half-integers for the concrete family.

**The only human bridge required to identify these formal results with an admissible cut-and-project scheme is lattice admissibility.** The report proves that the image of `Z³` under the displayed map is a discrete full-rank lattice of covolume `6`, that the physical projection restricted to it is injective, and that its internal projection is dense in `R²`. These facts are not Lean theorem declarations or assumed Lean axioms. The report separately discusses optional closed-window and rational-polytope variants; neither is needed for the headline negation.

The circle/internal-line results are retained as a clearly labeled secondary reading. The torus lemmas are supporting results. No general classification of cut-and-project BRS is asserted.

## Contents and reproduction

- `report.tex`, `report.pdf`: self-contained construction, proofs, citations, and formalization boundary.
- `lean4/BRSVolume.lean`: single-file Lean development and axiom audits.
- `lean4/lean-toolchain`, `lean4/lakefile.toml`, `lean4/lake-manifest.json`: pinned Lean/Mathlib v4.33.0 project.
- `verify.py`: supplemental exact rational checks of the circle identity and physical counting bridge.
- `verification.txt`: successful compiler audits, supplemental checks, and PDF verification.
- `LICENSE.trureturing`: upstream Apache-2.0 license.

```sh
cd lean4
lake exe cache get && lake build
cd ..
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The source was successfully compiled against the pinned Mathlib environment. Axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`; no proof admissions or additional axioms are present.

The transfer-function definition and four coboundary lemmas are adapted from `D5/S1/Phase/HeckeOstrowskiCoboundary.lean` in [trureturing](https://github.com/the-omega-institute/trureturing), immutable commit **`1be30b25c4fe6cd46397090ca09b5696eb62ea78`**, under Apache-2.0. The namespace and imports were adapted. The upstream license is included, and no trureturing import is required.

The report cites Kesten (Acta Arithmetica 12, 1966, 193–212), Grepstad–Lev (GAFA 25, 2015, 87–133), and Haynes–Kelly–Koivusalo (Israel Journal of Mathematics 212, 2016, 189–201). The counterexample uses classical bounded remainder constructions.

Submitted by AlyciaBHZ on behalf of the Omega Institute (trureturing project, https://github.com/the-omega-institute/trureturing).
