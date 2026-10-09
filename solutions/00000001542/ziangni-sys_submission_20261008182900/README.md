# Conjecture 00000001542: disproof

The actual Euclidean equilateral triangle has three vertices and at most two distances at every pin, including zero. The exact real exponent satisfies 3^(687/1000)>2, so the literal universal coefficient-one bound fails. This does not refute asymptotic Omega(n^0.687), a bound with a smaller multiplicative constant, or a sufficiently-large-n version.

## Formal scope

Lean constructs the actual Euclidean plane vertices (0,0), (1,0), (1/2,sqrt(3)/2), proves all actual distances, vertex injectivity and finite-set cardinality three. Pinned distances are actual finite images under the Euclidean distance function, including zero; their cardinality is bounded by two. The exponent inequality uses 687/1000>2/3 and cubing 3^(2/3) to obtain9>8, without numerical approximation. The final theorem negates the literal universal bound on nonempty finite subsets of the plane.

## Reproduction and validation

Use Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b as pinned publicly in lakefile and manifest. From lean/, run lake update if packages are absent and lake build. Local ignored .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary computation is needed.

One final full lake build succeeded after a draft constructor-name fix, without warnings. All six final printed axiom audits use exactly propext, Classical.choice and Quot.sound. No incomplete proof, custom axiom, native decision or unsafe code occurs. The one-page PDF compiled without layout warnings, rendered with Poppler and passed visual inspection without clipping or overlap.
