# Parent adversarial review: 00000006953

Verdict: PASS

The parent read the exact bilingual source, the complete Main.lean and the mathematical paper. The source says variance-proportional allocation is optimal, rather than allocation proportional to standard deviations. With equal weights and observation costs, the explicit independent strata with values +/-1 and +/-2 have variances 1 and 4. Five observations give the exact variance-proportional allocation (1,4), without rounding. Its variance is 1/2; (2,3) instead has variance 11/24 at the same cost. This strictly better competitor disproves optimality.

The Lean sample space is the full five-bit Cartesian product, and the actual measure is count scaled by 1/32. Its probability normalization and all joint coordinate-pattern masses are proved. The estimator divides the actual sums by positive admissible stratum counts and then averages the two strata. Its variances use ProbabilityTheory.variance, with the Bochner integral reduced to the exact finite sum. Both relevant estimators are proved unbiased. The universal comparison in Optimal is correctly contradicted by the admissible value 2; no optimization value or variance is assigned by definition.

The exact rational auxiliary enumeration, fresh lake build, direct warningAsError command and PDF export passed. The printed axioms are only propext, Classical.choice and Quot.sound. The review marking script checks all artifact hashes against BUILD.json. Reviewed Main.lean SHA-256: 27a839c1556167db62950a9c6ba0d3c647fedc7295ab506e38ddc9e9fe3513df.

The parent viewed both final 1500-pixel PDF pages. The formulas, proof and formalization correspondence are complete and legible without overlap or clipping. No numerical simulation or external independent review is claimed.
