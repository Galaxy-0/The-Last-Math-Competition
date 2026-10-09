# Conjecture 00000003793: disproof

For every fixed positive step size, the genuine projected gradient method for f(x)=x^2/2+x^4/4 on the closed convex full line has an explicit divergent initial point. The objective is genuinely 1-strongly convex and has unique minimizer zero. Strong convexity alone therefore cannot ensure the claimed global linear convergence.

## Formal scope

Lean proves the actual derivative, exact nonnegative curvature remainder and full 1-strong-convex Jensen inequality. It proves the unique minimizer, verifies the unique nearest-point metric projection onto the full line, and defines the true fixed-step projected iteration. For every positive step alpha it selects R=sqrt(3/alpha), proves magnitude doubling and all-n lower bounds, proves that the full magnitude sequence tends to positive infinity, and disproves convergence to the minimizer. No derivative, curvature, projection or orbit certificate is assumed.

The source states no global gradient-Lipschitz or contraction bound, corresponding step restriction or adaptive rule. This result refutes the unrestricted fixed-step conclusion from strong convexity alone, not convergence theorems with those additional hypotheses. The failure occurs for every positive fixed step; it is not merely an oversized step on a globally smooth quadratic. The rate-constant constituent is unnecessary once convergence fails.

## Reproduction and validation

Use Lean 4.19.0 and publicly pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. From lean/, run lake update if packages are absent and lake build. Ignored local .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary computation is required.

One final full lake build succeeded after draft fixes. Ten final theorem audits use only propext, Classical.choice and Quot.sound. Only unused/redundant tactic and variable linter warnings occur. No incomplete proof, custom axiom, native decision or unsafe code occurs. The one-page PDF compiled without layout warnings, rendered with Poppler and passed visual inspection without clipping or overlap.
