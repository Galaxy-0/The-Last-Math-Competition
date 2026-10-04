# Disproof of conjecture 00000006073

The analytic objective f(x)=x³ has zero gradient at0, but0 is not a local minimum, so it is spurious under the source's explicit definition. Every positive starting point s has exact global forward gradient flow u(t)=s/(1+3st), tending to0. Its genuine gradient-flow basin contains(0,1) and has actual Lebesgue measure at least1.

The counterexample targets only the attraction-basin measure-zero clause. It explicitly uses a degenerate stationary inflection point and continuous gradient flow; the smoothing and Morse-index clauses are unused.

Run lake build in lean/ with Lean4.19.0. Public Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b and dependencies are pinned. The full report and source correspondence are in report.tex/report.pdf.
