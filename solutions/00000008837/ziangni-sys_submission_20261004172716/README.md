# Disproof of conjecture 00000008837

The final almost-sure convergence clause fails without existence of an operator zero. On the actual one-point probability space with its trivial filtration, the maximal monotone graph A(x)={1} has the unique unit resolvent J(x)=x-1. Zero noise is a genuine adapted martingale difference with pointwise and expected square sums zero, but every trajectory is x-n and its convergence event is empty.

The expected-rate clause is unused. See report.pdf and report.tex for the proof and source scope. The formalization in lean/Main.lean uses actual conditional expectations and almost-everywhere convergence. Run lake build from lean/ with the pinned public dependencies.
