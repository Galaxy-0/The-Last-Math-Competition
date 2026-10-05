# Disproof of conjecture 00000006076

For the genuine Euclidean strict saddle f(x,y)=x²-y², ordinary deterministic gradient descent with safe step1/4 has nonstationary stable-axis trajectories (s/2^n,0). For every positive saddle-neighborhood radius, such a trajectory starts inside, never exits and converges to the saddle. This refutes the unqualified deterministic neighborhood-escape claim. Randomized, perturbed or generic-start guarantees are explicitly outside the scope.

See report.pdf/report.tex and the pinned Lean project. Run lake build from lean/. The formalization uses actual Euclidean gradients, smoothness and Hessian derivatives, nondegenerate negative curvature, actual finite iterates, metric balls and geometric-sequence convergence.
