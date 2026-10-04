# Disproof of 00000008347

Use the standard reciprocal constant c(alpha)=liminf(q -> infinity) q*dist(q*alpha,Z), equivalently 1/nu(alpha), with reciprocal zero when nu is infinite. The actual factorial Liouville series L has c(L)=0. Therefore zero belongs to the spectrum over all irrationals and its closure, but not to [1/sqrt(5),1/2]. The source explicitly quantifies over all irrationals.

Lean proves actual nearest-integer minimization, full Liouville approximations at unbounded denominators, the liminf value, actual spectrum membership and closure membership. Main theorem: `Counterexample.counterexample`. The report confines the disproof to the closed-interval spectrum conjunct and cites the reciprocal convention.

Reproduce with Lean 4.19.0:

```sh
cd lean
lake exe cache get
lake build
```

Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Public dependency pins are included. Compile the report with `tectonic report.tex`.
