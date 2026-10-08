# Counterexample to 00000003552

For the genuine cube C_n = [-1,1]^n, its polar under the standard coordinate pairing is the cross-polytope sum |y_i| <= 1. Actual Lebesgue volumes give product 4^n/n!. At dimension 12 this is less than 1/2, hence less than 8/pi². The dimension 3 product is 32/3, not the claimed extremal value.

This targets the literal unnormalized, dimension-independent bound in the source. It does not refute the standard dimension-dependent symmetric Mahler conjecture or a normalized volume-product statement. The report explains the distinction.

Run `lake build` in `lean/` with Lean 4.19.0 and the pinned public Mathlib dependencies. The full proof and scope discussion are in `report.pdf` and `report.tex`.
