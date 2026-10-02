# Lean 4 verification for the disproof of TLMC conjecture 00000000521 (v2)

Pure Lean 4 core (v4.33.1), no Mathlib.

Object (literal reading of the conjecture): `β_{i,j}(I)` are the graded
Betti numbers **of the ideal `I` as a graded `R`-module** (`Tor^R(I, k)`),
not of `R/I`.  (v1 used the table of `R/I`, which carries the impossible
`β_{0,0} = 1` entry; that is the error the review caught.)

Contents of `Main.lean`:

* `beta i j` — the graded Betti numbers of the ideal
  `I(C4) = (x1x2, x2x3, x3x4, x4x1) ⊂ k[x1,x2,x3,x4]` as an `R`-module,
  i.e. of the minimal resolution
  `0 → R(−4) → R(−3)^4 → R(−2)^4 → I → 0`:
  `β_{0,2} = 4`, `β_{1,3} = 4`, `β_{2,4} = 1`, all other entries 0
  (`reproduce.py` verifies exactness per bidegree; the syzygies and their
  relation are displayed in the README/main.tex);
* `A j = β_{0,j} − β_{1,j} + β_{2,j}` — the alternating Betti sums:
  `A = (0, 0, 4, −4, 1)` with `A_j = 0` for `j ≥ 5`;
* `reg_bound` / `reg_attained` — `reg(I) = 2`;
* `attack_sign_changes` / `conjecture_00000000521_false` — the signs of the
  nonzero entries `4, −4, 1` run `+, −, +`: the sign changes **twice**,
  while the conjecture demands exactly once;
* `monotone_up_to_reg` — the monotonicity clause *holds* for this example,
  so the refutation is exactly the "exactly once" clause;
* `betaK13` / `K13_counterexample` — second counterexample, the star
  `K_{1,3}`: `A = (0, 0, 3, −3, 1)`, again two sign changes.

Build and audit:

    lake build
    lake env lean Check.lean

`Check.lean` prints `#print axioms` for every theorem; each of the 15
reports **"does not depend on any axioms"**.  No `sorry`, no
`native_decide`, no additional axioms — all proofs are `decide`/`rfl` on
closed integer data.

The numeric inputs are independently recomputed by `../reproduce.py`
(Taylor resolution of the module `I` tensored with `k`, Hilbert-series
cross-check, long-exact-sequence identity `A_j(I) = δ_{j0} − A_j(R/I)`,
and an explicit exactness/minimality check of the `C4` resolution).
