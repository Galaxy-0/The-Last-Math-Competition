# Disproof of TLMC Conjecture 00000000521 (v2: Betti numbers of the ideal I)

**Verdict: FALSE — under the literal reading of the conjecture, with the
Betti numbers of the ideal `I` itself (not of `R/I`).**

The conjecture text defines its object verbatim as follows:

> Definition: The alternating Betti sum A_j = Σ_i (−1)^i β_{i,j}(I) of a
> monomial ideal I. Conjecture: For all edge ideals, the sign of {A_j}
> changes exactly once as j crosses reg(I), and |A_j| is monotonically
> nondecreasing up to that point; this gives a combinatorial
> characterization of the graded Lefschetz property for edge ideals.

**Object (fixed in v2).** `β_{i,j}(I)` are the graded Betti numbers **of the
ideal `I` as a graded `R`-module**, i.e. `Tor_i^R(I, k)` (so `β_{0,j}(I)`
counts the minimal generators of `I` and `β_{0,0}(I) = 0` for every nonzero
ideal). v1 mistakenly used the Betti table of `R/I` (which has the extra
`β_{0,0} = 1` entry); that version was closed after review — thanks to the
reviewer for the correction. Every number below is recomputed for the module
`I` and cross-checked by four independent methods.

## The counterexample

Let `G = C4` be the 4-cycle and let `I = (x1x2, x2x3, x3x4, x4x1) ⊂
R = k[x1,x2,x3,x4]`. The minimal free resolution **of the module `I`** is

    0 → R(−4) --d2→ R(−3)^4 --d1→ R(−2)^4 → I → 0,

with `d1` given by the four adjacent-edge syzygies

    s12 = ( x3, −x1,  0,  0),  s23 = ( 0,  x4, −x2,  0),
    s34 = ( 0,   0,  x1, −x3),  s41 = ( x4,  0,  0, −x2),

and `d2` given by the single relation `ρ = (x4, x1, x2, −x3)` among them
(`x4·s12 + x1·s23 + x2·s34 − x3·s41 = 0`; the kernel of `d1` is exactly
`R·ρ`, the coefficient matrix of `(s12,s23,s34,s41)` having rank 3 and
determinant 0). Hence the graded Betti numbers of `I` are

    β_{0,2}(I) = 4,   β_{1,3}(I) = 4,   β_{2,4}(I) = 1   (all others 0),

so `reg(I) = max(j−i) = 2`, and

    A_0 = 0,  A_1 = 0,  A_2 = +4,  A_3 = −4,  A_4 = +1,  A_j = 0 (j ≥ 5).

The nonzero entries `4, −4, 1` have signs `+, −, +`: the sign changes
**twice**, not exactly once. The first change does occur as `j` crosses
`reg(I) = 2` (`+4 → −4`), but a second change `−4 → +1` occurs at `j = 3`.
Note the monotonicity clause **holds** for this example (`|A_0| ≤ |A_1| ≤
|A_2| = 0 ≤ 0 ≤ 4`), so the violation is exactly the "changes exactly once"
clause. Exactness of the displayed resolution is verified mechanically
(`d1∘d2 = 0`, per-bidegree homology `H_1 = H_2 = 0` over GF(10^9+7),
`coker(d1) ≅ I` checked against the Hilbert series degree by degree, and
all matrix entries of positive degree, so the resolution is minimal), and
`A_j` is cross-checked against `[t^j] (1−t)^4 · Hilb_I(t)`.

## Boundary (literal reading, all recomputed in `reproduce.py`)

* The reviewer is right that v1's `C3` example **satisfies** the conjecture
  literally: `I = (xy, xz, yz)` resolves as `0 → R(−3)^2 → R(−2)^3 → I → 0`,
  giving `A = (0, 0, 3, −2)` — exactly one change at `reg(I) = 2`. Likewise
  `P3` and `P4` give `(0, 0, 3, −2)` (hold), and `2K2` gives `(0, 0, 2, 0, −1)`
  (one change at `reg = 3`; holds).
* But the conjecture still fails, already on 4 vertices. The star `K_{1,3}`
  (`I = (x1x2, x1x3, x1x4)`, resolution `0 → R(−4) → R(−3)^3 → R(−2)^3 → I`)
  gives `A = (0, 0, 3, −3, 1)` — two sign changes; `paw` gives
  `(0, 0, 4, −4, 1)`, `diamond` `(0, 0, 5, −6, 2)`, `K4` `(0, 0, 6, −8, 3)`,
  `C5` `(0, 0, 5, −5, 0, 1)`, `C6` `(0, 0, 6, −6, −3, 6, −2)` (three changes).
* Reason (structural): for any edge ideal the long exact Tor sequence of
  `0 → I → R → R/I → 0` gives `A_j(I) = δ_{j0} − A_j(R/I)`; dropping the
  leading `A_0(R/I) = 1` removes exactly one sign change, so the literal
  conjecture holds iff the `R/I`-sequence changes sign exactly twice. Any
  graph with `β_{3,4}(R/I) ≠ 0` (`C4`, `K_{1,3}`, `K4`, `C5`, `C6`, ...) has
  three changes on the `R/I` side and hence **two** on the literal side.
* Exhaustive scan (Hilbert-cross-checked): among the 63 labeled graphs on 4
  vertices with ≥ 1 edge, **32** violate "exactly one sign change" under the
  literal reading (including the 6 single-edge graphs, whose `I` is a free
  module with `A = (0, 0, 1)` — zero changes); among the 1023 graphs on 5
  vertices, **908** violate it, and **100** additionally violate the
  monotonicity clause (e.g. `P3 ⊔ K2`: `A = (0, 0, 3, −1, −2, 1)`,
  `reg(I) = 3`, yet `|A_2| = 3 > |A_3| = 1`).

## Verification

* `reproduce.py` — self-contained (stdlib only) recomputation **for the
  module `I`**: (i) Taylor resolution of `I` tensored with `k = GF(1000000007)`,
  homology per bidegree → `β_{i,j}(I)`; (ii) cross-check `A_j` against
  `[t^j](1−t)^n·Hilb_I(t)` by direct monomial enumeration; (iii) cross-check
  the identity `A_j(I) = δ_{j0} − A_j(R/I)`; (iv) explicit per-bidegree
  exactness + minimality check of the hand-written `C4` resolution displayed
  above; (v) named examples and exhaustive scans on 4 and 5 vertices.
  Run: `python3 reproduce.py` (exit 0).
* `lean4/` — Lean 4 (v4.33.1, no Mathlib) formalization **under the literal
  definition**: the Betti table of the module `I(C4)` (`β_{0,2} = 4`,
  `β_{1,3} = 4`, `β_{2,4} = 1`), the alternating sums `A = (0, 0, 4, −4, 1)`,
  `reg(I) = 2` (attained and maximal), the **two** sign changes (≠ 1), and —
  for precision — the fact that the monotonicity clause holds, so the failure
  is exactly the "exactly once" clause. A second theorem records the star
  `K_{1,3}` (`A = (0, 0, 3, −3, 1)`, two changes). Zero axioms, zero `sorry`:

      cd lean4 && lake build && lake env lean Check.lean

  every `#print axioms` reports "does not depend on any axioms".
* `build/main.pdf` — the write-up (`main.tex`, compiled with tectonic).

## Changes from v1 (closed PR #130)

* Object corrected: Betti numbers of the ideal `I` (literal reading), not of
  `R/I`. All tables, sums and scans recomputed for the module `I`.
* Counterexample replaced: `C3` (holds literally, as the reviewer showed) is
  replaced by `C4`; `K_{1,3}` added as a second counterexample.
* Lean theorem now refutes the conjecture under its literal `β_{i,j}(I)`
  definition, with the monotonicity clause proved to hold.
