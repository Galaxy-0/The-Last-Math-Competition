# Solution Review — Conjecture 00000008535 (PR 314)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003091740`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — χ of a lattice = generating function of its Möbius function; conjecture: for a supersolvable geometric lattice all characteristic roots are real and NEGATIVE; in general the min of the root-modulus spectrum is controlled by the Möbius absolute value of the minimal antichain.
- LaTeX: compiled ok (pdflatex twice, exit 0), 1-page PDF; included main.pdf genuine, page count matches verification.json.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings (warnings-as-errors), v4.19.0, Std only.
- Forbidden content: none — no sorry/admit/native_decide/axiom/unsafe/implemented_by/extern.
- Auxiliary code: none present (`auxiliary_scripts_rerun: []`); sha256 of Main.lean/main.tex match verification.json; axiom printout (propext only) reproduced by my fresh build.
## Semantic audit
Conjecture's literal clause (EN): "The roots of the characteristic polynomial of a geometric lattice are real and negative when the lattice is supersolvable" (CN: 超可解时根为实负数).

Lean definitions verified faithful to standard mathematics:
- `LatticeLaws`: partial order + bottom/top + meet as greatest lower bound (`∀ z, z ≤ x → z ≤ y → z ≤ meet x y`) + join as least upper bound — correct lattice axioms.
- `Graded`: rank(bottom)=0 and every cover raises rank by exactly 1 — correct.
- `Atomistic`: every element = fold-join of atoms below it (empty join = bottom) — correct.
- `Semimodular`: `∀ x y, Covers (meet x y) x → Covers y (join x y)` — the standard upper-semimodularity implication; `Geometric := LatticeLaws ∧ Graded ∧ Atomistic ∧ Semimodular` is the standard definition of a finite geometric lattice.
- `ModularElement m := ∀ x ≤ y, join x (meet m y) = meet (join x m) y` — the standard modular-element identity; `Supersolvable := ∃ maximal chain all of whose elements are modular` — Stanley's standard characterization.
- `MobiusRecurrence mu := ∀ x, Σ_{y ≤ x} mu(y) = [x = bot]` — the DEFINING recurrence of the Möbius function (the conjecture's own definition); `characteristicAt := Σ_x mu(x) * t^(rank top − rank x)` — the standard characteristic polynomial χ_L(t).
- Witness `booleanOne`: the 2-element lattice {0<1} (rank 0,1). `booleanOne_geometric` and `booleanOne_supersolvable` are proved by kernel `decide` over the full universal properties (not asserted). `mobius_correct` verifies μ(0,0)=1, μ(0,1)=−1 from the recurrence. `positive_characteristic_root : characteristicAt booleanOne mobius 1 = 0` — χ(t) = t−1 vanishes at t = 1 > 0.
- `NegativeRootClaim := ∀ n L mu, Geometric L → Supersolvable L → MobiusRecurrence L mu → ∀ r : Int, characteristicAt L mu r = 0 → r < 0` — the integer-root specialization of the conjecture's real-negativity clause; integer roots are real, so conjecture-true ⟹ specialization-true. `conjecture8535_false : ¬ NegativeRootClaim` instantiates with booleanOne and root 1. Sound contrapositive bridge; for this witness it is even stronger than needed since the degree-1 polynomial's only root is 1.
- Hypotheses check: B₁ is genuinely geometric (atomistic, graded, semimodular) and supersolvable — all verified element-wise in Lean, and the Möbius function is pinned by its defining recurrence. The counterexample satisfies every hypothesis the conjecture imposes.
- Not a vacuous trick: the decisive objects — lattice, geometric/supersolvable structure, Möbius function, characteristic polynomial — are all defined and verified; only the final root statement is specialized to integers (with a correct logical implication argument, documented in the report).
- Robustness: under the alternative "generating function" convention Σ μ(x) t^{rank x} = 1 − t the root is still t = 1. The mathematical truth (Stanley) is that supersolvable geometric lattices factor χ into POSITIVE integer roots — the conjecture's "negative" is exactly wrong, and this witness catches it.
- LaTeX↔Lean match: report states μ(0,0)=1, μ(0,1)=−1, χ(t) = t−1, root 1, and describes the same lattice properties and theorems as the Lean file.
## Issues found
- Minor (non-blocking): the witness is the rank-1 Boolean lattice; a skeptic could ask for a higher-rank example, but B_n has χ = (t−1)^n with the same positive root 1, so the rank-1 case is representative, and the conjecture nowhere excludes it.
- Minor: the conjecture's second clause (modulus/antichain) is not separately addressed; unnecessary since the first clause of the conjunction is refuted.
## Verdict rationale
The two-element Boolean lattice is a supersolvable geometric lattice whose characteristic polynomial t−1 has the strictly positive root 1, directly contradicting the conjecture's assertion that all characteristic roots of supersolvable geometric lattices are real and negative. All lattice-theoretic hypotheses are genuinely verified in Lean (not assumed), the build is clean with warnings-as-errors, the LaTeX matches, and no forbidden content exists.

## Disposition
APPROVED — merged into main (PR 314). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
