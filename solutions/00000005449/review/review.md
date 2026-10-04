# Solution Review — Conjecture 00000005449 (PR 401)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004042902`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "the detection power of a single [random group-structure] check is at least one half at noncommutative witnesses" (with clauses on k-check exponential error, automorphism correction, and trivial-aut=1); the definition names commutativity spot checks (交换性抽查) as the canonical check.
- LaTeX: recompiled with pdflatex (twice) in /tmp/tlmc-review5/scratch/pr-401, exit 0, 1 page; shipped report.pdf (32529 bytes, 1 page — matches VERIFICATION.md's pdfinfo) extracts to the same content as report.tex. Real matching PDF.
- Lean build: `lake build` exit 0 (1180 jobs per VERIFICATION.md; my rebuild replayed Main); only output = 5 info lines from `#print axioms`, standard `[propext, Classical.choice, Quot.sound]` (witness: `[propext, Quot.sound]`); no warnings.
- Forbidden content: grep over lean/Main.lean (only source file): no hits for sorry/admit/native_decide/axiom decl/unsafe/implemented_by/extern/skipKernelTC. Finite checks use kernel `decide` (not native_decide). Toolchain 4.19.0, mathlib pinned c44e0c8e.
- Auxiliary code: no scripts; independent recomputation with python3 in TWO ways: (a) enumeration under the report's stated dihedral multiplication rules → |G|=8, 40 commuting ordered pairs of 64, detection = 24/64 = 3/8 < 1/2; (b) fully independent construction of D₄ as the permutation closure of ρ=(0123), σ=(1 3) in S₄ (verified subgroup) → same 40/24 split, commuting fraction 5/8 = k/|G| with k=5 conjugacy classes — the classical sharp case.
## Semantic audit
Literal claim (EN): "the detection power of a single check is at least one half at noncommutative witnesses"; CN: 单次检查的检测力在非交换 witness 处至少为二分之一. The definition line explicitly names commutativity spot checks, so the standard experiment — draw X,Y independent uniform from G, detect iff XY≠YX — is the check named by the conjecture itself. Lean encodings:
- `abbrev G := DihedralGroup 4` — Mathlib's actual symmetry group of the square, its group structure and Fintype used as-is.
- `def detectedPairs : Finset (G × G) := Finset.univ.filter (fun p => p.1 * p.2 ≠ p.2 * p.1)` / `commutingPairs` dually — the actual detection event.
- `theorem genuine_noncommuting_witness : (DihedralGroup.r 1 : G) * DihedralGroup.sr 0 ≠ DihedralGroup.sr 0 * (DihedralGroup.r 1 : G)` — the witness group is genuinely nonabelian (decide-checked).
- Sampling law: `drawWeight = 1/8`, `pairWeight = product of draw masses`, with proved nonnegativity (`uniform_pair_mass_nonnegative`) and normalization (`uniform_draw_total_mass`, `uniform_pair_total_mass`) — a bona fide independent uniform probability distribution, not an assumed number.
- `theorem actual_detection_probability : detectionProbability = 3 / 8` (sum of pair weights over the actual event) and `theorem single_check_below_half : detectionProbability < 1 / 2`.
- Final: `theorem conjecture_5449_counterexample : Fintype.card G = 8 ∧ (∃ x y : G, x * y ≠ y * x) ∧ (∀ p, 0 ≤ pairWeight p) ∧ (∑ p, pairWeight p) = 1 ∧ detectionProbability = 3/8 ∧ ¬((1/2 : ℚ) ≤ detectionProbability)`.
Contradiction with the claim: detection power at a noncommutative witness is exactly 3/8 < 1/2, refuting the ≥1/2 clause (one false conjunct kills the conjecture; the automorphism-correction clauses are rightly left alone). NOT vacuous: the group is provably nonabelian, the distribution is proved valid, and the probability is computed from the actual event. Not an artifact of the x=y convention: excluding the diagonal gives 24/56 = 3/7 < 1/2, and restricting both draws to non-identity elements gives 24/49 < 1/2 (my computation), so every plausible sampling reading stays below 1/2. This is moreover the classical sharp case of the Gustafson 5/8 theorem (nonabelian G has commuting fraction ≤ 5/8, equality at D₄/Q₈), so D₄ is the canonical — not a contrived edge — counterexample. The mathlib group operations are used without any assumed multiplication table; `decide` here is ordinary kernel evaluation over 64 pairs.
## Issues found
none blocking
## Verdict rationale
The submission uses the exact check named in the conjecture's definition (commutativity spot check), a genuinely nonabelian group (Mathlib's DihedralGroup 4, noncommutativity decided), a proved-valid independent uniform sampling law, and computes the detection probability exactly as 3/8 < 1/2, directly contradicting the literal "at least one half" clause. My two independent enumerations confirm 40 commuting / 24 noncommuting pairs, and the violation persists under every alternative sampling convention I tested (3/7 and 24/49), matching the classical sharp 5/8 bound. Build, PDF, and axiom audits are all clean.

## Disposition
APPROVED — merged into main (PR 401). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
