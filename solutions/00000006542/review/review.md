# Solution Review — Conjecture 00000006542 (PR 357)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "the reciprocals of the poles [of the Ihara zeta] are the adjacency spectrum", in a finite correspondence whose kernel is regular-graph covering structure.
- LaTeX: recompiled in /tmp/tlmc-review2/scratch/pr-357, pdflatex twice exit 0; shipped main.pdf genuine (text ratio 0.9896 vs recompiled; all diffs are superscript/math-ligature extraction artifacts); all 21 files' SHA-256 match VALIDATION.json (auxiliary-verification.json matches after accounting for its CRLF endings — restored pristine after my verification run).
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings (warningAsError=true; `set_option maxHeartbeats/maxRecDepth` are legitimate effort options, not proof-skipping). `#print axioms` for all principal theorems: only [propext, Classical.choice, Quot.sound]. Toolchain lean4:v4.19.0, bundled Std only.
- Forbidden content: grep for sorry/admit/native_decide/axiom-decls/unsafe/implemented_by/extern/skipKernelTC over lean/Main.lean and verify.py — no matches. Heavy `decide` usage is kernel computation over Fin 3/Fin 6/Int lists (legitimate; not native_decide).
- Auxiliary code: verify.py run under python3 — exit 0, prints "00000006542 PASS: two prime rotation classes; exact pole factorization; det(I-A)=-4"; its regenerated output is byte-identical (modulo CRLF) to shipped auxiliary-verification.json; recorded logs (verification/root-auxiliary-verification.log, lean-axioms.log) match my own runs. Independent re-derivation (my own numpy): Bass determinant formula for C3 (m=n=3) gives det(I−uA+u²I) = (1−u)²(1+u+u²)² = (1−u³)², agreeing with the submission's Euler-product computation Z_{C3}(u) = 1/(1−u³)²; adjacency eigenvalues {2,−1,−1}; det(I−A) = −4 ≠ 0 so 1 is not an eigenvalue; poles' reciprocals {1, ω, ω²} are disjoint from the spectrum.
## Semantic audit
Literal conjecture clause refuted: "the reciprocals of the poles are the adjacency spectrum" (极点的倒数为邻接谱). Necessary consequence: if u ≠ 0 is an Ihara pole then u⁻¹ is an adjacency eigenvalue. The submission refutes it on C3, the finite connected simple 2-regular triangle — which the source does not exclude (no minimum-degree-3 clause), and which even satisfies the "regular graphs" clause of the kernel statement, so the counterexample survives the stricter readings.

Lean formalization quality (lean/Main.lean) — the conjecture's objects are all present and derived, not assumed:
- Darts with tail/head/reverse/next on Fin 6; `Step d e := head d = tail e ∧ e ≠ reverse d` is the exact backtrackless-tailless step; `step_is_forced` proves every reduced walk is confined to the two successor orbits (01,12,20) and (02,21,10).
- `ClosedWalk` = positive-length periodic dart sequences with the step condition across period boundaries (closed + tailless); `fromFiniteWord` shows every finite cyclic reduced word of every length embeds (no walks omitted).
- `Primitive` = no shorter period repeated ≥ 2 times (usual proper-power condition); `primitive_iff_length_three` is symbolic over ALL lengths (not a bounded search); `RotationEquivalent` is literal cyclic rotation; `PrimeCycle := Quotient rotationSetoid` is an actual quotient, with `prime_cycles_complete`/`prime_cycles_nodup` proving exactly two prime classes.
- `iharaZeta` is the defining Euler product folded over that complete duplicate-free list: `theorem actual_euler_product : iharaZeta.numerator=[1] ∧ iharaZeta.denominator=[1,0,0,-2,0,0,1] ∧ ... = polyPow (oneMinusPower 3) 2` — i.e. Z(u) = 1/(1−u³)², matching my independent Bass-formula computation.
- `HasPoleAt` is the exact algebraic meromorphic-pole certificate (D = (u−a)^m·Q, Q(a)≠0, N(a)≠0); `pole_at_one_order_two : HasPoleAt iharaZeta 1 2` with `residual_value : evaluate residual 1 = 9`, `numerator_value : ... = 1` — a genuine uncancelled order-2 pole at u=1 over ℂ, no analytic continuation or determinant-identity assumption smuggled in.
- `Eigenvalue S value := ∃ v, (∃ i, v i ≠ 0) ∧ ∀ i, adjacencyAction S v i = value * v i` with the true matrix rows (v₀ ↦ v₁+v₂ etc.); `one_not_adjacency_eigenvalue` holds for every `ScalarLaws K` (char ≠ 2 field laws, hence for ℂ) — not restricted to integer vectors; the integer instance is only a consistency check.
- Final theorem:
```
theorem conjecture6542_false {K : Type} (S : ScalarLaws K) :
    ¬(HasPoleAt iharaZeta 1 2 → Eigenvalue S S.one)
```
  The actual zeta has a pole at 1 (whose reciprocal is 1, `one_is_its_reciprocal`), yet 1 is not an adjacency eigenvalue — so the pole-reciprocal-to-spectrum implication fails, refuting the conjecture's bridge clause regardless of set-vs-multiset readings (the failure is at membership level, as the tex notes). Non-vacuous: both sides instantiated with actually-proved facts; universal over all eligible scalar fields, hence covering ℂ.

Interpretation disclosure: the conjecture's other clauses (index, finite domain, covering kernel) are not interpreted — the refutation only needs the pole/eigenvalue clause, which is explicit in both languages. The standard theory (Horton–Stark–Terras conventions, primes not modulo reversal) is used and cited.
## Issues found
none blocking
## Verdict rationale
The Lean project genuinely derives Z_{C3}(u) = 1/(1−u³)² from the standard Ihara definitions (complete symbolic classification of primitive cycles, actual rotation quotient, real Euler product), certifies the order-2 pole at u=1 exactly, and proves 1 is not an adjacency eigenvalue over any char≠2 field including ℂ — I confirmed every numeric fact independently via the Bass determinant formula. The conjecture's literal claim that pole reciprocals form the adjacency spectrum fails on C3 under every plausible reading, the build is clean with only standard axioms, and all auxiliary outputs reproduce.

## Disposition
APPROVED — merged into main (PR 357). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
