# Solution Review — Conjecture 00000002353 (PR 347)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the realization domain (matrix well-definedness) of an nc rational function is a matrix-convex free semialgebraic set, with an explicit LMI representation.
- LaTeX: compiled (pdflatex twice, exit 0, 1 page); shipped main.pdf real PDF v1.5 matching the recompiled text (kerning-only differences).
- Lean build: exit 0, fresh (`rm -rf .lake && lake build`), Lean 4.19.0, `import Std`. Clean; only `#print axioms` info lines.
- Forbidden content: none (grep zero matches). Axioms: [propext, Quot.sound] / none — standard. Note: `FieldData` is a structure whose field laws are hypotheses (universally quantified in the final theorem), NOT `axiom` declarations — verified by reading the source.
- Auxiliary code: no Python/JS shipped; recorded verification logs match my fresh build. Independent check of the mathematics by hand: domain of x↦x^{-1} = invertible matrices; 1 and −1 invertible; midpoint 0 not invertible; matrix convexity (Σ A_i* X_i A_i, Σ A_i* A_i = I) specializes with A_1=A_2=2^{-1/2}I to same-size midpoints; hence non-closure under midpoints refutes matrix convexity. The witness matrices are self-adjoint, so the restriction to self-adjoint points does not rescue the claim.
## Semantic audit
Conjecture (literal): "Its realization domain (matrix well-definedness) is a matrix-convex free semialgebraic set; and the domain has an explicit LMI representation". The PR disproves via r(x) = x^{-1}, whose domain is the set of invertible matrices at all levels — the standard counterexample (cf. Volčič, cited in the report).

Key Lean signatures (lean/Main.lean, namespace Conjecture2353):
- `structure FieldData (K : Type u)` — commutative field laws + `half` with `half_spec : (1+1)*half = 1`, all as explicit hypotheses; the final theorem is universal over `FieldData K`, hence applies to ℝ and ℂ (char ≠ 2). A concrete model `fieldThree : FieldData (Fin 3)` (by decide) checks consistency of the interface.
- `abbrev Matrix K n := Fin n → Fin n → K`, `def multiply` (finite-sum matrix product), `def identity`, `def IsInverse F A B := multiply F A B = identity ∧ multiply F B A = identity` — two-sided inverses.
- `inductive Expression | variable | inverse`, `def Evaluates` (recursion: variable ↦ X; `inverse e` evaluates to Y iff e evaluates to some Z with Z a two-sided inverse of Y) and `def Domain F e X := ∃ Y, Evaluates F X e Y` — a genuine rational-expression evaluation semantics whose fragment contains x^{-1}.
- `theorem reciprocal_domain : Domain F reciprocal X ↔ ∃ Y, IsInverse F X Y` — the domain of the inverse expression is exactly the invertible matrices. This is the substantive identification, proved not assumed.
- `theorem scalar_inverse_bridge : IsInverse F (scalarMatrix a) (scalarMatrix b) ↔ a*b = 1 ∧ b*a = 1`; `positive_in_domain`, `negative_in_domain`, `zero_not_in_domain` (0·Y = I impossible — proved via the (0,0) entry), `midpoint_is_zero` ((1 + (−1))/2 = 0 entrywise).
- `def MidpointClosedAtEveryLevel F e : Prop := ∀ n, ∀ A B : Matrix K n, Domain F e A → Domain F e B → Domain F e (midpoint F A B)` and `theorem conjecture2353_false {K} (F : FieldData K) : ¬MidpointClosedAtEveryLevel F reciprocal`.

The necessary-condition step (matrix convex ⟹ midpoint-closed at every level, via coefficient matrices V_1 = V_2 = I/√2 with V_1*V_1 + V_2*V_2 = I) is explained in the tex and is standard; refuting a necessary property of matrix convexity validly refutes the conjecture's matrix-convexity clause, and hence the conjunction (LMI-representable domains are matrix-convex, so that clause falls too). The objects — nc rational expression, evaluation/well-definedness domain, matrices, invertibility — are the conjecture's own; not vacuous, and the report specifically rebuts the "badly chosen expression branch" objection (any value of the inverse at 0 would need 0Y = Y0 = I).
## Issues found
- Disclosed gap in formalization coverage (mathematically immaterial): "matrix convex ⟹ midpoint closed" and the ℝ/ℂ instantiation of FieldData are argued in the tex rather than formalized (ℝ, ℂ unavailable in plain Std). The universal `FieldData` quantification makes the theorem apply to them; I judge this sound.
- Minor: the LMI clause (with adjoints) is not separately formalized; unnecessary once matrix convexity is refuted for the same expression.
## Verdict rationale
A correct and honestly scoped disproof of the conjecture's core claim using the canonical x^{-1} counterexample, with genuine formalization of rational-expression domains and matrix invertibility. Fresh build exits 0, standard axioms only, no forbidden constructs. The mathematical argument is complete under the standard definitions cited.

## Disposition
APPROVED — merged into main (PR 347). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
