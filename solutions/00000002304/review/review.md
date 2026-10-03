# Solution Review — Conjecture 00000002304 (PR 332)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003130000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — under GENERAL linear actions, equality k(GV) = k(G)k(V) holds exactly when V is faithful irreducible and G is of fixed-point-free type; otherwise strict inequality (plus a character-degree closure clause for the equality-class list).
- LaTeX: compiled ok (pdflatex twice, exit 0, 0 errors); included main.pdf real PDF v1.5, 2 pages, matches tex.
- Lean build: fresh build after `rm -rf .lake`, exit 0, no warnings; axioms propext/Classical.choice/Quot.sound exactly as recorded.
- Forbidden content: none. (`set_option maxHeartbeats 0` only disables the heartbeat budget; kernel checking is unaffected.)
- Auxiliary code: none shipped (`auxiliary_scripts_rerun: []`); nothing to run. No computational claims beyond the finite group computations, which are kernel-decided.
## Semantic audit
Conjecture literal claim: "The classification of equality under general linear actions: exactly when V is faithful irreducible and G is of fixed-point-free type ...; otherwise strict inequality." Both language versions state the general-action scope; neither imposes faithfulness or coprimality as a hypothesis. The disproof: G = C2 acting TRIVIALLY on V = F2 (nonzero one-dimensional); then GV = C2 × C2 is abelian, so k(GV) = 4 = 2·2 = k(G)k(V). Equality holds although the action is not faithful (kernel = G) and G is not of fixed-point-free type (the involution fixes every vector) — i.e., equality occurs outside the claimed equality class, refuting "otherwise strict inequality".

Lean definitions all faithful and genuine:
- `GroupData`/`FieldData`/`VectorSpaceData` carry the full algebraic laws; `C2`, `F2`, `V2` on Fin 2 verify them by kernel decide (F2 includes 0 ≠ 1 and the inverse law); `basis_vector_nonzero` rules out the zero-module artifact.
- `LinearAction` = action laws plus additivity and scalar-linearity (`map_add`, `map_smul`); `action_inverse` shows the acting maps are automorphisms; `trivialAction` is the action above.
- `Faithful ρ := ∀ g h, (∀ v, ρ.act g v = ρ.act h v) → g = h`; `not_faithful` uses 0 ≠ 1 directly.
- `semidirectMul ρ (x,y) = (x.1 + ρ.act x.2 y.1, x.2 * y.2)` — the standard semidirect product formula; `GV` verifies all group laws on the 4-element carrier.
- Class numbers are genuine: `Conjugate H x y := ∃ g, H.mul (H.mul g x) (H.inv g) = y`; `HasClassNumber H n` = a setoid whose relation is exactly conjugacy plus a bijection Fin n → Quotient. `conjugacy_C2`/`conjugacy_GV` prove conjugacy = equality (abelian), and `C2_class_number`/`V2_class_number`/`GV_class_number` give 2, 2, 4 via explicit quotient bijections (four-element enumeration `pairCode`).

Final theorems: `counterexample : HasClassNumber C2 2 ∧ HasClassNumber V2.additive 2 ∧ HasClassNumber GV 4 ∧ 4 = 2*2 ∧ ¬Faithful trivialAction`, and `conjecture2304_false : ¬ ClaimedEqualityNecessity` where `ClaimedEqualityNecessity := ∀ (ρ : LinearAction C2 F2 V2) (H : GroupData (Bit×Bit)), H.mul = semidirectMul ρ → H.one = (0,0) → ∀ kG kV kGV, HasClassNumber C2 kG → HasClassNumber V2.additive kV → HasClassNumber H kGV → kGV = kG*kV → Faithful ρ` — the "equality implies faithful" necessary condition of the source classification, restricted to the concrete group/field/space (a universal general-action classification necessarily implies this instance).

(i) Definitions faithful. (ii) Hypotheses: the conjecture quantifies over general linear actions with no faithfulness/coprimality hypothesis; the trivial action of the nontrivial group C2 on the nonzero space F2 is such an action. (iii) The equality 4 = 2·2 with ¬Faithful directly contradicts the necessity direction of the stated classification ("otherwise strict inequality"). (iv) Not vacuous: nonzero space (explicitly proved), nontrivial group, genuine semidirect product, genuine conjugacy-class quotient counts — all the conjecture's decisive objects are present; the trivial action is the mathematical point of the counterexample, not a trick. LaTeX matches Lean: same example, same numbers 2/2/4, same structures and theorem names.
## Issues found
- Judgment call for the organizer (non-blocking as stated): the counterexample uses a trivial action and |G| = char(F) = 2, so it does NOT touch the classical k(GV) problem with its faithfulness or coprimality hypotheses. The submission is transparent about this and scopes itself to the conjecture exactly as written, which says "general linear actions" and asserts strict inequality "otherwise". If the organizers intended the classical restricted setting, the conjecture text would need those hypotheses added; as stated, the refutation stands.
- Non-blocking: the character-degree "closure" clause of the conjecture is not formalized; the false necessary condition (faithfulness for equality) already refutes the classification, as the tex notes.
## Verdict rationale
The conjecture as literally stated claims a complete equality classification over general linear actions, with strict inequality in all remaining cases; the submission exhibits a genuine, nondegenerate linear action (trivial action of C2 on F2) attaining equality without being faithful, and proves every component — group, field, vector space, semidirect product, conjugacy-class counts 2/2/4, nonfaithfulness — in Lean with only standard axioms. Everything compiles and runs. Approved as a disproof of the conjecture as stated, with the classical-setting caveat noted above.

## Disposition
APPROVED — merged into main (PR 332). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
