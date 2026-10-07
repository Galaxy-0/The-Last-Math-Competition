# Solution Review — Conjecture 00000004044 (PR 645)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005073007`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — HH¹ of a quiver algebra solvable iff its oriented cycles are all broken after removing at most one vertex; decision table complete for n ≤ 6; `conjecture.md` is byte-identical to `conjectures/00000004044.md`.
- Change scope: only the submission folder was added.
- LaTeX: independently rebuilt (exit 0); shipped/rebuilt text matches up to glyph extraction artifacts.
- Lean build: `lake build` exit 0, zero errors, zero warnings.
- Forbidden content: none executable; no `sorry`, no `native_decide`, no axiom declarations.
- Axioms: independent run — `conjecture_00000004044_false`, `conjecture_00000004044_iff_fails`, `paths_bijective` all use only `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs reproduce; SHA-256 manifest stale (see Issues).
- Semantic audit: pass (below).
- Independent arithmetic check: the derivation identity, the bracket relation, the non-innerness computation and the derived-series induction were all re-derived by hand.

## Semantic audit
The refutation targets the English text exactly: HH¹ solvable ⟸ cycles broken by at most one vertex. One failing direction falsifies the biconditional and a fortiori the universal formula; since the counterexample has n = 2 vertices, it also falsifies the claimed completeness of the n ≤ 6 decision table. The witness is non-degenerate: the generalized Kronecker quiver K₃ (two vertices, three parallel arrows 1 → 2) has no closed path of positive length (proved by a path-shape induction: every path has length 0 or is a single arrow 1 → 2), so the right-hand side holds with S = ∅ ("at most one" includes zero, and `CyclesBrokenByAtMostOneVertex` quantifies over closed paths of positive length, which is exactly the oriented-cycle condition). The path algebra kK₃ is a quiver algebra in both standard senses: finite-dimensional, and I = 0 = R_Q² is admissible since K₃ has no composable pair of arrows (paths_bijective confirms the basis is exactly the five paths e₁, e₂, α₀, α₁, α₂).

The Hochschild machinery is built directly and faithfully — Mathlib's `Derivation` requires commutativity, so `Der k A` (Leibniz subalgebra of End under the commutator), `Inn k A` (the ad's, a Lie ideal via [D, ad a] = ad(Da)), and `HH1 = Der/Inn` with the quotient Lie structure are defined from scratch, matching the standard description of HH¹(A,A); `LieAlgebra.IsSolvable` is Mathlib's derived-series definition.

The linear-algebra core checks out. I verified from the multiplication table (e₁αᵢ = αᵢ = αᵢe₂, e_i² = e_i, all other products 0) that the α_l-coordinate of xy is x_{e₁}y_{α_l} + x_{α_l}y_{e₂}, whence D_{ij} (α_j ↦ αᵢ, everything else killed) satisfies the Leibniz rule on both α- and e-coordinates; that [D_{im},D_{mj}] = D_{im}D_{mj} − D_{mj}D_{im} = D_{ij} (the reverse composition kills because D_{im} lands in kαᵢ and D_{mj} annihilates αᵢ for i ≠ j); and that D_{ij} is not inner, since ad(a)(α_j) = (a_{e₁} − a_{e₂})α_j has zero α_i-coordinate while D_{ij}(α_j) = αᵢ. In the quotient, d_{ij} = [d_{im}, d_{mj}] for any third index m, so induction keeps every d_{ij} in every derived term; a vanishing term would make d₀₁ = 0, i.e. D₀₁ inner — contradiction. The argument uses no characteristic assumption, so it works over every field, exactly as claimed. The report also transparently discloses that the Chinese body's 可约 ("reducible") reading is not addressed, while the English "solvable" and the conjecture's own name ("solvability criterion") are the reading refuted — a reasonable and honestly stated choice.

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale (hashes of `conjecture.md` and the main Lean file do not match the shipped files; the shipped `conjecture.md` is byte-identical to the official source and the shipped Lean file builds cleanly with clean axioms).

## Verdict
APPROVED. A correct, non-degenerate, fully formalized counterexample inside the claimed-complete range, in all characteristics; all audited checks reproduce.
