# Solution Review — Conjecture 00000007755 (PR 841)

**Submission:** earthking11 — `earthking11_submission_20261007091244`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-07

## Checklist results
- Conjecture read: yes — the source asserts (i) that for each fixed degree `d` there are only finitely many postcritically finite (PCF) polynomials with algebraic coefficients, and (ii) that for `d = 2` the count `N(H)` of PCF parameters of height at most `H` is asymptotic to `C·H^{1/2}`.
- Change scope: only the allowed submission directory `solutions/00000007755/earthking11_submission_20261007091244/` was added. Base metadata marks the conjecture unsolved and no prior valid solution existed. The PR explicitly supersedes the earlier, defective PR #826 and explains that defect.
- LaTeX: `solution.tex` read in full. The disproof is elementary, self-contained, and complete.
- Lean build: Lean 4.33.1, Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474` (exact official dependencies). `lake build` exit 0 (`1969 jobs`, including the final `Main` target). A direct `lake env lean -DwarningAsError=true Main.lean` reports only a style-linter notice (`linter.style.haveILetI`, `haveI` vs `have`, at `Main.lean:124`) promoted to an error; this is cosmetic and does not affect the kernel-checked proof.
- Forbidden content: no `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC` anywhere in the submission's Lean sources.
- Auxiliary code: none is supplied or needed.
- Axioms: `#print axioms` for `infinite_normalized_pcf_parameters`, `infinite_normalized_quadratic_pcf`, and `normalized_affine_conjugate_iff` reports only `[propext, Classical.choice, Quot.sound]`.

## Semantic audit
The submission works in the normalized quadratic family `F_c(X) = X² + c` over `K = AlgebraicClosure ℚ`, whose unique critical point is `0`. It defines the critical-orbit polynomials `P_0 = 0`, `P_{n+1} = P_n² + T` and `Q_0 = 1`, `Q_{n+1} = T·Q_n² + 1`, and proves the identity `P_{n+1}(T) = T·Q_n(T)`. For every `n ≥ 1`, `Q_n(0) = 1` and the coefficient of `T` in `Q_n` equals `1`, so `Q_n` is nonconstant and has a nonzero root in the algebraically closed field `K`.

For each prime `p`, a nonzero root `c_p` of `Q_{p-1}` satisfies `F_{c_p}^{∘p}(0) = P_p(c_p) = 0`, while `F_{c_p}(0) = c_p ≠ 0`; hence the critical point has exact minimal period `p` and `F_{c_p}` is PCF. Distinct primes give distinct parameters, so the set of PCF parameters is infinite. The Lean theorem `infinite_normalized_pcf_parameters : Set.Infinite {c : K | PCF (normalized c)}` formalizes exactly this. Finally `normalized_affine_conjugate_iff : AffineConjugate c d ↔ c = d` proves that distinct parameters in this normalized family are not affinely conjugate, so the counterexamples are distinct in the moduli space of quadratic maps. This directly falsifies clause (i) of the conjecture, even when read up to affine conjugacy; a disproof of a conjunct disproves the conjecture.

## Issues found
- Minor, non-blocking: the style linter flags `haveI` at `Main.lean:124` (prefer `have`). No mathematical or kernel impact.

## Verdict rationale
The construction is correct and fully formalized; the Lean project compiles with only the three standard axioms and contains no forbidden content. The submission correctly refutes the finiteness assertion of conjecture 00000007755 (the second, height-asymptotic clause is not needed). The earlier defect of PR #826 (a family contained in a single affine-conjugacy class) is explicitly repaired.

## Disposition
APPROVED — ready to merge (PR 841).
