# Solution Review — Conjecture 00000007676 (PR 339)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003104000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — the q-Eulerian polynomial A_n(q,t)=Σ q^{maj} t^{des} is asserted to have the gamma-expansion A_n=Σ_j γ_{n,j}(q) t^j(1+t)^{n-1-2j}, and γ_{n,j}(q) is conjectured to lie in N[q] with monomial count equal to the peak-set family cardinality; submission shows the asserted expansion itself does not exist already at n=2.
- LaTeX: compiled ok (pdflatex twice, exit 0, zero errors); shipped main.pdf is a real 2-page PDF (46 KB) matching main.tex; recompile also 2 pages.
- Lean build: fresh build exit 0, "Build completed successfully", `-DwarningAsError=true`; only `#print axioms` info (propext, Quot.sound).
- Forbidden content: none found.
- Auxiliary code: verify.cjs exit 0, output identical to auxiliary-results.json; my independent sympy/brute-force check: A_2(q,t)=1+q·t, not palindromic in t, and {γ : γ(q)(1+t)=1+qt} is empty (also fails at n=3: A_3=1+(2q+2q²)t+q³t²) — asymptotic/expansion logic in the report is correct.
## Semantic audit
Conjecture (EN+CN, reproduced verbatim in SOURCE.md — verified by exact diff): the Definition clause asserts A_n "has the gamma-expansion" (的 γ-展开为). At n=2 the standard gamma range is j=0 only, so the claim is 1+qt = γ_{2,0}(q)(1+t); the t⁰ coefficient forces γ=1 and the t¹ coefficient forces γ=q — impossible for any function γ, a fortiori for N[q] polynomials. Hence the expansion asserted in the definition does not exist, so the properties attributed to γ_{n,j}(q) cannot hold; the statement as written is refuted. The submission explicitly and honestly scopes this (SOURCE.md: "a conditional claim assuming such an expansion already exists would not be refuted").

Lean: `IsPermutation f` = injective ∧ surjective on Fin 2 (true bijections, not labels); `wordMap_encode` proves every map is encoded, and `permutationWords_exact`/`permutationWords_nodup`/`all_permutations_represented` make S_2 genuinely present (the anti-#286 requirement). `descents p = [1]` iff second entry smaller, with `usual_labels_same_order` justifying label shift — maj uses one-based positions as required. `eulerianTwo_formula : eulerianTwo q t = 1 + q * t` proved by simp. N[q] is represented by `List Nat` + Horner evaluation (`evalNonnegativePolynomial`), which is exactly arbitrary N[q] polynomials. `gammaSum 2 gamma q t = evalNonnegativePolynomial (gamma 0) q * (1+t)` with the standard range ⌊(n−1)/2⌋. Key theorems:
- `no_scalar_gamma_expansion : ¬ (∃ c : Int, ∀ t, eulerianTwo 2 t = c * (1+t))` — after specializing q=2: t=0 gives c=1, t=1 gives 3=2c; contradiction, with sign unrestricted.
- `Conjecture7676AtTwo := ∃ gamma, ∀ words, FullPermutationEnumeration words → ∀ q t, qEulerian words q t = gammaSum 2 gamma q t` — the n=2 necessary instance over any complete duplicate-free enumeration; `conjecture7676_counterexample : ¬ Conjecture7676AtTwo`.
The evaluation-identity formulation is sound: a polynomial identity implies all integer evaluation identities, so refuting the latter refutes the former (report explains this). Hypotheses satisfied (the two words are the actual bijections), not vacuous; report table (12→1, 21→qt) matches Lean's `statistics`.
## Issues found
- Ambiguity (non-blocking): under a strictly conditional reading ("if the expansion exists, then γ ∈ N[q] and monomial counts match"), the first clause would be vacuously satisfiable and this argument would not apply; but both the English and Chinese Definition clauses assert the expansion exists, so the refutation targets the statement as written. Submission discloses this openly.
## Verdict rationale
A_2(q,t)=1+qt cannot be written as γ(q)(1+t) for any γ, so the gamma-expansion asserted by the conjecture's own definition does not exist and the conjecture's objects are ill-defined; the Lean proof derives this from the genuine (maj,des) statistics on the true S_2 with bijections verified, quantifying over any complete enumeration. Builds clean with warnings-as-errors, auxiliary outputs reproduce, and my independent computation confirms both n=2 and n=3 failures. Genuine disproof as stated.

## Disposition
APPROVED — merged into main (PR 339). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
