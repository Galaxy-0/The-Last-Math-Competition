# Solution Review — Conjecture 00000008178 (PR 375)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004023414`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — conjunctive ABC conjecture: density exponent formula; the smallest ABC hit (smallest a+b=c) is the classical (2, 3^10·109, 23^5); optimal search complexity X^{2/3+ε} (disproof: (3,125,128) is an ABC hit with c = 128 < 23^5 = 6436343).
- LaTeX: compiled from scratch in /tmp/tlmc-review5/scratch/pr-375 (pdflatex twice, exit 0, 2 pages, no errors); shipped report.pdf is a real PDF with text identical to the recompile.
- Lean build: `rm -rf .lake && lake build` from a clean tree exit 0 ("Build completed successfully", 1801 tasks, zero warnings), toolchain leanprover/lean4:v4.19.0, Mathlib pinned at c44e0c8ee63ca166450922a373c7409c5d26b00b; `lake env lean Main.lean` exit 0; `#print axioms counterexample` shows only [propext, Classical.choice, Quot.sound]. (Dependencies source-built; artifacts seeded from my own identical-revision build — package git revisions verified identical — with this project's closure and Main.lean compiled in place.)
- Forbidden content: grep over all .lean files for `sorry`, `admit`, `native_decide`, `axiom` declarations, `unsafe`, `@[implemented_by]`, `extern`, `skipKernelTC` — nothing found. `decide` (kernel elaboration) is used only on small numerals (≤ 23^5 ≈ 6.4·10^6), not `native_decide`.
- Auxiliary code: none shipped; I independently re-derived everything with my own python3: 3+125=128; pairwise gcds all 1; 3·125·128 = 48000 = 2^7·3·5^3, rad = 30 < 128; 30^4 = 810000 < 2097152 = 128^3 (so 30 ≤ 128^{3/4} exactly); 2 + 3^10·109 = 6436343 = 23^5; rad of the claimed triple = 15042. Also confirmed both readings of the cutoff's n: 30 ≤ 128^{3/4} ≈ 38.05 and 30 ≤ 48000^{3/4} ≈ 3242.9. A scan for the actual smallest hit confirms (1,8,9) with c = 9 — the conjecture's minimality clause is false by a wide margin; the submitted witness (all entries > 1, avoiding any a=1 convention debate) suffices.
## Semantic audit
Conjecture (literal, EN+CN): "the smallest ABC hit (the smallest a + b = c) is the classical type (2, 3^{10} times 109, 23^5)" / "ABC-hits 的最小（a+b=c 的最小命中）为 (2,3^10·109,23^5) 型经典". Minimality is explicitly measured by c = a+b. The conjunctive structure means refuting the minimality clause refutes the conjecture; the density and algorithm clauses are left standing, as the report states.

Lean encodings (namespace `ABC8178`):
- `def radical (n : ℕ) : ℕ := n.primeFactors.prod id` — the radical from the actual prime-divisor multiset (Mathlib `Nat.primeFactors`), not an assumed value; `witness_primeFactors : (3*125*128).primeFactors = {2,3,5}` is proved from prime-power factorizations, then `witness_radical : radical (3*125*128) = 30`.
- `def ABCTriple a b c := 0 < a ∧ a < b ∧ a + b = c ∧ Coprime a b ∧ Coprime a c ∧ Coprime b c`; `def ABCHit := ABCTriple ∧ radical (a*b*c) < c`; `def CutoffHit ε := ABCHit ∧ (radical (a*b*c) : ℝ) ≤ c^(1-ε)` — the standard ABC-hit objects plus the conjecture's own power-cutoff wording.
- `def IsSmallestHit c₀ := ∀ a b c, ABCHit a b c → c₀ ≤ c` and `def IsSmallestCutoffHit ε c₀ := ∀ a b c, CutoffHit ε a b c → c₀ ≤ c` — the necessary minimality conditions implied by "the smallest hit is …".
- `theorem witness_cutoff : CutoffHit (1/4) 3 125 128` (via `witness_cutoff_bound : (30:ℝ) ≤ 128^(3/4)` using `Real.rpow_le_rpow_iff`, `Real.rpow_mul`, exact arithmetic), `theorem claimed_sum : 2 + 3^10*109 = 23^5`, `theorem smaller : 128 < 23^5`, `theorem not_smallest_hit : ¬ IsSmallestHit (23^5)`, `theorem not_smallest_cutoff_hit : ¬ IsSmallestCutoffHit (1/4) (23^5)`, and the combined final theorem
  `theorem counterexample : 0 < (1/4:ℝ) ∧ (1/4:ℝ) < 1 ∧ CutoffHit (1/4) 3 125 128 ∧ 128 < (23^5:ℕ) ∧ ¬ IsSmallestHit (23^5) ∧ ¬ IsSmallestCutoffHit (1/4) (23^5)`.

(i) Definitions faithful: rad, ABC triple (positivity, a<b, a+b=c, pairwise coprimality), ABC hit (rad(abc) < c), c-minimality — all standard and exactly the conjecture's objects; the cutoff uses Mathlib real exponentiation. (ii) Hypotheses satisfied: (3,125,128) is a coprime hit with rad 30 < 128 and satisfies the cutoff at ε = 1/4 under both readings of the cutoff's n (c and abc; the report proves the c-reading and notes abc ≥ c makes the abc-reading weaker). (iii) Contradiction: a hit with c = 128 exists while the conjectured minimum is 23^5 = 6436343 > 128, so `23^5 ≤ 128` is false — the minimality clause, and with it the conjunction, fails. (iv) Not vacuous: real ABC-hit objects with the actual radical computed, not assumed numerics; refuting a necessary condition of the conjectured minimum is sound (no assumption that the claimed triple is a hit is needed, and `claimed_sum` shows the triple was interpreted correctly).

Robustness across readings: under the plain "ABC hit = rad(abc) < c" definition the disproof is immediate; if "hit" were read through the density clause's cutoff class, the witness still lies in the ε = 1/4 class for both choices of the cutoff's radicand, while the claimed triple itself fails the cutoff for ε ≳ 0.39 — no reading rescues the clause.
## Issues found
none blocking
## Verdict rationale
(3,125,128) is an elementary, exactly verified ABC hit strictly smaller (in c = a+b) than the conjectured minimal triple, so the conjecture's minimality clause is false as literally stated in both languages. The Lean project computes the radical from actual prime factors, proves the cutoff inequality over ℝ, and negates both minimality notions with only standard axioms; build, PDF, and README/VERIFICATION.md records all check out, and my independent factorization agrees everywhere.

## Disposition
APPROVED — merged into main (PR 375). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
