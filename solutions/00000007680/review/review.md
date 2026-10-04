# Solution Review — Conjecture 00000007680 (PR 361)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "For fixed a, in every valid partition congruence (b,m) [p(an+b)≡0 mod m ∀n≥0], m's prime factors all lie in a negative-discriminant QF-represented set mod 24a; and for each such m the count of valid b in {0,…,a-1} equals ω(m), the number of distinct prime factors of m."
- LaTeX: recompiled twice with pdflatex, exit 0, zero errors; shipped main.pdf is a real PDF whose content matches the tex.
- Lean build: fresh `rm -rf .lake && lake build`, exit 0, zero warnings (`moreLeanArgs = ["-DwarningAsError=true"]`), Lean 4.19.0, `Std` only.
- Forbidden content: none. Single grep hit for "admit" is the English word "admitting" in the doc comment at Main.lean:64 ("conditional on (a,m) admitting a valid positive b") — verified not the `admit` tactic. `#print axioms conjecture7680_counterexample` = [propext, Classical.choice, Quot.sound] — standard.
- Auxiliary code: no Python/JS shipped (symbolic proof); verification/ contains build logs (build_0/1/2.log, exit 0 recorded), AUTHOR_RESULT.json, INDEPENDENT_REVIEW.md — consistent with my fresh build. Independently re-derived: ω(1)=0; for a=2, m=1 every residue b∈{0,1} is valid since x % 1 = 0 always (definitionally, for any p including the partition function).
## Semantic audit
Conjecture's literal count clause: "对每个这样的 m，使同余成立的 b 在 {0,…,a-1} 中的个数恰为 m 的不同素因子个数" (for each such m, the count of valid b in {0,…,a-1} is exactly ω(m)). The domain is "正整数 a,b,m" — positive integers — so m=1 is inside the stated domain, and m=1 occurs in valid pairs since p(2n+1)≡0 (mod 1) holds trivially for all n.

Lean encodes the actual objects: `def Congruence (p : Nat → Nat) (a b m : Nat) : Prop := ∀ n : Nat, p (a*n+b) % m = 0` (the real universally-quantified congruence); `residueCount p a m` filters all of `List.finRange a` (the complete residue set {0,…,a-1}); `distinctPrimeFactorCount m` is the honest ω(m) via `Prime p ∧ p ∣ m` with `Prime p := 2 ≤ p ∧ ∀ d ∣ p, d = 1 ∨ d = p`. Final theorem:

`theorem conjecture7680_counterexample (p : Nat → Nat) : ¬ CountAssertion p ∧ ¬ PositiveCountAssertion p`

with `CountAssertion p := ∀ a m, 0 < a → 0 < m → (∃ b, 0 < b ∧ b < a ∧ Congruence p a b m) → residueCount p a m = distinctPrimeFactorCount m` (and the positive-residue variant). Two key soundness points: (i) `CountAssertion` is an implication OF the literal conjecture clause — the conjecture, applying to every m occurring in a valid pair, in particular asserts the count for every m having a valid b in (0,a); so ¬CountAssertion ⟹ the conjecture's count clause is false. The extra existence hypothesis weakens the assertion being negated, which is the safe direction. (ii) The witness `(a,b,m) = (2,1,1)`: `every_sequence_mod_one` gives the congruence mod 1 for ANY sequence, `actual_residue_count` gives residueCount = 2 and `actual_positive_residue_count` gives 1, while `omega_one : distinctPrimeFactorCount 1 = 0`. Both 2≠0 and 1≠0, so both readings of the b-positivity convention are refuted. Generality over arbitrary `p : Nat → Nat` strictly strengthens the counterexample — it applies to the genuine partition function with no finite table or unproved identity.

The first (quadratic-form) clause is untouched — correctly so, since m=1 has no prime factors and satisfies it vacuously; refuting one conjunct of a conjunction suffices. Not vacuous: the negation is of a nontrivial universally-quantified assertion and the witnessing (a,b,m) is explicit.
## Issues found
none blocking
- Disclosed interpretation call: the refutation uses the literal "positive integers" domain, which includes m=1. An m≥2 reformulation would survive; the author explicitly flags this boundary in main.tex ("A reformulation imposing m≥2 would be a different assertion and is not addressed here"). Under the competition's authoritative-literal-statement adjudication this is in scope.
## Verdict rationale
The Lean theorem genuinely refutes the conjecture's exact-count clause on the literal positive-integer domain, with the real congruence definition, the complete residue-set count, and the honest ω(m); the arbitrary-sequence parameterization strengthens rather than weakens the counterexample. All builds are clean with only standard logical axioms, and the LaTeX faithfully documents both the argument and its scope boundary. The m=1 edge-case nature is disclosed and legitimate under the literal bilingual statement.

## Disposition
APPROVED — merged into main (PR 361). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
