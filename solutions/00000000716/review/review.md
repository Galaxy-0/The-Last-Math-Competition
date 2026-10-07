# Solution Review — Conjecture 00000000716 (PR 718)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005144549`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (EN+CN): the correction term (sign) in Γ_p(a)·Γ_p(1−a) = ±1 is an explicit function of p mod 4. `conjecture.md` byte-identical to the official file.
- LaTeX: independent rebuild exits 0; shipped PDF matches in content (shipped file uses xdvipdfmx; extraction artifacts only).
- Lean build: exit 0, 8708 jobs, zero errors/warnings.
- Forbidden content: none.
- Axioms: my independent `CheckJ6.lean` over all 11 theorems: exactly `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs verified; CRLF manifest artifact only.
- Sanity check: mor_p(1)·mor_p(0) = −1, mor_p(p−1) ≡ (p−2)! ≡ 1 (mod p) (Wilson), mor_3(4) ≡ −1, mor_7(4)² ≡ 1 (mod 7) — all confirmed numerically; also cross-checked against the published formula Γ_p(x)Γ_p(1−x) = (−1)^{x₀} (x₀ the first p-adic digit), which plainly depends on x mod p, not on p mod 4.

## Semantic audit
The submission builds Morita's p-adic gamma function Γ_p on Z_p from scratch rather than assuming it: mor_p(n) = (−1)^n ∏_{0<j<n, p∤j} j; the approximants mor_p(appr x k) form a Cauchy sequence (Morita congruence mor_p(n) ≡ mor_p(m) mod p^k whenever n ≡ m, proved via the generalized Wilson theorem — product of units of Z/p^k is −1, using that ±1 are the only self-inverse units mod odd prime powers); the limit Γ_p is continuous, interpolates mor_p on N, and is unique with these properties. This is the standard construction and it makes every later value computation a theorem about the genuine Γ_p.

The conjecture's quantifier over a is unspecified, so both readings are refuted, each by the exact negation. Reading (A) (one f of p mod 4 working for all p, a): `not_function_of_p_mod_four` — for every odd prime p, Γ_p(1)Γ_p(0) = −1 but Γ_p(2)Γ_p(1−2) = 1 in Z_p (Γ_p(−1) ≡ mor_p(p−1) ≡ 1 mod p, computed through mor_p(p) ≡ mor_p(0)); since 1 ≠ −1 in ZMod p, the product is not even a function of p alone. Reading (B) (for fixed a, a function of p mod 4): `not_function_of_p_mod_four_at_four` — at a = 4 the product is −1 mod 3 for p = 3 and 1 mod 7 for p = 7, and 3 ≡ 7 (mod 4); a Z-units-valued sign s would have to be ±1, and both choices contradict a `decide`-closed finite computation. Both proofs only use mod-p consequences of hypothetical equalities in Z_p, which is sound.

Interpretive honesty is exemplary: the tex explicitly identifies the reading under which the conjecture is TRUE (a = 1/2: Γ_p(1/2)² = (−1)^{(p+1)/2}, the classical reflection formula, is a function of p mod 4) and states that it does not adopt that reading because the conjecture quantifies over general a. The refutation targets exactly what is written.

## Issues found
- None blocking.

## Verdict
APPROVED. A substantial and correct Lean construction of Morita's Γ_p, with two exact-negation refutations of the written claim (dependence on a at fixed p; dependence on p beyond p mod 4 at fixed a = 4), clean build and axioms, and a scrupulously honest reading section.
