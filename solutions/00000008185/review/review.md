# Solution Review — Conjecture 00000008185 (PR 653)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005075927`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — three laws (Vaughan-type bound with C = 4, finite exception law with last element 79, and the "G(k)=k first holds at threshold k ≥ 7" clause); `conjecture.md` is byte-identical to `conjectures/00000008185.md`.
- Change scope: only the submission folder was added.
- LaTeX: independently rebuilt (exit 0); shipped/rebuilt text matches (0.9999 agreement after normalization).
- Lean build: `lake build` exit 0, zero errors, zero warnings.
- Forbidden content: none executable; no `sorry`, no `native_decide`, no axiom declarations.
- Axioms: independent run — `C8185.conjecture_8185_false` uses only `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs reproduce; SHA-256 manifest stale (see Issues).
- Semantic audit: pass (below).
- Independent arithmetic check: the inequality C(t+k,k) + M ≤ t^k with t = 3k + 4^k·M was verified numerically for k = 2..8 and M ∈ {0,1,5,100,10⁶}; also the multiset count for k=2, t=10 (44 actual sums ≤ C(12,2)=66).

## Semantic audit
The third law is refuted under its literal text, which is explicit in both languages: "the high-dimensional generalization G(4) = 16 — namely G(k) = k — first holds at threshold k at least 7". The five natural readings — G(7)=7; G(k)=k for all k ≥ 7; G(k)=k eventually beyond some K ≥ 7; the least k ≥ 2 with G(k)=k exists and is ≥ 7; the least k ≥ 1 with G(k)=k is ≥ 7 — are each formalized and each proved false, so the clause fails however the garbled "threshold" is parsed. Refuting it suffices for the conjunction; the first two laws are honestly declared out of scope.

The definitions are faithful to Hardy–Littlewood: `IsSumAtMost k s n` says n is a sum of at most s positive k-th powers (a list with length ≤ s, entries > 0); `Suffices k s` says some N works for all n ≥ N; `waringG k = sInf {s | Suffices k s}`. The sInf-of-empty junk value is handled carefully: `waringG_ne` first proves the set is nonempty when G(k) = k ≥ 2 (otherwise sInf = 0 ≠ k), and `waringG_ge` assumes nonemptiness explicitly; `waringG 1 = 1` is proved outright (n = n¹ suffices; the empty sum does not).

The mathematics is the classical counting lower bound, proved from scratch: a sum of at most k positive k-th powers with n ≤ t^k has all bases ≤ t, and padding with zeros exhibits n as the k-th-power sum of a k-element multiset from {0,…,t}; there are C(t+k,k) such multisets (`mem_image_powSum` via `Sym (Fin (t+1)) k` and `Sym.card_sym_eq_choose`). The purely elementary inequality C(t+k,k) + M ≤ t^k for t = 3k + 4^k·M rests on k!·C ≤ (t+k)^k, 3^k(t+k)^k ≤ 4^k t^k (since t ≥ 3k), 4^k + 1 ≤ 3^k·k! (proved by induction), and C ≥ t+1 > 4^k·M; I verified (4^k+1)C ≤ 4^k t^k and the final inequality numerically across a range of k and M. Hence [M, t^k] contains more integers than there are multisets, so arbitrarily large n are not sums of at most k (a fortiori ≤ k) positive k-th powers. That is exactly G(k) ≥ k+1 for k ≥ 2, which kills every reading of the clause; the witness exponents are not degenerate (the failure holds at k = 7 itself).

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale (hashes of `conjecture.md` and the main Lean file do not match the shipped files; the shipped `conjecture.md` is byte-identical to the official source and the shipped Lean file builds cleanly with clean axioms).

## Verdict
APPROVED. A faithful, self-contained formalization of the classical counting obstruction; the clause is refuted under every literal reading, and all audited checks reproduce.
