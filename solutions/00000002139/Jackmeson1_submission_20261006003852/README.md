# Prove conjecture 00000002139: the floor-sum recursion follows the Euclidean algorithm and makes O(log m) calls

- **Object.** F(n,m,a,b) = Σ_{i<n} ⌊(a·i + b)/m⌋ (AtCoder Library `floor_sum`, retrieved docs and code); `floorSum` uses ℕ division and is proved equal to the true rational floor (`floorSum_cast`).
- **Recursion.** Reduce a, b mod m, then swap modulus and slope via the lattice-point identity F(n,m,a,b) = F(⌊y/m⌋, a, m, y mod m) for a ≥ 1, b < m, y = an + b (`floorSum_swap`); this is the Euclid-like algorithm of the retrieved OI-wiki page.
- **Euclid path.** `fsRec` (stopping when the slope is 0) computes F, and its (modulus, slope) call path equals Euclid's trace on (m, a), whose last modulus is gcd(m, a).
- **Complexity.** At most 2·log₂ m + 1 calls (and at most 2·log₂ min(a,m) + 2), for every n and b; consecutive Fibonacci inputs need log₂ m + 1 calls (`fsRec_fib`), so the worst case is Θ(log m).
- **AtCoder loop.** The exact ACL loop (`aclRec`, early exit when y < m) also computes F; its path is a prefix of Euclid's trace and it makes at most 2·log₂ m + 1 iterations. Signed a, b reduce to this case by one normalization step (`floorSumInt_recursion`).
- **Reading choices.** "Its recursion" is not specified in the text: the standard ACL / OI-wiki recursion is used, with both stopping rules formalized; complexity = number of calls (bit complexity not addressed); m ≥ 1.
- **Main theorem.** `C2139.floorSum_recursion_euclid`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 362 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2139/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002139.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2139.floorSum_recursion_euclid`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-06): no solution folder for 00000002139 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
