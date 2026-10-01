# Disproof of TLMC conjecture 00000001040

**Verdict: FALSE** — counterexample at the prime **q = 5** (5 ≡ 2 mod 3).

## Conjecture

The complete-mapping polynomials (f with f(x)+x a permutation) at q ≡ 2 (mod 3)
form the complete equivalence class of x³ type (a cubic classification of
complete mappings).

## Attack

At q = 5 the two sides of the classification come apart completely:

1. **Complete mappings exist.** f(x) = 2x is a complete mapping: 2x is the
   permutation (0,2,4,1,3) and f+x = 3x is the permutation (0,3,1,4,2).
2. **The x³-type class is empty.** x³ + x is not a permutation — its values on
   F₅ are (0,2,0,0,3): x = 0, 2, 3 all map to 0. More strongly, *no* member of
   the affine x³-family A(x+B)³ + C (A ∈ F₅ˣ, B, C ∈ F₅) is a complete
   mapping: f + x = A·y³ + y + (C−B) with y = x+B, and A·y³ + y is a
   permutation for no A ∈ F₅ˣ:
   - A=1: (0,2,0,0,3) — 0,2,3 collide
   - A=2: (0,3,3,2,2) — 1,2 and 3,4 collide
   - A=3: (0,4,1,4,1) — 1,3 and 2,4 collide
   - A=4: (0,0,4,1,0) — 0,1,4 collide at 0
3. **Census.** Exactly 15 linear complete mappings ax+b exist (slopes
   a ∈ {1,2,3}, b ∈ F₅; a = 0 not a permutation, a = 4 gives (a+1)x = 5x = 0
   constant). Brute force over all 5! = 120 permutations of F₅ (every function
   F₅ → F₅ is a polynomial of degree < 5) shows Z₅ has exactly 15 complete
   mappings in total — precisely the linear ones. The x³ class contributes 0.

Hence the complete mappings at q ≡ 2 (mod 3) are *not* the x³-type class:
the classification is false. (Also a fortiori: the 15 complete mappings are
linear, and no degree-preserving equivalence — affine, EA, linear — can place
a degree-1 polynomial in the degree-3 x³ class.)

## Boundary

- q = 5 is the smallest non-degenerate prime power with q ≡ 2 mod 3.
  q = 2 is degenerate: F₂ admits no complete mapping, so the conjecture holds
  vacuously there.
- The same obstruction persists at every prime q ≡ 2 mod 3, q ≥ 5: f = 2x has
  f + x = 3x a permutation (3 ∤ q), and this degree-1 complete mapping cannot
  belong to the x³ equivalence class. At q = 11 x³ itself happens to be a
  complete mapping (−1 is a quadratic non-residue mod 11, so x³+x = x(x²+1)
  has the single root 0), but the classification still must exclude the
  coexisting linear complete mappings, e.g. 2x.

## Files

| File | Purpose |
| --- | --- |
| `README.md` | this file |
| `main.tex` | formal write-up (self-contained, no absolute paths) |
| `build/main.pdf` | compiled PDF |
| `build/log.txt` | tectonic build log |
| `reproduce.py` | independent recomputation; `python3 reproduce.py` exits 0 iff all checks pass |
| `lean4/` | Mathlib-free Lean 4 (v4.33.1) verification |

## Lean verification

```sh
cd lean4
lake build
lake env lean Check.lean
```

`Main.lean` defines `isPerm5` (pairwise-distinctness test on F₅), `linCM`
(linear complete-mapping test), `cmsCount` and `cubeFamFails`, and proves:

- `q5_two_mod_three` : 5 % 3 = 2
- `f2x_complete` : 2x and 3x are both permutations of F₅
- `x3x_not_perm`, `x3x_collisions` : x³+x is not a permutation; 0, 2, 3 collide at 0
- `cube_family_empty` : no A(x+B)³ with A ∈ F₅ˣ, B ∈ F₅ is a complete mapping
- `linear_classification` : full 25-case classification of linear candidates
  (15 complete mappings with slopes 1, 2, 3)
- `disproof_00000001040` : the conjunction of the above numerical facts

All proofs are `decide` (kernel reduction over the explicit finite domain).
`Check.lean` audits every theorem with `#print axioms`; each reports "does not
depend on any axioms". Zero `sorry`, zero axioms, no `native_decide`.
`lean4/.gitignore` excludes `.lake/` and `lake-manifest.json`.
