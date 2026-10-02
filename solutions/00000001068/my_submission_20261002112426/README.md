# Disproof of TLMC Conjecture 00000001068

**Verdict: FALSE.** Counterexample at `p = 11`.

## The conjecture

The maximal sum-free subsets of `F_p` are exactly the intervals
`((p+1)/3, 2(p-1)/3)`, uniquely up to dilation (claimed as the complete
Diananda–Yap characterization over finite fields).

## Attack (p = 11)

- Claimed interval `I = ((p+1)/3, 2(p-1)/3) = (4, 20/3) = {5, 6}`, so `|I| = 2`.
- `A = {4, 5, 6, 7}` is sum-free in `F_11`:
  `A + A = {0,1,2,3,8,9,10} = F_11 \ A`, which is disjoint from `A`; `|A| = 4`.
- `I ⊊ A` and `A` is sum-free, hence `I` is **not** a maximal sum-free set.
  The same holds for every nonzero dilate: for `d = 1..10`, `dI` has exactly
  `2` elements and lies strictly inside the sum-free set `dA` (witnessed by
  `4d mod 11 ∈ dA \ dI`). So the conjectured family contains **no** maximal
  sum-free set at all at `p = 11`.
- Conversely, `A` **is** maximal sum-free: every `x ∉ A` lies in `A + A`
  (0 = 5+6, 1 = 5+7, 2 = 6+7, 3 = 7+7, 8 = 4+4, 9 = 4+5, 10 = 4+6), so no
  element can be added. Since `|A| = 4 ≠ 2 = |I|` and dilates preserve size,
  `A` is a maximal sum-free set that is **not** a dilate of `I`.

Both inclusions of the claimed characterization fail at `p = 11`.

## Boundary

- Brute force over all `2^11` subsets of `F_11` confirms: the maximum
  sum-free size is `4 (= ⌊(p+1)/3⌋)`, there are `15` maximal sum-free sets
  with sizes in `{3, 4}`, and `A = {4,5,6,7}` is one of the maximal ones.
- The attack is robust to endpoint conventions: with integer-division
  endpoints the open reading gives `(4, 6) = {5}` and the closed reading
  `[4, 6] = {4,5,6}`; both are still strictly contained in the sum-free set
  `A`, hence non-maximal under every reading.
- The breakage is not specific to `p = 11`: under the exact-rational open
  reading the claimed interval has size `0, 0, 0, 1, 2, 3` for
  `p = 2, 3, 5, 7, 11, 13` while the true maximum sum-free size is
  `1, 1, 2, 2, 4, 4` respectively — the claimed interval is non-maximal for
  every prime in this census. The true Diananda–Yap extremal interval is
  `{⌊p/3⌋+1, …, ⌊2p/3⌋}` (`{4,…,7}` for `p = 11`); the conjecture's open
  endpoints `((p+1)/3, 2(p-1)/3)` truncate it, which is what destroys
  maximality. A single counterexample (`p = 11`) refutes the conjecture.

## Reproduction

- `python3 reproduce.py` — independent recomputation of every number above
  (sum-freeness, maximality, brute-force census, dilates); exits 0 on success.
- `lean4/` — machine-checked formalization in pure Lean 4 (no Mathlib, no
  axioms, no `sorry`); see `lean4/README.md`.
- `main.tex` / `build/main.pdf` — full write-up.
