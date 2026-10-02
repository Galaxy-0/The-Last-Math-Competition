# Disproof of TLMC Conjecture 00000001068

**Original statement.** Definition: A sum-free set (A + A disjoint from A). Conjecture: The maximal sum-free subsets of F_p are exactly the intervals ((p+1)/3, 2(p−1)/3), uniquely up to dilation (the complete Diananda–Yap characterization over finite fields).

（原文定义句逐字引用自 `conjectures/00000001068.md` 的 English 段。）

## Disproof (counterexample at p = 11)

Take **A = {4, 5, 6, 7} ⊆ F_11**.

1. **A is sum-free.** A + A = {8,9,10,0, 9,10,0,1, 10,0,1,2, 0,1,2,3} = {0,1,2,3,8,9,10} = F_11 \ A, disjoint from A.

2. **A is inclusion-maximal sum-free.** Every x ∉ A lies in A + A (in fact A + A = F_11 \ A), so A ∪ {x} contains an element of its own double sum and is not sum-free. (A is even a *maximum* sum-free set in F_11, of the classical Diananda–Yap form {⌊p/3⌋+1, …, ⌊2p/3⌋}.)

3. **The conjectured interval is far too small.** ((p+1)/3, 2(p−1)/3) = (4, 20/3) = {5, 6} ⊆ F_11 has only **2** elements; every dilation c·{5,6} (c ∈ F_11^×) also has exactly 2 elements (and 0·I = {0}).

4. **A is not a dilation of the interval.** |A| = 4 ≠ 2 = |c·I| for all c ∈ F_11; exhaustively, no c ∈ {0,…,10} satisfies c·I = A.

Hence at p = 11 there exists a maximal sum-free subset of F_11 that is not of the form c·((p+1)/3, 2(p−1)/3), refuting the claimed characterization. (The failure is the open-interval formula itself: dropping the endpoints undercounts the extremal sets — the correct classical family is the closed integer interval [⌊p/3⌋+1, ⌊2p/3⌋], which at p = 11 is A itself.)

## Files

- `main.tex` — full write-up of the counterexample.
- `reproduce.py` — recomputes every number above from scratch; prints PASS/FAIL per check.
- `lean4/Main.lean` — machine-checked disproof: A sum-free, inclusion-maximal, |A| = 4, and no dilation of the interval equals A; all proofs are `rfl` over explicit F_11 computations.
- `lean4/Check.lean` — `#print axioms` audit for every theorem.

## Verification

- `pack.sh verify 00000001068` → PDF OK, LEAN BUILD OK, **VERIFY PASS**.
- Axiom audit: **7/7 theorems axiom-free** (no `sorry`, no `Classical.choice`, no `Quot.sound`, no `propext`).
