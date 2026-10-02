# Disproof of TLMC conjecture 00000001067

**Verdict: FALSE.**

## 1. The conjecture, quoted verbatim (object-consistency discipline)

Original text, `conjectures/00000001067.md` (English line, quoted character-for-character):

> Definition: A B_h set (unique h-fold sums). Conjecture: The maximal B₂ set in F_p has size ⌈√p⌉ + O(1), and the O(1) term equals 0 for p ≡ 3 mod 4 (an exact B₂ result).

Chinese line of the same file: 「定义：B_h 集(和唯一)。猜想：F_p 的最大 B₂ 集为 ⌈√p⌉ + O(1) 且 O(1) 项 = 0 对 p ≡ 3 mod 4(B₂ 精确)。」

**Correspondence between the original wording and the objects attacked here:**

- "A B_h set (unique h-fold sums)" with h = 2, taken in F_p: a subset A ⊆ F_p such that the 2-fold sums a+b (a, b ∈ A) are unique **up to permutation of the summands**, i.e. all unordered pairs with repetition {a, b} (a ≤ b) have pairwise distinct sums in F_p. This is the standard Sidon (B₂) condition in the additive group (Z/pZ, +). (Uniqueness of *ordered* sums is impossible for |A| ≥ 2 since (a,b) and (b,a) coincide, so the multiset reading is the only non-degenerate one.)
- "The maximal B₂ set in F_p has size ⌈√p⌉ + O(1)" — "maximal" = maximum cardinality M(p) = max{|A| : A ⊆ F_p is B₂}; the statement is M(p) = ⌈√p⌉ + O(1).
- "the O(1) term equals 0 for p ≡ 3 mod 4" — for primes p ≡ 3 (mod 4), M(p) = ⌈√p⌉ **exactly**.

The attack below uses exactly these objects: subsets of Z/pZ with distinct unordered pair sums mod p, maximum cardinality, primes p ≡ 3 (mod 4). No redefinition is involved.

## 2. The attack (counterexamples to the O(1) = 0 clause)

Complete exhaustive enumeration of all subsets of Z/pZ (all 2^p masks; equivalently, all k-subsets for every k) gives:

| p | p mod 4 | M(p) = max B₂ size (exhaustive) | ⌈√p⌉ | a maximum B₂ set | claim M(p) = ⌈√p⌉ |
|---|---------|--------------------------------|-------|------------------|--------------------|
| 11 | 3 | **3** | 4 | {0, 1, 3} | **violated (3 ≠ 4)** |
| 19 | 3 | **4** | 5 | {0, 1, 3, 7} | **violated (4 ≠ 5)** |

- p = 11 is the formal counterexample: 11 ≡ 3 (mod 4) yet M(11) = 3 ≠ 4 = ⌈√11⌉. A B₂ set of size 4 in Z/11Z would need its C(4+1,2) = 10 unordered pair sums to be distinct among the 11 residues; exhaustive enumeration of all C(11,4) = 330 four-subsets (and hence all ≥ 4-subsets, since every subset of a Sidon set is Sidon) shows none exists, while {0,1,3} achieves 3.
- p = 19 corroborates: all C(19,5) = 11628 five-subsets fail, all C(19,4) = 3876 four-subsets were checked and {0,1,3,7} works (pair sums 0,1,2,3,4,6,7,8,10,14 distinct mod 19), so M(19) = 4 ≠ 5 = ⌈√19⌉.
- Scope of the refutation: the weaker asymptotic part "⌈√p⌉ + O(1)" is *not* contradicted (the deviation is 1 in these examples); what is refuted is the conjecture's exactness clause "O(1) = 0 for p ≡ 3 mod 4", which is the claim the conjecture highlights ("an exact B₂ result"). One counterexample at a prime ≡ 3 (mod 4) suffices; the conjecture as stated is FALSE.

Boundary table (exact recomputation, primes p ≡ 3 mod 4):

| p | 3 | 7 | 11 | 19 | 23 | 31 | 43 | 47 | 59 |
|---|---|---|----|----|----|----|----|----|----|
| M(p) | 2 | 3 | 3 | 4 | 5 | 6 | 6 | 6 | 7 |
| ⌈√p⌉ | 2 | 3 | 4 | 5 | 5 | 6 | 7 | 7 | 8 |
| exact? | yes | yes | **no** | **no** | yes | yes | **no** | **no** | **no** |

The "O(1) = 0" behavior holds only for p ∈ {3, 7, 23, 31} among these and fails erratically from p = 11 on — consistent with the Erdős–Turán upper bound √p + 1/2, which already forbids M(11) = 4 and M(19) = 5 (√11 + 1/2 ≈ 3.82, √19 + 1/2 ≈ 4.86).

## 3. Lean 4 certificate (zero axioms, zero `sorry`)

`lean4/Main.lean` encodes subsets of Z/11Z as 11-bit masks (bit i ⟺ i ∈ A), `isB2 11 n` ⇔ "all unordered pair sums a+b (a ≤ b) are distinct mod 11", and proves:

- `check11` — exhaustive kernel-reduced check over all 2^11 = 2048 masks that no mask with ≥ 4 elements is B₂ (`rfl`);
- `allRange_spec` — the bridge lemma turning the exhaustive Bool check into a ∀-statement (induction, core lemmas only);
- `no_ge4_B2_Z11` — every B₂ subset of Z/11Z has ≤ 3 elements: ∀ n < 2^11, isB2 11 n = true → maskPop 11 n ≤ 3;
- `witness_B2_Z11` — {0,1,3} (mask 11) is a 3-element B₂ set: pair sums 0,1,3,2,4,6 distinct mod 11;
- `disproof_1067` — 11 % 4 = 3 ∧ (∀ n < 2^11, isB2 11 n → maskPop 11 n ≤ 3) ∧ isB2 11 11 ∧ maskPop 11 11 = 3 ∧ ⌈√11⌉ = 4.

`lean4/Check.lean` runs `#print axioms` on every theorem; all report **"does not depend on any axioms"** (no `propext`, no `Classical.choice`, no `Quot.sound`, no `sorryAx`). No `native_decide` is used.

## 4. Reproduction

```bash
# independent recomputation (pure Python, exhaustive over all k-subsets):
python3 reproduce.py          # prints M(11)=3, M(19)=4 and the boundary table

# Lean certificate:
cd lean4 && lake build && lake env lean Check.lean
```

Expected Lean output: build succeeds; `Check.lean` prints 5 lines, each "does not depend on any axioms".
