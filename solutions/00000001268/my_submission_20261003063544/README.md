# Disproof of conjecture `00000001268`

**Verdict: FALSE — the periodic word (abc)^∞ admits NO single-letter
repair to a rich word: every palindromic factor of the abc-periodic
word is a single letter (kernel-certified, all offsets and lengths),
so every abc-periodic factor of length 5 has only 4 distinct
palindromic factors {ε, a, b, c} while richness for length 5 requires
5 + 1 = 6 — and a single insertion at ANY position leaves abc-periodic
factors of every length in place.**

## The conjecture (verbatim from `conjectures/00000001268.md`)

> Definition: The palindromic defect is the count of defect letters of
> rich-in-palindromes words. Conjecture: Every infinite word can be
> repaired to a rich word by at most one letter insertion; and the
> minimality of the repair position is uniquely given by the defect
> center. (defect repair by a single insertion)

## The refutation

A finite word of length n is rich when it has n+1 distinct palindromic
factors (including ε); an infinite word is rich when all its factors
are rich. The periodic word (abc)^∞ is not rich, and no single
insertion repairs it:

1. **No long palindromic factors (kernel-certified, all offsets).**
   The letter at position k is 3-periodic. A palindromic factor of
   length L ≥ 2 at offset p would repeat letters at distances L−1 and
   (for L ≥ 3) L−2 — the first/last and second/second-to-last pairs.
   Writing L−1 = 3k + r (r ∈ {0,1,2}) and reducing each letter
   equation by 3k, the first pair forces a distance-1 or distance-2
   repetition when r = 1 or 2; when r = 0 the second pair forces one
   (distance (L−1)−1 ≡ 2 mod 3). All three cases contradict the
   3-periodicity lemma "no letter repetition at distance 1 or 2"
   (kernel-certified by a 3-window induction with definitional step).
   Hence every nonempty palindromic factor is a single letter: the
   abc-periodic word has exactly 4 distinct palindromic factors
   {ε, a, b, c}.

2. **Insertions leave abc-periodic factors in place.** After inserting
   one letter at ANY position p, the letters at positions p+1+d of the
   repaired word are still the abc-periodic letters at p+d
   (kernel-certified), so the repaired word contains purely
   abc-periodic factors of every length — e.g. length 5 (one of
   "abcab", "bcabc", "cabca").

3. **Such factors are not rich.** An abc-periodic length-5 factor has
   at most 4 distinct palindromic factors (step 1), but richness for
   length 5 requires 6: 4 < 6.

Therefore for every insertion position and every inserted letter, the
repaired word still contains a non-rich factor: no single-letter
insertion repairs (abc)^∞. With the repair itself impossible, the
conjecture's second clause (defect-center uniqueness of the repair
position) is vacuous.

## Verification

* `reproduce.py` — brute force: (i) the palindromic factors of
  (abc)^∞ of length ≤ 8 are exactly {ε, a, b, c}; (ii) each of the 9
  single-letter insertions (a/b/c after each of the 3 gap positions)
  still contains a purely abc-periodic length-5 factor with exactly 4
  palindromic factors < 6; (iii) the abc-periodic length-5/6 words
  "abcab"/"bcabc"/"cabca"/"abcabc"/... are all non-rich.
* Lean 4 (core, v4.33.1), `lean4/` — the 3-periodicity machinery
  (Q3/base1/base2), the 3-step reduction (let3_shift, reduceK, T3cases),
  the universal no-palindrome-of-length-≥2 theorem (no_pal), the
  post-insertion window facts (ins_window), and 4 < 6. All 9 audited
  theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the combinatorial core: no abc-periodic factor of
length ≥ 2 is a palindrome (universally over offsets and lengths), the
post-insertion window letters, and the numeric comparison. The
identification "rich word of length n ⟺ n+1 distinct palindromic
factors" (Droubay–Justin–Pirillo) is classical and cited in prose; the
enumeration of the 9 insertion instances is carried by the script.
