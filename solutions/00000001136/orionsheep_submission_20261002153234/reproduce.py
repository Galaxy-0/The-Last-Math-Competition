#!/usr/bin/env python3
"""Reproduce the numerical core of the disproof of TLMC conjecture 00000001136.

Conjecture 00000001136: BS(s1,...,sk) is Gorenstein if and only if every letter
of the word s1...sk occurs equally often.

Counterexample: w = s1 s2 s1 = w0 in S3 is a REDUCED word, but its letter counts
are (2, 1) -- unequal.  Yet every Bott-Samelson variety BS(s1,...,sk) built from a
reduced word is an iterated P1-bundle (Demazure 1974), hence smooth projective,
and smoothness implies Gorenstein (the local rings are regular, and regular local
rings are Gorenstein).  So BS(w0) is Gorenstein although the letters do NOT occur
equally often: the "only if" direction of the conjecture fails.

Run:  python3 reproduce.py
"""
from collections import Counter
from itertools import product

# S3 as one-line permutations of {1,2,3}: tuple p means x -> p[x-1].
IDENT = (1, 2, 3)
W0 = (3, 2, 1)  # longest element


def comp(f, g):
    """Composition f o g (apply g first) in one-line notation."""
    return tuple(f[g[x - 1] - 1] for x in (1, 2, 3))


def coxeter_length(p):
    """Coxeter length = number of inversions."""
    return sum(1 for i in range(3) for j in range(i + 1, 3) if p[i] > p[j])


S1 = (2, 1, 3)  # simple reflection s1: swaps 1,2
S2 = (1, 3, 2)  # simple reflection s2: swaps 2,3
LETTERS = {"s1": S1, "s2": S2}


def evaluate(word):
    """Evaluate a word (tuple of letters), leftmost letter applied first."""
    p = IDENT
    for L in word:
        p = comp(LETTERS[L], p)
    return p


def main():
    print("=== Disproof of conjecture 00000001136 (counterexample: w = s1 s2 s1) ===\n")

    # 1) The word s1 s2 s1 evaluates to the longest element w0 and is reduced.
    word = ("s1", "s2", "s1")
    assert evaluate(word) == W0, evaluate(word)
    print(f"1) {word} evaluates to {evaluate(word)} = w0 in S3")
    assert len(word) == coxeter_length(W0) == 3
    print(f"   len(word) = {len(word)} = Coxeter length(w0) = {coxeter_length(W0)}"
          "  -> REDUCED expression")

    # 2) Letter counts are unequal.
    counts = Counter(word)
    print(f"2) letter counts: s1 occurs {counts['s1']} times, s2 occurs "
          f"{counts['s2']} times -> {counts['s1']} != {counts['s2']}  (UNEQUAL)")

    # 3) Exhaustive check: EVERY reduced expression of w0 in S3 has unequal counts.
    reduced_w0 = [t for t in product(("s1", "s2"), repeat=3) if evaluate(t) == W0]
    print(f"3) all reduced expressions of w0: {reduced_w0}")
    for t in reduced_w0:
        c = Counter(t)
        assert c["s1"] != c["s2"], f"unexpected equal counts for {t}"
        print(f"   {t}: counts (s1={c['s1']}, s2={c['s2']}) -- unequal, "
              "no rewording of w0 fixes the conjecture")

    # 4) Geometric input (a theorem, not a computation): BS(s1,...,sk) for a reduced
    #    word is an iterated P1-bundle (Demazure, Ann. Sci. ENS 7 (1974)), hence
    #    smooth projective; smooth => regular local rings => Gorenstein.
    #    Therefore BS(w0) IS Gorenstein while its word has unequal letter counts.
    print("4) BS(s1,s2,s1) is an iterated P1-bundle, hence smooth projective, hence "
          "GORENSTEIN.")
    print("   Gorenstein: True, letters equally often: False -- the 'iff' FAILS.\n")
    print("Conjecture 00000001136 is DISPROVED.")
    print("All checks passed.")


if __name__ == "__main__":
    main()
