#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001268.

(abc)^infinity has exactly the palindromic factors {epsilon, a, b, c}
(no factor of length >= 2 is a palindrome: the letters are 3-periodic,
so a palindromic factor of length L would need 3 | (L-1) and 3 | (L-3)).
Each of the 9 single-letter insertions (letters a/b/c into the gaps
after a/b/c) still contains abc-periodic factors of every length, and
every abc-periodic factor of length n >= 5 has only 4 < n+1 palindromic
factors -- hence is NOT rich.  No single insertion repairs (abc)^infinity.
Exit 0 iff all checks pass.
"""
import sys


def word_letter(k):
    return "abc"[k % 3]


def is_pal(w):
    return w == w[::-1]


def distinct_pal_factors(n):
    """All distinct palindromic factors of length <= n of the infinite
    word (abc)^infinity."""
    pals = {""}
    for start in range(0, n + 6):
        for length in range(1, n + 1):
            w = "".join(word_letter(start + j) for j in range(length))
            if is_pal(w):
                pals.add(w)
    return pals


def word_after_insert(n, letter, gap):
    """The first 2n letters of the word obtained by inserting `letter`
    into (abc)^infinity after position `gap` (mod the period)."""
    out = []
    pos = 0
    src = 0
    while len(out) < 2 * n:
        if pos == gap:
            out.append(letter)
        else:
            out.append(word_letter(src))
            src += 1
        pos += 1
    return "".join(out)


def pal_factors_upto(w, n):
    pals = {""}
    for i in range(len(w)):
        for length in range(1, min(n, len(w) - i) + 1):
            f = w[i:i + length]
            if is_pal(f):
                pals.add(f)
    return pals


def main():
    # 1. (abc)^infinity: palindromic factors of length <= 8 are exactly
    #    {epsilon, a, b, c} -- no palindromic factor of length >= 2
    pals = distinct_pal_factors(8)
    assert pals == {"", "a", "b", "c"}, pals
    print("(abc)^infinity palindromic factors: {epsilon, a, b, c} — OK")

    # 2. abc-periodic factors of length 5 are not rich: e.g. "abcab" has
    #    only 4 distinct palindromic factors < 6 = 5 + 1
    for w in ("abcab", "bcabc", "cabca"):
        pf = pal_factors_upto(w, 5)
        rich_count = 6
        assert len(pf) < rich_count, (w, pf)
        print(f"  factor {w}: {len(pf)} palindromic factors {sorted(pf)}"
              f" < 6 — not rich")

    # 3. each of the 9 single insertions leaves a non-rich factor of
    #    length 5 (indeed length <= 6 palindromes < n+1 for n = 5)
    for letter in "abc":
        for gap in range(3):
            w = word_after_insert(8, letter, gap)
            # the factor just past the insertion point is pure abc-periodic
            factor = w[gap + 1:gap + 6]
            assert factor in ("abcab", "bcabc", "cabca"), (letter, gap, factor)
            pf = pal_factors_upto(factor, 5)
            assert len(pf) == 4, (letter, gap, factor, pf)
            # also: distinct palindromic factors of length <= 6 of a
            # length-6 pure factor are < 7
            f6 = w[gap + 1:gap + 7]
            assert f6 in ("abcabc", "bcabca", "cabcab")
            pf6 = pal_factors_upto(f6, 6)
            assert len(pf6) < 7, (letter, gap, f6, pf6)
            print(f"  insert {letter!r} after gap {gap}: factor {factor} "
                  f"has 4 palindromes < 6 — non-rich")
    print("ALL 9 single insertions leave non-rich factors — repair impossible")
    print("ALL CHECKS PASS — (abc)^infinity admits no single-letter repair")
    return 0


if __name__ == "__main__":
    sys.exit(main())
