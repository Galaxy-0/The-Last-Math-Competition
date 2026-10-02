#!/usr/bin/env python3
"""
Independent recomputation for the disproof of TLMC conjecture 00000001262.

Conjecture (as stated):
    The abelian complexity of balanced periodic words is eventually constant,
    equal to the alphabet size (the abelian constant class).

Counterexample: the word w = (aab)^infinity over {a, b} (alphabet size 2).
It is periodic (period 3) and balanced. Its abelian complexity is
    omega(3k) = 1,   omega(3k+1) = 2,   omega(3k+2) = 2   for all k >= 0,
so omega(n) = 1 at n = 3, 6, 9, ... and hence omega is NOT eventually 2.

This script
  1. enumerates ALL windows of w up to a finite length bound and recomputes
     omega(n) exactly (via Parikh vectors, not just a-counts),
  2. checks the pattern omega(3k)=1, omega(3k+1)=omega(3k+2)=2 for n <= N_MAX,
  3. verifies that w is balanced (per-length a-counts differ by at most 1),
  4. verifies that w is periodic with period 3,
  5. verifies the limit negation directly: for every N in 0..N_MAX there is
     an n >= N with omega(n) != 2 (namely the next multiple of 3).

Pure standard library; no external dependencies; no absolute paths.
Run:  python3 reproduce.py
"""

N_MAX = 60          # largest window length checked
PERIODS = 400       # periods of the word materialised (>= N_MAX + 3 needed)

WORD = "aab" * PERIODS
assert len(WORD) >= N_MAX + 3


def window_counts(n):
    """All (a_count, b_count) Parikh vectors of length-n windows, and all
    a-counts, over every window start (full enumeration, no residue shortcut)."""
    parikh = set()
    acounts = set()
    for s in range(len(WORD) - n + 1):
        win = WORD[s:s + n]
        a = win.count("a")
        parikh.add((a, n - a))
        acounts.add(a)
    return parikh, acounts


def omega(n):
    return len(window_counts(n)[0])


def main():
    print(f"word = (aab)^{PERIODS}  (first 12 letters: {WORD[:12]})")
    print(f"checking window lengths 1..{N_MAX}\n")

    # 1. omega table and pattern check
    table = {n: omega(n) for n in range(1, N_MAX + 1)}
    print("omega table:", " ".join(f"{n}:{table[n]}" for n in sorted(table)))

    ok_pattern = True
    for n, val in table.items():
        expected = 1 if n % 3 == 0 else 2
        if val != expected:
            ok_pattern = False
            print(f"  MISMATCH at n={n}: omega={val}, expected {expected}")
    print(f"pattern check omega(3k)=1, omega(3k+1)=omega(3k+2)=2 : "
          f"{'PASS' if ok_pattern else 'FAIL'}")

    # 2. balance: per-length a-counts differ by at most 1
    ok_balanced = True
    for n in range(1, N_MAX + 1):
        acounts = window_counts(n)[1]
        if max(acounts) - min(acounts) > 1:
            ok_balanced = False
            print(f"  NOT BALANCED at n={n}: a-counts {sorted(acounts)}")
    print(f"balance of (aab)^inf (all windows, lengths 1..{N_MAX})   : "
          f"{'PASS' if ok_balanced else 'FAIL'}")

    # 3. periodicity with period 3
    ok_periodic = all(WORD[i + 3] == WORD[i] for i in range(len(WORD) - 3))
    print(f"periodicity with period 3                               : "
          f"{'PASS' if ok_periodic else 'FAIL'}")

    # 4. limit negation: for every N there is n >= N with omega(n) != 2
    ok_limit = True
    for N in range(0, N_MAX):
        n = 3 * (N // 3 + 1)          # smallest multiple of 3 with n > N
        witness_ok = (n >= N) and (omega(n) != 2)
        if not witness_ok:
            ok_limit = False
            print(f"  LIMIT FAILURE at N={N}: witness n={n}, omega={omega(n)}")
    print(f"limit negation (for all N < {N_MAX}: exists n >= N, omega(n) != 2): "
          f"{'PASS' if ok_limit else 'FAIL'}")

    print()
    all_ok = ok_pattern and ok_balanced and ok_periodic and ok_limit
    print("RESULT:", "CONJECTURE FALSE — (aab)^inf is a balanced periodic word "
          "whose abelian complexity hits 1 at every multiple of 3"
          if all_ok else "SOMETHING FAILED")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
