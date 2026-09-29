#!/usr/bin/env python3
"""
Standalone reproduction of the disproof of TLMC conjecture 00000000340.

Conjecture: for every algebraic irrational alpha,
  liminf_N G_N(alpha) = 1 and limsup_N G_N(alpha) = infinity,
where G_N(alpha) = (prod_{j<=N} a_j)^{1/N} and a_j are the continued-fraction
partial quotients of alpha.

Counterexample: alpha = sqrt(2) = [1; 2, 2, 2, ...].
Everything below is computed in exact integer arithmetic:
  * the CF recurrence for sqrt(D) uses only integers (m, d, a);
  * G_N >= r  <=>  199^N <= 2^{N-1} * 100^N  (no floating point).
"""
import sys

def cf_sqrt2(n):
    """First n+1 partial quotients of sqrt(2) by the exact integer CF algorithm."""
    D = 2
    m, d, a0 = 0, 1, 1  # floor(sqrt(2)) = 1
    terms = [a0]
    for _ in range(n):
        m = d * a0 - m
        d = (D - m * m) // d
        a0 = (1 + m) // d      # floor((sqrt(D)+m)/d) with floor(sqrt(D)) = 1
        terms.append(a0)
    return terms

def prod_first_N(terms, N):
    p = 1
    for t in terms[:N]:
        p *= t
    return p

def main():
    ok = True
    def check(name, cond):
        nonlocal ok
        print(f"[{'PASS' if cond else 'FAIL'}] {name}")
        ok = ok and cond

    terms = cf_sqrt2(2000)
    check("a_1 = 1", terms[0] == 1)
    check("all partial quotients a_j (j>=2) equal 2", set(terms[1:]) == {2})

    # Exact identity: prod_{j<=N} a_j = 2^(N-1)
    identity = all(prod_first_N(terms, N) == 2 ** (N - 1) for N in range(1, 2001))
    check("prod_{j<=N} a_j = 2^(N-1) for all 1 <= N <= 2000", identity)

    # Geometric means (exact integer powers, float only for display)
    for N in (10, 100, 1000):
        G = prod_first_N(terms, N) ** (1.0 / N)
        target = 2 ** ((N - 1) / N)
        print(f"  G_{N} = {G:.9f}   (2^((N-1)/N) = {target:.9f})")
        check(f"G_{N} matches 2^((N-1)/N)", abs(G - target) < 1e-9)

    # G_N <= 2 for all N (limsup <= 2 < infinity): prod = 2^(N-1) <= 2^N
    check("G_N <= 2 for all 1 <= N <= 2000  (limsup = 2, not infinity)",
          all(2 ** (N - 1) <= 2 ** N for N in range(1, 2001)))

    # G_N >= sqrt(2) for all N >= 2 (liminf >= sqrt(2) > 1):
    #   G_N^2 >= 2  <=>  (2^(N-1))^2 >= 2^N
    check("G_N^2 >= 2 for all 2 <= N <= 2000  (liminf >= sqrt(2) > 1)",
          all(2 ** (2 * N - 2) >= 2 ** N for N in range(2, 2001)))

    # Sharp eventual bound: G_N >= 1.99  <=>  199^N <= 2^(N-1) * 100^N
    fails_at_138 = not (199 ** 138 <= 2 ** 137 * 100 ** 138)
    holds_at_139 = 199 ** 139 <= 2 ** 138 * 100 ** 139
    check("G_138 < 1.99 (threshold sharpness)", fails_at_138)
    check("G_N >= 1.99 for N = 139", holds_at_139)
    check("G_N >= 1.99 for all 139 <= N <= 1000",
          all(199 ** N <= 2 ** (N - 1) * 100 ** N for N in range(139, 1001)))

    # Concrete numeric certificate at N = 1000 (matches the Lean `decide`):
    check("199^1000 <= 2^999 * 100^1000  (G_1000 >= 1.99)",
          199 ** 1000 <= 2 ** 999 * 100 ** 1000)
    check("2^999 * 100^1000 <= 201^1000  (G_1000 <= 2.01)",
          2 ** 999 * 100 ** 1000 <= 201 ** 1000)

    print()
    if ok:
        print("ALL CHECKS PASS: sqrt(2) is an algebraic irrational counterexample;")
        print("liminf G_N = limsup G_N = 2, contradicting both claims (1 and infinity).")
        return 0
    print("SOME CHECK FAILED")
    return 1

if __name__ == "__main__":
    sys.exit(main())
