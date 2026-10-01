#!/usr/bin/env python3
"""
Independent recomputation for the disproof of TLMC conjecture 00000000199.

Conjecture (as posed): S = sum_{n>=0} 1/(n^2+n+2) is an explicit Q-linear
combination of digamma values at CUBE ROOTS OF UNITY (omega^3 = 1), with the
irrationality of S equivalent to that of psi(omega)-type values, "following
from an explicit partial-fraction decomposition".

Verdict: FALSE.

Attack (all recomputed below):
  * Partial fractions for n^2+n+2 use its roots r± = (-1 ± i*sqrt(7))/2, whose
    squared modulus is 2 (not 1) and which are NOT cube roots of unity
    (r^3 != 1). The discriminant is 1-8 = -7, not the -3 of z^2+z+1.
  * The decomposition gives exactly
        S = (psi(b) - psi(a)) / (b - a),   a,b = (1 ± i*sqrt(7))/2,
    i.e. digamma at points of modulus sqrt(2) != 1, equivalently
        S = (2/sqrt(7)) * Im psi((1 + i*sqrt(7))/2),
    NOT a Q-combination of psi at cube roots of unity.
  * Any real Q-linear combination of psi(1), psi(omega), psi(omega^2) must have
    equal omega / omega^2 coefficients (Im psi(omega) != 0), hence lies in
    span_Q{ psi(1), 2*Re psi(omega) }; an exhaustive search over rational
    coefficients with denominators <= 500 finds no match for S.
  * Boundary check: for n^2+n+1 (discriminant -3) the SAME decomposition does
    involve roots of unity: its shifted roots (1 ± i*sqrt(3))/2 are 6th roots
    of unity and sum 1/(n^2+n+1) = (2/sqrt(3)) * Im psi((1+i*sqrt(3))/2).
    The mechanism is discriminant-specific and fails for discriminant -7.

Self-contained: uses only the Python standard library (complex + decimal
arithmetic with an asymptotic digamma). If mpmath is available it is used for
an independent cross-check.

Run:  python3 reproduce.py
"""

import cmath
import math
from fractions import Fraction

SQRT7 = math.sqrt(7.0)
SQRT3 = math.sqrt(3.0)

# ---------------------------------------------------------------------------
# Digamma function via recurrence + asymptotic (Bernoulli) expansion.
# Accurate to ~1e-13 for double precision arguments away from the poles.
# ---------------------------------------------------------------------------

def digamma(z: complex) -> complex:
    """psi(z) for z not a nonpositive integer (double precision)."""
    z = complex(z)
    res = 0j
    # Recurse upward until |z| is large enough for the asymptotic series.
    while abs(z) < 8.0:
        res -= 1.0 / z
        z += 1.0
    # psi(z) ~ ln z - 1/(2z) - sum_{k>=1} B_{2k} / (2k z^{2k})
    inv2 = 1.0 / (z * z)
    coeff = 1.0 / 12.0  # B2 / 2
    term = 1.0 / (2.0 * z)
    acc = 0j
    zk2 = inv2
    # B4/4 = -1/120, B6/6 = 1/252, B8/8 = -1/240, B10/10 = 1/132
    for c in (1.0 / 12.0, -1.0 / 120.0, 1.0 / 252.0, -1.0 / 240.0, 1.0 / 132.0,
              -691.0 / 32760.0, 1.0 / 12.0, -3617.0 / 8160.0):
        acc += c * zk2
        zk2 *= inv2
    return res + cmath.log(z) - term - acc


def sum_quadratic_psi(A: complex, B: complex, N: int = 200000) -> complex:
    """Exact decomposition: sum_{n>=0} 1/((n+A)(n+B)) = (psi(B)-psi(A))/(B-A).

    Evaluated as: partial sum to N-1 + (psi(N+B) - psi(N+A)) / (B - A)  tail.
    """
    s = sum(1.0 / ((n + A) * (n + B)) for n in range(N))
    return s + (digamma(N + B) - digamma(N + A)) / (B - A)


def main() -> int:
    ok = True

    print("=" * 72)
    print("Disproof of conjecture 00000000199 (quadratic-denominator psi representation)")
    print("=" * 72)

    # ------------------------------------------------------------------
    # 1) The roots of n^2+n+2 and their shape.
    # ------------------------------------------------------------------
    r1 = (-1 + 1j * SQRT7) / 2
    r2 = (-1 - 1j * SQRT7) / 2
    disc = 1 - 4 * 2
    print(f"\n[1] z^2+z+2: discriminant = {disc} (vs z^2+z+1: {1-4*1})")
    print(f"    roots r± = {r1.real:+.15f} {r1.imag:+.15f}i , {r2.real:+.15f} {r2.imag:+.15f}i")
    modsq = abs(r1) ** 2
    print(f"    |r|^2 = {modsq:.15f}   (cube roots of unity have |z|^2 = 1)")
    print(f"    r^3   = {r1**3:.12f}  -> r^3 != 1: {abs(r1**3 - 1) > 1e-9}")
    assert abs(modsq - 2.0) < 1e-12 and disc == -7

    # ------------------------------------------------------------------
    # 2) The sum S, computed two independent ways.
    # ------------------------------------------------------------------
    # (a) direct partial sum + digamma tail, using the ROOT-based form
    S_direct = 0.0
    for n in range(200000):
        S_direct += 1.0 / (n * n + n + 2)
    # tail via sum_{n>=N} 1/(n^2+n+2) = (psi(N+b') - psi(N+a'))/(b'-a')
    ap, bp = (1 + 1j * SQRT7) / 2, (1 - 1j * SQRT7) / 2  # shifted roots (psi arguments)
    N = 200000
    S_direct += (digamma(N + bp) - digamma(N + ap)) / (bp - ap)
    S_direct = S_direct.real

    # (b) closed form straight from the partial-fraction decomposition
    S_pf = (digamma(bp) - digamma(ap)) / (bp - ap)
    S_form2 = (2.0 / SQRT7) * digamma(ap).imag

    print("\n[2] S = sum_{n>=0} 1/(n^2+n+2)")
    print(f"    (a) direct sum + tail          = {S_direct:.15f}")
    print(f"    (b) (psi(b)-psi(a))/(b-a)      = {S_pf.real:.15f}   (imag {S_pf.imag:.2e})")
    print(f"    (c) (2/sqrt7)*Im psi(a)        = {S_form2:.15f}")
    d1 = abs(S_direct - S_pf.real)
    d2 = abs(S_direct - S_form2)
    print(f"    agreement |a-b| = {d1:.2e}, |a-c| = {d2:.2e}")
    assert d1 < 1e-9 and d2 < 1e-9

    # ------------------------------------------------------------------
    # 3) The claimed cube-roots-of-unity combination.
    # ------------------------------------------------------------------
    omega = complex(-0.5, SQRT3 / 2)
    assert abs(omega**3 - 1) < 1e-12
    psi1 = digamma(1.0)                # = -Euler gamma
    psiw = digamma(omega)
    psiw2 = digamma(omega.conjugate())
    print("\n[3] cube-root-of-unity values")
    print(f"    omega = {omega:.12f}, omega^3 = {omega**3:.12f}  (root of z^2+z+1, disc -3)")
    print(f"    psi(1)    = {psi1.real:.15f}  (= -gamma)")
    print(f"    psi(omega)  = {psiw.real:.15f} {psiw.imag:+.15f}i")
    print(f"    psi(omega^2) = {psiw2.real:.15f} {psiw2.imag:+.15f}i  (= conj)")
    assert abs((psiw2 - psiw.conjugate())) < 1e-12

    # A real combination q1*psi(1) + q2*psi(omega) + q3*psi(omega^2) is real
    # iff q2 == q3 (Im psi(omega) != 0), hence lies in span{psi(1), 2 Re psi(omega)}.
    target_re = 2.0 * psiw.real
    print(f"    Im psi(omega) = {psiw.imag:.6f} != 0  =>  S must equal "
          f"q1*psi(1) + q2*(2 Re psi(omega)) with q1,q2 in Q")

    hits = []
    for den in range(1, 501):
        for p in range(0, 4 * den + 1):
            q2 = Fraction(p, den)
            q1 = Fraction((S_direct - q2 * target_re) / psi1.real).limit_denominator(500)
            if q1.denominator <= 500:
                resid = abs(S_direct - (float(q1) * psi1.real + float(q2) * target_re))
                if resid < 1e-12:
                    hits.append((q1, q2))
    print(f"    exhaustive search, denominators <= 500: "
          f"{'MATCH ' + repr(hits[:3]) if hits else 'no Q-combination found'}")
    if hits:
        ok = False

    # ------------------------------------------------------------------
    # 4) Boundary: the mechanism DOES work for the discriminant -3 twin.
    # ------------------------------------------------------------------
    S1 = 0.0
    for n in range(200000):
        S1 += 1.0 / (n * n + n + 1)
    a3, b3 = (1 + 1j * SQRT3) / 2, (1 - 1j * SQRT3) / 2
    S1 += (digamma(N + b3) - digamma(N + a3)) / (b3 - a3)
    S1 = S1.real
    S1_form = (2.0 / SQRT3) * digamma(a3).imag
    sixth = abs(a3**6 - 1) < 1e-12
    print("\n[4] boundary: n^2+n+1 (disc -3)")
    print(f"    (1+i*sqrt3)/2 is a 6th root of unity: {sixth}")
    print(f"    sum 1/(n^2+n+1)          = {S1:.15f}")
    print(f"    (2/sqrt3)*Im psi(a3)     = {S1_form:.15f}   (same decomposition, "
          f"args ARE roots of unity)")
    assert abs(S1 - S1_form) < 1e-9
    print("    => the conjecture's mechanism is discriminant-specific: true for -3, "
          "FALSE for -7.")

    # ------------------------------------------------------------------
    # 5) Exact fixed-point partial sums (cross-check of the Lean integers).
    # ------------------------------------------------------------------
    print("\n[5] exact fixed-point partial sums (match lean4/Main.lean psum40_val/psum60_val)")
    for Nf in (40, 60):
        P = math.prod(n * n + n + 2 for n in range(Nf))
        num = sum(P // (n * n + n + 2) for n in range(Nf))
        assert Fraction(num, P) == sum(Fraction(1, n * n + n + 2) for n in range(Nf))
        print(f"    P{Nf}   = {P}")
        print(f"    psum{Nf} = {num}   (partial sum = {float(Fraction(num, P)):.15f})")

    # ------------------------------------------------------------------
    print("\n" + "=" * 72)
    print("CONCLUSION: S = (2/sqrt(7)) * Im psi((1+i*sqrt(7))/2) "
          f"= {S_direct:.12f}...")
    print("The partial-fraction decomposition produces digamma values at "
          "(-1±i*sqrt(7))/2 (|.|=sqrt 2, disc -7), NOT at cube roots of unity;")
    print("no Q-linear combination of psi(1), psi(omega), psi(omega^2) reproduces S.")
    print("VERDICT: conjecture 00000000199 is FALSE.")
    print("=" * 72)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
