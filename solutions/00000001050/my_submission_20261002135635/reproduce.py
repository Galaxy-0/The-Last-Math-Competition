#!/usr/bin/env python3
"""Independent recomputation for the disproof of TLMC conjecture 00000001050.

Conjecture (verbatim): "For any composition of a permutation polynomial f with a
linearized polynomial, the image under the relative trace F_{q^2}/F_q is everything
if and only if the kernel is trivial."

Counterexample: q = 2, F4 = F2(omega) with omega^2 = omega + 1.
f = id (permutation polynomial), L(x) = omega*(x + x^2) (linearized).
ker L = {0, 1} (nontrivial), but Tr_{F4/F2}(L(F4)) = {0, 1} = F2 (surjective).

No third-party dependencies. Run: python3 reproduce.py
"""

# Element (a, b) represents a + b*omega in F2[omega]/(omega^2 + omega + 1).
def f4_add(u, v):
    return ((u[0] + v[0]) % 2, (u[1] + v[1]) % 2)

def f4_mul(u, v):
    a, b = u
    c, d = v
    # (a + b w)(c + d w) = ac + (ad + bc) w + bd w^2,  w^2 = 1 + w
    return ((a * c + b * d) % 2, (a * d + b * c + b * d) % 2)

ZERO = (0, 0)   # 0
ONE = (1, 0)    # 1
OMEGA = (0, 1)  # w
OMEGA2 = (1, 1) # w^2 = 1 + w
F4 = [ZERO, ONE, OMEGA, OMEGA2]

def f4_sq(u):
    return f4_mul(u, u)

def rel_trace(u):
    """Relative trace F4/F2: Tr(z) = z + z^2 (q = 2)."""
    return f4_add(u, f4_sq(u))

def L(x):
    """Linearized polynomial L(x) = omega*x + omega*x^2 = omega*(x + x^2)."""
    return f4_mul(OMEGA, f4_add(x, f4_sq(x)))

# --- sanity: field tables on all 16 pairs (commutativity + zero/one identities)
for a in F4:
    for b in F4:
        assert f4_add(a, b) == f4_add(b, a)
        assert f4_mul(a, b) == f4_mul(b, a)
        assert f4_mul(a, ONE) == a and f4_mul(a, ZERO) == ZERO
    assert f4_add(a, ZERO) == a
for a in F4:
    assert f4_mul(a, a) == f4_sq(a)

# --- the attack
kernel = [x for x in F4 if L(x) == ZERO]
trace_image = sorted(set(rel_trace(L(x)) for x in F4))

print("x          : ", F4)
print("ker L      : ", kernel)
print("L(F4)      : ", sorted(set(L(x) for x in F4)))
print("Tr(L(F4))  : ", trace_image)

assert kernel == [ZERO, ONE], "ker L must be {0, 1} (nontrivial)"
assert trace_image == [ZERO, ONE], "Tr(L(F4)) must be {0, 1} = F2 (surjective)"
assert ZERO in trace_image and ONE in trace_image

print()
print("RESULT: kernel nontrivial ({0,1}) yet Tr_{F4/F2}(L(F4)) = {0,1} = F2 surjective.")
print("RESULT: the biconditional 'trace-surjective iff kernel trivial' is FALSE.")
print("PASS: conjecture 00000001050 disproven at q = 2 with f = id, L(x) = w(x + x^2).")
