#!/usr/bin/env python3
"""
Independent reproduction for TLMC conjecture 00000002913 (REFUTED).

Conjecture: a degree-d polynomial map on F_q is injective when
q > d^2.

Refutation: d = 2, q = 5 > 4: x^2 on F_5 has 4^2 = 1^2 = 1 (mod 5)
-- not injective; image {0,1,4} of size 3 < 5.  Full enumeration:
NO quadratic map on F_5 or F_7 is injective (all images have size
<= (q+1)/2), while q > d^2 holds.
"""

# ---------- gate 1: the certified instance ----------
assert 5 > 2 * 2
sq = lambda x: (x * x) % 5
assert sq(4) == sq(1) == 1 and 4 != 1
img = {sq(x) for x in range(5)}
assert img == {0, 1, 4} and len(img) == 3 < 5
print("F_5, d = 2, q = 5 > 4: x^2 has 4^2 = 1^2 = 1 (collision); image {0,1,4}, size 3 — OK")

# ---------- gate 2: NO quadratic map is injective on F_5 or F_7 ----------
for q in (5, 7):
    assert q > 4  # the claimed threshold holds for d = 2
    non_inj = 0
    total = 0
    max_img = 0
    for a in range(q):
        for b in range(q):
            for c in range(q):
                if a == 0:
                    continue  # degree must be exactly 2
                total += 1
                img = {(a * x * x + b * x + c) % q for x in range(q)}
                max_img = max(max_img, len(img))
                if len(img) < q:
                    non_inj += 1
    assert non_inj == total, (q, non_inj, total)
    print(f"F_{q}: all {total} quadratic maps are non-injective "
          f"(max image size {max_img} <= (q+1)/2 = {(q+1)//2}); threshold q > d^2 = 4 holds — REFUTED")

# ---------- gate 3: plane version (x,y) -> (x^2, y^2) on F_5^2 ----------
img = {(sq(x), sq(y)) for x in range(5) for y in range(5)}
assert len(img) == 9 < 25 and ((1, 0) == (sq(1), sq(0))) and ((1, 0) == (sq(4), sq(0)))
print(f"plane map (x,y) -> (x^2, y^2) on F_5^2: image size {len(img)} < 25; "
      "(1,0) and (4,0) collide — OK")

print("\nALL CHECKS PASSED: conjecture 00000002913 REFUTED "
      "(q > d^2 with collisions: x^2 on F_5; no injective quadratics on F_5/F_7)")
