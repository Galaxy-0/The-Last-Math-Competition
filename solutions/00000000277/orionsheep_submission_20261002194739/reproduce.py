#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000000277."""
import sys

def main():
    vs = [(x, y) for x in range(-4, 5) for y in range(-4, 5)
          if x * x + y * y == 5]
    print("|k|^2 = 5 lattice vectors:", vs)
    assert len(vs) == 8
    assert 8 > 6
    # unboundedness indication: r_2(5^j) = 4(j+1)
    for j in (1, 2, 3, 4):
        m = 5 ** j
        cnt = sum(1 for x in range(-int(m**0.5) - 2, int(m**0.5) + 3)
                  for y in range(-int(m**0.5) - 2, int(m**0.5) + 3)
                  if x * x + y * y == m)
        print(f"r_2(5^{j}) = r_2({m}) = {cnt} (expected {4*(j+1)})")
        assert cnt == 4 * (j + 1)
    print("square torus eigenvalue multiplicity 8 > 6; multiplicities unbounded")
    print("ALL CHECKS PASS — conjecture refuted")
    return 0

if __name__ == "__main__":
    sys.exit(main())
