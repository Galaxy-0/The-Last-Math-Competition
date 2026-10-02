#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002021."""
import sys
from itertools import product

def main():
    table = [pow(a, 5, 11) for a in range(11)]
    print("a^5 mod 11 for a=0..10:", table)
    assert sorted(set(table)) == [0, 1, 10]
    S5 = {sum(c) % 11 for c in product([0, 1, 10], repeat=5)}
    print("5-fold sums of {0,1,10} mod 11:", sorted(S5))
    assert S5 == set(range(11))
    S17 = {sum(c) % 11 for c in product([0, 1, 10], repeat=17)}
    assert S17 == set(range(11))
    print("17-fold sums also cover all residues: no mod-11 obstruction exists")
    print("ALL CHECKS PASS — the 'local density obstruction mod 11' clause is false")
    return 0

if __name__ == "__main__":
    sys.exit(main())
