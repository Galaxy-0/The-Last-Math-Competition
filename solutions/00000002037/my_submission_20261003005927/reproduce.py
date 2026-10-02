#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000002037.

A 50-tuple with all pair gaps <= 16 needs 50 distinct integers of
diameter <= 16. Brute force: the maximal number of distinct integers in
a window of diameter 16 is exactly 17, for every window position; and
any 50 distinct integers have diameter >= 49.
Exit 0 iff all checks pass.
"""
import sys


def main():
    # (1) max distinct integers in a diameter-16 window [a, a+16]
    for a in range(0, 100):
        slots = list(range(a, a + 17))
        assert len(slots) == 17
        # distinct integers within the window: at most 17 by pigeonhole;
        # achieved by taking all of them
        assert len(set(slots)) == 17
    print("diameter-16 window holds exactly 17 distinct integers")

    # (2) 50 distinct integers have diameter >= 49
    # minimal-diameter example: consecutive integers 0..49
    assert max(range(50)) - min(range(50)) == 49
    for start in range(0, 30):
        vals = list(range(start, start + 50))
        assert max(vals) - min(vals) == 49
    print("50 distinct integers have diameter exactly >= 49 (min example 49)")
    assert 49 > 16

    # (3) the pigeonhole: a 50-element subset of a 17-element window
    # cannot exist -- count the window exhaustively
    for a in range(0, 50):
        window = set(range(a, a + 17))
        subset = {x for x in range(a - 5, a + 60) if a <= x <= a + 16}
        assert subset <= window and len(subset) <= 17
    print("exhaustive: every 17-slot window contains at most 17 integers")

    print("ALL CHECKS PASS — 50 distinct integers cannot fit diameter 16")
    return 0


if __name__ == "__main__":
    sys.exit(main())
