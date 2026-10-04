"""Independent exhaustive check for conjecture 00000000035 (Python 3 stdlib only).

Brute force over ALL 2^17 colorings of [17] = {1..17}: each has a monochromatic
triple x < y, x + y = z <= 17, with x*y + 1 prime.  For [16], the coloring
0010101110110101 has none, so N = 17 is the least N for the x < y reading.
Also reports the least N when x = y is allowed.
"""


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def triples(N, strict=True):
    return [(x, y, x + y) for x in range(1, N + 1)
            for y in range(x + 1 if strict else x, N + 1)
            if x + y <= N and is_prime(x * y + 1)]


def forced(N, strict=True):
    """True iff every 2-coloring of [N] has a monochromatic triple."""
    T = triples(N, strict)
    masks = [(1 << (x - 1)) | (1 << (y - 1)) | (1 << (z - 1)) for x, y, z in T]
    full = (1 << N) - 1
    for col in range(1 << N):
        if not any((col & m) == m or (col & m) == 0 for m in masks):
            return False, format(col, "0%db" % N)[::-1]
    return True, None


def main():
    T17 = triples(17)
    print("triples with x<y in [17]:", len(T17), T17)
    assert len(T17) == 31
    ok, _ = forced(17)
    assert ok
    print("all 2^17 colorings of [17] contain a monochromatic triple (x<y)")
    good = "0010101110110101"
    T16 = triples(16)
    assert not any(good[x - 1] == good[y - 1] == good[z - 1] for x, y, z in T16)
    print("coloring", good, "of [16] avoids all", len(T16), "triples (x<y)")
    ok16, _ = forced(16)
    assert not ok16
    least_loose = next(N for N in range(1, 18) if forced(N, strict=False)[0])
    print("least N when x = y is also allowed:", least_loose)
    assert least_loose == 7
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
