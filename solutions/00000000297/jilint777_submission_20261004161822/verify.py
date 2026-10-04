#!/usr/bin/env python3
"""Independent check for conjecture 00000000297 (Python 3 standard library only).

Method (different from the Lean proof, which is a short case analysis on an
infinite tiling): abstract a set of two Wang tiles {0, 1} to its compatibility
relations
    H = {(s, t) : east colour of s = west colour of t}   (t may sit right of s)
    V = {(s, t) : north colour of s = south colour of t} (t may sit above s).
For ALL 16 x 16 = 256 pairs of relations on {0, 1} (including relations that no
colouring realises) we check by brute force:
    (A) either the 3x3 square cannot be legally filled, or
    (B) there is a legal 2x2 torus pattern p, i.e. the tiling
        f(x, y) = p(x mod 2, y mod 2) is legal (periods (2,0) and (0,2)).
Since a tiling of the plane restricts to a legal 3x3 square, (A) means the set
does not tile, and (B) gives a doubly periodic tiling.  Hence no set of at most
two Wang tiles is aperiodic (one tile: take both tiles equal).
We also (C) run the same test on all pairs of concrete tiles with colours in
{0, 1, 2} (3^8 = 6561 ordered pairs), (D) check that 3x3 cannot be replaced by
2x2, and (E) cross-check the four explicit patterns used in the Lean proof.
"""
import itertools

PAIRS = [(0, 0), (0, 1), (1, 0), (1, 1)]


def all_relations():
    for bits in range(16):
        yield frozenset(p for i, p in enumerate(PAIRS) if bits >> i & 1)


def fillable(H, V, k):
    """Can a k x k square be legally filled?  Brute force over all 2^(k*k) fillings."""
    for cells in itertools.product((0, 1), repeat=k * k):
        g = lambda x, y: cells[x * k + y]
        if all((g(x, y), g(x + 1, y)) in H for x in range(k - 1) for y in range(k)) and \
           all((g(x, y), g(x, y + 1)) in V for x in range(k) for y in range(k - 1)):
            return True
    return False


def torus22(H, V):
    """Legal 2x2 torus patterns p (so f(x,y)=p[x%2][y%2] is a legal tiling)."""
    out = []
    for cells in itertools.product((0, 1), repeat=4):
        p = lambda x, y: cells[(x % 2) * 2 + (y % 2)]
        if all((p(x, y), p(x + 1, y)) in H and (p(x, y), p(x, y + 1)) in V
               for x in range(2) for y in range(2)):
            out.append(cells)
    return out


def tiling_ok(f, H, V, R=6):
    """Check a periodic pattern f on a window (enough for period-2 patterns)."""
    return all((f(x, y), f(x + 1, y)) in H and (f(x, y), f(x, y + 1)) in V
               for x in range(-R, R) for y in range(-R, R))


def main():
    ok = True
    n_obstructed = n_torus = 0
    for H in all_relations():
        for V in all_relations():
            f3 = fillable(H, V, 3)
            t = torus22(H, V)
            if f3 and not t:
                ok = False
                print("FAIL: 3x3 fillable but no 2x2 torus", sorted(H), sorted(V))
            if t:
                n_torus += 1
            else:
                n_obstructed += 1
    print(f"(A/B) 256 relation pairs: {n_torus} have a 2x2 torus, "
          f"{n_obstructed} have no legal 3x3 square")

    # (C) concrete tiles with colours in {0,1,2}
    tiles = list(itertools.product(range(3), repeat=4))  # (n, e, s, w)
    seen = set()
    count = 0
    for a in tiles:
        for b in tiles:
            T = (a, b)
            H = frozenset((s, t) for s in (0, 1) for t in (0, 1) if T[s][1] == T[t][3])
            V = frozenset((s, t) for s in (0, 1) for t in (0, 1) if T[s][0] == T[t][2])
            count += 1
            seen.add((H, V))
            if fillable(H, V, 3) and not torus22(H, V):
                ok = False
                print("FAIL (concrete):", T)
    print(f"(C) {count} ordered pairs of concrete tiles (colours 0..2): "
          f"{len(seen)} distinct relation pairs realised, all pass")

    # (D) 3x3 is needed: some pair has a legal 2x2 square but no 2x2 torus
    need3 = [(sorted(H), sorted(V)) for H in all_relations() for V in all_relations()
             if fillable(H, V, 2) and not torus22(H, V)]
    print(f"(D) relation pairs with a legal 2x2 square but no 2x2 torus: {len(need3)}"
          f" (e.g. H={need3[0][0]}, V={need3[0][1]})" if need3 else "(D) none")

    # (E) the case analysis of the Lean proof
    for H in all_relations():
        for V in all_relations():
            if not fillable(H, V, 3):
                continue
            AH = (0, 1) in H and (1, 0) in H
            AV = (0, 1) in V and (1, 0) in V
            # candidate patterns, as in the four cases of the Lean proof
            cand = []
            if AH and AV:
                cand.append(lambda x, y: (x + y) % 2)
            for t in (0, 1):
                if (t, t) in H and (t, t) in V:
                    cand.append(lambda x, y, t=t: t)
            if AV and (0, 0) in H and (1, 1) in H:
                cand.append(lambda x, y: y % 2)
            if AH and (0, 0) in V and (1, 1) in V:
                cand.append(lambda x, y: x % 2)
            if not any(tiling_ok(f, H, V) for f in cand):
                ok = False
                print("FAIL (E):", sorted(H), sorted(V))
    print("(E) every relation pair with a legal 3x3 square is tiled by one of the four "
          "patterns: constant, checkerboard, horizontal stripes, vertical stripes")

    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
    raise SystemExit(0 if ok else 1)


if __name__ == "__main__":
    main()
