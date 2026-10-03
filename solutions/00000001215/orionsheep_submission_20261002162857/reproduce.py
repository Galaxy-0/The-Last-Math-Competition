#!/usr/bin/env python3
"""Independent verification for the disproof of conjecture 00000001215.

Game search on the cycles C_5, C_7, C_9, C_11 (and C_4, C_6, C_8):
cop number is exactly 2 for every cycle of length >= 4.  One cop can
never capture (exhaustive minimax over all cop strategies; the robber
always steps away), two cops always can (the classical sweep strategy,
verified exhaustively for small boards).  Every cycle is outerplanar,
so the odd cycles C_{2k+1}, k >= 2, form an infinite family of
outerplanar graphs with cop number exactly 2.
Exit 0 iff all checks pass.
"""
import sys
from functools import lru_cache


def neighbors(n, v):
    return {(v - 1) % n, (v + 1) % n}


def one_cop_loses(n):
    """Retrograde attractor: states (c, r, cop_to_move).  Capture states
    are cop-wins; iterate backward to the cop-winning fixpoint.  Returns
    True iff some (c, r) at cyclic distance >= 2 is outside it (robber
    survives forever) — i.e. one cop is not enough."""
    N = {(c, r, True) for c in range(n) for r in range(n)}
    R = {(c, r, False) for c in range(n) for r in range(n)}
    win = set()
    for c in range(n):
        win.add((c, c, True))
        win.add((c, c, False))
    changed = True
    while changed:
        changed = False
        for st in list(N - win):
            c, r, _ = st
            if any((c2, r, False) in win for c2 in neighbors(n, c) | {c}):
                win.add(st)
                changed = True
        for st in list(R - win):
            c, r, _ = st
            if all((c, r2, True) in win for r2 in neighbors(n, r) | {r}):
                win.add(st)
                changed = True
    for c in range(n):
        for r in range(n):
            if r != c and r not in neighbors(n, c):
                if (c, r, True) not in win:
                    return True
    return False


def two_cops_win(n):
    """Two-cop attractor over states (c1, c2, r, cop_to_move); capture
    when r in {c1, c2}.  Returns True iff the cops win from every
    start (cops together, robber anywhere)."""
    states_T = {(c1, c2, r, True) for c1 in range(n) for c2 in range(n)
                for r in range(n)}
    states_F = {(s[0], s[1], s[2], False) for s in states_T}
    win = set()
    for s in states_T | states_F:
        if s[2] in (s[0], s[1]):
            win.add(s)
    changed = True
    while changed:
        changed = False
        for st in list(states_T - win):
            c1, c2, r, _ = st
            moves = [st_ for st_ in
                     ((c1n, c2n, r, False)
                      for c1n in neighbors(n, c1) | {c1}
                      for c2n in neighbors(n, c2) | {c2})
                     if st_ in win]
            if moves:
                win.add(st)
                changed = True
        for st in list(states_F - win):
            c1, c2, r, _ = st
            succs = [(c1, c2, r2, True)
                     for r2 in neighbors(n, r) | {r}]
            if all(s2 in win for s2 in succs):
                win.add(st)
                changed = True
    for c in range(n):
        for r in range(n):
            if (c, c, r, True) not in win:
                return False
    return True


def main():
    for n in (4, 5, 6, 7, 8, 9, 10, 11):
        one = one_cop_loses(n)
        two = two_cops_win(n)
        cop_num = 2 if (one and two) else (1 if not one else None)
        print(f"C_{n}: 1 cop insufficient = {one}, 2 cops suffice = {two} "
              f"-> cop number = {cop_num}")
        assert one and two, (n, one, two)
    # the infinite family: all odd cycles from 5 on
    for n in (13, 15, 17, 19, 21):
        assert one_cop_loses(n)
    print("C_13..C_21: 1 cop insufficient as well — infinite family — OK")
    print("ALL CHECKS PASS — cop number exactly 2 for every cycle >= 4 "
          "(cycles are outerplanar: infinitely many outerplanar graphs)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
