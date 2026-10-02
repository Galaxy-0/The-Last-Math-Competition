#!/usr/bin/env python3
"""Reproduction script for the disproof of TLMC conjecture 00000001211.

Conjecture (verbatim): "Definition: A poset game (delete an element and everything above it).
Conjecture: The P-positions of the poset game on Young's lattice have an explicit
characterization via perfect square partitions (the Young poset game)."

Positions are Young diagrams (partitions, encoded as tuples of non-increasing row lengths).
A move chomps a cell (i, j) (1-indexed): the cell and everything above-right of it is removed.

Two readings of the conjecture are refuted:

  Reading 1 (literal poset game, normal play): every nonempty position can chomp the corner
  cell (1, 1), which clears the whole diagram, so the unique P-position is the empty diagram
  and a perfect square such as (2, 2) is an N-position.

  Reading 2 (Chomp poison corner: taking (1, 1) loses, equivalently the move is forbidden):
  (2, 1) is a P-position that is not a square, while the squares (2, 2), (3, 3), (3, 3, 3)
  are N-positions.

Run:  python3 reproduce.py
Expects no third-party packages.
"""
from functools import lru_cache


def partitions_in_box(k: int):
    """All partitions fitting in a k x k box (at most k parts, each part <= k)."""
    def gen(maxpart, rows_left):
        yield ()
        if rows_left == 0:
            return
        for p in range(1, maxpart + 1):
            for rest in gen(p, rows_left - 1):
                yield (p,) + rest
    return sorted(set(gen(k, k)), key=lambda t: (sum(t), t))


def cells(lam):
    return [(i, j) for i, r in enumerate(lam, 1) for j in range(1, r + 1)]


def chomp(lam, ci, cj):
    """Remove every cell (r, c) with r >= ci and c >= cj; return the canonical partition."""
    rows = {}
    for (i, j) in cells(lam):
        if not (i >= ci and j >= cj):
            rows[i] = rows.get(i, 0) + 1
    if not rows:
        return ()
    return tuple(rows.get(r, 0) for r in range(1, max(rows) + 1))


@lru_cache(maxsize=None)
def wins_literal(lam):
    """True iff the player to move wins (reading 1: every cell, normal play)."""
    if lam == ():
        return False
    return any(not wins_literal(chomp(lam, i, j)) for (i, j) in cells(lam))


@lru_cache(maxsize=None)
def wins_chomp(lam):
    """True iff the player to move wins (reading 2: chomping (1, 1) is forbidden).

    Facing the lone poison cell (1,) the player must take it and loses, which is exactly the
    'no legal move' outcome of the forbidden-move model, so the game values agree with Chomp.
    """
    if lam == ():
        return False
    if lam == (1,):
        return False
    return any(not wins_chomp(chomp(lam, i, j)) for (i, j) in cells(lam) if (i, j) != (1, 1))


def is_square(lam):
    """Perfect-square partition: k rows, each of length k."""
    return len(lam) > 0 and len(lam) == lam[0] and all(p == lam[0] for p in lam)


def main():
    diagrams = partitions_in_box(5)
    assert len(diagrams) == 252, len(diagrams)

    squares = [l for l in diagrams if is_square(l)]
    assert squares == [(1,), (2, 2), (3, 3, 3), (4, 4, 4, 4), (5, 5, 5, 5, 5)]

    # ---- Reading 1: literal poset game ----
    p_literal = [l for l in diagrams if not wins_literal(l)]
    assert p_literal == [()], "literal reading must have P = {empty}"
    for s in squares:
        assert wins_literal(s), f"{s} is a square but must be N under reading 1"

    # ---- Reading 2: Chomp poison corner ----
    p_chomp = [l for l in diagrams if not wins_chomp(l)]
    assert len(p_chomp) == 24, len(p_chomp)
    assert (2, 1) in p_chomp and not is_square((2, 1))
    assert (2, 1) in p_chomp and not wins_chomp(())
    for s in [(2, 2), (3, 3, 3)]:
        assert is_square(s) and wins_chomp(s), f"{s} is a square but must be N under reading 2"
    assert wins_chomp((3, 3)), "(3, 3) (a 2x3 rectangle) is also N"
    assert [l for l in p_chomp if is_square(l)] == [(1,)]

    print("All assertions passed.  Summary (5x5 box, 252 Young diagrams):\n")
    print("Reading 1 (literal):  P-positions = {( )}  -- the empty diagram only")
    print("  counterexample: (2, 2) is a perfect square but an N-position\n")
    print("Reading 2 (Chomp poison corner): %d P-positions" % len(p_chomp))
    print("  P-positions:", ", ".join(str(p) for p in p_chomp))
    print("  counterexamples: (2, 1) is P but not a square;")
    print("                   (2, 2), (3, 3, 3) are squares but N (as is the 2x3 rectangle (3, 3)).")
    print("  (the only square that is P here is the degenerate (1,))")


if __name__ == "__main__":
    main()
