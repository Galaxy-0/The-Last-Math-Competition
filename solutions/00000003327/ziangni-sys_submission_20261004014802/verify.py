"""Exact, standard-library-only checks for conjecture 00000003327.

Independent of Lean: enumerate U/D words, compute signed prefix heights,
and cross-check the counts using a first-return Catalan convolution.
"""

from itertools import product
from math import comb


def is_hill_free_dyck(word: tuple[int, ...]) -> bool:
    heights = [0]
    for step in word:
        heights.append(heights[-1] + step)
    return (
        heights[-1] == 0
        and min(heights) >= 0
        and not any(
            heights[i] == 0 and word[i : i + 2] == (1, -1)
            for i in range(len(word) - 1)
        )
    )


def paths(n: int) -> list[str]:
    return [
        "".join("U" if s == 1 else "D" for s in word)
        for word in product((1, -1), repeat=2 * n)
        if is_hill_free_dyck(word)
    ]


def main() -> None:
    # Boundary cases check both the Dyck condition and hill exclusion.
    assert is_hill_free_dyck(())
    assert not is_hill_free_dyck((1, -1))
    assert not is_hill_free_dyck((-1, 1))
    assert not is_hill_free_dyck((1, 1))
    assert is_hill_free_dyck((1, 1, -1, -1))
    assert not is_hill_free_dyck((1, 1, -1, -1, 1, -1))

    # First return: a nonempty hill-free path is U A D B, where A is
    # a nonempty Dyck path and B is any hill-free Dyck path.
    catalan = [comb(2 * n, n) // (n + 1) for n in range(8)]
    recurrence = [1]
    for n in range(1, 8):
        recurrence.append(sum(catalan[k - 1] * recurrence[n - k]
                              for k in range(2, n + 1)))
    counts = [len(paths(n)) for n in range(8)]
    assert counts == recurrence == [1, 0, 1, 2, 6, 18, 57, 186]
    for n in (2, 3, 4):
        listing = paths(n)
        assert len(set(listing)) == len(listing)
        print(f"F_{n} = {len(listing)}: {', '.join(listing)}")
    assert counts[3] ** 2 < counts[2] * counts[4]
    print("Strict violation at n=3: F_3^2 = 4 < 6 = F_2 F_4.")
    print("Enumeration and Catalan first-return recurrence agree for n=0..7.")


if __name__ == "__main__":
    main()
