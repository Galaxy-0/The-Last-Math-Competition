"""Independent checks for conjecture 00000006542 only.

Finite walk checks are auxiliary. The Lean proof covers every length.
Uses Python standard library only and writes within this package.
"""
import hashlib
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
VERTICES = tuple(range(3))
DARTS = tuple((a, b) for a in VERTICES for b in VERTICES if a != b)


def allowed(a, b):
    return a[1] == b[0] and b != (a[1], a[0])


def rotation_class(word):
    return min(word[i:] + word[:i] for i in range(len(word)))


def is_primitive(word):
    n = len(word)
    return not any(n % p == 0 and word == word[:p] * (n // p)
                   for p in range(1, n))


def convolution(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def permutation_sign(p):
    inversions = sum(p[i] > p[j] for i in range(len(p))
                     for j in range(i + 1, len(p)))
    return (-1) ** inversions


def determinant(matrix):
    result = 0
    for p in itertools.permutations(range(len(matrix))):
        term = permutation_sign(p)
        for i, j in enumerate(p):
            term *= matrix[i][j]
        result += term
    return result


def main():
    assert len(DARTS) == 6
    for d in DARTS:
        assert sum(allowed(d, e) for e in DARTS) == 1
    paths = [(d,) for d in DARTS]
    by_length = []
    all_primes = set()
    for n in range(1, 16):
        closed = [p for p in paths if allowed(p[-1], p[0])]
        classes = {rotation_class(p) for p in closed}
        primes = {c for c in classes if is_primitive(c)}
        assert len(closed) == (6 if n % 3 == 0 else 0)
        assert len(classes) == (2 if n % 3 == 0 else 0)
        assert len(primes) == (2 if n == 3 else 0)
        all_primes.update(primes)
        by_length.append({"length": n, "closed_words": len(closed),
                          "rotation_classes": len(classes),
                          "prime_classes": len(primes)})
        paths = [p + (d,) for p in paths for d in DARTS if allowed(p[-1], d)]
    assert len(all_primes) == 2
    denominator = convolution([1, 0, 0, -1], [1, 0, 0, -1])
    residual = convolution([1, 1, 1], [1, 1, 1])
    factorized = convolution(convolution([-1, 1], [-1, 1]), residual)
    assert denominator == factorized == [1, 0, 0, -2, 0, 0, 1]
    assert sum(residual) == 9
    adjacency = [[int(i != j) for j in VERTICES] for i in VERTICES]
    one_minus_adjacency = [[int(i == j) - adjacency[i][j]
                            for j in VERTICES] for i in VERTICES]
    assert determinant(one_minus_adjacency) == -4
    files = ["SOURCE.md", "main.tex", "lean/Main.lean", "verify.py"]
    result = {
        "id": "00000006542", "status": "PASS",
        "scope": "Auxiliary bounded walk check; all-length proof is in Lean.",
        "walk_lengths": by_length, "prime_classes": sorted(all_primes),
        "denominator": denominator, "residual_at_one": sum(residual),
        "det_I_minus_A": determinant(one_minus_adjacency),
        "sha256": {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
                   for name in files},
        "pdf_status": "PDF validation is separate from this arithmetic check."
    }
    (HERE / "auxiliary-verification.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("00000006542 PASS: two prime rotation classes; exact pole factorization; det(I-A)=-4")


if __name__ == "__main__":
    main()
