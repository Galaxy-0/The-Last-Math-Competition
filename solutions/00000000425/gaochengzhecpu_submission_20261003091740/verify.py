"""Independent exact verification for conjecture 00000000425 only."""
from itertools import product
from pathlib import Path
import hashlib
import json
import re

LIMIT = 28
coefficients = [0] * 9
for a, b, c, d in product(range(3), repeat=4):
    if a >= b and a >= c and b >= d and c >= d:
        coefficients[a + b + c + d] += 1
assert coefficients == [1, 1, 3, 3, 4, 3, 3, 1, 1]
assert coefficients[1] ** 2 < coefficients[0] * coefficients[2]

def macmahon_prefix(side, limit):
    values = [1] + [0] * limit
    for i, j, k in product(range(1, side + 1), repeat=3):
        numerator, denominator = i + j + k - 1, i + j + k - 2
        old = values[:]
        values = [
            old[n] - (old[n - numerator] if n >= numerator else 0)
            for n in range(limit + 1)
        ]
        for n in range(denominator, limit + 1):
            values[n] += values[n - denominator]
    return values

def multiply(a, b, degree):
    return sum(a[degree - i] * b[i] for i in range(degree + 1))

root = Path(__file__).resolve().parent
lean_text = (root / "lean/Main.lean").read_text(encoding="utf-8")
prefixes = {}
for side in (1, 2, 3):
    values = macmahon_prefix(side, LIMIT)
    found = re.search(
        rf"def cube{side}Coefficients : List Int := \[([^\]]*)\]", lean_text
    )
    assert found is not None
    published = [int(x.strip()) for x in found.group(1).split(",")]
    assert values == published, f"Lean coefficient table disagrees for side {side}"
    prefixes[side] = values

assert prefixes[2][:9] == coefficients
assert all(c == 0 for c in prefixes[1][2:])
assert all(c == 0 for c in prefixes[2][9:])
assert prefixes[3][27] == 1 and prefixes[3][28] == 0
left = multiply(prefixes[2], prefixes[2], LIMIT)
right = multiply(prefixes[1], prefixes[3], LIMIT)
assert left == 0 and right == 1 and left - right == -1

files = ["SOURCE.md", "main.tex", "README.md", "lean/Main.lean",
         "lean/lakefile.toml", "lean/lean-toolchain", "verify.py"]
report = {
    "conjecture": "00000000425",
    "scalar_coefficients": coefficients,
    "macmahon_prefixes_through_28": prefixes,
    "cross_size_degree": LIMIT,
    "F2_squared_coefficient": left,
    "F1_times_F3_coefficient": right,
    "difference_coefficient": left - right,
    "sha256": {
        name: hashlib.sha256((root / name).read_bytes()).hexdigest()
        for name in files
    },
    "pdf_status": "PDF validation is separate from this arithmetic check.",
}
(root / "auxiliary-verification.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
print(json.dumps(report, indent=2))

