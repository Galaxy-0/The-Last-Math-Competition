"""Supplemental finite checks, not the proof of the infinite entropy limit."""
import itertools, json, math

results = []
for n in (1, 2):
    sites = list(itertools.product(range(n), repeat=2))
    patterns = list(itertools.product(range(3), repeat=len(sites)))
    assert len(patterns) == len(set(patterns)) == 3**(n*n)
    for p in patterns:
        finite_part = dict(zip(sites, p))
        configuration = lambda z: finite_part.get(z, 0)
        assert tuple(configuration(z) for z in sites) == p
        assert configuration((-1, 0)) == configuration((n, n)) == 0
    results.append({'n': n, 'enumerated_patterns': len(patterns),
                    'expected_count': 3**(n*n), 'extension_checks': 'PASS'})
assert math.log(3) > math.log(2)
print(json.dumps({'checks': results, 'log3': math.log(3), 'log2': math.log(2),
                  'status': 'PASS', 'scope': 'Supplement only; all-size real-limit theorem is proved in Lean.'}, indent=2))
