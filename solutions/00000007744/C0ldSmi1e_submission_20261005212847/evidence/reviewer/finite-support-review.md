# Independent finite supporting-computation review

Date: 2026-10-05. Scope: only the supplied supporting script; no candidate draft was read. This is not an asymptotic proof or acceptance of a submission.

## Supplied script identity and replay

- Original: `/private/tmp/tlmc7744-aux/check_small_ensembles.py`.
- SHA256: `f05ab5c6c3d19e904e8b0dae502d9400319f29d33af2456bcc13d57cd2beec08`, independently verified before copying.
- Independent copy: `replayed_check_small_ensembles.py` in this review folder.
- Interpreter: Python 3.14.2, `/opt/homebrew/opt/python@3.14/bin/python3.14`.
- Actual replay exit code: 0; stderr empty.
- Actual stdout SHA256: `9c59e7c82d90337db729b803af2c2ace517a5b5b5d0d8444253f0a6cca3cce3c`, matching the original output and authoritative `execution.json`.
- Complete replay output, stderr, execution command, interpreter version, timestamp, exit code, and hashes are retained in `finite-replay.stdout.json`, `finite-replay.stderr.txt`, and `finite-replay.execution.json`.

## Code inspection

The script forms every unordered vertex pair exactly once via `combinations(range(n), 2)`. A labeled simple d-regular graph necessarily has exactly nd/2 edges. Enumerating all subsets of that cardinality and retaining exactly those with every vertex degree d is complete and has no duplicate graphs. The adjacency matrix has one symmetric entry per retained edge and no loops. Every matrix-square entry is explicitly calculated by matrix multiplication, then the diagonal and trace are checked. All means, centered values, and scaled variances use integers and `Fraction`; there is no floating-point dependence. The formula `n * E[X²]` is valid for the centered X and exactly gives the variance after multiplying X by sqrt(n).

The expected graph counts are independently justified: on four labeled vertices the sole cubic simple graph is K4. Complementation bijects cubic graphs on six labeled vertices with simple 2-regular graphs on those vertices. Their components must be either one 6-cycle or two triangles. There are `6!/(6*2)=60` undirected labeled 6-cycles and `choose(6,3)/2=10` partitions into two triangles, hence 70 graphs in total.

## Independent alternate enumeration

`independent_count_check.py` traverses all 64 edge masks on four vertices and all 32,768 edge masks on six vertices, rather than filtering fixed-cardinality edge subsets. It uses bitset degrees, independently reconstructs the quadratic diagonal, computes exact ensemble means/variance, and checks complement component counts on six vertices.

Actual execution exit code: 0; stderr empty. Output is retained in `independent-counts.stdout.json`; execution metadata is retained in `independent-counts.execution.json`.

Results agree: one graph on four vertices; 70 graphs on six vertices; complements split into 60 single 6-cycles and 10 pairs of triangles; normalized quadratic trace always 3; uniform expectation 3; centered values 0; sqrt(n)-scaled variance 0. The supplied conjectured scalar formula evaluates to 8/9.

## Verdict and limitation

PASS for the stated exhaustive finite supporting scope. Enumeration and arithmetic are complete for n=4 and n=6. These finite checks alone do not prove an asymptotic contradiction, establish admissibility at unbounded sizes, identify a weak limit, or certify any Lean declaration. Those requirements remain pending until the frozen complete candidate is supplied.
