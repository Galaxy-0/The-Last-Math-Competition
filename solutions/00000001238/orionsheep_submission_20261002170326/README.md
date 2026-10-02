# Disproof of Conjecture 00000001238

**Verdict: FALSE (both clauses).**

Definition: The invariant-factor sequence of the Jacobi group encodes the torsion
structure of the graph Laplacian. Conjecture: Log-concavity of the invariant-factor
sequence of the torsion group holds for all graphs; and equality in the concavity
holds exactly for direct sums of cycles. (Jacobian invariant factors log-concave)

## The refutation in one paragraph

Take $K_{2,4}$. Its reduced Laplacian is $L_{24} =
[[4,-1,-1,-1,-1],[-1,2,0,0,0],[-1,0,2,0,0],[-1,0,0,2,0],[-1,0,0,0,2]]$, and the
unimodular matrices $U_{24}$, $V_{24}$ (both of determinant $-1$, entries in
`main.tex`/`lean4/Main.lean`) satisfy $U_{24} L_{24} V_{24} = \mathrm{diag}(1,1,2,2,8)$.
Hence $\mathrm{Jac}(K_{2,4}) \cong \mathbb{Z}/2 \times \mathbb{Z}/2 \times
\mathbb{Z}/8$ with invariant-factor sequence $(2,2,8)$, whose middle concavity
inequality $2\cdot2 \ge 2\cdot8$ fails: $4 < 16$. Clause (i) is false. Separately,
$K_4$ has $\mathrm{Jac}(K_4) = \mathbb{Z}/4 \times \mathbb{Z}/4$ (sequence $(4,4)$,
$16 = 16$: equality in the concavity) although $K_4$ is not a direct sum of cycles —
its edge $\{0,1\}$ lies on the two distinct triangles $\{0,1,2\}$ and $\{0,1,3\}$, and
every connected 4-vertex cactus (all 31 of them) has $\le 4$ edges and
$\tau \in \{1,3,4\}$, while $K_4$ has 6 edges and $\tau = 16$. Clause (ii) is false.
Finally the two clauses are jointly unsatisfiable even on the conjecture's own
equality class: the cactus $C_3 \vee C_3 \vee C_6$ (a direct sum of cycles) has
invariant factors $(3,3,6)$ with $9 < 18$ — not log-concave.

## Corroborating sweep

Over all $2^{15}$ graphs on six labeled vertices (26,704 connected, SNF of each
reduced Laplacian by determinantal divisors): 75 nontrivial sequences of length $\ge
2$ violate an interior inequality; 15 graphs have torsion exactly
$\mathbb{Z}/2\times\mathbb{Z}/2\times\mathbb{Z}/8$ ($K_{2,4}$ among them); 3,793
graphs have equality sequences of length $\ge 2$ yet are not cacti (31 of length
$\ge 3$, e.g. $K_6$ with $(6,6,6,6)$).

## Reading and robustness

Conventions match the pipeline's confirmed instance (SNF $(1,1,2,2,8)$, nontrivial
factors $[2,2,8]$, $2^2=4<2\cdot8=16$): log-concavity = interior inequalities
$d_i^2 \ge d_{i-1}d_{i+1}$; equality = all interior equalities; direct sum of cycles
= cactus. The counterexamples are convention-robust: $K_{2,4}$'s failure is an
interior strict inequality (persists under full-sequence and endpoint-augmented
readings), and $K_4$/$K_5$ fail "exactly" under any reading (a group-theoretic
reading of "direct sum of cycles" would make clause (ii) vacuous).

## What is and is not claimed

- We refute only the literal two-clause statement at the concrete graphs $K_{2,4}$
  and $K_4$ (reinforced by $K_5$ and the cactus $C_3\vee C_3\vee C_6$).
- Smith theory of Laplacians, the matrix-tree theorem and the cactus decomposition
  of cycle-sum Jacobians are used as tools, not disputed.

## Contents

- `main.tex`, `build/main.pdf` — formal write-up (unimodular SNF certificates,
  spanning-tree sanity checks, cactus classification, sweep table, reading
  conventions and robustness).
- `reproduce.py` — standalone script (no absolute paths, pure standard library,
  ~15 s): rebuilds both counterexamples from adjacency masks, verifies the
  unimodular products and determinantal divisors, classifies all 4-vertex cacti,
  and runs the exhaustive 6-vertex sweep.
- `lean4/` — Lean 4 project (toolchain `leanprover/lean4:v4.33.1`, core only)
  proving, with **zero axioms and zero `sorry`** (audited in `Check.lean`, 11/11
  axiom-free):
  - `Tlmc1238.snf_L24`: $U_{24}L_{24}V_{24} = \mathrm{diag}(1,1,2,2,8)$, $\det = -1$
    both;
  - `Tlmc1238.snf_LK4`: $U_4L^{\circ}(K_4)V_4 = \mathrm{diag}(1,4,4)$, $\det = 1$
    both;
  - `Tlmc1238.lap24_is_minor` / `lapK4_is_minor`: matrices = reduced Laplacians of
    edge bitmasks 510 ($K_{2,4}$) and 615 ($K_4$);
  - `Tlmc1238.K4_edge_in_two_triangles`, `seq_228_not_logconcave`,
    `seq_44_logconcave_eq`, `seq_555_equalities`, `seq_336_not_logconcave`,
    `violation_arith`, `refute`.

Run `python3 reproduce.py` and, in `lean4/`, `lake build && lake env lean Check.lean`.
