# Disproof of TLMC conjecture 00000000404

**Verdict: FALSE.**

## Conjecture

In the Schur expansion of the plethysm `s_{(2)}[s_{(n)}]`, the coefficients
of even-indexed partitions `nu` are all even.

## Attack (n = 2)

Via the lambda-ring identity `s2[f] = (f*f + psi^2(f))/2` with
`f = s2 = (p11 + p2)/2`:

```
s_{(2)}[s_{(2)}] = (p1111 + 2 p211 + 3 p22 + 2 p4) / 8
                 = s_{(4)} + s_{(2,2)}
```

Schur extraction (Hall orthogonality + the S4 character table, verified by
Murnaghan–Nakayama):

| nu        | coefficient | parity |
|-----------|-------------|--------|
| (4)       | 1           | ODD    |
| (3,1)     | 0           | —      |
| (2,2)     | 1           | ODD    |
| (2,1,1)   | 0           | —      |
| (1,1,1,1) | 0           | —      |

Both nonzero coefficients are `1` — **odd**.  Under every natural reading of
"even-indexed nu" the conjecture fails at `n = 2`:

* `|nu|` even: `nu = (4)` (also `(2,2)`) has coefficient 1;
* all parts even: both `(4)` and `(2,2)` have coefficient 1;
* first part even: `(4)` (also `(2,2)`) has coefficient 1;
* even length: `nu = (2,2)` has coefficient 1.

Dimension cross-checks (Weyl / hook–content), consistent with the
multiplicity-free decomposition: for GL4,
`dim Sym^2(Sym^2 C^4) = 55 = 35 + 20 = dim s_(4) + dim s_(2,2)`;
for GL2, `6 = 5 + 1`.

## Boundary

* `n = 1`: `s_{(2)}[s_{(1)}] = s_{(2)}`, coefficient of `(2)` is 1 (odd) —
  fails already there.
* general `n` (computed `n <= 6`): `s_{(2)}[s_{(n)}] = sum_j s_{(2n-2j, 2j)}`,
  every coefficient exactly 1; each summand has even size / all parts even /
  first part even (and even length for `n >= 2`).  No `n` rescues the
  conjecture.

## Machine verification

`lean4/` (core Lean only, toolchain `leanprover/lean4:v4.33.1`): the power-sum
identity, S4 character-table orthogonality, the five Schur coefficients with
parity, the dimension identities `55 = 35 + 20`, and the `n = 1` boundary are
all proved with `rfl`/`decide`.  Axiom audit (`lake env lean Check.lean`):
all six theorems **do not depend on any axioms** — no `sorry`, no `propext`,
no `Quot.sound`, no `Classical.choice`, no `Lean.ofReduceBool`.

## Reproduce

```
python3 reproduce.py                       # 13 checks, exit code 0
cd lean4
lake build
lake env lean Check.lean                   # "does not depend on any axioms" x6
cd .. && tectonic main.tex --outdir build  # rebuilds build/main.pdf
```

(If elan is not on PATH: `export ELAN_HOME=<elan home> &&
export PATH="$ELAN_HOME/bin:$PATH"` first.)

## Files

* `main.tex`, `build/main.pdf`, `build/log.txt` — write-up
* `reproduce.py` — standalone recomputation (stdlib only)
* `lean4/Main.lean` — formal proof; `lean4/Check.lean` — axiom audit;
  `lean4/lakefile.toml`, `lean4/lean-toolchain`, `lean4/README.md`
