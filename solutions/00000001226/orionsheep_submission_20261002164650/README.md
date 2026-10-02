# Disproof of TLMC conjecture 00000001226

**Verdict: FALSE.**

## Conjecture (original text, verbatim)

> Conjecture: The expected firefighter survival on 3-regular graphs is
> 0.65n for an explicit constant (random firefighting expectation).
> (中文：猜想：3-正则图的 firefighter 的存活期望为 0.65n 的常数(随机消防期望)。)

The conjecture asserts a linear expected-survival law with the explicit
constant `0.65` on the class of 3-regular graphs.

## Attack (n = 4, the smallest 3-regular graph: K4)

Standard firefighter process (Hartnell): the fire breaks out at one vertex;
each turn `f` vertices are protected, then fire spreads to every unprotected
neighbour of a burning vertex; the process ends when no unprotected vertex is
adjacent to the fire. "Survival" = number of vertices never burned.

On `K4` the process is **forced**: whatever vertex the fire starts at and
whatever the first move is, the outcome is the same. So the expected survival
equals that constant outcome under *every* probability law — the undefined
phrase "random firefighting expectation" never has to be interpreted:

| firefighters per turn | process on K4                    | saved | 0.65n = 13/5 |
|-----------------------|----------------------------------|-------|--------------|
| f = 1 (standard)      | defend 1 of {1,2,3}; other two burn; no move left | **1** (= 0.25n) | 2.6 |
| f = 2                 | defend 2; the third burns; defend it; done        | **2** (= 0.5n)  | 2.6 |
| f = 3                 | defend all; fire cannot spread                    | **3** (= 0.75n) | 2.6 |

The claimed expectation `13/5` would force `5 * E[saved] = 13`, and
`5 * s != 13` for every natural number `s` — the forced expectation is an
integer, `0.65n` at `n = 4` is not.  The conjecture fails on the **first**
member of the class of 3-regular graphs, for every `f` and every strategy,
random or not.  (`f = 1` is the standard model.)

## No cubic graph of order n <= 10 reaches 0.65n under any reading

Exact dynamic programming over all process states (rational arithmetic,
`reproduce.py`), E[saved] with fire start averaged over all vertices:

| graph (n)     | uniform any vertex | uniform fire front | optimal play | worst play | 0.65n |
|---------------|--------------------|--------------------|--------------|------------|-------|
| K4 (4)        | 1                  | 1                  | 1            | 1          | 13/5  |
| K3,3 (6)      | 2                  | 2                  | 2            | 2          | 39/10 |
| prism C3xK2 (6)| 2                 | 2                  | 2            | 2          | 39/10 |
| cube Q3 (8)   | 73/28 (~2.61)      | 3                  | 3            | 2          | 26/5  |
| Wagner M8 (8) | 31/14 (~2.21)      | 8/3 (~2.67)        | 3            | 2          | 26/5  |
| Petersen (10) | 7/3 (~2.33)        | 3                  | 3            | 2          | 13/2  |

* "optimal play" maximises over **all** strategies (protect any unburned
  vertex), so it is an upper bracket for every randomised reading: even the
  best play on every tested graph stays strictly below `0.65n`.
* The n = 4 and n = 6 rows are exhaustive over **all** cubic graphs of those
  orders (isomorphism classes 1 + 2, verified by the script's canonical
  enumeration): every 3-regular graph with n <= 6 refutes the claim under
  all four readings.

## Scope at large n (Monte-Carlo, f = 1, random cubic graphs)

Under the two canonical random strategies the saved fraction decreases
toward 0 — the fire sweeps a random cubic graph:

| n    | uniform any vertex | uniform fire front |
|------|--------------------|--------------------|
| 256  | 0.038              | 0.044              |
| 1024 | 0.012              | 0.013              |
| 4096 | 0.003              | 0.004              |

(These simulations are scope evidence only; the disproof above is exact.)

## Machine verification

`lean4/` (core Lean only, toolchain `leanprover/lean4:v4.33.1`, bare `Nat`):
the full forced K4 process for `f = 1, 2, 3` (every first move), the uniform
expectation `(1+1+1)/3 = 1`, the distribution-free weighted form, and the
arithmetic kill `forall s : Nat, 5 * s != 13` are proved with
`decide`/explicit terms.  Axiom audit (`lake env lean Check.lean`): all
fifteen theorems **do not depend on any axioms** — no `sorry`, no `propext`,
no `Quot.sound`, no `Classical.choice`, no `Lean.ofReduceBool`.

## Reproduce

```
python3 reproduce.py                       # all checks PASS, exit code 0
cd lean4
lake build
lake env lean Check.lean                   # "does not depend on any axioms" x15
cd .. && tectonic main.tex --outdir build  # rebuilds build/main.pdf
```

(If elan is not on PATH: `export ELAN_HOME=<elan home> &&
export PATH="$ELAN_HOME/bin:$PATH"` first.)

## Files

* `main.tex`, `build/main.pdf`, `build/log.txt` — write-up
* `reproduce.py` — standalone recomputation (stdlib only)
* `lean4/Main.lean` — formal proof; `lean4/Check.lean` — axiom audit;
  `lean4/lakefile.toml`, `lean4/lean-toolchain`, `lean4/README.md`
