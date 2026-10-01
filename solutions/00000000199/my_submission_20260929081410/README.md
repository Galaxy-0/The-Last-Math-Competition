# Disproof of TLMC conjecture 00000000199 (quadratic-denominator psi representation)

## Verdict: FALSE

**Conjecture.** `S = Σ_{n≥0} 1/(n²+n+2)` is an explicit Q-linear combination of digamma values
at **cube roots of unity** (`ω³ = 1`), and the irrationality of `S` is equivalent to that of
`ψ(ω)`-type values, via an explicit partial-fraction decomposition.

**Attack.** The partial-fraction decomposition of `1/(n²+n+2)` necessarily uses the roots of
`z²+z+2`, i.e. `r± = (−1±i√7)/2`:

- discriminant `1−8 = −7`, not the `−3` of `z²+z+1` (whose roots are the primitive cube roots
  of unity);
- `|r±|² = 2 ≠ 1` — not unimodular, hence not roots of unity at all;
- directly, `r³ = (5−i√7)/2 ≠ 1`, `r̄³ ≠ 1`, `r² ≠ 1`, `r ≠ 1`.

The exact decomposition is
```
S = (ψ(b) − ψ(a)) / (b − a),   a,b = (1±i√7)/2
  = (2/√7) · Im ψ((1+i√7)/2)
  = 1.18682733772005388216084306111871622595690295…
```
— digamma at arguments of modulus `√2` in `Q(√−7)`, **not** at cube roots of unity, and no
Q-linear reduction to `ψ(1), ψ(ω), ψ(ω²)` exists through it. Since `Im ψ(ω) = 2.4232666… ≠ 0`,
any *real* Q-combination `q₁ψ(1)+q₂ψ(ω)+q₃ψ(ω²)` has `q₂ = q₃`, i.e. lies in
`span_Q{ψ(1), 2Re ψ(ω)}`; an exhaustive search with denominators ≤ 500 finds no match for `S`.

**Boundary.** For `n²+n+1` (disc `−3`) the same decomposition gives arguments `(1±i√3)/2`,
which ARE 6th roots of unity, and `Σ 1/(n²+n+1) = (2/√3)·Im ψ((1+i√3)/2) = 1.79814728056269…`.
The conjecture's mechanism is discriminant-specific: valid for disc `−3`, false for disc `−7`.

## Files

| file | content |
|---|---|
| `README.md` | this file (verdict, attack, boundary) |
| `main.tex` | full write-up (no absolute paths) |
| `build/main.pdf`, `build/log.txt` | compiled PDF (tectonic) and build log |
| `reproduce.py` | self-contained recomputation (stdlib only): `python3 reproduce.py` |
| `lean4/Main.lean` | core-Lean concretization of the attack (22 theorems) |
| `lean4/Check.lean` | axiom audit (`#print axioms` on every theorem) |
| `lean4/lakefile.toml`, `lean4/lean-toolchain`, `lean4/README.md` | Lean build config |

## Reproduction

```sh
# numeric
python3 reproduce.py

# Lean (toolchain leanprover/lean4:v4.33.1, core only, no Mathlib)
cd lean4 && lake build && lake env lean Check.lean
# every line of the audit prints "... does not depend on any axioms"

# PDF
tectonic main.tex --outdir build
```

**Axiom audit:** all 22 Lean theorems are closed computations (`rfl`/`decide`) over
`Q(√−7)` / `Q(√−3)` triples and exact fixed-point rational partial sums —
zero axioms (`propext`/`Quot.sound`/`Classical.choice` all absent), zero `sorry`.
