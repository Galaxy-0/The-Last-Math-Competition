# 00000000508: complete universal numerical proof draft

The complete Lean proof establishes that extremal positions of
`β_{k,k+d}` form an antichain in the standard shifted diagram coordinates
`(k,d)`, for **every** table `β : ℕ → ℤ → ℕ`. It also proves exact
equivalence of the BCP99 extremality predicate with maximal shifted support,
incomparability of distinct corners, and strict decrease of shifted degree
when homological degree increases.

The universal theorem has no algebraic hypotheses: every actual monomial
ideal's numerical Betti table is an input. There is no unproved assertion
about a resolution, Tor module, or an ideal-to-table map. Signed degree
indices avoid excluding negative shifts. This package does not construct
an individual ideal.

The source does not explicitly specify the position order. The package
uses the standard `(k,d)` order indicated by `β_{k,k+d}` and the primary
definition in [Bayer–Charalambous–Popescu, introduction, p. 1](https://www.math.columbia.edu/~bayer/papers/Betti_BCP99/Betti_BCP99.pdf).
Raw `(k,j)` coordinates have a different product order. The separate
checked numerical diagnostic demonstrates that distinction and is not
claimed to arise from a monomial ideal. Independent semantic review must
confirm the standard shifted-coordinate reading.

Files:

- `original.md`: exact assigned source, hash checked against `task.json`.
- `obligations.md`: source role, exact statements, checked dependencies,
  missing connections, and acceptance method, saved before implementation.
- `lean/Main.lean`: complete definitions and six proved declarations.
- `lean/Audit.lean`: declaration types and axiom audit.
- `lean/CoordinateDiagnostic.lean`: explicitly non-ideal coordinate example.
- `proof.tex`: mathematical proof source; no worker-produced PDF.
- `source-correspondence.md`: source-to-Lean and source-to-report audit.
- `verification.json` and compilation logs: actual local checks.

Pinned toolchain: Lean 4.33.0. Pinned Mathlib revision:
`db584cd6d46c92f209a44c0f1c829460d327499d`. The supplied lake configuration,
manifest and toolchain file were preserved. `.lake/packages` is the existing
public dependency-cache junction and was treated as read-only. The only
compiled object emitted by this worker is its own `Main.olean` in its own
build directory.

From this directory's `lean` subdirectory, local check commands are:

```powershell
& 'D:/Projects/AI4Math/math-exploration/toolchains/lean-4.33.0-windows/bin/lake.exe' env lean Main.lean
& 'D:/Projects/AI4Math/math-exploration/toolchains/lean-4.33.0-windows/bin/lake.exe' env lean -o .lake/build/lib/lean/Main.olean Main.lean
& 'D:/Projects/AI4Math/math-exploration/toolchains/lean-4.33.0-windows/bin/lake.exe' env lean Audit.lean
& 'D:/Projects/AI4Math/math-exploration/toolchains/lean-4.33.0-windows/bin/lake.exe' env lean CoordinateDiagnostic.lean
```

All four invocations completed successfully. The axiom audit for every
principal theorem reports only `propext` and `Quot.sound`, with no
`sorryAx`, custom axioms, native oracle, or added premises. A nonempty
coordinate diagnostic also compiles; it is explanatory evidence only.

This is a complete **worker draft**, not accepted solve evidence. The
manager owns the deterministic build/audit, PDF generation, and freeze;
an independent reviewer owns source-bound semantic review. No acceptance
gate, PDF generation, external submission, commit, push, or PR was performed.
The source-order interpretation is the material remaining review issue.
