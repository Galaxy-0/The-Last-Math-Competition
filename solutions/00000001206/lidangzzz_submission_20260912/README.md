# Solution to Conjecture TLMC-00000001206 (nim-sum period law)

**Status: PROVED (unconditional, elementary). Machine-verified in Lean 4.**

Conjecture (conjectures/00000001206.md): the period of the pointwise nim-sum
of two periodic Grundy sequences divides the lcm of the two periods.

## Contents

- `main.tex` / `main.pdf` — complete self-contained mathematical proof
  (definitions, three lemmas, theorem, corollary deriving the conjecture;
  remark that the argument works for any pointwise binary operation).
- `NimSumPeriod.lean` — Lean 4 formalization: `conjecture1206_true` proves
  the faithful statement for all ℕ-valued periodic sequences (Grundy
  sequences are ℕ-valued, so the conjecture follows a fortiori); in fact
  `pointwise_period_dvd` proves it for an arbitrary binary operation.
- `lean_project/` — standalone lake project (toolchain
  `leanprover/lean4:v4.31.0`, Mathlib `v4.31.0`): `lake build` succeeds.
- `Verify1206.lean` — verification suite (submission file + tests +
  `#print axioms`); not part of the built library.

## Verification record (2026-09-12)

All of the following were executed and passed:

1. **Compilation**: `lake env lean NimSumPeriod.lean` — exit code 0 and
   **zero bytes of output** (zero errors, zero warnings).
   Compiler: Lean 4.31.0 (arm64), Mathlib v4.31.0.
2. **Standalone build**: `lake build` in `lean_project/` —
   `Build completed successfully (8559 jobs)` against a local Mathlib
   cache; on a fresh machine run `lake exe cache get && lake build`.
3. **No unproved goals**: the only occurrence of "sorry" in the sources is
   the phrase "no `sorry`" in the header comment; there is no `admit`,
   no `native_decide`, no custom `axiom` declaration.
4. **Axiom audit**: `#print axioms` reports both `conjecture1206_true` and
   `nimsum_period` depend only on `[propext, Classical.choice,
   Quot.sound]` — the standard axiom base of Mathlib; in particular no
   `sorryAx`.
5. **Non-vacuity and definitional sanity** (machine-checked in
   `Verify1206.lean`):
   - the theorem's hypotheses are satisfiable (parity sequence, period 2;
     mod-3 sequence, period 3);
   - `minPeriod (fun _ => 7) = 1` (constant sequence);
   - `minPeriod (fun n => n % 2) = 2` (parity);
   - **sharpness**: `minPeriod (fun n => n % 2 ^^^ n % 3) = 6`,
     exactly `lcm 2 3`, so the divisibility bound of the theorem is
     attained and no strengthening is possible in general;
   - the theorem instance `minPeriod (n % 2 ^^^ n % 3) ∣ lcm 2 3`.

## Scope of the machine guarantee

Machine-checked: the Lean statement `conjecture1206` as written, and hence
the theorem for every ℕ-valued periodic sequence and any binary operation.
Argued mathematically (in `main.tex` §4), not machine-checked: the reading
of the English/Chinese conjecture into that statement (the Lean version is
strictly stronger on the sequence side, since Grundy sequences are a subset
of ℕ-valued sequences). Trusted infrastructure: the Lean 4 kernel and
Mathlib v4.31.0 (community standard).

## Proof idea

1. Multiples of a period are periods (induction).
2. lcm(p₁, p₂) is a period of the pointwise nim-sum (it is a common
   multiple of both periods).
3. The minimal period of a one-sided periodic sequence divides every
   period (Euclidean division; the remainder would be a smaller positive
   period, contradicting minimality).

Hence π(nim-sum) | lcm(p₁, p₂).
