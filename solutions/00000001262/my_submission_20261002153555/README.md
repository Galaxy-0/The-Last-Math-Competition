# Disproof of Conjecture 00000001262

**Verdict: FALSE.**

## The conjecture (quoted verbatim from the statement)

> Definition: Abelian complexity. Conjecture: The abelian complexity of balanced
> periodic words is eventually constant, equal to the alphabet size (the abelian
> constant class).

That is: for every balanced periodic word w over an alphabet of size q, there
should exist N with ω(n) = q for all n ≥ N, where ω(n) = the number of distinct
Parikh vectors (letter-multiplicity vectors) of length-n windows of w.

## The counterexample in one paragraph

Take the balanced periodic word **w = (aab)^∞** over {a, b}, so q = 2. Every
length-n window contains either ⌊2n/3⌋ or ⌈2n/3⌉ letters a (shifting a window by
one changes the a-count by at most 1, and shifting by 3 is a cyclic permutation
of the period, hence changes nothing), so w **is balanced**, and it is periodic
by construction. Its abelian complexity is determined by the residue of n mod 3:
a length-3k window is always a cyclic permutation of (aab)^k and therefore has
the *single* Parikh vector (2k, k), while lengths 3k+1 and 3k+2 each admit
exactly two Parikh vectors. Hence

    ω(3k) = 1,   ω(3k+1) = 2,   ω(3k+2) = 2     for all k ≥ 0,

i.e. the sequence is the periodic pattern 2, 2, 1, 2, 2, 1, ... It hits 1 at
n = 3, 6, 9, ... — arbitrarily far out — so it is **not** eventually constant,
and in particular not eventually equal to the alphabet size 2. One balanced
periodic word suffices to refute the conjecture.

## What is formally proved (Lean 4, core only, zero axioms, zero `sorry`)

Namespace `Tlmc1262` (toolchain `leanprover/lean4:v4.33.1`, no Mathlib):

- The word is a function `ch : Nat → Nat` (`1` = a, `0` = b, with `b` exactly in
  phase 2). 3-periodicity `ch (s+1+1+1) = ch s` (`ch_shift`) is derived by pure
  structural recursion through an explicit 3-phase clock (`cycle`, `ph`), because
  the core library's `%` lemmas depend on `propext` and the package must be
  axiom-free.
- `A s n` counts the letters a in the length-n window starting at `s`; Parikh
  vectors of equal-length windows are equal iff their `A`-values are equal.
- `A_shift3 : ∀ n s, A (s+1+1+1) n = A s n` (cyclic permutation) and
  `A_shiftQ : ∀ q r n, A (3*q + r) n = A r n` (faithfulness of the three
  residue-class starts: every window start is `3*q + r` by Euclidean division).
- `A0_triple / A1_triple / A2_triple : ∀ k, A i (3*k) = 2*k` for `i = 0, 1, 2`.
- **`omega_triple : ∀ k, omega (3 * k) = 1`** — the full universal statement,
  not a finite enumeration. Every length-3k window is a cyclic permutation of
  `(aab)^k`, so all Parikh vectors coincide.
- `omega_triple_succ : ∀ k, omega (3*k + 1) = 2` and
  `omega_triple_succ2 : ∀ k, omega (3*k + 2) = 2` — the word *would* satisfy the
  conjectured value at the other two residues, isolating exactly where it breaks.
- **`not_eventually_two : ¬ (∃ N, ∀ n ≥ N, omega n = 2)`** — the formal negation
  of the conjecture's "eventually constant equal to alphabet size" for this
  word: given any N, take n = 3*(N+1) ≥ N and `omega_triple` forces ω(n) = 1 ≠ 2.
- Sanity anchors `omega 1 = 2`, `omega 2 = 2`, `omega 3 = 1` (kernel-computed).

`Check.lean` re-audits all 27 theorems with `#print axioms` and with a Lean
metaprogram that **throws if any theorem depends on any axiom**: the audit
passes with zero axioms (no `propext`, no `Classical.choice`, no `Quot.sound`,
no `sorryAx`).

## Contents

- `main.tex`, `build/main.pdf` — formal write-up: definition of abelian
  complexity, balance and periodicity of (aab)^∞, the residue-class count
  (2k,k) / (2k+1,2k+1,2k) / (2k+2,2k+1,2k+1), the ω table, and the refutation.
- `reproduce.py` — standalone script (pure standard library, no absolute paths):
  enumerates all windows of (aab)^∞ up to n = 60, recomputes ω(n), checks the
  pattern ω(3k)=1, ω(3k+1)=ω(3k+2)=2, checks balancedness (per-length a-counts
  differ by at most 1) and periodicity, and re-verifies the limit negation by
  exhibiting, for every N in a range, an n ≥ N with ω(n) ≠ 2.
- `lean4/` — Lean 4 project (`lake build`; then `lake env lean Check.lean`).

Run: `python3 reproduce.py`, and in `lean4/`: `lake build && lake env lean Check.lean`.

## Scope of the refutation

The conjecture quantifies over all balanced periodic words; a single
counterexample refutes it, and the formalization proves the counterexample's
properties **universally in k** (∀ k, ω(3k) = 1) together with the limit
negation — no finite witness stands in for an infinite statement anywhere.
