# Disproof of TLMC Conjecture 00000001136

**Definition and conjecture (verbatim from `conjectures/00000001136.md`).** "Definition: Complete intersection property of Bott–Samelson varieties means some power of the canonical bundle is very ample and the cohomology ring is completely determined by Chern classes. Conjecture: BS(s₁,…,s_k) is Gorenstein if and only if each letter of the word s₁…s_k occurs equally often; and in the Gorenstein case, the shift of the dualizing sheaf is given by reversal of the word."

**Verdict: DISPROVED.**

## Counterexample

Take the reduced word `w = s₁s₂s₁`, which is the longest element `w₀` of the symmetric
group `S₃`:

* the word is **reduced**: it evaluates to `w₀ = (3,2,1)` and its length `3` equals the
  Coxeter length of `w₀` (the number of inversions, also `3`);
* the letter counts are **unequal**: `s₁` occurs `2` times, `s₂` occurs `1` time
  (`2 ≠ 1`);
* yet `BS(s₁,s₂,s₁)` **is Gorenstein**: for a reduced word, `BS(s₁,…,s_k)` is an
  iterated `ℙ¹`-bundle (Demazure, *Désingularisation des variétés de Schubert
  généralisées*, Ann. Sci. ENS 7 (1974)), hence smooth and projective; smoothness
  means all local rings are regular, and regular local rings are Gorenstein
  (standard commutative algebra, e.g. Matsumura, *Commutative Ring Theory*, §19).

So `BS(s₁,s₂,s₁)` is Gorenstein while its letters do **not** occur equally often —
the "only if" direction of the conjecture fails, and the conjecture is false.

**Robustness.** An exhaustive search in `S₃` shows `w₀` has exactly two reduced
expressions, `s₁s₂s₁` and `s₂s₁s₂`, with counts `(2,1)` and `(1,2)`; no rewording of
`w₀` satisfies the conjecture's condition. (Since *every* Bott–Samelson variety is
smooth hence Gorenstein, the "if and only if" would in fact force **every** word to
have equally often occurring letters — plainly false already in `S₃`.)

With the "iff" dead, the claimed "reversal of the word" description of the dualizing
shift is moot for this conjecture (for a smooth variety the dualizing sheaf is simply
the canonical bundle).

## Files

* `reproduce.py` — recomputes every number: evaluation `s₁s₂s₁ = w₀`, reducedness
  (length = inversion count = 3), letter counts `(2,1)`, and the exhaustive list of
  reduced expressions of `w₀` in `S₃`. Run `python3 reproduce.py`.
* `main.tex` — short note; compile with `tectonic main.tex`.
* `lean4/Main.lean` — bare-core Lean 4 formalization (no Mathlib, no `sorry`):
  `S₃` and the word are concrete `Nat`-valued data; the geometric input is the
  abstract predicate `G` with the classical hypothesis `∀ w, G w` (smoothness ⇒
  Gorenstein for every Bott–Samelson variety); `conjecture_1136_false` derives
  `¬(∀ w, G w ↔ EqualCounts w)` from the witness `w = s₁s₂s₁`.
* `lean4/Check.lean` — `#print axioms` audit of every theorem.

## Reproduction

```bash
python3 reproduce.py
cd lean4 && lake build && lake env lean Check.lean
```

## Axiom audit

All six theorems (`counts_s1`, `counts_s2`, `counts_not_equal`, `word_eval_w0`,
`word_reduced`, `conjecture_1136_false`) are axiom-free: they depend on no axioms
whatsoever (no `sorry`, no `Classical.choice`, no `propext`, no `Quot.sound`).
