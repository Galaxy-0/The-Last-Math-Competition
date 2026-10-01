# Disproof of TLMC conjecture 00000000477

**Verdict: FALSE.**

## The conjecture

For promotion on the set `LE(P)` of linear extensions of a finite poset `P`,
the lcm of the promotion orbit lengths divides `#LE(P)` (a divisibility
motivated by homomesy).

## The attack

Counterexample: the Ferrers poset of the Young diagram of shape `(3, 2)`.

- `#LE(P) = 5`: linear extensions of this poset are exactly the standard Young
  tableaux of shape `(3,2)`, and there are 5 (hook length formula:
  `5!/(4*3*1*2*1) = 120/24 = 5`). Confirmed by brute-force enumeration of all
  `5! = 120` cell orderings in `reproduce.py` and by kernel enumeration of all
  `5^5` candidate tuples in `lean4/Main.lean`.
- Promotion (Schutzenberger, jeu de taquin) acts on the 5 tableaux as
  `t1 -> t3 -> t4 -> t1` and `t2 -> t5 -> t2`: two orbits, of lengths **3** and
  **2**.
- `lcm(3, 2) = 6`, and `6` does **not** divide `5`.

Hence the conjecture's divisibility fails: `lcm(orbit lengths) = 6 > 5 =
#LE(P)`, so it cannot divide it.

## Files

- `main.tex`, `build/main.pdf` — write-up (verdict, counterexample, orbits, boundary).
- `build/log.txt` — tectonic build log.
- `reproduce.py` — independent recomputation:
  `python3 reproduce.py` prints `#LE = 5`, orbit lengths `[2, 3]`, `lcm = 6`,
  `divides? False`, and asserts each of these.
- `lean4/` — core Lean 4 certificate (no Mathlib, toolchain
  `leanprover/lean4:v4.33.1`). Build and audit:
  ```sh
  cd lean4 && lake build && lake env lean Check.lean
  ```
  Every `#print axioms` in the audit reports **does not depend on any axioms**
  (no `propext`, no `Quot.sound`, no `Classical.choice`); no `sorry`.

## Boundary of the result

- The refutation is a single explicit poset; it falsifies the universal claim.
  Nothing is claimed about posets where divisibility may hold.
- The counterexample is minimal in an interesting way: `3 + 2 = 5 = #LE(P)`,
  i.e. the orbit decomposition of the whole extension set is `3 + 2`, but the
  lcm of the two orbit lengths exceeds the total. The obstruction is that
  promotion orbits on a non-rectangular shape need not be uniform.
- Known contrast: for rectangular shapes promotion is unipotent/single-orbit
  (Haiman; Reiner-Stanton-White cyclic sieving framework), which is the case
  the homomesy literature most often relies on; the conjecture overreached by
  extending divisibility to arbitrary posets.
