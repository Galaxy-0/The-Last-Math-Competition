# Solution Review — Conjecture 00000004294 (PR 336)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003104000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — "the classes of abelian groups for which the subgroup lattice is a complete invariant are exactly the class of prime-power-order groups together with the class of rank-1 torsion-free groups"; submission refutes the prime-power clause with C2 vs C3.
- LaTeX: compiled ok (pdflatex x2, exit 0, 0 errors, 2 pages); shipped main.pdf is a real PDF v1.5, 2 pages, 35 KB, hash matches verification.json.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, "Build completed successfully", warnings-as-errors enabled; toolchain v4.19.0; no warnings.
- Forbidden content: none — no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `@[implemented_by]`, `extern`. Final theorems depend only on [propext, Quot.sound].
- Auxiliary code: none shipped (verification.json: auxiliary_scripts_rerun: []). All recorded SHA256 hashes match the on-disk files, including Main.lean = proof_source_sha256.
- Folder name: `gaochengzhecpu_submission_20261003104000` — matches the pattern.
## Semantic audit
Complete invariant on a class K means: for G, H ∈ K, isomorphic invariants imply isomorphic groups. The conjecture asserts this for K = prime-power-order abelian groups (prime allowed to vary — "the class of prime-power-order groups" / 素幂阶群之类; the union with rank-1 torsion-free groups is irrelevant to the refutation). Key Lean definitions, all faithful:
- `AbelianGroupData (Fin 2)` / `(Fin 3)`: actual mod-2 / mod-3 addition, all abelian group laws kernel-decided.
- `Prime p := 2 ≤ p ∧ ∀ d ∣ p, d = 1 ∨ d = p`; `HasPrimePowerOrder A := ∃ p e, Prime p ∧ 0 < e ∧ Nonempty (Bijection A (Fin (p^e)))` — C2 = 2^1 and C3 = 3^1 both qualify (`order2_prime_power`, `order3_prime_power` with real bijections).
- `Subgroup D` = arbitrary Prop-valued carrier closed under 0/+/− (NO finite coding); `subgroup2_membership`/`subgroup3_membership` prove the exact classification x ∈ K ↔ x = 0 ∨ 1 ∈ K for EVERY subgroup — so the lattices are the genuine 2-element subgroup lattices.
- Lattice structure: `meet` = intersection predicate, `join` = intersection of all subgroups containing both (generated subgroup); `SubgroupOrderIso` = mutually inverse maps on the whole subgroup types with `order_iff : Included (f H) (f K) ↔ Included H K`; generic theorems `orderIso_preserves_meet` / `orderIso_preserves_join` then give lattice-isomorphism status.
- `GroupIso` = bijection + additivity; `groups_not_isomorphic` rules out every iso (no injection Fin 3 → Fin 2, pigeonhole).
Final theorems:
- `subgroupLatticesIso : SubgroupOrderIso group2 group3` (via the flag maps {0}↦{0}, G↦H, with `to2_to3`, `to3_to2`, `to3_order` all proved from the classification)
- `groups_not_isomorphic : ¬ Nonempty (GroupIso group2 group3)`
- `conjecture04294_false : ¬ PrimePowerLatticeCompleteness` where `PrimePowerLatticeCompleteness : ∀ (A B : Type) (D : AbelianGroupData A) (E : AbelianGroupData B), HasPrimePowerOrder A → HasPrimePowerOrder B → Nonempty (SubgroupOrderIso D E) → Nonempty (GroupIso D E)`.
Both groups satisfy the conjecture's class hypothesis (abelian, prime-power order), their subgroup lattices are genuinely isomorphic (both are the two-element chain; iso proved over ALL subgroups, with meet/join preservation), yet the groups are not isomorphic (cardinalities 2 and 3). This contradicts the conjecture's "exactly the class of prime-power-order groups" claim under its natural reading. Non-vacuous: the subgroup lattices, the lattice isomorphism, and the group isomorphism are the conjecture's actual objects. LaTeX matches Lean (same C2/C3, same two-element chain, same theorem names).
## Issues found
- Interpretation-dependent (non-blocking): the refutation requires the prime to vary across the class, which is the plain reading of both language versions ("the class of prime-power-order groups" / 素幂阶群之类). The submission itself flags that it does NOT refute the different fixed-p assertion (comparing only p-groups for one common p). SOURCE.md states this scope honestly.
## Verdict rationale
Clean fresh build with warnings-as-errors and standard axioms only, LaTeX compiles to the matching PDF, hashes all verified, and the Lean formalization quantifies over all actual subgroups and constructs a real order/lattice isomorphism between the subgroup lattices of C2 and C3 together with a proof that no group isomorphism exists. Both groups are prime-power-order abelian groups as the conjecture states, so the conjecture's complete-invariant claim for that class is genuinely refuted under its natural reading.

## Disposition
APPROVED — merged into main (PR 336). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
