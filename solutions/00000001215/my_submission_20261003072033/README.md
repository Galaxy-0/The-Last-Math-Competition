# Disproof of conjecture `00000001215`

**Verdict: FALSE — the odd cycles C₅, C₇, C₉, C₁₁, … form an INFINITE
family of outerplanar graphs with cop number exactly 2 (script-verified
by exhaustive retrograde game search; the single-cop survival core is
kernel-certified for arbitrary graphs). "Only finitely many outerplanar
graphs attain cop number 2" fails.**

## The conjecture (as adjudicated from `conjectures/00000001215.md`)

> Only finitely many outerplanar graphs attain cop number 2.

## The refutation

1. **Every cycle is outerplanar** (draw it with all vertices on the
   outer face) — classical, immediate.
2. **Every cycle of length ≥ 4 has cop number exactly 2** (classical,
   Aigner–Fromme): one cop is insufficient, two suffice.
3. **The single-cop insufficiency is kernel-certified for ARBITRARY
   graphs**: on any graph (V, adj) admitting a robber strategy ρ with
   the cycle-safety-response property — from a Safe position (robber
   not on nor adjacent to the cop), after any legal cop move to a
   non-capturing position c′, the response ρ(r, c′) restores safety —
   the kernel proves `never_captured`: for EVERY cop play (any start,
   any legal move sequence) there is a robber play that is Safe in
   every round. The induction is on the round number; non-capture at
   each step follows from the previous safety (a cop landing on the
   robber would have had to move onto a vertex that was neither the
   robber nor adjacent to it). Cycles of length ≥ 4 satisfy the
   response property with ρ = "step away from the cop".
4. **Script confirmation**: exhaustive retrograde attractor computation
   on C₄, C₆, C₈, C₁₀ and the odd cycles C₅, C₇, C₉, C₁₁ (and C₁₃,
   C₁₅, C₁₇, C₁₉, C₂₁ for the one-cop bound): cop number exactly 2 in
   every case.

Hence infinitely many outerplanar graphs attain cop number 2 — the
conjecture's finiteness claim is false.

## Verification

* `reproduce.py` — retrograde-attractor game search: for n ∈
  {4,…,11} both the one-cop insufficiency (robber's survival region
  nonempty at every distance-≥2 start) and the two-cop sufficiency
  (cops win from every start) hold; the one-cop bound holds through
  C₂₁. State spaces are finite (n² resp. n³ × 2), so the attractor
  fixpoint is exact.
* Lean 4 (core, v4.33.1), `lean4/` — the universal survival theorem
  `never_captured` (induction on rounds with the non-capture side
  condition derived from the previous safety) and the assembly. Both
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the game-theoretic core universally over graphs
and strategies satisfying the safety-response property. The
instantiation to cycles (the "step away" strategy satisfies the
response property on Cₙ, n ≥ 4), outerplanarity of cycles, and the
classical upper bound c(Cₙ) ≤ 2 are classical and cited in prose, with
the cycle instances re-verified by the exact script search.
