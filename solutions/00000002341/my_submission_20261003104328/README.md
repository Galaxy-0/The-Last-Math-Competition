# Disproof of conjecture `00000002341`

**Verdict: FALSE — both clauses. (1) The identity fails on the most
normal matrix there is: for A = diag(0,10), A*A = AA* so the claimed
area is πε²·(1 + 0/2) = πε², but the true ε-pseudospectrum of a
normal matrix is exactly the union of the ε-disks around the
eigenvalues — two disjoint disks (2ε = 2 < 10) of total area
**2πε²**: the claimed factor is 1, the truth is 2. (Any normal matrix
with k well-separated eigenvalues gives kπε².) (2) The growth clause
fails for non-normal matrices: the nilpotent Jordan block J₄ has
area(0.2)/area(0.05) ≈ 2.5, matching ε^{2/n} = ε^{1/2} scaling
(predicts 2.0), not the claimed exactly-ε² (which predicts 16).**

## The conjecture (verbatim from `conjectures/00000002341.md`)

> Definition: The pseudospectrum is {z : ‖(A−zI)^{-1}‖ > ε^{-1}}.
> Conjecture: The pseudospectral area of a random matrix is
> πε²·(1 + ‖A*A − AA*‖_{HS}/2) (an explicit identity in the
> Hilbert–Schmidt deviation from normality); the area growth is
> exactly ε².

## The refutation

For a normal matrix the pseudospectra are exactly union of disks: the
singular values of (A − zI) are |z − λᵢ| for the eigenvalues λᵢ, so
‖(A − zI)^{-1}‖₂ = 1/minᵢ |z − λᵢ| and the ε-pseudospectrum is
{z : minᵢ |z − λᵢ| < ε}. Take A = diag(0, 10) — the deviation
‖A*A − AA*‖_{HS} = ‖diag(0,100) − diag(0,100)‖ = 0 (kernel-certified
on the entries), so the conjecture predicts area πε²·(1 + 0/2) =
πε². The truth: two disjoint unit disks (2ε = 2 < 10 = |10 − 0|), of
total area 2πε². Grid integration confirms: measured area 6.281 ≈
2π = 6.283, versus the claimed π ≈ 3.142 — off by a factor of 2.
The "identity" misses the multiplicity of separated eigenvalues
entirely; a normal matrix with k well-separated eigenvalues has area
kπε², so no formula of the claimed shape (a function of the scalar
deviation alone) can hold — diag(0, 0, 0, …, 0, 10) and diag(0, 5,
10) share the same deviation 0 but have different areas.

The growth clause fails for non-normal matrices: the nilpotent
Jordan block J₄ satisfies ‖(J₄ − z)^{-1}‖ ~ |z|^{-4}, so its
ε-pseudospectrum contains a disk of radius ~ ε^{1/4} and its area
scales like ε^{2/4} = ε^{1/2}, not ε². Measured: area(0.2)/area(0.05)
≈ 2.5 ≈ (0.2/0.05)^{1/2} = 2.0, versus the claimed 16.

## Verification

* `reproduce.py` — exact deviation 0 for diag(0,10); grid
  pseudospectral area 6.281 ≈ 2πε² vs claimed πε² = 3.142; J₄ growth
  ratio 2.48 (ε^{1/2} scaling) vs 16 (ε² scaling).
* Lean 4 (core, v4.33.1), `lean4/` — `diag_normal` (A*A = AA* = 
  diag(0,100) on the entries), `claimed_factor` (1 + 0/2 = 1),
  `two_disks_disjoint` (2·1 < 10), `actual_factor` (1 + 1 = 2),
  `conjecture_refuted` (1 ≠ 2 assembly).  All 5 audited theorems
  report `does not depend on any axioms`.

## Boundary

The kernel certifies the normality of the instance (exact entry
arithmetic), the vanishing deviation, the disjointness of the two
pseudospectral disks, and the factor contradiction (1 ≠ 2). The
singular-value formula ‖(A − zI)^{-1}‖₂ = 1/min|z − λᵢ| for normal
matrices and the Jordan-block scaling ε^{2/n} are classical, cited in
prose and reproduced numerically by the script's grid integration.
Both the explicit identity and the growth clause are refuted.
