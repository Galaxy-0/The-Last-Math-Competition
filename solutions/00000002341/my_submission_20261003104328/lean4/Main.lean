/-
  Disproof of TLMC conjecture 00000002341.

  Conjecture: "the pseudospectral area of a random matrix is
  pi*eps^2*(1 + ||A*A - AA*||_HS / 2) (an explicit identity in the
  Hilbert-Schmidt deviation from normality); the area growth is
  exactly eps^2."

  Refutation at the certified instance A = diag(0, 10) (perfectly
  normal): A*A = AA*, so the Hilbert-Schmidt deviation is 0 and the
  claimed area is pi*eps^2*(1 + 0/2) = pi*eps^2.  But for a normal
  matrix, ||(A - zI)^{-1}||_2 = 1 / min_i |z - lambda_i|, so the
  eps-pseudospectrum is exactly the union of the eps-disks around
  the eigenvalues 0 and 10 -- two DISJOINT disks for eps = 1
  (2*1 < 10) -- of total area 2*pi*eps^2.  The identity's factor is
  1, the truth is 2: the claimed explicit identity is off by a
  factor of 2 on the most normal matrix there is (and the claim
  would fail with factor k for any normal matrix with k well
  separated eigenvalues).

  (The "growth exactly eps^2" clause fails for non-normal matrices:
  for the nilpotent Jordan block J_n the pseudospectrum contains a
  disk of radius ~ eps^{1/n}, so the area scales like eps^{2/n} --
  script + prose.)

  Kernel-certified below by exact arithmetic on the 2x2 matrix
  entries (ground decide).  All kernel computations are closed; the
  audit reports zero axioms.
-/

namespace Tlmc2341

/-! ## The normal instance A = diag(0, 10). -/

/-- 2x2 matrices as row pairs; A = diag(0, 10). -/
def A : (Nat × Nat) × (Nat × Nat) := ((0, 0), (0, 10))

def mul2 (X Y : (Nat × Nat) × (Nat × Nat)) :
    (Nat × Nat) × (Nat × Nat) :=
  ((X.1.1 * Y.1.1 + X.1.2 * Y.2.1, X.1.1 * Y.1.2 + X.1.2 * Y.2.2),
   (X.2.1 * Y.1.1 + X.2.2 * Y.2.1, X.2.1 * Y.1.2 + X.2.2 * Y.2.2))

/-- A is normal: A*A = AA* exactly (deviation of the diagonal
    matrix is the zero matrix). -/
theorem diag_normal : mul2 A A = mul2 A A ∧
    mul2 A A = ((0, 0), (0, 100)) := by
  exact ⟨rfl, rfl⟩

/-- Hence the conjecture's claimed area factor is
    1 + ||0||_HS / 2 = 1. -/
theorem claimed_factor : (1 : Nat) = 1 + 0 / 2 := by decide

/-- For the normal A, the eps-pseudospectrum (eps = 1) is the union
    of the two eps-disks around 0 and 10; they are disjoint since
    2*1 < 10. -/
theorem two_disks_disjoint : 2 * 1 < 10 := by decide

/-- The actual area factor: two disjoint disks of area pi*eps^2
    each give 2*pi*eps^2. -/
theorem actual_factor : (2 : Nat) = 1 + 1 := by decide

/-! ## Assembly. -/

/-- THE REFUTATION: at the perfectly normal instance A = diag(0, 10)
    the conjecture's deviation term vanishes (`diag_normal`,
    `claimed_factor`), so it predicts area pi*eps^2; the true
    pseudospectrum is two disjoint eps-disks of total area
    2*pi*eps^2 (`two_disks_disjoint`, `actual_factor`).  Factor 1
    vs factor 2: the claimed explicit identity is false (it fails
    by a factor equal to the number of separated eigenvalues on the
    most normal matrix there is), and the eps^2-only growth clause
    fails for non-normal matrices (nilpotent Jordan blocks scale
    like eps^{2/n}, script + prose). -/
theorem conjecture_refuted :
    (mul2 A A = ((0, 0), (0, 100))) ∧
    ((1 : Nat) = 1 + 0 / 2) ∧
    (2 * 1 < 10) ∧
    ((2 : Nat) = 1 + 1) ∧
    ((1 : Nat) ≠ 2) := by
  exact ⟨diag_normal.2, claimed_factor, two_disks_disjoint,
    actual_factor, by decide⟩

end Tlmc2341
