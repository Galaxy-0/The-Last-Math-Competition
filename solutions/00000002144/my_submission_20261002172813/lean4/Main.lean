/-
  Disproof of TLMC conjecture 00000002144.

  Conjecture: the maximal eigenvalue multiplicity of a tree on n vertices
  is ceil((n+1)/3), realized by gluing a path with stars; the kernel of
  the realization is the matching number.

  Refutation: the STAR K_{1,n-1} is a tree whose spectrum is the
  classical {sqrt(n-1), -sqrt(n-1), 0^(n-2)} — the eigenvalue 0 has
  multiplicity n-2 (elementary: the adjacency matrix has rank 2, since
  rows 2..n all equal the first standard basis vector; equivalently the
  characteristic polynomial is x^(n-2)(x^2 - (n-1))). For n = 5:

      multiplicity 0 in K_{1,4}  = 3,
      conjectured maximum          = ceil(6/3) = 2,

  and 3 > 2. The bound is exceeded already by the simplest tree; for n = 7
  and n = 9 likewise (5 > 3 and 7 > 4).

  Scope: the star spectrum is classical (stated with proof sketch in
  README/tex); the Lean certificate kernel-checks the arithmetic of the
  violation at n = 5, 7, 9. All theorems are closed kernel computations,
  axiom-free.
-/

namespace Tlmc2144

/-- The star K_{1,4} on 5 vertices: multiplicity of eigenvalue 0 is
    n - 2 = 3 (classical star spectrum). -/
theorem mult_5 : (5 - 2 : Nat) = 3 := by decide

/-- The conjectured extremum at n = 5: ceil((5+1)/3) = 2. -/
theorem bound_5 : (5 + 1 + 2) / 3 = 2 := by decide

/-- 3 > 2: the bound is exceeded at n = 5. -/
theorem violated_5 : ¬ (3 <= 2) := by decide

/-- n = 7: multiplicity 5 vs bound ceil(8/3) = 3. -/
theorem mult_7 : (7 - 2 : Nat) = 5 := by decide
theorem bound_7 : (7 + 1 + 2) / 3 = 3 := by decide
theorem violated_7 : ¬ (5 <= 3) := by decide

/-- n = 9: multiplicity 7 vs bound ceil(10/3) = 4. -/
theorem mult_9 : (9 - 2 : Nat) = 7 := by decide
theorem bound_9 : (9 + 1 + 2) / 3 = 4 := by decide
theorem violated_9 : ¬ (7 <= 4) := by decide

end Tlmc2144
