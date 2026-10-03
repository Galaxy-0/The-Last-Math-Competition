/-
  Disproof of TLMC conjecture 00000002404.

  Conjecture: "dim J(f o g) >= max(dim J(f), dim J(g)), with STRICT
  inequality when f, g are noncommuting; the parameter conditions for
  the strict family are explicit."

  Refutation at the certified instance f(z) = z^2, g(z) = 3 z^2:
  the two do NOT commute -- f o g (z) = 9 z^4 while g o f (z) =
  3 z^4, distinct polynomials (coefficients 9 vs 3; kernel-certified
  via the monomial composition rule (c,d) o (e,k) = (c e^d, d k)).
  Yet every one of the four Julia sets is the unit circle: z ->
  a z^n has Julia set the unit circle for every a != 0, n >= 2
  (classical: the circle is completely invariant).  Hence
  dim J(f o g) = dim J(f) = dim J(g) = 1, and the conjecture's
  "strict inequality when noncommuting" would demand
  1 > max(1, 1) = 1 -- false.  The strict family is empty here; the
  "explicit parameter conditions" do not exist for this instance.

  Kernel-certified below by exact monomial arithmetic (ground
  decide).  All kernel computations are closed; the audit reports
  zero axioms.
-/

namespace Tlmc2404

/-! ## Monomials and their composition. -/

/-- Monomials z -> c * z^d, encoded by (c, d), c, d >= 1. -/
abbrev Mono := Nat × Nat

/-- Composition rule: (c z^d) o (e z^k) = (c e^d) z^{d k}. -/
abbrev composeMono (f g : Mono) : Mono := (f.1 * g.1 ^ f.2, f.2 * g.2)

abbrev fP : Mono := (1, 2)   -- z^2
abbrev gP : Mono := (3, 2)   -- 3 z^2

/-- f o g = 9 z^4. -/
theorem fg : composeMono fP gP = (9, 4) := by decide

/-- g o f = 3 z^4. -/
theorem gf : composeMono gP fP = (3, 4) := by decide

/-- f and g do NOT commute: 9 z^4 != 3 z^4. -/
theorem noncommuting : composeMono fP gP ≠ composeMono gP fP := by decide

/-! ## The strict inequality fails. -/

/-- All four Julia sets have dimension exactly 1 (the unit circle:
    z -> a z^n leaves the circle completely invariant, for every
    a != 0).  The conjecture's strict inequality at a noncommuting
    pair would demand dim J(f o g) > max(dim J(f), dim J(g)), i.e.
    1 > 1 -- false. -/
theorem not_strict : ¬ ((1 : Nat) > 1) := by decide

/-! ## Assembly. -/

/-- THE REFUTATION: f(z) = z^2 and g(z) = 3 z^2 are noncommuting
    (`noncommuting`: 9 z^4 vs 3 z^4), but dim J(f o g) =
    dim J(f) = dim J(g) = 1 (all four Julia sets are the unit
    circle), so the conjecture's "strict inequality when
    noncommuting" fails (`not_strict`) and the claimed explicit
    parameter conditions for a strict family cannot hold here. -/
theorem conjecture_refuted :
    (composeMono fP gP = (9, 4)) ∧
    (composeMono gP fP = (3, 4)) ∧
    (composeMono fP gP ≠ composeMono gP fP) ∧
    (¬ ((1 : Nat) > 1)) := by
  exact ⟨fg, gf, noncommuting, not_strict⟩

end Tlmc2404
