import Mathlib

/-!
# Conjecture 00000001012: the subdegrees of PSL(n, q) acting on PG(n - 1, q)

Let `F` be a finite field with `q` elements and `n ≥ 2`.  The group
`PSL(n, F) = SL(n, F) / Z(SL(n, F))` (Mathlib's `Matrix.ProjectiveSpecialLinearGroup`) acts
on the point set of the projective space `PG(n - 1, F) = ℙ F (Fin n → F)` (the lines of
`F^n`), through Mathlib's action of `SL(n, F)` on lines.

The *subdegrees* of a transitive permutation group are the sizes of the orbits of a point
stabilizer.  We prove that for every point `p` the stabilizer `Stab(p)` has exactly two
orbits, namely `{p}` and the set of all other points, so that the subdegrees are exactly
`1` and `(q ^ n - q) / (q - 1)`.  The key input is Mathlib's theorem that `SL(n, F)` acts
2-transitively on the projective space (`Projectivization.specialLinearGroup_is_two_pretransitive`
and its matrix version), which passes to PSL because PSL acts through SL.
-/

open MulAction Projectivization
open scoped LinearAlgebra.Projectivization

namespace Conjecture1012

/-- The projective special linear group `PSL(n, F) = SL(n, F) / Z(SL(n, F))`. -/
abbrev PSL (n : ℕ) (F : Type*) [Field F] :=
  Matrix.ProjectiveSpecialLinearGroup (Fin n) F

/-- The point set of the projective space `PG(n - 1, F)`: the one-dimensional subspaces
of `F ^ n`. -/
abbrev PG (n : ℕ) (F : Type*) [Field F] := ℙ F (Fin n → F)

variable {F : Type*} [Field F] {n : ℕ}

/-- The action of `PSL(n, F)` on points is the action of any lift in `SL(n, F)`. -/
theorem psl_smul_eq (g : Matrix.SpecialLinearGroup (Fin n) F) (x : PG n F) :
    (g : PSL n F) • x = g • x :=
  Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk g x

/-- `PSL(n, F)` acts 2-transitively on the points of `PG(n - 1, F)`. -/
theorem psl_two_transitive {a b c d : PG n F} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : PSL n F, g • a = c ∧ g • b = d := by
  obtain ⟨g, h1, h2⟩ := (is_two_pretransitive_iff.mp (inferInstance :
    IsMultiplyPretransitive (Matrix.SpecialLinearGroup (Fin n) F) (PG n F) 2)) hab hcd
  exact ⟨g, by rw [psl_smul_eq]; exact h1, by rw [psl_smul_eq]; exact h2⟩

/-- The orbit of `p` under its own stabilizer is `{p}`. -/
theorem orbit_stabilizer_self (p : PG n F) :
    orbit (stabilizer (PSL n F) p) p = {p} := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    exact Set.mem_singleton_iff.mpr (mem_stabilizer_iff.mp h.2)
  · intro hx
    rw [Set.mem_singleton_iff.mp hx]
    exact mem_orbit_self p

/-- The orbit of a point `x ≠ p` under `Stab(p)` is the set of all points other than `p`. -/
theorem orbit_stabilizer_of_ne (p x : PG n F) (hx : x ≠ p) :
    orbit (stabilizer (PSL n F) p) x = {p}ᶜ := by
  ext y
  constructor
  · rintro ⟨h, rfl⟩ hy
    have h2 : (h : PSL n F) • p = p := mem_stabilizer_iff.mp h.2
    have h3 : (h : PSL n F) • x = (h : PSL n F) • p := by
      rw [h2]; exact Set.mem_singleton_iff.mp hy
    exact hx (smul_left_cancel _ h3)
  · intro hy
    obtain ⟨g, hg1, hg2⟩ := psl_two_transitive (a := p) (b := x) (c := p) (d := y)
      (Ne.symm hx) (Ne.symm hy)
    exact ⟨⟨g, hg1⟩, hg2⟩

variable [Fintype F]

/-- Point count of `PG(n - 1, q)` in the form `q ^ n = N (q - 1) + 1`. -/
theorem pow_eq_card_points (n : ℕ) :
    Fintype.card F ^ n = Nat.card (PG n F) * (Fintype.card F - 1) + 1 := by
  have h := Projectivization.card' (k := F) (V := Fin n → F)
  simpa [Nat.card_fun, Nat.card_eq_fintype_card] using h

/-- Elementary arithmetic: if `q ^ n = N (q - 1) + 1` with `q ≥ 2`, `n ≥ 2`, then `N ≥ 3` and
`N - 1 = (q ^ n - q) / (q - 1)`, the division being exact. -/
theorem arith {q n N : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) (h : q ^ n = N * (q - 1) + 1) :
    3 ≤ N ∧ N - 1 = (q ^ n - q) / (q - 1) ∧ (q - 1) * ((q ^ n - q) / (q - 1)) = q ^ n - q := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have hsq : (r + 2) ^ 2 ≤ (r + 2) ^ n := Nat.pow_le_pow_right (by omega) hn
  have h1 : r + 2 - 1 = r + 1 := by omega
  rw [h1] at h
  have hN : 3 ≤ N := by
    by_contra hc
    have : N ≤ 2 := by omega
    have : N * (r + 1) ≤ 2 * (r + 1) := Nat.mul_le_mul_right _ this
    nlinarith
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h4 : (r + 2) ^ n - (r + 2) = M * (r + 1) := by
    apply Nat.sub_eq_of_eq_add
    rw [h]; ring
  refine ⟨hN, ?_, ?_⟩
  · rw [h1, h4, Nat.mul_div_cancel _ (by omega)]
    simp
  · rw [h1, h4, Nat.mul_div_cancel _ (by omega)]
    ring

/-- The number of points of `PG(n - 1, q)` is `(q ^ n - 1) / (q - 1)`. -/
theorem card_points (n : ℕ) :
    Nat.card (PG n F) = (Fintype.card F ^ n - 1) / (Fintype.card F - 1) := by
  have h := Projectivization.card'' F (Fin n → F)
  simpa [Nat.card_fun, Nat.card_eq_fintype_card] using h

/-- Cardinality of the complement of a point. -/
theorem card_compl_point (p : PG n F) :
    Nat.card ({p}ᶜ : Set (PG n F)) = Nat.card (PG n F) - 1 := by
  rw [Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton]

/-- The nontrivial subdegree `(q ^ n - q) / (q - 1)` is at least `2`, so it differs from `1`. -/
theorem subdegree_ge_two (hn : 2 ≤ n) :
    2 ≤ (Fintype.card F ^ n - Fintype.card F) / (Fintype.card F - 1) := by
  have hq : 2 ≤ Fintype.card F := Nat.succ_le_of_lt Fintype.one_lt_card
  obtain ⟨h3, h4, -⟩ := arith hq hn (pow_eq_card_points (F := F) n)
  omega

/-- Why `n ≥ 2` is needed: `PG(0, q)` has a single point, so there is no nontrivial
subdegree when `n = 1`. -/
theorem card_points_one : Nat.card (PG 1 F) = 1 := by
  have hq : 2 ≤ Fintype.card F := Nat.succ_le_of_lt Fintype.one_lt_card
  rw [card_points, pow_one, Nat.div_self (by omega)]

/-- **Main theorem (conjecture 00000001012).**  Let `F` be a finite field with `q` elements,
`n ≥ 2`, and let `PSL(n, q)` act on the point set of `PG(n - 1, q)`.  Then:
1. the action is transitive and faithful;
2. for every point `p`, the orbits of the stabilizer `Stab(p)` are exactly `{p}` and the set
   of the remaining points, and these are two different orbits (so there are exactly two);
3. these orbits have sizes `1` and `(q ^ n - q) / (q - 1)` respectively; the division is
   exact, and the latter equals (number of points) `- 1 = (q ^ n - 1) / (q - 1) - 1`;
4. hence the set of subdegrees is exactly `{1, (q ^ n - q) / (q - 1)}`, two distinct
   numbers. -/
theorem subdegrees_PSL (hn : 2 ≤ n) (p : PG n F) :
    IsPretransitive (PSL n F) (PG n F) ∧ FaithfulSMul (PSL n F) (PG n F) ∧
    Set.range (fun x : PG n F => orbit (stabilizer (PSL n F) p) x) =
      {{p}, {p}ᶜ} ∧
    ({p} : Set (PG n F)) ≠ {p}ᶜ ∧
    Nat.card (orbitRel.Quotient (stabilizer (PSL n F) p) (PG n F)) = 2 ∧
    Nat.card (orbit (stabilizer (PSL n F) p) p) = 1 ∧
    (∀ x : PG n F, x ≠ p → Nat.card (orbit (stabilizer (PSL n F) p) x) =
      (Fintype.card F ^ n - Fintype.card F) / (Fintype.card F - 1)) ∧
    (Fintype.card F - 1) * ((Fintype.card F ^ n - Fintype.card F) / (Fintype.card F - 1)) =
      Fintype.card F ^ n - Fintype.card F ∧
    (Fintype.card F ^ n - Fintype.card F) / (Fintype.card F - 1) =
      (Fintype.card F ^ n - 1) / (Fintype.card F - 1) - 1 ∧
    Set.range (fun x : PG n F => Nat.card (orbit (stabilizer (PSL n F) p) x)) =
      {1, (Fintype.card F ^ n - Fintype.card F) / (Fintype.card F - 1)} ∧
    1 ≠ (Fintype.card F ^ n - Fintype.card F) / (Fintype.card F - 1) := by
  have hq : 2 ≤ Fintype.card F := Nat.succ_le_of_lt Fintype.one_lt_card
  obtain ⟨hN3, hNd, hexact⟩ := arith hq hn (pow_eq_card_points (F := F) n)
  set d := (Fintype.card F ^ n - Fintype.card F) / (Fintype.card F - 1) with hd
  -- there is a point other than `p`
  have : Nontrivial (PG n F) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x₀, hx₀⟩ := exists_ne p
  have hne : ({p} : Set (PG n F)) ≠ {p}ᶜ := by
    intro h
    have : x₀ ∈ ({p} : Set (PG n F)) := by rw [h]; exact hx₀
    exact hx₀ this
  have hrange : Set.range (fun x : PG n F => orbit (stabilizer (PSL n F) p) x) =
      {{p}, {p}ᶜ} := by
    ext O
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x = p
      · left; rw [hx]; exact orbit_stabilizer_self p
      · right; exact orbit_stabilizer_of_ne p x hx
    · rintro (rfl | rfl)
      · exact ⟨p, orbit_stabilizer_self p⟩
      · exact ⟨x₀, orbit_stabilizer_of_ne p x₀ hx₀⟩
  have hcard_ne : ∀ x : PG n F, x ≠ p →
      Nat.card (orbit (stabilizer (PSL n F) p) x) = d := by
    intro x hx
    rw [orbit_stabilizer_of_ne p x hx, card_compl_point, hNd]
  have hcard_p : Nat.card (orbit (stabilizer (PSL n F) p) p) = 1 := by
    rw [orbit_stabilizer_self p, Nat.card_unique]
  refine ⟨?_, inferInstance, hrange, hne, ?_, hcard_p, hcard_ne, hexact, ?_, ?_, ?_⟩
  · -- Mathlib: the action is primitive, in particular transitive
    infer_instance
  · -- the orbits are indexed by the quotient, injectively
    have hinj := orbitRel.Quotient.orbit_injective (G := stabilizer (PSL n F) p)
      (α := PG n F)
    have hr : Set.range (orbitRel.Quotient.orbit (G := stabilizer (PSL n F) p)
        (α := PG n F)) = {{p}, {p}ᶜ} := by
      rw [← hrange]
      ext O
      simp only [Set.mem_range]
      constructor
      · rintro ⟨Q, rfl⟩
        induction Q using Quotient.inductionOn' with
        | h x => exact ⟨x, (orbitRel.Quotient.orbit_mk x).symm⟩
      · rintro ⟨x, rfl⟩
        exact ⟨Quotient.mk'' x, orbitRel.Quotient.orbit_mk x⟩
    rw [← Nat.card_range_of_injective hinj, hr, Nat.card_coe_set_eq, Set.ncard_pair hne]
  · rw [← card_points, ← hNd]
  · ext k
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x = p
      · left; rw [hx]; exact hcard_p
      · right; exact hcard_ne x hx
    · rintro (rfl | rfl)
      · exact ⟨p, hcard_p⟩
      · exact ⟨x₀, hcard_ne x₀ hx₀⟩
  · have := subdegree_ge_two (F := F) hn
    omega

end Conjecture1012
