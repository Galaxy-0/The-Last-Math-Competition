import Mathlib

/-!
# Conjecture 00000001543 (disproved)

*Statement.* Any `n` points on an irreducible real algebraic curve determine at least
`c * n^(4/3)` distinct distances.

*Refutation.* The line `y = 0` is the zero set of the irreducible polynomial `Y`; it is an
irreducible real algebraic curve.  The `n` points `(0,0), (1,0), ..., (n-1,0)` on it determine
at most `n - 1` distinct (Euclidean) distances, and `n - 1 < c * n^(4/3)` for every `c > 0`
once `n` is large.  So no positive constant works, not even one depending on the curve, and
not even for all sufficiently large `n` only.

The plane is `EuclideanSpace ℝ (Fin 2)` (Euclidean distance); coordinates are `p 0` (x) and
`p 1` (y).
-/

open MvPolynomial

namespace C1543

/-- The real plane with its Euclidean metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Zero set in `ℝ²` of a real polynomial in the two coordinates `X 0 = x`, `X 1 = y`. -/
def zeroSet (f : MvPolynomial (Fin 2) ℝ) : Set Plane :=
  {p | eval (fun i => p i) f = 0}

/-- An irreducible real algebraic curve: the (infinite) zero set of an irreducible polynomial
`f ∈ ℝ[x, y]`.  (Infiniteness excludes degenerate zero sets such as that of `x² + y²`.) -/
def IsIrreducibleRealCurve (C : Set Plane) : Prop :=
  ∃ f : MvPolynomial (Fin 2) ℝ, Irreducible f ∧ C = zeroSet f ∧ C.Infinite

/-- The set of distinct distances determined by a finite point set `P`:
the image of `(p, q) ↦ ‖p - q‖` over ordered pairs of distinct points of `P`. -/
noncomputable def distances (P : Finset Plane) : Finset ℝ :=
  P.offDiag.image fun pq => dist pq.1 pq.2

/-- The `x`-axis `y = 0`. -/
def xAxis : Set Plane := zeroSet (X 1)

lemma mem_xAxis (p : Plane) : p ∈ xAxis ↔ p 1 = 0 := by
  simp [xAxis, zeroSet]

/-- The point `(t, 0)`. -/
noncomputable def pt (t : ℝ) : Plane := EuclideanSpace.single 0 t

lemma pt_mem (t : ℝ) : pt t ∈ xAxis := by
  rw [mem_xAxis]; simp [pt]

lemma dist_pt (s t : ℝ) : dist (pt s) (pt t) = |s - t| := by
  rw [← Real.dist_eq]
  exact PiLp.dist_single_same 2 (fun _ : Fin 2 => ℝ) 0 s t

lemma pt_injective : Function.Injective pt := by
  intro s t h
  have := congrArg (fun p : Plane => p 0) h
  simpa [pt] using this

/-- The `x`-axis is an irreducible real algebraic curve. -/
theorem xAxis_isIrreducibleRealCurve : IsIrreducibleRealCurve xAxis := by
  refine ⟨X 1, (X_prime (R := ℝ) (σ := Fin 2) (i := 1)).irreducible, rfl, ?_⟩
  have h : Set.range pt ⊆ xAxis := by rintro _ ⟨t, rfl⟩; exact pt_mem t
  exact (Set.infinite_range_of_injective pt_injective).mono h

/-- `n` equally spaced points on the `x`-axis. -/
noncomputable def collinear (n : ℕ) : Finset Plane :=
  (Finset.range n).image fun k : ℕ => pt (k : ℝ)

lemma collinear_card (n : ℕ) : (collinear n).card = n := by
  rw [collinear, Finset.card_image_of_injective]
  · simp
  · intro a b h; exact_mod_cast pt_injective h

lemma collinear_subset (n : ℕ) : (↑(collinear n) : Set Plane) ⊆ xAxis := by
  intro p hp
  simp only [collinear, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp
  obtain ⟨k, -, rfl⟩ := hp
  exact pt_mem k

/-- The `n` collinear points determine at most `n - 1` distinct distances
(namely `1, 2, ..., n - 1`). -/
theorem distances_collinear_card_le (n : ℕ) : (distances (collinear n)).card ≤ n - 1 := by
  have hsub : distances (collinear n) ⊆ (Finset.Ico 1 n).image fun k : ℕ => (k : ℝ) := by
    intro d hd
    simp only [distances, collinear, Finset.mem_image, Finset.mem_offDiag,
      Prod.exists] at hd
    obtain ⟨p, q, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hne⟩, rfl⟩ := hd
    rw [Finset.mem_range] at ha hb
    have hab : a ≠ b := by rintro rfl; exact hne rfl
    rw [dist_pt, Finset.mem_image]
    refine ⟨Int.natAbs ((a : ℤ) - b), ?_, ?_⟩
    · rw [Finset.mem_Ico]; omega
    · rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; rfl
  calc (distances (collinear n)).card
      ≤ ((Finset.Ico 1 n).image fun k : ℕ => (k : ℝ)).card := Finset.card_le_card hsub
    _ ≤ (Finset.Ico 1 n).card := Finset.card_image_le
    _ = n - 1 := by simp

/-- For every `c > 0`, `n - 1 < c * n^(4/3)` for all `n ≥ ⌈c⁻³⌉ + 1`. -/
lemma eventually_lt (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ((n - 1 : ℕ) : ℝ) < c * (n : ℝ) ^ (4 / 3 : ℝ) := by
  refine ⟨⌈(c ^ 3)⁻¹⌉₊ + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbig : (c ^ 3)⁻¹ < n := by
    have := Nat.le_ceil ((c ^ 3)⁻¹)
    have : (⌈(c ^ 3)⁻¹⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith
  -- `c * n^(1/3) > 1`
  have hcube : (1 : ℝ) < (c * (n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
    rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 3 : ℝ)), ← Real.rpow_mul hn0.le]
    norm_num
    have hc3 : 0 < c ^ 3 := by positivity
    rw [inv_lt_iff_one_lt_mul₀ hc3] at hbig
    linarith
  have hone : 1 < c * (n : ℝ) ^ (1 / 3 : ℝ) := by
    by_contra h
    push Not at h
    have h0 : 0 ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have := pow_le_one₀ (n := 3) h0 h
    linarith
  have hsplit : (n : ℝ) ^ (4 / 3 : ℝ) = n * (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hn0, Real.rpow_one]
  have hle : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  rw [hsplit]
  calc ((n - 1 : ℕ) : ℝ) ≤ n := hle
    _ = n * 1 := by ring
    _ < n * (c * (n : ℝ) ^ (1 / 3 : ℝ)) := by gcongr
    _ = c * (n * (n : ℝ) ^ (1 / 3 : ℝ)) := by ring

/-- **Main theorem (strong form).**  On the irreducible curve `y = 0`, for every `c > 0` there
is `N` such that for every `n ≥ N` some `n` points of the curve determine fewer than
`c * n^(4/3)` distinct distances. -/
theorem xAxis_violates :
    IsIrreducibleRealCurve xAxis ∧
      ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ P : Finset Plane, (↑P : Set Plane) ⊆ xAxis ∧ P.card = n ∧
          ((distances P).card : ℝ) < c * (P.card : ℝ) ^ (4 / 3 : ℝ) := by
  refine ⟨xAxis_isIrreducibleRealCurve, fun c hc => ?_⟩
  obtain ⟨N, hN⟩ := eventually_lt c hc
  refine ⟨N, fun n hn => ⟨collinear n, collinear_subset n, collinear_card n, ?_⟩⟩
  rw [collinear_card]
  calc ((distances (collinear n)).card : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast distances_collinear_card_le n
    _ < _ := hN n hn

/-- **Disproof, uniform constant.**  There is no `c > 0` such that every finite set of points
on every irreducible real algebraic curve determines at least `c * n^(4/3)` distinct
distances. -/
theorem not_uniform :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ C : Set Plane, IsIrreducibleRealCurve C →
      ∀ P : Finset Plane, (↑P : Set Plane) ⊆ C →
        c * (P.card : ℝ) ^ (4 / 3 : ℝ) ≤ (distances P).card := by
  rintro ⟨c, hc, h⟩
  obtain ⟨N, hN⟩ := xAxis_violates.2 c hc
  obtain ⟨P, hP, -, hlt⟩ := hN N le_rfl
  exact absurd (h _ xAxis_isIrreducibleRealCurve P hP) (not_le.mpr hlt)

/-- **Disproof, curve-dependent constant and large `n` only.**  It is not true that every
irreducible real algebraic curve `C` admits `c > 0` and `N` with: every set of `n ≥ N` points
on `C` determines at least `c * n^(4/3)` distinct distances. -/
theorem not_per_curve_eventually :
    ¬ ∀ C : Set Plane, IsIrreducibleRealCurve C →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ P : Finset Plane, (↑P : Set Plane) ⊆ C → N ≤ P.card →
        c * (P.card : ℝ) ^ (4 / 3 : ℝ) ≤ (distances P).card := by
  intro h
  obtain ⟨c, hc, N, hN⟩ := h _ xAxis_isIrreducibleRealCurve
  obtain ⟨N', hN'⟩ := xAxis_violates.2 c hc
  obtain ⟨P, hP, hcard, hlt⟩ := hN' (max N N') (le_max_right _ _)
  exact absurd (hN P hP (hcard ▸ le_max_left _ _)) (not_le.mpr hlt)

end C1543
