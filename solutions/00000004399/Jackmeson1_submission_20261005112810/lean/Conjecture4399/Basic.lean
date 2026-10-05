import Mathlib

/-!
# Conjecture 00000004399 is false

Conjecture (verbatim): "A common graph is a graph for which the sum of its density and that of its
complement has a uniform lower bound over all graphs. Conjecture: There exists a non-complete
non-bipartite common graph of order 6, and 6 is the minimal order of such graphs."

Conventions.  Graphs are finite simple graphs (`SimpleGraph (Fin n)`).  The density of `H` in `G`
is the homomorphism density `t(H, G) = hom(H, G) / |V(G)|^|V(H)|`; `Gᶜ` is the complement.
"Non-complete" is `H ≠ ⊤`, "non-bipartite" is `¬ H.Colorable 2`, the order is the number of
vertices, and `e(H)` is the number of edges.  Three readings of "common" are formalized:

* `Common` (the standard notion, finite form): asymptotically `t(H,G) + t(H,Gᶜ) ≥ 2^{1-e(H)}`, i.e. for every
  `ε > 0` the bound `2^{1-e(H)} - ε` holds for all graphs on at least `N(ε)` vertices;
* `CommonPos`: some positive constant `b` bounds `t(H,G) + t(H,Gᶜ)` from below for all graphs on at
  least `N` vertices;
* `CommonUniform`: some positive constant `b` bounds it from below for all graphs with at least one
  vertex (the exact bound `2^{1-e(H)}` for all such graphs is a special case, `commonExact_uniform`).

Under `Common` and `CommonPos` the bowtie (two triangles sharing a vertex: order 5, connected,
non-complete, non-bipartite) is common, so 6 is not the minimal order.  The proof is Goodman's
bound for triangles (`goodman`) plus Cauchy–Schwarz: `hom(bowtie, G) = ∑_v T(v)^2`, where `T(v)`
counts ordered pairs `(a, b)` with `v a b` a triangle, which gives
`t(bowtie,G) + t(bowtie,Gᶜ) ≥ 1/32 - 3/(8n)` for every graph on `n ≥ 1` vertices
(`bowtie_density_bound`).  Under `CommonUniform` no graph with an edge is common (test it on the
one-vertex graph), so no non-bipartite common graph of order 6 exists.
-/

namespace Conjecture4399

open Finset

variable {V : Type*}

/-- Number of graph homomorphisms `H → G`. -/
noncomputable def hom {W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : ℕ := Nat.card (H →g G)

/-- Homomorphism density `t(H, G) = hom(H, G) / |V(G)|^|V(H)|`. -/
noncomputable def homDensity {W : Type*} [Fintype W] (H : SimpleGraph W) [Fintype V]
    (G : SimpleGraph V) : ℝ :=
  (hom H G : ℝ) / (Fintype.card V : ℝ) ^ Fintype.card W

/-- Number of edges. -/
noncomputable def numEdges {W : Type*} (H : SimpleGraph W) : ℕ := Nat.card H.edgeSet

/-- **Standard definition** (finite form): `H` is common if for every `ε > 0`, every graph `G` on
sufficiently many vertices satisfies `t(H,G) + t(H,Gᶜ) ≥ 2^{1-e(H)} - ε`. -/
def Common {m : ℕ} (H : SimpleGraph (Fin m)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    (2 : ℝ) / 2 ^ numEdges H - ε ≤ homDensity H G + homDensity H Gᶜ

/-- Reading with an unspecified positive asymptotic lower bound. -/
def CommonPos {m : ℕ} (H : SimpleGraph (Fin m)) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    b ≤ homDensity H G + homDensity H Gᶜ

/-- Reading with a positive lower bound uniform over all graphs with at least one vertex. -/
def CommonUniform {m : ℕ} (H : SimpleGraph (Fin m)) : Prop :=
  ∃ b : ℝ, 0 < b ∧ ∀ n ≥ 1, ∀ G : SimpleGraph (Fin n), b ≤ homDensity H G + homDensity H Gᶜ

/-- The conjecture, for a given notion of commonness. -/
def ConjectureClaim (IsCommon : ∀ m : ℕ, SimpleGraph (Fin m) → Prop) : Prop :=
  (∃ H : SimpleGraph (Fin 6), H ≠ ⊤ ∧ ¬ H.Colorable 2 ∧ IsCommon 6 H) ∧
  ∀ m < 6, ∀ H : SimpleGraph (Fin m), H ≠ ⊤ → ¬ H.Colorable 2 → ¬ IsCommon m H

/-! ### The bowtie -/

/-- The bowtie: triangles `{0,1,2}` and `{0,3,4}` sharing the vertex `0`. -/
def bowtie : SimpleGraph (Fin 5) where
  Adj a b := a ≠ b ∧ ((a.val ≤ 2 ∧ b.val ≤ 2) ∨ ((a.val = 0 ∨ 3 ≤ a.val) ∧ (b.val = 0 ∨ 3 ≤ b.val)))
  symm := ⟨fun _ _ h => ⟨h.1.symm, by omega⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel bowtie.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a.val ≤ 2 ∧ b.val ≤ 2) ∨
    ((a.val = 0 ∨ 3 ≤ a.val) ∧ (b.val = 0 ∨ 3 ≤ b.val)))))

theorem bowtie_numEdges : numEdges bowtie = 6 := by
  rw [numEdges, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  decide

theorem bowtie_ne_top : bowtie ≠ ⊤ := by
  intro h
  have h13 : (⊤ : SimpleGraph (Fin 5)).Adj 1 3 := by simp
  rw [← h] at h13
  exact absurd h13 (by decide)

theorem bowtie_not_bipartite : ¬ bowtie.Colorable 2 := by
  rintro ⟨C⟩
  have h01 := C.valid (show bowtie.Adj 0 1 by decide)
  have h02 := C.valid (show bowtie.Adj 0 2 by decide)
  have h12 := C.valid (show bowtie.Adj 1 2 by decide)
  revert h01 h02 h12
  generalize C 0 = a; generalize C 1 = b; generalize C 2 = c
  revert a b c; decide

theorem bowtie_connected : bowtie.Connected := by
  have h0 : ∀ v : Fin 5, bowtie.Reachable v 0 := by
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.refl _
    all_goals exact SimpleGraph.Adj.reachable (by decide)
  exact ⟨fun u v => (h0 u).trans (h0 v).symm⟩

/-! ### Counting bowtie homomorphisms -/

/-- Ordered pairs `(a, b)` such that `v, a, b` span a triangle of `G`. -/
abbrev TriSet (G : SimpleGraph V) (v : V) : Type _ :=
  {p : V × V // G.Adj v p.1 ∧ G.Adj v p.2 ∧ G.Adj p.1 p.2}

/-- `T(v)`: the number of triangle homomorphisms sending a fixed vertex of `K₃` to `v`. -/
noncomputable def tri (G : SimpleGraph V) (v : V) : ℕ := Nat.card (TriSet G v)

/-- A bowtie homomorphism is a center `v` with two triangles through it. -/
def bowtieEquiv (G : SimpleGraph V) : (bowtie →g G) ≃ Σ v : V, TriSet G v × TriSet G v where
  toFun f := ⟨f 0, ⟨(f 1, f 2), f.map_adj (by decide), f.map_adj (by decide),
      f.map_adj (by decide)⟩, ⟨(f 3, f 4), f.map_adj (by decide), f.map_adj (by decide),
      f.map_adj (by decide)⟩⟩
  invFun x := ⟨![x.1, x.2.1.1.1, x.2.1.1.2, x.2.2.1.1, x.2.2.1.2], by
    obtain ⟨v, ⟨⟨a, b⟩, h1, h2, h3⟩, ⟨⟨c, d⟩, h4, h5, h6⟩⟩ := x
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
         first
         | exact h1 | exact h1.symm | exact h2 | exact h2.symm | exact h3 | exact h3.symm
         | exact h4 | exact h4.symm | exact h5 | exact h5.symm | exact h6 | exact h6.symm)⟩
  left_inv f := by
    ext i
    fin_cases i <;> rfl
  right_inv x := by
    obtain ⟨v, ⟨⟨a, b⟩, h1⟩, ⟨⟨c, d⟩, h2⟩⟩ := x
    rfl

theorem hom_bowtie [Fintype V] (G : SimpleGraph V) : hom bowtie G = ∑ v, tri G v ^ 2 := by
  classical
  rw [hom, Nat.card_congr (bowtieEquiv G), Nat.card_sigma]
  simp [tri, sq]


/-! ### Goodman's bound for triangles -/

section Goodman

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Indicator that `x y z` is a monochromatic triangle (in `G` or in `Gᶜ`). -/
def mono (x y z : V) : ℕ :=
  (if G.Adj x y ∧ G.Adj x z ∧ G.Adj y z then 1 else 0) +
    (if Gᶜ.Adj x y ∧ Gᶜ.Adj x z ∧ Gᶜ.Adj y z then 1 else 0)

/-- Indicator of a bichromatic angle at `x` with legs `x y`, `x z`. -/
def ang (x y z : V) : ℕ :=
  (if G.Adj x y ∧ Gᶜ.Adj x z then 1 else 0) + (if Gᶜ.Adj x y ∧ G.Adj x z then 1 else 0)

/-- Indicator that `x, y, z` are pairwise distinct. -/
def dist3 (x y z : V) : ℕ := if x ≠ y ∧ x ≠ z ∧ y ≠ z then 1 else 0

omit [Fintype V] in
/-- A triangle that is not monochromatic has exactly two bichromatic angles. -/
theorem pointwise (x y z : V) :
    2 * mono G x y z + ang G x y z + ang G y x z + ang G z x y = 2 * dist3 x y z := by
  rcases eq_or_ne x y with rfl | hxy
  · by_cases h : G.Adj z x <;> simp [mono, ang, dist3, h]
  rcases eq_or_ne x z with rfl | hxz
  · by_cases h : G.Adj y x <;> simp [mono, ang, dist3, h]
  rcases eq_or_ne y z with rfl | hyz
  · by_cases h : G.Adj y x <;> simp [mono, ang, dist3, h] <;> tauto
  simp only [mono, ang, dist3, SimpleGraph.compl_adj, G.adj_comm y x, G.adj_comm z x,
    G.adj_comm z y, ne_eq, hxy, hxz, hyz, hxy.symm, hxz.symm, hyz.symm, not_false_eq_true,
    true_and, and_self]
  by_cases p : G.Adj x y <;> by_cases q : G.Adj x z <;> by_cases r : G.Adj y z <;> simp [p, q, r]

omit [DecidableEq V] in
theorem tri_eq (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    tri H v = ∑ y, ∑ z, if H.Adj v y ∧ H.Adj v z ∧ H.Adj y z then 1 else 0 := by
  rw [tri, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  exact Fintype.sum_prod_type' (fun y z => if H.Adj v y ∧ H.Adj v z ∧ H.Adj y z then 1 else 0)

omit [DecidableEq V] in
theorem sum_adj (H : SimpleGraph V) [DecidableRel H.Adj] (x : V) :
    ∑ y, (if H.Adj x y then 1 else 0 : ℕ) = H.degree x := by
  rw [← H.card_neighborFinset_eq_degree, H.neighborFinset_eq_filter, Finset.card_filter]

omit [Fintype V] [DecidableEq V] in
theorem ite_and_one (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then 1 else 0 : ℕ) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  rw [ite_zero_mul_ite_zero, one_mul]

theorem sum_ang (x : V) : ∑ y, ∑ z, ang G x y z = 2 * (G.degree x * Gᶜ.degree x) := by
  simp only [ang, Finset.sum_add_distrib, ite_and_one, ← Finset.mul_sum, ← Finset.sum_mul,
    sum_adj]
  ring

theorem sum_dist3 :
    ∑ x : V, ∑ y : V, ∑ z : V, dist3 x y z =
      Fintype.card V * ((Fintype.card V - 1) * (Fintype.card V - 2)) := by
  have inner : ∀ x y : V, ∑ z, dist3 x y z = if x = y then 0 else Fintype.card V - 2 := by
    intro x y
    split_ifs with h
    · subst h; simp [dist3]
    · have e : (Finset.univ.filter fun z => x ≠ y ∧ x ≠ z ∧ y ≠ z) =
          (Finset.univ.erase x).erase y := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]; tauto
      have hy : y ∈ Finset.univ.erase x := Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ y⟩
      simp only [dist3]
      rw [← Finset.card_filter, e, Finset.card_erase_of_mem hy,
        Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
      omega
  have outer : ∀ x : V, ∑ y, (if x = y then 0 else Fintype.card V - 2) =
      (Fintype.card V - 1) * (Fintype.card V - 2) := by
    intro x
    have h1 : ∀ y : V, (if x = y then 0 else Fintype.card V - 2) +
        (if x = y then Fintype.card V - 2 else 0) = Fintype.card V - 2 :=
      fun y => by split_ifs <;> simp
    have h2 := Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => h1 y)
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ x), Finset.sum_const,
      Finset.card_univ, smul_eq_mul] at h2
    rw [Nat.sub_one_mul]
    omega
  simp_rw [inner, outer, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Double-counting identity**: `2·(monochromatic) + 3·(bichromatic angles) = 2·(distinct triples)`. -/
theorem goodman_identity :
    2 * (∑ x, ∑ y, ∑ z, mono G x y z) + 3 * (∑ x, ∑ y, ∑ z, ang G x y z) =
      2 * (∑ x : V, ∑ y : V, ∑ z : V, dist3 x y z) := by
  have h : ∑ x, ∑ y, ∑ z, (2 * mono G x y z + ang G x y z + ang G y x z + ang G z x y) =
      ∑ x : V, ∑ y : V, ∑ z : V, 2 * dist3 x y z := by
    simp_rw [pointwise]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have h2 : ∑ x, ∑ y, ∑ z, ang G y x z = ∑ x, ∑ y, ∑ z, ang G x y z := Finset.sum_comm
  have h3 : ∑ x, ∑ y, ∑ z, ang G z x y = ∑ x, ∑ y, ∑ z, ang G x y z := by
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
    exact Finset.sum_comm
  rw [h2, h3] at h
  omega

/-- **Goodman's bound**: the triangle homomorphism counts of `G` and `Gᶜ` sum to at least
`n(n-1)(n-5)/4`. -/
theorem goodman (hn : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) * (Fintype.card V - 1) * (Fintype.card V - 5) / 4 ≤
      ∑ v, (tri G v : ℝ) + ∑ v, (tri Gᶜ v : ℝ) := by
  set n := Fintype.card V with hn_def
  have hM : ∑ v, tri G v + ∑ v, tri Gᶜ v = ∑ x, ∑ y, ∑ z, mono G x y z := by
    simp only [tri_eq, mono, Finset.sum_add_distrib]
  have hid := goodman_identity G
  rw [sum_dist3, ← hM] at hid
  simp only [sum_ang] at hid
  have hdeg : ∀ x : V, G.degree x + Gᶜ.degree x + 1 = n := by
    intro x
    have h1 := G.degree_compl (v := x)
    have h2 := G.degree_lt_card_verts x
    omega
  have hang : ∀ x : V, (2 * ((G.degree x : ℝ) * Gᶜ.degree x)) ≤ ((n : ℝ) - 1) ^ 2 / 2 := by
    intro x
    have h := hdeg x
    have : (G.degree x : ℝ) + Gᶜ.degree x = n - 1 := by
      have : ((G.degree x + Gᶜ.degree x + 1 : ℕ) : ℝ) = n := by exact_mod_cast h
      push_cast at this; linarith
    nlinarith [sq_nonneg ((G.degree x : ℝ) - Gᶜ.degree x)]
  have hA : ∑ x, (2 * ((G.degree x : ℝ) * Gᶜ.degree x)) ≤ n * (((n : ℝ) - 1) ^ 2 / 2) := by
    calc ∑ x, (2 * ((G.degree x : ℝ) * Gᶜ.degree x)) ≤ ∑ _x : V, ((n : ℝ) - 1) ^ 2 / 2 :=
          Finset.sum_le_sum (fun x _ => hang x)
      _ = n * (((n : ℝ) - 1) ^ 2 / 2) := by simp [Finset.card_univ, hn_def]
  have hR : (2 : ℝ) * (∑ v, (tri G v : ℝ) + ∑ v, (tri Gᶜ v : ℝ)) +
      3 * ∑ x, (2 * ((G.degree x : ℝ) * Gᶜ.degree x)) = 2 * (n * ((n - 1) * (n - 2))) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hid
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] at this
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at this
    push_cast at this ⊢
    linarith
  nlinarith [hA, hR]

end Goodman

/-! ### The bowtie is common -/

/-- For every finite graph `G` on `n ≥ 1` vertices,
`t(bowtie, G) + t(bowtie, Gᶜ) ≥ 1/32 - 3/(8n)`. -/
theorem bowtie_density_bound [Fintype V] (G : SimpleGraph V) (hn : 1 ≤ Fintype.card V) :
    1 / 32 - 3 / (8 * (Fintype.card V : ℝ)) ≤ homDensity bowtie G + homDensity bowtie Gᶜ := by
  classical
  set n := Fintype.card V with hn_def
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hd : ∀ H : SimpleGraph V, 0 ≤ homDensity bowtie H := fun H => by
    unfold homDensity; positivity
  rcases lt_or_ge n 12 with hsmall | hsmall
  · have : (n : ℝ) < 12 := by exact_mod_cast hsmall
    have : 1 / 32 - 3 / (8 * (n : ℝ)) ≤ 0 := by
      rw [sub_nonpos, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    linarith [hd G, hd Gᶜ]
  have hn12 : (12 : ℝ) ≤ n := by exact_mod_cast hsmall
  set S1 := ∑ v, (tri G v : ℝ)
  set S2 := ∑ v, (tri Gᶜ v : ℝ)
  set Q1 := ∑ v, (tri G v : ℝ) ^ 2
  set Q2 := ∑ v, (tri Gᶜ v : ℝ) ^ 2
  have hcs1 : S1 ^ 2 ≤ n * Q1 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun v => (tri G v : ℝ))
    simpa [Finset.card_univ, hn_def] using this
  have hcs2 : S2 ^ 2 ≤ n * Q2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun v => (tri Gᶜ v : ℝ))
    simpa [Finset.card_univ, hn_def] using this
  have hg := goodman G (by omega)
  have hsum : n ^ 2 * (n - 6) / 4 ≤ S1 + S2 := by nlinarith
  have hsq : (n ^ 2 * (n - 6) / 4) ^ 2 ≤ (S1 + S2) ^ 2 :=
    pow_le_pow_left₀ (by nlinarith) hsum 2
  have hQ : n ^ 4 * (n - 6) ^ 2 / 32 ≤ n * (Q1 + Q2) := by nlinarith [sq_nonneg (S1 - S2)]
  have hdens : homDensity bowtie G + homDensity bowtie Gᶜ = (Q1 + Q2) / n ^ 5 := by
    simp only [homDensity, hom_bowtie, Fintype.card_fin, Q1, Q2]
    push_cast
    ring
  rw [hdens, le_div_iff₀ (by positivity)]
  have key : (1 / 32 - 3 / (8 * (n : ℝ))) * n ^ 5 = n ^ 4 * (n - 12) / 32 := by
    field_simp; ring
  rw [key]
  have h4 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  have : (n : ℝ) ^ 4 * (n - 12) / 32 * n ≤ (n : ℝ) ^ 4 * (n - 6) ^ 2 / 32 := by
    have e : (n : ℝ) ^ 4 * (n - 6) ^ 2 / 32 - n ^ 4 * (n - 12) / 32 * n = 36 * n ^ 4 / 32 := by
      ring
    have : (0 : ℝ) ≤ 36 * n ^ 4 / 32 := by positivity
    linarith
  nlinarith

theorem bowtie_common : Common bowtie := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / (8 * ε))
  refine ⟨N + 1, fun n hn G => ?_⟩
  have h := bowtie_density_bound G (by simp; omega)
  rw [Fintype.card_fin] at h
  have hnr : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hnpos : (0 : ℝ) < n := by linarith
  have : 3 / (8 * (n : ℝ)) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hN
    have : (N : ℝ) * (8 * ε) ≤ ε * (8 * n) := by nlinarith
    linarith
  rw [bowtie_numEdges]
  norm_num at h ⊢
  linarith

theorem bowtie_commonPos : CommonPos bowtie := by
  obtain ⟨N, hN⟩ := bowtie_common (1 / 64) (by norm_num)
  refine ⟨1 / 64, by norm_num, N, fun n hn G => ?_⟩
  have := hN n hn G
  rw [bowtie_numEdges] at this
  norm_num at this ⊢
  linarith

/-! ### The uniform reading: no graph with an edge is common -/

theorem hom_eq_zero_of_adj {W : Type*} (H : SimpleGraph W) {a b : W} (hab : H.Adj a b)
    (G : SimpleGraph (Fin 1)) : hom H G = 0 := by
  rw [hom, Nat.card_eq_zero]
  left
  refine ⟨fun f => ?_⟩
  have := f.map_adj hab
  rw [Subsingleton.elim (f a) (f b)] at this
  exact G.loopless.irrefl _ this

theorem not_commonUniform {m : ℕ} (H : SimpleGraph (Fin m)) {a b : Fin m} (hab : H.Adj a b) :
    ¬ CommonUniform H := by
  rintro ⟨c, hc, h⟩
  have := h 1 le_rfl ⊥
  simp [homDensity, hom_eq_zero_of_adj H hab] at this
  linarith

theorem exists_adj_of_not_bipartite {m : ℕ} (H : SimpleGraph (Fin m)) (h : ¬ H.Colorable 2) :
    ∃ a b, H.Adj a b := by
  by_contra hne
  simp only [not_exists] at hne
  exact h ⟨SimpleGraph.Coloring.mk (fun _ => 0) (fun hab => absurd hab (hne _ _))⟩

/-- The exact bound `2^{1-e(H)}` for all graphs with at least one vertex is a special case. -/
theorem commonExact_uniform {m : ℕ} (H : SimpleGraph (Fin m))
    (h : ∀ n ≥ 1, ∀ G : SimpleGraph (Fin n),
      (2 : ℝ) / 2 ^ numEdges H ≤ homDensity H G + homDensity H Gᶜ) : CommonUniform H :=
  ⟨2 / 2 ^ numEdges H, by positivity, h⟩

/-! ### Main theorem -/

/-- **Conjecture 00000004399 is false** under each of the three readings of "common": under the
standard and the positive-asymptotic readings the bowtie is a connected, non-complete,
non-bipartite common graph of order 5, so 6 is not the minimal order; under the uniform reading no
non-bipartite graph is common, so none of order 6 exists. -/
theorem conjecture4399_false :
    ¬ ConjectureClaim (fun _ H => Common H) ∧ ¬ ConjectureClaim (fun _ H => CommonPos H) ∧
      ¬ ConjectureClaim (fun _ H => CommonUniform H) := by
  refine ⟨fun h => h.2 5 (by norm_num) bowtie bowtie_ne_top bowtie_not_bipartite bowtie_common,
    fun h => h.2 5 (by norm_num) bowtie bowtie_ne_top bowtie_not_bipartite bowtie_commonPos,
    fun h => ?_⟩
  obtain ⟨H, -, hnb, hc⟩ := h.1
  obtain ⟨a, b, hab⟩ := exists_adj_of_not_bipartite H hnb
  exact not_commonUniform H hab hc

/-- The witness, with all of its properties. -/
theorem bowtie_witness :
    Fintype.card (Fin 5) = 5 ∧ bowtie.Connected ∧ bowtie ≠ ⊤ ∧ ¬ bowtie.Colorable 2 ∧
      numEdges bowtie = 6 ∧ Common bowtie ∧ CommonPos bowtie :=
  ⟨by simp, bowtie_connected, bowtie_ne_top, bowtie_not_bipartite, bowtie_numEdges,
    bowtie_common, bowtie_commonPos⟩

end Conjecture4399
