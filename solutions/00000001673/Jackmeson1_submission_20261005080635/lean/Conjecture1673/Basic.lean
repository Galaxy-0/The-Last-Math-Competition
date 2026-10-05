import Mathlib

/-!
# Conjecture 00000001673: the inducibility of `C₆` is not `(√3 - 1)/2`

(A) In any graph at most two of the sets `b \ {x}` induce `C₆` (2-regularity of `C₆` makes two
deleted vertices twins; `C₆` has no twins); averaging over 7-sets, every graph on `n ≥ 7` vertices
has induced `C₆` density `≤ 2/7 < (√3 - 1)/2`.  (B) Every blow-up of the triangular prism
`K₃ □ K₂` has no induced `C₆`, while balanced `C₆` blow-ups give `ind(C₆) ≥ 5/324 > 0`.
An induced copy of `C₆` is an induced embedding `SimpleGraph.cycleGraph 6 ↪g G`
(`SimpleGraph.Embedding`: injective and `G.Adj (f i) (f j) ↔ (cycleGraph 6).Adj i j`).
-/
open Finset SimpleGraph Filter Topology

namespace C1673

section Local

variable {V : Type*} {G : SimpleGraph V}

/-- The finset `s` induces a copy of `C₆` in `G`: it is the vertex set of an induced embedding of
the 6-cycle `cycleGraph 6`. -/
def InducesC6 (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ f : cycleGraph 6 ↪g G, univ.map f.toEmbedding = s

/-- `C₆` is 2-regular. -/
lemma c6_deg : ∀ i : Fin 6, (univ.filter fun j => (cycleGraph 6).Adj i j).card = 2 := by decide

/-- `C₆` has no twins. -/
lemma c6_twinFree : ∀ i j : Fin 6, i ≠ j →
    ∃ k, k ≠ i ∧ k ≠ j ∧ ¬((cycleGraph 6).Adj i k ↔ (cycleGraph 6).Adj j k) := by decide

/-- `C₆` is triangle-free. -/
lemma c6_triangleFree : ∀ a b c : Fin 6,
    (cycleGraph 6).Adj a b → (cycleGraph 6).Adj b c → ¬(cycleGraph 6).Adj a c := by decide

/-- Inside an induced `C₆`, every vertex has exactly two neighbours. -/
lemma deg_two [DecidableRel G.Adj] {s : Finset V} (hs : InducesC6 G s) {w : V} (hw : w ∈ s) :
    (s.filter (G.Adj w)).card = 2 := by
  obtain ⟨f, rfl⟩ := hs
  obtain ⟨i, -, rfl⟩ := mem_map.1 hw
  rw [filter_map, card_map]
  convert c6_deg i using 2
  ext j; simp

/-- Two distinct vertices of an induced `C₆` are distinguished by a third vertex of it. -/
lemma twin_free {s : Finset V} (hs : InducesC6 G s) {y z : V} (hy : y ∈ s) (hz : z ∈ s)
    (hyz : y ≠ z) : ∃ w ∈ s, w ≠ y ∧ w ≠ z ∧ ¬(G.Adj y w ↔ G.Adj z w) := by
  obtain ⟨f, rfl⟩ := hs
  obtain ⟨i, -, rfl⟩ := mem_map.1 hy
  obtain ⟨j, -, rfl⟩ := mem_map.1 hz
  obtain ⟨k, hki, hkj, hk⟩ := c6_twinFree i j (fun h => hyz (by rw [h]))
  refine ⟨f k, mem_map_of_mem _ (mem_univ _), fun h => hki (f.injective h),
    fun h => hkj (f.injective h), ?_⟩
  simpa using hk

/-- If `b \ {x}` and `b \ {y}` both induce `C₆`, then `x` and `y` have the same neighbours in
`b \ {x, y}` (count degrees of `w` in the two copies). -/
lemma pair_twins [DecidableEq V] {b : Finset V} {x y : V} (hx : x ∈ b) (hy : y ∈ b) (hxy : x ≠ y)
    (hbx : InducesC6 G (b.erase x)) (hby : InducesC6 G (b.erase y)) {w : V} (hw : w ∈ b)
    (hwx : w ≠ x) (hwy : w ≠ y) : G.Adj w x ↔ G.Adj w y := by
  classical
  have h1 : b.erase y = insert x ((b.erase x).erase y) := by
    rw [erase_right_comm, insert_erase (mem_erase.2 ⟨hxy, hx⟩)]
  have h2 : b.erase x = insert y ((b.erase x).erase y) := by
    rw [insert_erase (mem_erase.2 ⟨hxy.symm, hy⟩)]
  have d1 := deg_two hby (mem_erase.2 ⟨hwy, hw⟩)
  have d2 := deg_two hbx (mem_erase.2 ⟨hwx, hw⟩)
  rw [h1, filter_insert] at d1
  rw [h2, filter_insert] at d2
  by_cases ha : G.Adj w x <;> by_cases hb : G.Adj w y <;>
    simp only [ha, hb, if_true, if_false] at d1 d2
  · exact iff_of_true ha hb
  · rw [card_insert_of_notMem (by simp)] at d1; omega
  · rw [card_insert_of_notMem (by simp)] at d2; omega
  · exact iff_of_false ha hb

/-- **Local bound.** For any vertex set `b`, at most two of the sets `b \ {x}` induce `C₆`. -/
lemma erase_count_le_two [DecidableEq V] [DecidablePred (InducesC6 G)] (b : Finset V) :
    (b.filter fun x => InducesC6 G (b.erase x)).card ≤ 2 := by
  by_contra h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := two_lt_card.1 (not_le.1 h)
  simp only [mem_filter] at hx hy hz
  obtain ⟨w, hw, hwy, hwz, hne⟩ := twin_free hx.2 (mem_erase.2 ⟨hxy.symm, hy.1⟩)
    (mem_erase.2 ⟨hxz.symm, hz.1⟩) hyz
  exact hne (by
    rw [G.adj_comm y, G.adj_comm z]
    exact pair_twins hy.1 hz.1 hyz hy.2 hz.2 (mem_of_mem_erase hw) hwy hwz)

end Local

section Count

open scoped Classical

variable {n : ℕ}

/-- Number of 6-element vertex subsets of `G` that induce `C₆`. -/
noncomputable def c6Count (G : SimpleGraph (Fin n)) : ℕ :=
  ((univ : Finset (Fin n)).powersetCard 6 |>.filter (InducesC6 G)).card

/-- Induced `C₆` density of `G`: `#{6-sets inducing C₆} / C(n, 6)`. -/
noncomputable def c6Density (G : SimpleGraph (Fin n)) : ℝ := (c6Count G : ℝ) / (n.choose 6 : ℝ)

/-- Maximum induced `C₆` density over all graphs on `n` vertices. -/
noncomputable def maxC6Density (n : ℕ) : ℝ := ⨆ G : SimpleGraph (Fin n), c6Density G

/-- The inducibility of `C₆`, read as `limsup_{n → ∞} max_{|G| = n} density`. -/
noncomputable def indC6 : ℝ := limsup maxC6Density atTop

/-- **Averaging over 7-sets.** `(n - 6) · #{6-sets inducing C₆} ≤ 2 · C(n, 7)`. -/
theorem count_mul_le (G : SimpleGraph (Fin n)) : c6Count G * (n - 6) ≤ n.choose 7 * 2 := by
  have h7 : n.choose 7 = ((univ : Finset (Fin n)).powersetCard 7).card := by simp
  rw [c6Count, h7]
  refine card_mul_le_card_mul (fun a b => a ⊆ b) (fun a ha => ?_) (fun b hb => ?_)
  · rw [mem_filter, mem_powersetCard] at ha
    rw [← show (aᶜ).card = n - 6 by rw [card_compl, Fintype.card_fin, ha.1.2]]
    refine card_le_card_of_injOn (fun x => insert x a) (fun x hx => ?_) (fun x hx y _ hxy => ?_)
    · rw [mem_coe, mem_compl] at hx
      simp [bipartiteAbove, mem_powersetCard, card_insert_of_notMem hx, ha.1.2, subset_insert]
    · have : x ∈ insert y a := by
        rw [← show insert x a = insert y a from hxy]; exact mem_insert_self x a
      exact (mem_insert.1 this).resolve_right (mem_compl.1 (mem_coe.1 hx))
  · rw [mem_powersetCard] at hb
    have hsub : bipartiteBelow (fun a b => a ⊆ b)
        (((univ : Finset (Fin n)).powersetCard 6).filter (InducesC6 G)) b ⊆
        (b.filter fun x => InducesC6 G (b.erase x)).image b.erase := by
      intro a ha
      simp only [bipartiteBelow, mem_filter, mem_powersetCard] at ha
      obtain ⟨⟨⟨-, ha6⟩, hind⟩, hab⟩ := ha
      obtain ⟨x, hxb, hxa⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hab (by
        rintro rfl; omega))
      have hae : a = b.erase x := eq_of_subset_of_card_le
        (fun y hy => mem_erase.2 ⟨by rintro rfl; exact hxa hy, hab hy⟩)
        (by rw [card_erase_of_mem hxb]; omega)
      exact mem_image.2 ⟨x, mem_filter.2 ⟨hxb, hae ▸ hind⟩, hae.symm⟩
    exact (card_le_card hsub).trans (card_image_le.trans (erase_count_le_two b))

/-- **Main bound.** For every `n ≥ 7` and every graph `G` on `n` vertices, the induced `C₆` density
is at most `2/7`. -/
theorem c6Density_le (hn : 7 ≤ n) (G : SimpleGraph (Fin n)) : c6Density G ≤ 2 / 7 := by
  have h1 := count_mul_le G
  have h2 := Nat.choose_succ_right_eq n 6
  have hpos : 0 < n.choose 6 := Nat.choose_pos (by omega)
  have h3 : c6Count G * 7 ≤ 2 * n.choose 6 :=
    Nat.le_of_mul_le_mul_right (c := n - 6) (by nlinarith) (by omega)
  rw [c6Density, div_le_div_iff₀ (by exact_mod_cast hpos) (by norm_num)]
  exact_mod_cast h3

lemma c6Density_nonneg (G : SimpleGraph (Fin n)) : 0 ≤ c6Density G := by unfold c6Density; positivity

theorem maxC6Density_le (hn : 7 ≤ n) : maxC6Density n ≤ 2 / 7 := ciSup_le (c6Density_le hn)

lemma maxC6Density_nonneg (n : ℕ) : 0 ≤ maxC6Density n := Real.iSup_nonneg c6Density_nonneg

/-- `2/7 < (√3 - 1)/2`. -/
theorem two_sevenths_lt : (2 / 7 : ℝ) < (Real.sqrt 3 - 1) / 2 := by
  have : (11 / 7 : ℝ) < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

lemma eventually_le : ∀ᶠ m in atTop, maxC6Density m ≤ 2 / 7 :=
  eventually_atTop.2 ⟨7, fun _ hm => maxC6Density_le hm⟩

/-- limsup reading: `ind(C₆) ≤ 2/7`. -/
theorem indC6_le : indC6 ≤ 2 / 7 :=
  limsup_le_of_le (isCoboundedUnder_le_of_le atTop maxC6Density_nonneg) eventually_le

/-- liminf reading. -/
theorem liminf_le : liminf maxC6Density atTop ≤ 2 / 7 :=
  liminf_le_of_frequently_le eventually_le.frequently
    (isBoundedUnder_of ⟨0, maxC6Density_nonneg⟩)

/-- Limit reading: if `max_{|G| = n} density` converges to `L`, then `L ≤ 2/7`. -/
theorem lim_le {L : ℝ} (h : Tendsto maxC6Density atTop (𝓝 L)) : L ≤ 2 / 7 :=
  le_of_tendsto h eventually_le

/-- Graph-sequence reading: for graphs `G m` on `m` vertices, `limsup density (G m) ≤ 2/7`. -/
theorem seq_limsup_le (G : ∀ m : ℕ, SimpleGraph (Fin m)) :
    limsup (fun m => c6Density (G m)) atTop ≤ 2 / 7 :=
  limsup_le_of_le (isCoboundedUnder_le_of_le atTop fun m => c6Density_nonneg (G m))
    (eventually_atTop.2 ⟨7, fun _ hm => c6Density_le hm _⟩)

/-! ### A positive lower bound: balanced blow-ups of `C₆` -/

/-- Residue map `Fin n → Fin 6`, `v ↦ v mod 6`. -/
def res (n : ℕ) (v : Fin n) : Fin 6 := ⟨v.val % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The blow-up of `C₆` on `Fin n` with parts the residue classes mod 6. -/
def c6Blowup (n : ℕ) : SimpleGraph (Fin n) := (cycleGraph 6).comap (res n)

lemma res_mk {n a : ℕ} (i : Fin 6) (h : 6 * a + i < n) : res n ⟨6 * a + i, h⟩ = i :=
  Fin.ext (by simp only [res]; omega)

/-- For `φ : Fin 6 → Fin (n / 6)`, the induced copy `i ↦ 6 φ(i) + i` of `C₆` in `c6Blowup n`. -/
def copy {n : ℕ} (φ : Fin 6 → Fin (n / 6)) : cycleGraph 6 ↪g c6Blowup n where
  toFun i := ⟨6 * φ i + i, by have := (φ i).2; have := i.2; omega⟩
  inj' i j h := by
    have hv := congrArg Fin.val h; have := i.2; have := j.2; simp only at hv; ext; omega
  map_rel_iff' {i j} := by
    change (cycleGraph 6).Adj (res n ⟨6 * φ i + i, _⟩) (res n ⟨6 * φ j + j, _⟩) ↔ _
    rw [res_mk, res_mk]

theorem c6Count_blowup_ge (n : ℕ) : (n / 6) ^ 6 ≤ c6Count (c6Blowup n) := by
  have hcard : (univ : Finset (Fin 6 → Fin (n / 6))).card = (n / 6) ^ 6 := by simp
  rw [← hcard, c6Count]
  refine card_le_card_of_injOn (fun φ => univ.map (copy φ).toEmbedding) ?_ ?_
  · intro φ _
    rw [mem_coe, mem_filter, mem_powersetCard, card_map, card_univ, Fintype.card_fin]
    exact ⟨⟨subset_univ _, rfl⟩, copy φ, rfl⟩
  · intro φ _ ψ _ h
    funext i
    have : copy φ i ∈ univ.map (copy ψ).toEmbedding := by
      rw [← show univ.map (copy φ).toEmbedding = univ.map (copy ψ).toEmbedding from h]
      exact mem_map_of_mem _ (mem_univ i)
    obtain ⟨j, -, hj⟩ := mem_map.1 this
    have hv := congrArg Fin.val hj
    have := i.2; have := j.2
    change 6 * (ψ j : ℕ) + j = 6 * (φ i : ℕ) + i at hv
    obtain rfl : j = i := Fin.ext (by omega)
    ext; omega

theorem c6Density_blowup_ge {m : ℕ} (hm : 1 ≤ m) :
    (5 / 324 : ℝ) ≤ c6Density (c6Blowup (6 * m)) := by
  have h1 := c6Count_blowup_ge (6 * m)
  rw [show 6 * m / 6 = m by omega] at h1
  have h1' : (m : ℝ) ^ 6 ≤ c6Count (c6Blowup (6 * m)) := by exact_mod_cast h1
  have h2 : ((6 * m).choose 6 : ℝ) ≤ (6 * m : ℝ) ^ 6 / 720 := by
    have := Nat.choose_le_pow_div (α := ℝ) 6 (6 * m)
    norm_num [Nat.factorial] at this; exact this
  have hpos : (0 : ℝ) < (6 * m).choose 6 := by exact_mod_cast Nat.choose_pos (by omega)
  rw [c6Density, le_div_iff₀ hpos]
  calc 5 / 324 * ((6 * m).choose 6 : ℝ) ≤ 5 / 324 * ((6 * m : ℝ) ^ 6 / 720) := by gcongr
    _ = (m : ℝ) ^ 6 := by ring
    _ ≤ _ := h1'

theorem maxC6Density_ge {m : ℕ} (hm : 1 ≤ m) : (5 / 324 : ℝ) ≤ maxC6Density (6 * m) :=
  (c6Density_blowup_ge hm).trans (le_ciSup (Set.finite_range _).bddAbove _)

/-- limsup reading: `ind(C₆) ≥ 5/324 > 0`. -/
theorem indC6_ge : (5 / 324 : ℝ) ≤ indC6 :=
  le_limsup_of_frequently_le
    (frequently_atTop.2 fun N => ⟨6 * (N + 1), by omega, maxC6Density_ge (by omega)⟩)
    ⟨2 / 7, eventually_le⟩

end Count

section Prism

/-- The triangular prism `K₃ □ K₂`. -/
def prism : SimpleGraph (Fin 3 × Fin 2) := (⊤ : SimpleGraph (Fin 3)) □ (⊤ : SimpleGraph (Fin 2))

/-- Any blow-up `prism.comap p` of the triangular prism (vertex `v` replaced by the independent
set `p⁻¹ {v}`; balanced or not) contains no induced `C₆`. -/
theorem prism_blowup_no_C6 {V : Type*} (p : V → Fin 3 × Fin 2) :
    IsEmpty (cycleGraph 6 ↪g prism.comap p) := by
  refine ⟨fun f => ?_⟩
  have hadj : ∀ i j, (cycleGraph 6).Adj i j ↔ prism.Adj (p (f i)) (p (f j)) :=
    fun _ _ => f.map_adj_iff.symm
  have hinj : Function.Injective (fun i => p (f i)) := by
    intro i j hij
    by_contra hne
    obtain ⟨k, -, -, hk⟩ := c6_twinFree i j hne
    exact hk (by rw [hadj, hadj]; simp only at hij; rw [hij])
  have hsurj := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, rfl⟩ |>.2
  obtain ⟨a, ha⟩ := hsurj (0, 0)
  obtain ⟨b, hb⟩ := hsurj (1, 0)
  obtain ⟨c, hc⟩ := hsurj (2, 0)
  simp only at ha hb hc
  refine c6_triangleFree a b c ((hadj a b).2 ?_) ((hadj b c).2 ?_) ((hadj a c).2 ?_)
  · rw [ha, hb]; simp [prism, boxProd_adj]
  · rw [hb, hc]; simp [prism, boxProd_adj]
  · rw [ha, hc]; simp [prism, boxProd_adj]

/-- Hence every blow-up of the prism on `Fin n` has induced `C₆` density `0`. -/
theorem prism_c6Density {n : ℕ} (p : Fin n → Fin 3 × Fin 2) : c6Density (prism.comap p) = 0 := by
  classical
  rw [c6Density, c6Count, card_eq_zero.2, Nat.cast_zero, zero_div]
  exact filter_eq_empty_iff.2 fun s _ ⟨f, _⟩ => (prism_blowup_no_C6 p).false f

end Prism

/-- **Disproof of conjecture 00000001673.** (A) For `n ≥ 7` every density is `< (√3 - 1)/2`; the
limsup (`indC6`), the liminf and any limit of `maxC6Density`, and the limsup along any graph
sequence, all differ from `(√3 - 1)/2`. (B) No sequence of triangular-prism blow-ups has density
tending to `indC6`, and at each `n = 6m` they fall `5/324` short of the maximum. -/
theorem not_conjecture :
    (∀ n ≥ 7, ∀ G : SimpleGraph (Fin n), c6Density G < (Real.sqrt 3 - 1) / 2) ∧
    indC6 ≠ (Real.sqrt 3 - 1) / 2 ∧
    liminf maxC6Density atTop ≠ (Real.sqrt 3 - 1) / 2 ∧
    ¬ Tendsto maxC6Density atTop (𝓝 ((Real.sqrt 3 - 1) / 2)) ∧
    (∀ G : ∀ m : ℕ, SimpleGraph (Fin m),
      limsup (fun m => c6Density (G m)) atTop ≠ (Real.sqrt 3 - 1) / 2) ∧
    (∀ p : ∀ n : ℕ, Fin n → Fin 3 × Fin 2,
      ¬ Tendsto (fun n => c6Density (prism.comap (p n))) atTop (𝓝 indC6)) ∧
    (∀ m ≥ 1, ∀ p : Fin (6 * m) → Fin 3 × Fin 2,
      c6Density (prism.comap p) + 5 / 324 ≤ maxC6Density (6 * m)) := by
  have h := two_sevenths_lt
  refine ⟨fun n hn G => (c6Density_le hn G).trans_lt h, fun e => ?_, fun e => ?_,
    fun e => ?_, fun G e => ?_, fun p e => ?_, fun m hm p => ?_⟩
  · linarith [indC6_le]
  · linarith [liminf_le]
  · linarith [lim_le e]
  · linarith [seq_limsup_le G]
  · simp only [prism_c6Density] at e
    linarith [tendsto_nhds_unique tendsto_const_nhds e, indC6_ge]
  · rw [prism_c6Density, zero_add]; exact maxC6Density_ge hm

end C1673
