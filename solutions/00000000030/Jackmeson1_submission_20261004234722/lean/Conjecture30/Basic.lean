import Mathlib

/-!
# Conjecture 00000000030 is false

The conjecture: there is an absolute `c > 0` such that whenever `A ⊆ [N]` with `|A| ≥ N^(1/2 - c)`,
the set `{a² : a ∈ A}` is intersective.

The conjecture as written is universal ("whenever"); that is the reading refuted here, under four
notions of "intersective":

* the standard Sárközy–Furstenberg notion: `R` is intersective if every `E ⊆ ℕ` of positive upper
  density contains two distinct elements whose difference lies in `R`, i.e. `R ∩ (E - E) ≠ ∅` with a
  nonzero difference (`IsIntersective`), or the same tested only on sets `E` of positive natural
  density (`IsIntersectiveNat`, a weaker requirement);
* the literal parenthetical of the statement: `R` meets every set of positive (upper or natural)
  density (`MeetsDenseSets`, `MeetsDenseSetsNat`).

Witness: `A_N = {a ∈ [N] : 3 ∤ a}` (any `N ≥ 3`; it lies in `{1,…,N}` and in `{0,…,N-1}`) has
`|A_N| ≥ √N ≥ N^(1/2 - c)`, every `a²` with `a ∈ A_N` is `≡ 1 (mod 3)`, while `E = 3ℕ` has natural
density `1/3` and `E - E ⊆ 3ℤ`. This is the classical local obstruction: an intersective set must
contain a nonzero multiple of every natural number.
-/

open Filter Topology

namespace C30

/-! ### Densities and intersectivity -/

/-- `|E ∩ [N]|`, where `[N] = {1, …, N}`. -/
noncomputable def countIn (E : Set ℕ) (N : ℕ) : ℕ := by
  classical exact ((Finset.Icc 1 N).filter (· ∈ E)).card

/-- Upper density `limsup_{N → ∞} |E ∩ [N]| / N`. -/
noncomputable def upperDensity (E : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => (countIn E N : ℝ) / N) atTop

/-- `E` has natural density `d`: `|E ∩ [N]| / N → d`. -/
def HasNatDensity (E : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (countIn E N : ℝ) / N) atTop (𝓝 d)

/-- Standard notion: every `E` of positive upper density contains two distinct elements `x ≠ y`
whose difference `x - y` lies in `R` (so `R ∩ (E - E) ≠ ∅` with a nonzero difference). -/
def IsIntersective (R : Set ℕ) : Prop :=
  ∀ E : Set ℕ, 0 < upperDensity E → ∃ x ∈ E, ∃ y ∈ E, x ≠ y ∧ ∃ r ∈ R, (r : ℤ) = (x : ℤ) - y

/-- Weaker variant: only sets `E` of positive natural density are tested (again with `x ≠ y`). -/
def IsIntersectiveNat (R : Set ℕ) : Prop :=
  ∀ E : Set ℕ, (∃ d > 0, HasNatDensity E d) →
    ∃ x ∈ E, ∃ y ∈ E, x ≠ y ∧ ∃ r ∈ R, (r : ℤ) = (x : ℤ) - y

/-- Literal parenthetical: `R` meets every set of positive upper density. -/
def MeetsDenseSets (R : Set ℕ) : Prop :=
  ∀ E : Set ℕ, 0 < upperDensity E → (R ∩ E).Nonempty

/-- Literal parenthetical, natural-density version. -/
def MeetsDenseSetsNat (R : Set ℕ) : Prop :=
  ∀ E : Set ℕ, (∃ d > 0, HasNatDensity E d) → (R ∩ E).Nonempty

/-- The conjecture, for an ambient interval `box N` (`[N]`) and a notion of intersectivity. -/
def Conjecture (box : ℕ → Finset ℕ) (Intersective : Set ℕ → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∀ A : Finset ℕ, A ⊆ box N →
    (N : ℝ) ^ ((1 : ℝ) / 2 - c) ≤ (A.card : ℝ) → Intersective ((fun a => a ^ 2) '' (A : Set ℕ))

/-! ### The dense test sets `mℕ` -/

/-- The multiples of `m`. -/
def multiples (m : ℕ) : Set ℕ := {n | m ∣ n}

lemma countIn_multiples (m N : ℕ) : countIn (multiples m) N = N / m := by
  classical
  rw [← Nat.Ioc_filter_dvd_card_eq_div N m]
  unfold countIn
  congr 1
  ext x
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  simp only [multiples, Set.mem_ofPred_eq]
  omega

/-- `mℕ` has natural density `1/m`. -/
theorem hasNatDensity_multiples {m : ℕ} (hm : 0 < m) : HasNatDensity (multiples m) (1 / m) := by
  unfold HasNatDensity
  simp_rw [countIn_multiples]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have lower : Tendsto (fun N : ℕ => (1 : ℝ) / m - ((m - 1) / m) / N) atTop (𝓝 (1 / m)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (((m : ℝ) - 1) / m))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h3 : (N : ℝ) + 1 ≤ m * ((N / m : ℕ) : ℝ) + m := by
      have := Nat.lt_div_mul_add (a := N) hm
      exact_mod_cast (by nlinarith [Nat.div_add_mod N m, Nat.mod_lt N hm] : N + 1 ≤ m * (N / m) + m)
    have : (1 : ℝ) / m - ((m - 1) / m) / N = ((N : ℝ) - (m - 1)) / (m * N) := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) hN']
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h3 : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
    rw [div_le_div_iff₀ hN' hm']
    rw [le_div_iff₀ hm'] at h3
    nlinarith

theorem upperDensity_multiples {m : ℕ} (hm : 0 < m) : upperDensity (multiples m) = 1 / m :=
  (hasNatDensity_multiples hm).limsup_eq

/-- If `mℕ` and `mℕ - mℕ` both miss `R`, then `R` is not intersective, in any of the four senses. -/
theorem not_intersective_of_multiples {R : Set ℕ} {m : ℕ} (hm : 0 < m)
    (h1 : R ∩ multiples m = ∅)
    (h2 : ¬ ∃ x ∈ multiples m, ∃ y ∈ multiples m, ∃ r ∈ R, (r : ℤ) = (x : ℤ) - y) :
    ¬ IsIntersective R ∧ ¬ IsIntersectiveNat R ∧ ¬ MeetsDenseSets R ∧ ¬ MeetsDenseSetsNat R := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hu : 0 < upperDensity (multiples m) := by rw [upperDensity_multiples hm]; positivity
  have hn : ∃ d > 0, HasNatDensity (multiples m) d :=
    ⟨1 / m, by positivity, hasNatDensity_multiples hm⟩
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨x, hx, y, hy, -, r, hr, e⟩ := h _ hu
    exact h2 ⟨x, hx, y, hy, r, hr, e⟩
  · obtain ⟨x, hx, y, hy, -, r, hr, e⟩ := h _ hn
    exact h2 ⟨x, hx, y, hy, r, hr, e⟩
  · simpa [h1] using h _ hu
  · simpa [h1] using h _ hn

/-- A set of residues `≡ 1 (mod 3)` is not intersective, in any of the four senses: test it
against `E = 3ℕ` (natural density `1/3`), for which `E ∩ R = ∅` and `(E - E) ∩ R = ∅`. -/
theorem not_intersective_of_mod3 {R : Set ℕ} (hR : ∀ r ∈ R, r % 3 = 1) :
    ¬ IsIntersective R ∧ ¬ IsIntersectiveNat R ∧ ¬ MeetsDenseSets R ∧ ¬ MeetsDenseSetsNat R := by
  refine not_intersective_of_multiples (m := 3) (by norm_num) ?_ ?_
  · ext r
    simp only [Set.mem_inter_iff, multiples, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hr hd
    have := hR r hr
    omega
  · rintro ⟨x, hx, y, hy, r, hr, h⟩
    have := hR r hr
    simp only [multiples, Set.mem_ofPred_eq] at hx hy
    omega

/-- No finite set of positive integers is intersective, in any of the four senses: test it
against `E = mℕ` with `m > max R`. -/
theorem finite_not_intersective (R : Finset ℕ) (h0 : 0 ∉ R) :
    ¬ IsIntersective (R : Set ℕ) ∧ ¬ IsIntersectiveNat (R : Set ℕ) ∧
      ¬ MeetsDenseSets (R : Set ℕ) ∧ ¬ MeetsDenseSetsNat (R : Set ℕ) := by
  set m := R.sup id + 1
  have hlt : ∀ r ∈ R, 0 < r ∧ r < m := fun r hr =>
    ⟨Nat.pos_of_ne_zero (fun h => h0 (h ▸ hr)), Nat.lt_succ_of_le (Finset.le_sup (f := id) hr)⟩
  refine not_intersective_of_multiples (m := m) (by omega) ?_ ?_
  · ext r
    simp only [Set.mem_inter_iff, Finset.mem_coe, multiples, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hr hd
    obtain ⟨h1, h2⟩ := hlt r hr
    exact absurd (Nat.le_of_dvd h1 hd) (by omega)
  · rintro ⟨x, hx, y, hy, r, hr, h⟩
    obtain ⟨h1, h2⟩ := hlt r (by simpa using hr)
    simp only [multiples, Set.mem_ofPred_eq] at hx hy
    have hxy : x = y + r := by omega
    have : m ∣ r := (Nat.dvd_add_right hy).mp (hxy ▸ hx)
    exact absurd (Nat.le_of_dvd h1 this) (by omega)

/-! ### The sets `A_N` -/

lemma sq_mod_three {a : ℕ} (h : ¬ 3 ∣ a) : a ^ 2 % 3 = 1 := by
  have : a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases this with h1 | h1 <;> simp [Nat.pow_mod, h1]

/-- `A_N = {a < N : 3 ∤ a}`; it lies in `{1, …, N}` and in `{0, …, N - 1}`. -/
def goodSet (N : ℕ) : Finset ℕ := (Finset.range N).filter (fun a => ¬ 3 ∣ a)

lemma goodSet_subset_Icc (N : ℕ) : goodSet N ⊆ Finset.Icc 1 N := by
  intro a ha
  simp only [goodSet, Finset.mem_filter, Finset.mem_range] at ha
  simp only [Finset.mem_Icc]
  omega

lemma goodSet_subset_range (N : ℕ) : goodSet N ⊆ Finset.range N := Finset.filter_subset _ _

lemma count_bound (N : ℕ) : 2 * N ≤ 3 * Nat.count (fun a => ¬ 3 ∣ a) N + 2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N 3 with h | h
    · interval_cases N <;> simp [Nat.count_succ]
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
      have hM := ih M (by omega)
      rw [Nat.count_add]
      have h3 : Nat.count (fun k => ¬ 3 ∣ M + k) 3 = 2 := by
        simp only [Nat.count_succ, Nat.count_zero]
        split_ifs <;> omega
      omega

lemma goodSet_card_bound (N : ℕ) : 2 * N ≤ 3 * (goodSet N).card + 2 := by
  have := count_bound N
  rwa [Nat.count_eq_card_filter_range] at this

/-- `|A_N| ≥ √N ≥ N^(1/2 - c)` for every `N ≥ 3` and every `c ≥ 0`. -/
theorem goodSet_size {N : ℕ} (hN : 3 ≤ N) {c : ℝ} (hc : 0 ≤ c) :
    Real.sqrt N ≤ (goodSet N).card ∧ (N : ℝ) ^ ((1 : ℝ) / 2 - c) ≤ (goodSet N).card := by
  have hm := goodSet_card_bound N
  set m := (goodSet N).card
  have hm2 : 2 ≤ m := by omega
  have h2 : N ≤ 2 * m := by omega
  have hsq : N ≤ m ^ 2 := by nlinarith
  have hs : Real.sqrt N ≤ m := by
    calc Real.sqrt N ≤ Real.sqrt ((m : ℝ) ^ 2) := Real.sqrt_le_sqrt (by exact_mod_cast hsq)
      _ = m := Real.sqrt_sq (Nat.cast_nonneg _)
  refine ⟨hs, ?_⟩
  calc (N : ℝ) ^ ((1 : ℝ) / 2 - c) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by linarith)
    _ = Real.sqrt N := (Real.sqrt_eq_rpow _).symm
    _ ≤ m := hs

lemma goodSet_squares_mod3 (N : ℕ) : ∀ r ∈ (fun a => a ^ 2) '' (goodSet N : Set ℕ), r % 3 = 1 := by
  rintro r ⟨a, ha, rfl⟩
  simp only [goodSet, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha
  exact sq_mod_three ha.2

/-! ### Main results -/

/-- **Main theorem.** For every `c ≥ 0` and every `N ≥ 3`, the set `A_N = {a ∈ [N] : 3 ∤ a}`
satisfies the hypotheses of the conjecture (under both conventions for `[N]`), yet its set of
squares is not intersective in any of the four senses. -/
theorem main_family (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hN : 3 ≤ N) :
    goodSet N ⊆ Finset.Icc 1 N ∧ goodSet N ⊆ Finset.range N ∧
      (N : ℝ) ^ ((1 : ℝ) / 2 - c) ≤ (goodSet N).card ∧ Real.sqrt N ≤ (goodSet N).card ∧
      ¬ IsIntersective ((fun a => a ^ 2) '' (goodSet N : Set ℕ)) ∧
      ¬ IsIntersectiveNat ((fun a => a ^ 2) '' (goodSet N : Set ℕ)) ∧
      ¬ MeetsDenseSets ((fun a => a ^ 2) '' (goodSet N : Set ℕ)) ∧
      ¬ MeetsDenseSetsNat ((fun a => a ^ 2) '' (goodSet N : Set ℕ)) := by
  obtain ⟨hs, hp⟩ := goodSet_size hN hc
  exact ⟨goodSet_subset_Icc N, goodSet_subset_range N, hp, hs,
    not_intersective_of_mod3 (goodSet_squares_mod3 N)⟩

lemma not_conjecture_of {box : ℕ → Finset ℕ} {P : Set ℕ → Prop}
    (hbox : ∀ N, goodSet N ⊆ box N)
    (hP : ∀ N, ¬ P ((fun a => a ^ 2) '' (goodSet N : Set ℕ))) : ¬ Conjecture box P := by
  rintro ⟨c, hc, h⟩
  exact hP 3 (h 3 (goodSet 3) (hbox 3) (goodSet_size le_rfl hc.le).2)

/-- **The conjecture is false**, for `[N] = {1,…,N}` and for `[N] = {0,…,N-1}`, and for each of
the four notions of "intersective". -/
theorem conjecture_false :
    ¬ Conjecture (Finset.Icc 1) IsIntersective ∧ ¬ Conjecture (Finset.Icc 1) IsIntersectiveNat ∧
    ¬ Conjecture (Finset.Icc 1) MeetsDenseSets ∧ ¬ Conjecture (Finset.Icc 1) MeetsDenseSetsNat ∧
    ¬ Conjecture Finset.range IsIntersective ∧ ¬ Conjecture Finset.range IsIntersectiveNat ∧
    ¬ Conjecture Finset.range MeetsDenseSets ∧ ¬ Conjecture Finset.range MeetsDenseSetsNat := by
  have h := fun N => not_intersective_of_mod3 (goodSet_squares_mod3 N)
  exact ⟨not_conjecture_of goodSet_subset_Icc (fun N => (h N).1),
    not_conjecture_of goodSet_subset_Icc (fun N => (h N).2.1),
    not_conjecture_of goodSet_subset_Icc (fun N => (h N).2.2.1),
    not_conjecture_of goodSet_subset_Icc (fun N => (h N).2.2.2),
    not_conjecture_of goodSet_subset_range (fun N => (h N).1),
    not_conjecture_of goodSet_subset_range (fun N => (h N).2.1),
    not_conjecture_of goodSet_subset_range (fun N => (h N).2.2.1),
    not_conjecture_of goodSet_subset_range (fun N => (h N).2.2.2)⟩

/-- **Finitary reading.** For every `M`, the set `B_M = 3ℕ ∩ [M]` has `|B_M| ≥ (M - 2)/3`, and
neither `B_M` nor `B_M - B_M` meets the squares of any `A_N`. So no finitary density version
(with any threshold `δ ≤ 1/4` and `M ≥ 8`) can hold either. -/
theorem finitary_witness (N M : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 M ∧ M ≤ 3 * B.card + 2 ∧
      ∀ x ∈ B, ∀ y ∈ B, ∀ a ∈ goodSet N, (a ^ 2 : ℤ) ≠ (x : ℤ) - y ∧ a ^ 2 ≠ x := by
  classical
  refine ⟨(Finset.Icc 1 M).filter (· ∈ multiples 3), Finset.filter_subset _ _, ?_, ?_⟩
  · have := countIn_multiples 3 M
    unfold countIn at this
    rw [this]
    omega
  · intro x hx y hy a ha
    simp only [Finset.mem_filter] at hx hy
    have hR := goodSet_squares_mod3 N (a ^ 2) ⟨a, by simpa using ha, rfl⟩
    have hx3 : 3 ∣ x := hx.2
    have hy3 : 3 ∣ y := hy.2
    constructor
    · intro h
      have : ((a ^ 2 : ℕ) : ℤ) = (x : ℤ) - y := by push_cast; exact h
      omega
    · intro h
      omega

/-- **Infinite-`A` reading.** `A_∞ = {a : 3 ∤ a}` has `|A_∞ ∩ [N]| ≥ N^(1/2 - c)` for all `N ≥ 3`,
and its squares are not intersective in any of the four senses. -/
theorem infinite_version (c : ℝ) (hc : 0 ≤ c) :
    (∀ N : ℕ, 3 ≤ N → (N : ℝ) ^ ((1 : ℝ) / 2 - c) ≤ countIn {a | ¬ 3 ∣ a} N) ∧
      ¬ IsIntersective ((fun a => a ^ 2) '' {a | ¬ 3 ∣ a}) ∧
      ¬ IsIntersectiveNat ((fun a => a ^ 2) '' {a | ¬ 3 ∣ a}) ∧
      ¬ MeetsDenseSets ((fun a => a ^ 2) '' {a | ¬ 3 ∣ a}) ∧
      ¬ MeetsDenseSetsNat ((fun a => a ^ 2) '' {a | ¬ 3 ∣ a}) := by
  classical
  refine ⟨fun N hN => ?_, not_intersective_of_mod3 ?_⟩
  · refine (goodSet_size hN hc).2.trans ?_
    have : goodSet N ⊆ (Finset.Icc 1 N).filter (· ∈ {a | ¬ 3 ∣ a}) := by
      intro a ha
      have h1 := goodSet_subset_Icc N ha
      simp only [goodSet, Finset.mem_filter] at ha
      simp only [Finset.mem_filter, Set.mem_ofPred_eq]
      exact ⟨h1, ha.2⟩
    unfold countIn
    exact_mod_cast Finset.card_le_card (by convert this)
  · rintro r ⟨a, ha, rfl⟩
    exact sq_mod_three ha

/-- **Every finite `A`.** For every `N` and every `A ⊆ {1, …, N}` (of any size), the set
`{a² : a ∈ A}` is not intersective in any of the four senses (these are infinitary notions, and a
finite set of positive integers never satisfies them). This says nothing about an infinite square
set, nor about a finitary (quantitative) sparsification statement; the reading refuted in this file
is the universal one ("whenever"), via `conjecture_false`. -/
theorem no_finite_square_set_intersective (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    ¬ IsIntersective ((fun a => a ^ 2) '' (A : Set ℕ)) ∧
      ¬ IsIntersectiveNat ((fun a => a ^ 2) '' (A : Set ℕ)) ∧
      ¬ MeetsDenseSets ((fun a => a ^ 2) '' (A : Set ℕ)) ∧
      ¬ MeetsDenseSetsNat ((fun a => a ^ 2) '' (A : Set ℕ)) := by
  classical
  have h0 : 0 ∉ A.image (fun a => a ^ 2) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro a ha h
    have := Finset.mem_Icc.mp (hA ha)
    have : a = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    omega
  have := finite_not_intersective (A.image (fun a => a ^ 2)) h0
  simpa only [Finset.coe_image] using this

end C30
