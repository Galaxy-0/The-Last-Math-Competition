import Mathlib

/-!
# Conjecture 00000000591 (disproof)

Claim: on numerical semigroups of embedding dimension 3, the ratio of the Wilf surplus
`e * n(S) - F(S) - e` to `F(S)` tends to `0` (with an explicit rate).
Here `e` is the embedding dimension, `F` the Frobenius number and `n(S)` the number of
nongaps (elements of `S`) below `F`.

We refute it with the family `S_k = ⟨6, 12k+10, 18k+15⟩` (`k : ℕ`), for which we prove,
for *every* `k`, via an explicit Apery-set membership characterisation (w.r.t. `6`):
* `S_k` is a numerical semigroup of embedding dimension exactly `3`;
* its Frobenius number is `42k+29` (in the sense of Mathlib's `FrobeniusNumber`);
* `n(S_k) = 21k+15` and the genus of `S_k` is `21k+15`;
* the surplus is `21k+13`, so `surplus / F ≥ 1/3` for all `k`, while `F → ∞`.
-/

namespace C591

/-! ## General definitions -/

/-- A numerical semigroup: an additive submonoid of `ℕ` with finite complement. -/
def IsNumericalSemigroup (S : AddSubmonoid ℕ) : Prop := {x : ℕ | x ∉ S}.Finite

/-- The minimal generating system (the atoms): nonzero elements of `S` that are not a sum
of two nonzero elements of `S`. -/
def minimalGenerators (S : AddSubmonoid ℕ) : Set ℕ :=
  {x | x ∈ S ∧ x ≠ 0 ∧ ∀ y ∈ S, ∀ z ∈ S, y + z = x → y = 0 ∨ z = 0}

/-- Embedding dimension: the cardinality of the minimal generating system. -/
noncomputable def embeddingDim (S : AddSubmonoid ℕ) : ℕ := (minimalGenerators S).ncard

/-- `F` is the Frobenius number of `S` (largest gap); this is Mathlib's
`FrobeniusNumber F S`, since the closure of `S` is `S`. -/
def IsFrob (S : AddSubmonoid ℕ) (F : ℕ) : Prop := FrobeniusNumber F (S : Set ℕ)

/-- `n(S)`: the number of nongaps (elements of `S`) smaller than the Frobenius number `F`. -/
noncomputable def nongaps (S : AddSubmonoid ℕ) (F : ℕ) : ℕ := {x : ℕ | x ∈ S ∧ x < F}.ncard

/-- The genus: the number of gaps. -/
noncomputable def genus (S : AddSubmonoid ℕ) : ℕ := {x : ℕ | x ∉ S}.ncard

/-- The Wilf surplus `e * n(S) - F - e` (as an integer). -/
noncomputable def surplus (S : AddSubmonoid ℕ) (F : ℕ) : ℤ :=
  (embeddingDim S : ℤ) * nongaps S F - F - embeddingDim S

/-- The conjecture (Frobenius reading): along embedding-dimension-3 numerical semigroups,
`surplus / F → 0` as `F → ∞`. -/
def RatioTendsToZero : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ S : AddSubmonoid ℕ, IsNumericalSemigroup S →
    embeddingDim S = 3 → ∀ F : ℕ, IsFrob S F → N ≤ F → |(surplus S F : ℝ) / F| < ε

/-- Variant with `g` read as the genus in both places: `(e * n - genus - e) / genus → 0`. -/
def GenusRatioTendsToZero : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ S : AddSubmonoid ℕ, IsNumericalSemigroup S →
    embeddingDim S = 3 → ∀ F : ℕ, IsFrob S F → N ≤ genus S →
      |((embeddingDim S : ℝ) * nongaps S F - genus S - embeddingDim S) / genus S| < ε

/-! ## The family `S_k = ⟨6, 12k+10, 18k+15⟩` -/

/-- `S_k = ⟨6, 12k+10, 18k+15⟩ = ⟨6, 2m, 3m⟩` with `m = 6k+5`. -/
def S (k : ℕ) : AddSubmonoid ℕ := AddSubmonoid.closure {6, 12 * k + 10, 18 * k + 15}

/-- Apery-set membership predicate w.r.t. `6`: the Apery set is
`{0, 2m, 4m, 3m, 5m, 7m}` (residues `0, 4, 2, 3, 1, 5` mod 6), `m = 6k+5`. -/
def P (k x : ℕ) : Prop :=
  x % 6 = 0 ∨ (x % 6 = 4 ∧ 12 * k + 10 ≤ x) ∨ (x % 6 = 2 ∧ 24 * k + 20 ≤ x) ∨
  (x % 6 = 3 ∧ 18 * k + 15 ≤ x) ∨ (x % 6 = 1 ∧ 30 * k + 25 ≤ x) ∨
  (x % 6 = 5 ∧ 42 * k + 35 ≤ x)

instance (k : ℕ) : DecidablePred (P k) := fun x => by unfold P; infer_instance

lemma P_add (k x y : ℕ) (hx : P k x) (hy : P k y) : P k (x + y) := by
  unfold P at *
  rcases hx with h | h | h | h | h | h <;> rcases hy with h' | h' | h' | h' | h' | h' <;> omega

lemma mem_S_of_P (k x : ℕ) (h : P k x) : x ∈ S k := by
  have g6 : (6 : ℕ) ∈ S k := AddSubmonoid.subset_closure (by simp)
  have ga : 12 * k + 10 ∈ S k := AddSubmonoid.subset_closure (by simp)
  have gb : 18 * k + 15 ∈ S k := AddSubmonoid.subset_closure (by simp)
  have six : ∀ t, 6 * t ∈ S k := fun t => by
    have := AddSubmonoid.nsmul_mem (S k) g6 t
    simpa [smul_eq_mul, mul_comm] using this
  -- write `x = w + 6 t` with `w` the Apery element of the residue class
  have key : ∀ w, w ∈ S k → w ≤ x → x % 6 = w % 6 → x ∈ S k := fun w hw hle hmod => by
    have : x = w + 6 * ((x - w) / 6) := by omega
    rw [this]; exact add_mem hw (six _)
  unfold P at h
  rcases h with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
  · exact key 0 (zero_mem _) (Nat.zero_le _) (by omega)
  · exact key _ ga h' (by omega)
  · exact key _ (add_mem ga ga) (by omega) (by omega)
  · exact key _ gb h' (by omega)
  · exact key _ (add_mem ga gb) (by omega) (by omega)
  · exact key _ (add_mem (add_mem ga ga) gb) (by omega) (by omega)

lemma P_of_mem_S (k x : ℕ) (h : x ∈ S k) : P k x := by
  induction h using AddSubmonoid.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    unfold P; omega
  | zero => unfold P; omega
  | add y z _ _ hy hz => exact P_add k y z hy hz

/-- **Apery-set characterisation**, valid for every `k`. -/
theorem mem_S_iff (k x : ℕ) : x ∈ S k ↔ P k x := ⟨P_of_mem_S k x, mem_S_of_P k x⟩

/-- The Frobenius number of `S_k` is `42k+29`, for every `k`. -/
theorem frob_S (k : ℕ) : IsFrob (S k) (42 * k + 29) := by
  unfold IsFrob
  rw [frobeniusNumber_iff, AddSubmonoid.closure_eq]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [mem_S_iff]; unfold P; omega
  · rw [mem_S_iff]; unfold P; omega

lemma gaps_eq (k : ℕ) : {x : ℕ | x ∉ S k} =
    ↑((Finset.range (42 * k + 30)).filter (fun x => ¬ P k x)) := by
  ext x
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range, mem_S_iff]
  constructor
  · intro h; refine ⟨?_, h⟩; by_contra hc; apply h; unfold P; omega
  · exact fun h => h.2

lemma nongaps_eq (k : ℕ) : {x : ℕ | x ∈ S k ∧ x < 42 * k + 29} =
    ↑((Finset.range (42 * k + 30)).filter (fun x => P k x)) := by
  ext x
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range, mem_S_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
  · rintro ⟨h1, h2⟩; refine ⟨h2, ?_⟩
    by_contra hc
    have : x = 42 * k + 29 := by omega
    subst this; unfold P at h2; omega

/-- Symmetry of `S_k`: for `x ≤ F = 42k+29`, `F - x ∈ S_k ↔ x ∉ S_k`. -/
lemma P_symm (k x : ℕ) (hx : x ≤ 42 * k + 29) : P k (42 * k + 29 - x) ↔ ¬ P k x := by
  obtain ⟨y, hy, hxy⟩ : ∃ y, 42 * k + 29 - x = y ∧ x + y = 42 * k + 29 := ⟨_, rfl, by omega⟩
  rw [hy]
  unfold P
  simp only [not_or, not_and, not_le]
  have h : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by omega
  rcases h with h | h | h | h | h | h
  · have : y % 6 = 5 := by omega
    simp [h, this]; omega
  · have : y % 6 = 4 := by omega
    simp [h, this]; omega
  · have : y % 6 = 3 := by omega
    simp [h, this]; omega
  · have : y % 6 = 2 := by omega
    simp [h, this]; omega
  · have : y % 6 = 1 := by omega
    simp [h, this]; omega
  · have : y % 6 = 0 := by omega
    simp [h, this]; omega

/-- Hence `x ↦ F - x` swaps elements and gaps in `[0, F]`. -/
lemma card_P_eq (k : ℕ) :
    ((Finset.range (42 * k + 30)).filter (fun x => P k x)).card =
    ((Finset.range (42 * k + 30)).filter (fun x => ¬ P k x)).card := by
  apply Finset.card_nbij' (fun x => 42 * k + 29 - x) (fun x => 42 * k + 29 - x)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx ⊢
    exact ⟨by omega, fun h => (P_symm k x (by omega)).1 h hx.2⟩
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx ⊢
    exact ⟨by omega, (P_symm k x (by omega)).2 hx.2⟩
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
    have := hx.1; dsimp only; omega
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
    have := hx.1; dsimp only; omega

lemma card_split (k : ℕ) :
    ((Finset.range (42 * k + 30)).filter (fun x => P k x)).card = 21 * k + 15 ∧
    ((Finset.range (42 * k + 30)).filter (fun x => ¬ P k x)).card = 21 * k + 15 := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range (42 * k + 30))
    (fun x => P k x)
  rw [Finset.card_range, card_P_eq] at h
  rw [card_P_eq]; omega

theorem isNumericalSemigroup_S (k : ℕ) : IsNumericalSemigroup (S k) := by
  unfold IsNumericalSemigroup; rw [gaps_eq]; exact Finset.finite_toSet _

theorem genus_S (k : ℕ) : genus (S k) = 21 * k + 15 := by
  unfold genus; rw [gaps_eq, Set.ncard_coe_finset]; exact (card_split k).2

theorem nongaps_S (k : ℕ) : nongaps (S k) (42 * k + 29) = 21 * k + 15 := by
  unfold nongaps; rw [nongaps_eq, Set.ncard_coe_finset]; exact (card_split k).1

/-- The minimal generators of `S_k` are exactly `6, 12k+10, 18k+15`. -/
theorem minimalGenerators_S (k : ℕ) :
    minimalGenerators (S k) = {6, 12 * k + 10, 18 * k + 15} := by
  ext x
  simp only [minimalGenerators, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, mem_S_iff]
  constructor
  · rintro ⟨hx, hx0, hirr⟩
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2, h3⟩ := hne
    -- a non-generator element splits off a generator
    obtain ⟨g, hg, hlt, hp⟩ : ∃ g, (g = 6 ∨ g = 12 * k + 10 ∨ g = 18 * k + 15) ∧ g < x ∧
        P k (x - g) := by
      unfold P at hx
      rcases hx with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
      · exact ⟨6, by omega, by omega, by unfold P; omega⟩
      · exact ⟨6, by omega, by omega, by unfold P; omega⟩
      · exact ⟨12 * k + 10, by omega, by omega, by unfold P; omega⟩
      · exact ⟨6, by omega, by omega, by unfold P; omega⟩
      · exact ⟨18 * k + 15, by omega, by omega, by unfold P; omega⟩
      · exact ⟨18 * k + 15, by omega, by omega, by unfold P; omega⟩
    have hPg : P k g := by unfold P; omega
    have := hirr g hPg (x - g) hp (by omega)
    omega
  · intro hx
    refine ⟨by unfold P; omega, by omega, fun y hy z hz hyz => ?_⟩
    unfold P at hy hz
    rcases hy with h | h | h | h | h | h <;> rcases hz with h' | h' | h' | h' | h' | h' <;> omega

theorem embeddingDim_S (k : ℕ) : embeddingDim (S k) = 3 := by
  unfold embeddingDim
  rw [minimalGenerators_S, Set.ncard_insert_of_notMem (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega),
    Set.ncard_pair (by omega)]

theorem surplus_S (k : ℕ) : surplus (S k) (42 * k + 29) = 21 * k + 13 := by
  unfold surplus; rw [embeddingDim_S, nongaps_S]; push_cast; ring

/-- For every `k`, `surplus(S_k) / F(S_k) ≥ 1/3`. -/
theorem ratio_ge (k : ℕ) : (1 : ℝ) / 3 ≤ (surplus (S k) (42 * k + 29) : ℝ) / (42 * k + 29 : ℕ) := by
  rw [surplus_S, div_le_div_iff₀ (by norm_num) (by positivity)]
  push_cast; nlinarith

/-- **Main theorem.** The conjecture (Frobenius reading) is false. -/
theorem not_ratioTendsToZero : ¬ RatioTendsToZero := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 3) (by norm_num)
  have := hN (S N) (isNumericalSemigroup_S N) (embeddingDim_S N) _ (frob_S N) (by omega)
  have h2 := ratio_ge N
  have hpos : (0 : ℝ) ≤ (surplus (S N) (42 * N + 29) : ℝ) / (42 * N + 29 : ℕ) := by
    rw [surplus_S]; positivity
  rw [abs_of_nonneg hpos] at this
  linarith

/-- **Main theorem (genus reading).** With `g` read as the genus, the ratio is `≥ 1`. -/
theorem not_genusRatioTendsToZero : ¬ GenusRatioTendsToZero := by
  intro h
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  have := hN (S N) (isNumericalSemigroup_S N) (embeddingDim_S N) _ (frob_S N)
    (by rw [genus_S]; omega)
  rw [embeddingDim_S, nongaps_S, genus_S] at this
  have hval : ((3 : ℕ) : ℝ) * ((21 * N + 15 : ℕ) : ℝ) - ((21 * N + 15 : ℕ) : ℝ) - ((3 : ℕ) : ℝ)
      = 2 * ((21 * N + 15 : ℕ) : ℝ) - 3 := by ring
  rw [hval] at this
  have hg : (0 : ℝ) < ((21 * N + 15 : ℕ) : ℝ) := by positivity
  have hge : (1 : ℝ) ≤ (2 * ((21 * N + 15 : ℕ) : ℝ) - 3) / ((21 * N + 15 : ℕ) : ℝ) := by
    rw [le_div_iff₀ hg]; push_cast; linarith
  rw [abs_of_nonneg (by linarith)] at this
  linarith

end C591
