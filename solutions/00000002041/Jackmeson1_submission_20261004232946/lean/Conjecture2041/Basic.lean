import Mathlib

/-!
# Conjecture 00000002041 is false

**Conjecture (official text).** Definition: a complete sequence satisfies
`Σ_{a ∈ A, a ≤ n} ≥ n`. Conjecture: every set of density `≥ 0.24` is a complete sequence covering
minimally; the threshold `0.24` can be improved to an explicit `(1 - 1/e)`-type bound.

The definition is garbled (the summand of `Σ` is missing) and "density" is unqualified, so we
formalize the enumerated readings below, which include the usual universal reading of the displayed
definition, and refute the first clause under all of them with ONE witness

  `A = {1} ∪ {4k : k ≥ 1}`.

Density readings (each holds for `A`, with value `1/4 ≥ 0.24`):
* natural (asymptotic) density `lim |A ∩ [1,n]| / n` (exists and equals `1/4`);
* lower density `liminf |A ∩ [1,n]| / n`, upper density `limsup |A ∩ [1,n]| / n`;
* Schnirelmann density (Mathlib's `schnirelmannDensity`, `inf_{n ≥ 1} |A ∩ [1,n]| / n`).

Completeness readings (each fails for `A`):
* standard completeness: every positive integer is a sum of distinct elements of `A`;
* eventual completeness: every sufficiently large integer is such a sum;
* "covering minimally": `A` is a minimal complete sequence, or contains one;
* the stated `Σ` condition with summand `a`: `Σ_{a ∈ A, a ≤ n} a ≥ n` for all `n ≥ 1`;
* the stated `Σ` condition with summand `1`: `#{a ∈ A : a ≤ n} ≥ n` for all `n ≥ 1`.

Key fact: every element of `A` is `≡ 0` or `1 (mod 4)` and `1` is the only element `≡ 1`, so every
sum of distinct elements of `A` is `≡ 0` or `1 (mod 4)`; no `n ≡ 2, 3 (mod 4)` is representable.

Excluded variant: the *eventual* summand-`a` condition (`Σ_{a ∈ A, a ≤ n} a ≥ n` only for large `n`)
is not refuted; `A` satisfies it for every `n ≥ 8` (it fails only at `n = 2, 3, 6, 7`).
-/

open Filter Topology Finset
open scoped Classical

namespace C2041

/-! ## Definitions (for an arbitrary set `S ⊆ ℕ`) -/

/-- The counting function `|S ∩ {1, …, n}|`, exactly the quantity used by Mathlib's
`schnirelmannDensity`. -/
noncomputable def count (S : Set ℕ) (n : ℕ) : ℕ := #{a ∈ Ioc 0 n | a ∈ S}

/-- `S` has natural (asymptotic) density `δ`: `|S ∩ [1,n]| / n → δ`. -/
def HasNatDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (count S n : ℝ) / n) atTop (𝓝 δ)

/-- Lower asymptotic density `liminf |S ∩ [1,n]| / n`. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  liminf (fun n : ℕ => (count S n : ℝ) / n) atTop

/-- Upper asymptotic density `limsup |S ∩ [1,n]| / n`. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  limsup (fun n : ℕ => (count S n : ℝ) / n) atTop

/-- `n` is a sum of distinct elements of `S` (each element used at most once). -/
def IsSubsetSum (S : Set ℕ) (n : ℕ) : Prop :=
  ∃ T : Finset ℕ, (T : Set ℕ) ⊆ S ∧ ∑ a ∈ T, a = n

/-- Complete sequence (standard): every positive integer is a sum of distinct elements of `S`. -/
def IsCompleteSeq (S : Set ℕ) : Prop := ∀ n : ℕ, 0 < n → IsSubsetSum S n

/-- Eventually complete: every sufficiently large integer is a sum of distinct elements. -/
def IsEventuallyComplete (S : Set ℕ) : Prop := ∃ N : ℕ, ∀ n ≥ N, IsSubsetSum S n

/-- Minimal complete sequence: complete, and removing any element destroys completeness. -/
def IsMinimalComplete (S : Set ℕ) : Prop :=
  IsCompleteSeq S ∧ ∀ x ∈ S, ¬ IsCompleteSeq (S \ {x})

/-- The stated condition with summand `a`: `Σ_{a ∈ S, a ≤ n} a ≥ n` for every `n ≥ 1`. -/
def SigmaCond (S : Set ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ ∑ a ∈ range (n + 1) with a ∈ S, a

/-- The stated condition with summand `1`: `#{a ∈ S : a ≤ n} ≥ n` for every `n ≥ 1`. -/
def CountCond (S : Set ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ #{a ∈ range (n + 1) | a ∈ S}

/-- All readings of "`S` has density `≥ 0.24`". -/
noncomputable def densityReadings : List (Set ℕ → Prop) :=
  [fun S => ∃ δ : ℝ, HasNatDensity S δ ∧ (0.24 : ℝ) ≤ δ,
   fun S => (0.24 : ℝ) ≤ lowerDensity S,
   fun S => (0.24 : ℝ) ≤ upperDensity S,
   fun S => (0.24 : ℝ) ≤ schnirelmannDensity S]

/-- All readings of "`S` is a complete sequence (covering minimally)". -/
def completenessReadings : List (Set ℕ → Prop) :=
  [IsCompleteSeq, IsEventuallyComplete, IsMinimalComplete,
   fun S => ∃ B ⊆ S, IsCompleteSeq B,
   fun S => ∃ B ⊆ S, IsMinimalComplete B,
   fun S => ∃ B ⊆ S, IsEventuallyComplete B,
   SigmaCond, CountCond]

/-! ## The witness -/

/-- The witness `A = {1} ∪ {4k : k ≥ 1}`. -/
def A : Set ℕ := {n | n = 1 ∨ (0 < n ∧ 4 ∣ n)}

/-- Every sum of distinct elements of `A` is `≡ 0` or `1 (mod 4)`. -/
lemma sum_mod_four (T : Finset ℕ) (hT : (T : Set ℕ) ⊆ A) :
    (∑ a ∈ T, a) % 4 = 0 ∨ (∑ a ∈ T, a) % 4 = 1 := by
  have h4 : 4 ∣ ∑ a ∈ T.erase 1, a := Finset.dvd_sum fun a ha => by
    rcases hT (Finset.mem_of_mem_erase ha) with h | ⟨_, h⟩
    · exact absurd h (Finset.ne_of_mem_erase ha)
    · exact h
  by_cases h1 : 1 ∈ T
  · rw [← Finset.add_sum_erase T _ h1]; omega
  · rw [Finset.erase_eq_of_notMem h1] at h4; omega

/-- No `n ≡ 2, 3 (mod 4)` is a sum of distinct elements of `A`. -/
lemma not_subsetSum (n : ℕ) (hn : n % 4 = 2 ∨ n % 4 = 3) : ¬ IsSubsetSum A n := by
  rintro ⟨T, hT, rfl⟩
  have := sum_mod_four T hT
  omega

lemma isSubsetSum_mono {S B : Set ℕ} (h : B ⊆ S) {n : ℕ} (hB : IsSubsetSum B n) :
    IsSubsetSum S n := by
  obtain ⟨T, hT, hs⟩ := hB
  exact ⟨T, hT.trans h, hs⟩

theorem A_not_complete : ¬ IsCompleteSeq A := fun h => not_subsetSum 2 (by norm_num) (h 2 two_pos)

theorem A_not_eventuallyComplete : ¬ IsEventuallyComplete A := by
  rintro ⟨N, hN⟩
  exact not_subsetSum (4 * N + 2) (by omega) (hN _ (by omega))

/-- No subset of `A` is complete (so `A` neither is nor contains a (minimal) complete sequence). -/
theorem subset_not_complete {B : Set ℕ} (hB : B ⊆ A) : ¬ IsCompleteSeq B :=
  fun h => not_subsetSum 2 (by norm_num) (isSubsetSum_mono hB (h 2 two_pos))

theorem subset_not_eventuallyComplete {B : Set ℕ} (hB : B ⊆ A) : ¬ IsEventuallyComplete B := by
  rintro ⟨N, hN⟩
  exact not_subsetSum (4 * N + 2) (by omega) (isSubsetSum_mono hB (hN _ (by omega)))

/-- `Σ_{a ∈ A, a ≤ 2} a = 1 < 2`. -/
theorem A_not_sigmaCond : ¬ SigmaCond A := by
  intro h
  have hset : ({a ∈ range (2 + 1) | a ∈ A} : Finset ℕ) = {1} := by
    ext a; rw [mem_filter]; simp only [A, Set.mem_ofPred_eq, mem_range, mem_singleton]; omega
  have := h 2 two_pos
  rw [hset, sum_singleton] at this
  omega

/-- `#{a ∈ A : a ≤ 2} = 1 < 2`. -/
theorem A_not_countCond : ¬ CountCond A := by
  intro h
  have hset : ({a ∈ range (2 + 1) | a ∈ A} : Finset ℕ) = {1} := by
    ext a; rw [mem_filter]; simp only [A, Set.mem_ofPred_eq, mem_range, mem_singleton]; omega
  have := h 2 two_pos
  rw [hset, card_singleton] at this
  omega

/-! ## Densities of the witness -/

/-- `|A ∩ [1,n]| = 1 + ⌊n/4⌋` for `n ≥ 1`. -/
lemma count_A (n : ℕ) (hn : 0 < n) : count A n = 1 + n / 4 := by
  unfold count
  have hsplit : ({a ∈ Ioc 0 n | a ∈ A} : Finset ℕ) =
      ({a ∈ Ioc 0 n | a = 1} : Finset ℕ) ∪ {a ∈ Ioc 0 n | 4 ∣ a} := by
    ext a; rw [mem_union, mem_filter, mem_filter, mem_filter]; simp only [A, Set.mem_ofPred_eq, mem_Ioc]; omega
  have hone : ({a ∈ Ioc 0 n | a = 1} : Finset ℕ) = {1} := by
    ext a; simp only [mem_filter, mem_Ioc, mem_singleton]; omega
  have hdisj : Disjoint ({a ∈ Ioc 0 n | a = 1} : Finset ℕ) {a ∈ Ioc 0 n | 4 ∣ a} := by
    rw [hone, Finset.disjoint_singleton_left, mem_filter]; omega
  rw [hsplit, card_union_of_disjoint hdisj, hone, card_singleton, Nat.Ioc_filter_dvd_card_eq_div]

/-- `1/4 ≤ |A ∩ [1,n]| / n ≤ 1/4 + 1/n` for `n ≥ 1`. -/
lemma count_A_bounds (n : ℕ) (hn : 0 < n) :
    (1 / 4 : ℝ) ≤ (count A n : ℝ) / n ∧ (count A n : ℝ) / n ≤ 1 / 4 + 1 / n := by
  rw [count_A n hn]
  have h1 : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
  have h2 : n < 4 * (n / 4) + 4 := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have r1 : (4 : ℝ) * ((n / 4 : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
  have r2 : (n : ℝ) < 4 * ((n / 4 : ℕ) : ℝ) + 4 := by exact_mod_cast h2
  push_cast
  constructor
  · rw [le_div_iff₀ hnr]; linarith
  · rw [div_le_iff₀ hnr, add_mul, one_div_mul_cancel hnr.ne']; linarith

/-- The natural density of `A` exists and equals `1/4`. -/
theorem A_hasNatDensity : HasNatDensity A (1 / 4) := by
  have hup : Tendsto (fun n : ℕ => (1 / 4 : ℝ) + 1 / n) atTop (𝓝 (1 / 4)) := by
    simpa using (tendsto_const_nhds (x := (1 / 4 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · exact eventually_atTop.2 ⟨1, fun n hn => (count_A_bounds n hn).1⟩
  · exact eventually_atTop.2 ⟨1, fun n hn => (count_A_bounds n hn).2⟩

theorem A_lowerDensity : lowerDensity A = 1 / 4 := A_hasNatDensity.liminf_eq

theorem A_upperDensity : upperDensity A = 1 / 4 := A_hasNatDensity.limsup_eq

/-- The Schnirelmann density of `A` is at least `1/4`. -/
theorem A_schnirelmann : (1 / 4 : ℝ) ≤ schnirelmannDensity A :=
  le_schnirelmannDensity_iff.2 fun n hn => (count_A_bounds n hn).1

/-! ## Main theorem -/

/-- `A` has density `≥ 0.24` under each enumerated density reading. -/
theorem A_dense : ∀ D ∈ densityReadings, D A := by
  have q : (0.24 : ℝ) ≤ 1 / 4 := by norm_num
  simp only [densityReadings, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨⟨1 / 4, A_hasNatDensity, q⟩, A_lowerDensity ▸ q, A_upperDensity ▸ q,
    q.trans A_schnirelmann⟩

/-- `A` fails each enumerated completeness reading. -/
theorem A_not_complete_any : ∀ C ∈ completenessReadings, ¬ C A := by
  simp only [completenessReadings, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨A_not_complete, A_not_eventuallyComplete, fun h => A_not_complete h.1,
    fun ⟨B, hB, h⟩ => subset_not_complete hB h, fun ⟨B, hB, h⟩ => subset_not_complete hB h.1,
    fun ⟨B, hB, h⟩ => subset_not_eventuallyComplete hB h, A_not_sigmaCond, A_not_countCond⟩

/-- **Conjecture 00000002041 is false.** For each enumerated reading `D` of "density `≥ 0.24`"
and each enumerated reading `C` of "is a complete sequence (covering minimally)", the claim
"every set satisfying `D` satisfies `C`" fails, and so does its conjunction with any further
clause `P` (the `(1 - 1/e)`-improvement clause). One witness, `A = {1} ∪ {4k : k ≥ 1}`, works
for all enumerated readings. -/
theorem conjecture_2041_false (P : Prop) :
    ∀ D ∈ densityReadings, ∀ C ∈ completenessReadings,
      ¬ ((∀ S : Set ℕ, D S → C S) ∧ P) :=
  fun D hD C hC h => A_not_complete_any C hC (h.1 A (A_dense D hD))

/-! ## Supplement: no natural/lower-density threshold `θ ≤ 1` works

`B = ℕ \ {2}` has natural density `1` but `2` is not a sum of distinct elements of `B`. So the
"improved `(1 - 1/e)`-type threshold" clause also fails under the natural and lower density readings
with standard completeness, whatever threshold `θ ≤ 1` is meant. -/

/-- `B = ℕ \ {2}`. -/
def B : Set ℕ := {n | n ≠ 2}

theorem B_not_complete : ¬ IsCompleteSeq B := by
  rintro h
  obtain ⟨T, hT, hs⟩ := h 2 two_pos
  have hsub : T ⊆ ({0, 1} : Finset ℕ) := fun a ha => by
    have hle : a ≤ ∑ x ∈ T, x := Finset.single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) ha
    have hne : a ≠ 2 := hT ha
    simp only [mem_insert, mem_singleton]; omega
  have := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
  simp at this; omega

lemma count_B (n : ℕ) (hn : 2 ≤ n) : count B n = n - 1 := by
  unfold count
  have : ({a ∈ Ioc 0 n | a ∈ B} : Finset ℕ) = (Ioc 0 n).erase 2 := by
    ext a; rw [mem_filter, mem_erase]; simp only [B, Set.mem_ofPred_eq]; tauto
  rw [this, card_erase_of_mem (by simp; omega), Nat.card_Ioc]; rfl

theorem B_hasNatDensity : HasNatDensity B 1 := by
  have hlow : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_ <;>
    refine eventually_atTop.2 ⟨2, fun n hn => ?_⟩ <;>
    have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  · rw [count_B n hn, Nat.cast_sub (by omega), le_div_iff₀ hnr, sub_mul,
      one_div_mul_cancel hnr.ne']; simp
  · rw [count_B n hn, Nat.cast_sub (by omega), div_le_iff₀ hnr]; simp

/-- For every threshold `θ ≤ 1`, "every set of natural (or lower) density `≥ θ` is complete" is
false. -/
theorem no_threshold (θ : ℝ) (hθ : θ ≤ 1) :
    ¬ (∀ S : Set ℕ, (∃ δ : ℝ, HasNatDensity S δ ∧ θ ≤ δ) → IsCompleteSeq S) ∧
    ¬ (∀ S : Set ℕ, θ ≤ lowerDensity S → IsCompleteSeq S) :=
  ⟨fun h => B_not_complete (h B ⟨1, B_hasNatDensity, hθ⟩),
   fun h => B_not_complete (h B ((show lowerDensity B = 1 from B_hasNatDensity.liminf_eq) ▸ hθ))⟩

end C2041
