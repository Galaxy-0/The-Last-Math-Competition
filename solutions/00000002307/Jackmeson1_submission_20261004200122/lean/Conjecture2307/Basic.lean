import Mathlib

/-!
# Conjecture 00000002307 is false

Conjecture 00000002307 reads:

> Definition: The Fitting height and derived length are two invariants of solvable groups.
> Conjecture: Fitting height ≤ 2·(derived length) − 1 (a linear bound); the bound is controlled by
> layerwise projections of supersolvable towers; tightness is attained by extremal examples with
> total derived chain 2.

We formalize the two mathematical clauses and refute each of them:

* (i)  the linear bound `h(G) ≤ 2·dl(G) − 1` for every finite solvable group `G` (read in `ℤ`);
* (iii) tightness at derived length two: some solvable group has `dl(G) = 2` and `h(G) = 2·dl(G) − 1`.

Clause (ii) ("controlled by layerwise projections of supersolvable towers") is not a precise
mathematical statement; it is not needed, because the conjunction of the three clauses fails as soon
as clause (i) or clause (iii) fails, and both fail.

Definitions follow the standard ones (e.g. Wikipedia, "Fitting length" and "Solvable group"):

* a *Fitting chain* of length `n` is a subnormal series `1 = H₀ ⊴ H₁ ⊴ ⋯ ⊴ Hₙ = G` whose successive
  quotients `Hᵢ₊₁ / Hᵢ` are nilpotent; the *Fitting length* (Fitting height, nilpotent length) is the
  smallest length of a Fitting chain;
* the *derived length* is the least `n` with `G⁽ⁿ⁾ = 1`.

Main results:

* `fittingLength_le_derivedLength` : `h(G) ≤ dl(G)` for every solvable group;
* `not_linearBound` : the trivial group violates clause (i), since `h = dl = 0` and `0 > 2·0 − 1`;
* `not_tightAtDerivedLengthTwo` : clause (iii) fails, since `dl(G) = 2` forces `h(G) ≤ 2 < 3`;
* `conjecture_00000002307_false` : the conjecture (clauses (i) and (iii)) is false.

For completeness we also record what *is* true: `linearBound_of_nontrivial` (clause (i) holds for
nontrivial groups) and `derivedLength_le_one_of_tight` (equality `h = 2·dl − 1` forces `dl ≤ 1`).
-/

namespace Conjecture2307

universe u

section Definitions

variable (G : Type u) [Group G]

/-- A Fitting chain of length `n`: subgroups `1 = H 0 ≤ H 1 ≤ ⋯ ≤ H n = G`, each normal in the
next, with nilpotent successive quotients `H (i+1) / H i`. -/
structure FittingChain (n : ℕ) where
  /-- the terms of the chain (only `H 0, …, H n` matter) -/
  H : ℕ → Subgroup G
  bot : H 0 = ⊥
  top : H n = ⊤
  le_succ : ∀ i < n, H i ≤ H (i + 1)
  normal : ∀ i < n, ((H i).subgroupOf (H (i + 1))).Normal
  nilpotent : ∀ i < n, ∀ [((H i).subgroupOf (H (i + 1))).Normal],
    Group.IsNilpotent (H (i + 1) ⧸ (H i).subgroupOf (H (i + 1)))

/-- The Fitting length (Fitting height): the smallest length of a Fitting chain. -/
noncomputable def fittingLength : ℕ :=
  sInf {n | Nonempty (FittingChain G n)}

/-- The derived length: the least `n` with `G⁽ⁿ⁾ = 1`. -/
noncomputable def derivedLength : ℕ :=
  sInf {n | derivedSeries G n = ⊥}

end Definitions

/-- Clause (i) of the conjecture: `h(G) ≤ 2·dl(G) − 1` for every finite solvable group, read in `ℤ`. -/
def LinearBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G →
    (fittingLength G : ℤ) ≤ 2 * (derivedLength G : ℤ) - 1

/-- Clause (iii) of the conjecture: the bound is attained by a solvable group of derived length 2. -/
def TightAtDerivedLengthTwo : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsSolvable G ∧ derivedLength G = 2 ∧
    (fittingLength G : ℤ) = 2 * (derivedLength G : ℤ) - 1

section Lemmas

variable {G : Type u} [Group G]

theorem fittingLength_le {n : ℕ} (c : FittingChain G n) : fittingLength G ≤ n :=
  Nat.sInf_le ⟨c⟩

/-- A quotient `A / B` with `⁅A, A⁆ ≤ B` is abelian, hence nilpotent. -/
theorem isNilpotent_quotient_of_commutator_le (A B : Subgroup G) (h : ⁅A, A⁆ ≤ B)
    [(B.subgroupOf A).Normal] : Group.IsNilpotent (A ⧸ B.subgroupOf A) := by
  let _ : CommGroup (A ⧸ B.subgroupOf A) :=
    { (inferInstance : Group (A ⧸ B.subgroupOf A)) with
      mul_comm := by
        intro a b
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        apply h
        have hc := Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2)
        convert hc using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv, mul_inv_rev,
          mul_assoc] }
  infer_instance

theorem derivedSeries_succ_le (k : ℕ) : derivedSeries G (k + 1) ≤ derivedSeries G k := by
  rw [derivedSeries_succ]
  exact Subgroup.commutator_le_left _ _

/-- If `G⁽ᵈ⁾ = 1`, the reversed derived series is a Fitting chain of length `d`. -/
def derivedFittingChain (d : ℕ) (hd : derivedSeries G d = ⊥) : FittingChain G d where
  H i := derivedSeries G (d - i)
  bot := by simpa using hd
  top := by simp
  le_succ i hi := by
    have e : d - i = d - (i + 1) + 1 := by omega
    rw [e]
    exact derivedSeries_succ_le _
  normal _ _ := inferInstance
  nilpotent i hi := by
    intro _
    apply isNilpotent_quotient_of_commutator_le
    have e : d - i = d - (i + 1) + 1 := by omega
    rw [e, derivedSeries_succ]

theorem derivedSeries_derivedLength [Group.IsSolvable G] : derivedSeries G (derivedLength G) = ⊥ :=
  Nat.sInf_mem (Group.IsSolvable.solvable (G := G))

/-- The key inequality: the Fitting length is at most the derived length. -/
theorem fittingLength_le_derivedLength [Group.IsSolvable G] : fittingLength G ≤ derivedLength G :=
  fittingLength_le (derivedFittingChain _ derivedSeries_derivedLength)

theorem one_le_derivedLength [Group.IsSolvable G] [Nontrivial G] : 1 ≤ derivedLength G := by
  by_contra h0
  have h : derivedLength G = 0 := by omega
  have hbot := (derivedSeries_derivedLength (G := G))
  rw [h, derivedSeries_zero] at hbot
  exact bot_ne_top hbot.symm

/-- Clause (i) does hold for every nontrivial solvable group. -/
theorem linearBound_of_nontrivial [Group.IsSolvable G] [Nontrivial G] :
    (fittingLength G : ℤ) ≤ 2 * (derivedLength G : ℤ) - 1 := by
  have h1 := fittingLength_le_derivedLength (G := G)
  have h2 := one_le_derivedLength (G := G)
  omega

/-- Equality in the bound forces derived length at most one (abelian groups). -/
theorem derivedLength_le_one_of_tight [Group.IsSolvable G]
    (h : (fittingLength G : ℤ) = 2 * (derivedLength G : ℤ) - 1) : derivedLength G ≤ 1 := by
  have h1 := fittingLength_le_derivedLength (G := G)
  omega

end Lemmas

section TrivialGroup

theorem derivedLength_unit : derivedLength Unit = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  show derivedSeries Unit 0 = ⊥
  exact Subsingleton.elim _ _

/-- The chain `1 = G` of length zero. -/
def trivialFittingChain : FittingChain Unit 0 where
  H _ := ⊥
  bot := rfl
  top := Subsingleton.elim _ _
  le_succ _ h := absurd h (Nat.not_lt_zero _)
  normal _ h := absurd h (Nat.not_lt_zero _)
  nilpotent _ h := absurd h (Nat.not_lt_zero _)

theorem fittingLength_unit : fittingLength Unit = 0 :=
  Nat.eq_zero_of_le_zero (fittingLength_le trivialFittingChain)

end TrivialGroup

/-- Clause (i) fails: the trivial group is finite and solvable with `h = dl = 0`, and `0 > 2·0 − 1`. -/
theorem not_linearBound : ¬ LinearBound := by
  intro h
  have := h Unit inferInstance
  rw [fittingLength_unit, derivedLength_unit] at this
  norm_num at this

/-- Clause (iii) fails: a solvable group of derived length 2 has Fitting length at most 2 < 3. -/
theorem not_tightAtDerivedLengthTwo : ¬ TightAtDerivedLengthTwo := by
  rintro ⟨G, _, hs, h2, heq⟩
  have := derivedLength_le_one_of_tight heq
  omega

/-- **Conjecture 00000002307 is false**: clauses (i) and (iii) cannot both hold — in fact each one
fails on its own. -/
theorem conjecture_00000002307_false : ¬ (LinearBound ∧ TightAtDerivedLengthTwo) :=
  fun h => not_linearBound h.1

end Conjecture2307
