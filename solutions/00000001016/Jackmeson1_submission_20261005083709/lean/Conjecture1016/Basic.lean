import Mathlib

/-!
# Conjecture 00000001016: no binary self-dual `[84,12]` code exists

Conjecture text: "The [84,12,12] binary extremal self-dual code ... does not exist; moreover,
the automorphism group of every [84,12] binary self-dual code contains no element of order 11,
and the minimum distance is at most 11."

Standard definitions (MacWilliams-Sloane, Huffman-Pless): a binary linear `[n,k]` code is a
`k`-dimensional subspace `C` of `F_2^n`; its dual is `C^perp = {x | x . c = 0 for all c in C}` for
the standard dot product; `C` is self-dual iff `C = C^perp`; the minimum distance is the least
Hamming weight of a nonzero codeword; an automorphism is a coordinate permutation mapping `C`
onto `C` (over `F_2` the monomial automorphisms are exactly the permutations).

Since the dot product is nondegenerate, `dim C + dim C^perp = n`, so a self-dual code has
`2 * dim C = n`. For `n = 84` this forces `dim C = 42`, so no self-dual `[84,12]` code exists.
The first claim is therefore proved outright, and the two universal claims hold vacuously.
-/

open Module

namespace C1016

/-- Binary words of length `n`, i.e. `F_2^n`. -/
abbrev Word (n : ℕ) := Fin n → ZMod 2

/-- A binary linear code of length `n`: a subspace of `F_2^n`. -/
abbrev BinaryCode (n : ℕ) := Submodule (ZMod 2) (Word n)

/-- The standard dot product `x . y = sum_i x_i y_i` on `F_2^n`, as a bilinear form. -/
def dotForm (n : ℕ) : LinearMap.BilinForm (ZMod 2) (Word n) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => x ⬝ᵥ y) (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => smul_dotProduct _ _ _) (fun _ _ _ => dotProduct_add _ _ _)
    (fun _ _ _ => dotProduct_smul _ _ _)

/-- The dual code `C^perp = {x | x . c = 0 for every c in C}`. -/
def dual {n : ℕ} (C : BinaryCode n) : BinaryCode n := (dotForm n).orthogonal C

theorem mem_dual {n : ℕ} (C : BinaryCode n) (x : Word n) :
    x ∈ dual C ↔ ∀ c ∈ C, c ⬝ᵥ x = 0 := Iff.rfl

/-- `C` is self-dual: `C = C^perp`. -/
def IsSelfDual {n : ℕ} (C : BinaryCode n) : Prop := C = dual C

/-- Minimum distance: the least Hamming weight of a nonzero codeword. -/
noncomputable def minDistance {n : ℕ} (C : BinaryCode n) : ℕ :=
  sInf {d | ∃ c ∈ C, c ≠ 0 ∧ hammingNorm c = d}

/-- `σ` is an automorphism of `C`: the coordinate permutation `c ↦ c ∘ σ` maps `C` onto `C`. -/
def IsAutomorphism {n : ℕ} (C : BinaryCode n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ c : Word n, c ∘ σ ∈ C ↔ c ∈ C

/-- The dot product is nondegenerate (test against the unit vectors). -/
theorem dotForm_nondegenerate (n : ℕ) : (dotForm n).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · funext i
    have h := hx (Pi.single i 1)
    simp only [dotForm, LinearMap.mk₂_apply, dotProduct_single, mul_one] at h
    simpa using h
  · funext i
    have h := hy (Pi.single i 1)
    simp only [dotForm, LinearMap.mk₂_apply, single_dotProduct, one_mul] at h
    simpa using h

/-- `dim C + dim C^perp = n` for every binary linear code of length `n`. -/
theorem finrank_add_finrank_dual {n : ℕ} (C : BinaryCode n) :
    finrank (ZMod 2) C + finrank (ZMod 2) (dual C) = n := by
  have h := LinearMap.BilinForm.finrank_orthogonal (dotForm_nondegenerate n) C
  have hle : finrank (ZMod 2) C ≤ finrank (ZMod 2) (Word n) := Submodule.finrank_le C
  simp only [Module.finrank_fin_fun] at hle h
  unfold dual
  omega

/-- A self-dual binary code of length `n` has dimension exactly `n / 2`. -/
theorem two_mul_finrank_of_selfDual {n : ℕ} {C : BinaryCode n} (h : IsSelfDual C) :
    2 * finrank (ZMod 2) C = n := by
  have := finrank_add_finrank_dual C
  rw [← h] at this
  omega

/-- No binary self-dual code of length 84 has dimension 12. -/
theorem no_selfDual_84_12 (C : BinaryCode 84) (h : IsSelfDual C) :
    finrank (ZMod 2) C ≠ 12 := by
  have := two_mul_finrank_of_selfDual h
  omega

/-- Conjecture 00000001016, all three claims:
(1) there is no binary self-dual `[84,12,12]` code (extremal or not);
(2) no binary self-dual `[84,12]` code has an automorphism of order 11;
(3) every binary self-dual `[84,12]` code has minimum distance at most 11.
Claim (1) is a genuine non-existence result; (2) and (3) hold vacuously, because by
`no_selfDual_84_12` there is no binary self-dual `[84,12]` code at all. -/
theorem conjecture_1016 :
    (¬ ∃ C : BinaryCode 84, IsSelfDual C ∧ finrank (ZMod 2) C = 12 ∧ minDistance C = 12) ∧
    (∀ C : BinaryCode 84, IsSelfDual C → finrank (ZMod 2) C = 12 →
      ∀ σ : Equiv.Perm (Fin 84), IsAutomorphism C σ → orderOf σ ≠ 11) ∧
    (∀ C : BinaryCode 84, IsSelfDual C → finrank (ZMod 2) C = 12 → minDistance C ≤ 11) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨C, hC, hk, -⟩
    exact no_selfDual_84_12 C hC hk
  · intro C hC hk
    exact absurd hk (no_selfDual_84_12 C hC)
  · intro C hC hk
    exact absurd hk (no_selfDual_84_12 C hC)

end C1016
