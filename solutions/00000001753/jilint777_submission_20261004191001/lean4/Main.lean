/-!
# Conjecture 00000001753: spin character values of `2·S_n` on even classes

The conjecture claims that every spin character `χ` of the double cover `2·S_n` satisfies
`|χ(g)| ≤ 2^{⌊n/4⌋-1}` for every `g` lying over an even permutation ("alternating classes").

We refute this for `n = 5`, where the bound is `2^{1-1} = 1`, for **both** double covers of `S_5`.

* `2·S_5` is given by Schur's presentation with generators `t_1,…,t_4` and a central `z`
  (`z² = 1`):
  - `Ŝ_5` (`Cover.hat`):   `t_i² = 1`, `(t_i t_{i+1})³ = 1`, `(t_i t_j)² = z` for `|i-j| ≥ 2`;
  - `S̃_5` (`Cover.tilde`): `t_i² = z`, `(t_i t_{i+1})³ = z`, `(t_i t_j)² = z` for `|i-j| ≥ 2`.
  By von Dyck's theorem, a representation of the presented group with `z ↦ -I` (a *spin*
  representation) is exactly a list of matrices satisfying these relations with `z` replaced by
  `-I` (`IsSpinRep`). A word `w` in the `t_i` lies over the permutation `wordPerm n w`
  (`t_i ↦ (i i+1)`; the Coxeter relations are checked in `perm_relations`).
* Matrices have entries in `ℤ[ζ]`, `ζ = e^{πi/4}` (`Z8`), a subring of `ℂ`.
  `SpansMatrices` says that the matrices of all words span `M_d(ℚ(ζ))`; then every invariant
  subspace of `ℂ^d` is invariant under all of `M_d(ℂ)`, so the representation is irreducible and
  its character is an irreducible spin character.
* `T5` is the basic spin representation of `Ŝ_5` (degree 4); `gens .tilde = i·T5` is the one of
  `S̃_5`. We check the relations (`spinRep`) and irreducibility (`spans`, an explicit
  certificate: `5·E_ab` as a `ℤ[ζ]`-combination of 16 words).
* `g = t_1 t_2` lies over the 3-cycle `(1 2 3)` (an even permutation) and
  `χ(g) = tr(T_1 T_2) = ∓2`, so `|χ(g)|² = 4 > 1`.

Main results: `conjecture_00000001753_false (c : Cover) : ¬ Claim c 5`, and
`conjecture_00000001753_false_both : ¬ Claim .hat 5 ∧ ¬ Claim .tilde 5`.

`Claim c n` is a *weakening* of the conjecture (it only quantifies over spin representations
realized over `ℤ[ζ]`, over elements given by words in the `t_i`, and only constrains `|χ(g)|²`
when it is a rational integer), so refuting it refutes the conjecture.

Cited, not formalized: Schur's theorem that the presented group has order `2·5! = 240` (so it is
the double cover `2·S_5`). Lean shows the lower bound ingredients: `z ↦ -I ≠ I` (`z_ne_one`) and
the 120 words in `permWords` lie over 120 distinct permutations (`perm_words_distinct`), so the
presented group has at least 240 elements.
-/

namespace Spin1753

/-! ## 1. The ring `ℤ[ζ]`, `ζ = e^{πi/4}` -/

/-- `⟨a, b, c, d⟩` is `a + bζ + cζ² + dζ³`, where `ζ = e^{πi/4}`, so `ζ⁴ = -1`, `ζ² = i` and
`ζ - ζ³ = √2`. -/
structure Z8 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

namespace Z8
def zero : Z8 := ⟨0, 0, 0, 0⟩
def one : Z8 := ⟨1, 0, 0, 0⟩
/-- `i = ζ²`. -/
def I : Z8 := ⟨0, 0, 1, 0⟩
/-- `-i = ζ⁶`. -/
def negI : Z8 := ⟨0, 0, -1, 0⟩
def ofInt (q : Int) : Z8 := ⟨q, 0, 0, 0⟩
def add (x y : Z8) : Z8 := ⟨Int.add x.a y.a, Int.add x.b y.b, Int.add x.c y.c, Int.add x.d y.d⟩
def neg (x : Z8) : Z8 := ⟨Int.neg x.a, Int.neg x.b, Int.neg x.c, Int.neg x.d⟩
/-- Multiplication, using `ζ⁴ = -1`:
`(a + bζ + cζ² + dζ³)(e + fζ + gζ² + hζ³)`. -/
def mul : Z8 → Z8 → Z8
  | ⟨a, b, c, d⟩, ⟨e, f, g, h⟩ =>
  ⟨Int.sub (Int.mul a e) (Int.add (Int.mul b h) (Int.add (Int.mul c g) (Int.mul d f))),
   Int.sub (Int.add (Int.mul a f) (Int.mul b e)) (Int.add (Int.mul c h) (Int.mul d g)),
   Int.sub (Int.add (Int.mul a g) (Int.add (Int.mul b f) (Int.mul c e))) (Int.mul d h),
   Int.add (Int.add (Int.mul a h) (Int.mul b g)) (Int.add (Int.mul c f) (Int.mul d e))⟩
/-- Complex conjugation: `ζ ↦ ζ⁻¹ = -ζ³`, `ζ² ↦ -ζ²`, `ζ³ ↦ -ζ`. -/
def conj (x : Z8) : Z8 := ⟨x.a, -x.d, -x.c, -x.b⟩
def pow (x : Z8) : Nat → Z8
  | 0 => one
  | k + 1 => mul (pow x k) x
end Z8

/-- `|x|² = x · x̄`. -/
def normSq (x : Z8) : Z8 := Z8.mul x (Z8.conj x)

def z (a b c d : Int) : Z8 := ⟨a, b, c, d⟩

/-! ## 2. Matrices (lists of rows) -/

abbrev Mat := List (List Z8)

/-- Dot product (zero terms of the first vector are skipped, which does not change the value). -/
def dot : List Z8 → List Z8 → Z8
  | x :: xs, y :: ys => if x = Z8.zero then dot xs ys else Z8.add (Z8.mul x y) (dot xs ys)
  | _, _ => Z8.zero

def col (B : Mat) (j : Nat) : List Z8 := B.map (fun r => r.getD j Z8.zero)

/-- Matrix product. -/
def mmul (A B : Mat) : Mat :=
  A.map (fun r => (List.range (B.headD []).length).map (fun j => dot r (col B j)))

def ident (d : Nat) : Mat :=
  (List.range d).map (fun i => (List.range d).map (fun j => if i = j then Z8.one else Z8.zero))

def zeroMat (d : Nat) : Mat := (List.range d).map (fun _ => (List.range d).map (fun _ => Z8.zero))

/-- The matrix unit `E_ab`. -/
def unitMat (d a b : Nat) : Mat :=
  (List.range d).map (fun i => (List.range d).map (fun j =>
    if i = a ∧ j = b then Z8.one else Z8.zero))

def madd (A B : Mat) : Mat := List.zipWith (List.zipWith Z8.add) A B
def msmul (c : Z8) (M : Mat) : Mat := M.map (fun r => r.map (Z8.mul c))
def mneg (M : Mat) : Mat := M.map (fun r => r.map Z8.neg)

def trace (M : Mat) : Z8 :=
  (List.range M.length).foldl (fun s i => Z8.add s ((M.getD i []).getD i Z8.zero)) Z8.zero

def IsSquare (d : Nat) (M : Mat) : Prop := M.length = d ∧ ∀ r ∈ M, r.length = d

/-- `ρ(t_{w₀} t_{w₁} ⋯)`: the matrix of the word `w` (letters `0,…,n-2` stand for `t_1,…,t_{n-1}`). -/
def eval (d : Nat) (T : List Mat) : List Nat → Mat
  | [] => ident d
  | i :: w => w.foldl (fun M j => mmul M (T.getD j [])) (T.getD i [])

/-! ## 3. Permutations: the projection `2·S_n → S_n`, `t_i ↦ (i i+1)` -/

/-- Right multiplication of a permutation (in one-line notation) by the transposition `(i i+1)`. -/
def swapAdj (p : List Nat) (i : Nat) : List Nat :=
  (p.set i (p.getD (i + 1) 0)).set (i + 1) (p.getD i 0)

/-- The permutation `s_{w₀} s_{w₁} ⋯` of `{0,…,n-1}` (one-line notation) under which the word `w`
lies. -/
def wordPerm (n : Nat) (w : List Nat) : List Nat := w.foldl swapAdj (List.range n)

/-- Number of inversions. -/
def inversions : List Nat → Nat
  | [] => 0
  | x :: xs => (xs.filter (fun y => decide (y < x))).length + inversions xs

/-- `p` is an even permutation. -/
def IsEven (p : List Nat) : Prop := inversions p % 2 = 0

instance (p : List Nat) : Decidable (IsEven p) := by unfold IsEven; infer_instance

/-! ## 4. Spin representations of `2·S_n`, irreducibility, the conjecture -/

/-- The two double covers of `S_n` (Schur). -/
inductive Cover
  | hat
  | tilde
deriving DecidableEq

/-- The image of `t_i²` and of `(t_i t_{i+1})³` under a spin representation: `1` for `Ŝ_n`,
`ρ(z) = -I` for `S̃_n`. -/
def relRHS : Cover → Nat → Mat
  | .hat, d => ident d
  | .tilde, d => mneg (ident d)

/-- `T = [ρ(t_1), …, ρ(t_{n-1})]` satisfies Schur's relations with `z ↦ -I`, i.e. (von Dyck)
it defines a spin representation of the double cover `c` of `S_n` of degree `d`. -/
def IsSpinRep (c : Cover) (n d : Nat) (T : List Mat) : Prop :=
  0 < d ∧ T.length = n - 1 ∧ (∀ M ∈ T, IsSquare d M) ∧
  (∀ i, i < n - 1 → eval d T [i, i] = relRHS c d) ∧
  (∀ i, i < n - 2 → eval d T [i, i + 1, i, i + 1, i, i + 1] = relRHS c d) ∧
  (∀ j, j < n - 1 → ∀ i, i < j - 1 → eval d T [i, j, i, j] = mneg (ident d))

instance (c : Cover) (n d : Nat) (T : List Mat) : Decidable (IsSpinRep c n d T) := by
  unfold IsSpinRep IsSquare; infer_instance

/-- `Σ cₖ ρ(wₖ)`. -/
def lincomb (d : Nat) (T : List Mat) : List (Z8 × List Nat) → Mat
  | [] => zeroMat d
  | (c, w) :: rest => madd (msmul c (eval d T w)) (lincomb d T rest)

/-- The matrices of the words span `M_d(ℚ(ζ))`: every matrix unit `E_ab` times some nonzero
`N ∈ ℤ[ζ]` is a `ℤ[ζ]`-combination of matrices `ρ(w)` of words in the generators. Hence the
algebra spanned by `ρ` is all of `M_d(ℂ)` and `ρ` is irreducible over `ℂ`. -/
def SpansMatrices (d : Nat) (T : List Mat) : Prop :=
  ∀ a, a < d → ∀ b, b < d → ∃ N : Z8, N ≠ Z8.zero ∧ ∃ cs : List (Z8 × List Nat),
    (∀ p ∈ cs, ∀ i ∈ p.2, i < T.length) ∧ lincomb d T cs = msmul N (unitMat d a b)

/-- The square of the conjectured bound `2^{⌊n/4⌋-1}` (for `n ≥ 4` the exponent is a genuine
natural number; we only use `n = 5`, where it is `1`). -/
def boundSq (n : Nat) : Int := 4 ^ (n / 4 - 1)

/-- The conjecture for the cover `c` of `S_n`, in the weakened form we refute: for every
irreducible spin representation `T` of degree `d` over `ℤ[ζ]` and every word `w` lying over an
even permutation, if `|χ(w)|² = q` is a rational integer then `q ≤ (2^{⌊n/4⌋-1})²`. -/
def Claim (c : Cover) (n : Nat) : Prop :=
  ∀ (d : Nat) (T : List Mat), IsSpinRep c n d T → SpansMatrices d T →
    ∀ w : List Nat, (∀ i ∈ w, i < n - 1) → IsEven (wordPerm n w) →
      ∀ q : Int, normSq (trace (eval d T w)) = Z8.ofInt q → q ≤ boundSq n

/-! ## 5. The basic spin representation of `2·S_5` -/

/-- The basic spin representation of `Ŝ_5`: `T5 = [ρ(t_1), …, ρ(t_4)]`, entries `z a b c d =
a + bζ + cζ² + dζ³`. It is the Clifford-algebra representation `t_i ↦ (ξ_i - ξ_{i+1})/√2`
(`ξ_1,…,ξ_5` anticommuting involutions in `M_4(ℂ)`), written in a basis of a `G`-stable
`ℤ[ζ]`-lattice so that all entries are integral (`verify.py` checks both models). -/
def T5 : List Mat :=
  [[[z 0 0 0 0, z 0 0 0 0, z (-1) 0 0 0, z 0 0 1 0],
    [z 0 0 0 0, z 0 0 0 (-1), z 1 0 1 0, z 0 0 0 0],
    [z 0 0 0 0, z 1 0 0 0, z 0 0 0 1, z 0 0 0 0],
    [z 0 0 (-1) 0, z 0 0 (-1) 0, z 0 1 0 0, z 0 0 0 0]],
   [[z 0 0 0 0, z 0 0 0 0, z 1 0 0 0, z 0 0 0 0],
    [z 0 0 0 (-1), z 0 0 0 0, z 0 0 0 0, z 0 0 (-1) 0],
    [z 1 0 0 0, z 0 0 0 0, z 0 0 0 0, z 0 0 0 0],
    [z 0 0 0 0, z 0 0 1 0, z 0 (-1) 0 0, z 0 0 0 0]],
   [[z 0 0 0 (-1), z 0 0 0 0, z 0 0 0 0, z (-1) 0 (-1) 0],
    [z 0 0 0 1, z 0 1 0 0, z (-1) 0 0 0, z 0 0 1 0],
    [z (-1) 0 0 0, z (-1) 0 1 0, z 0 (-1) 0 0, z 0 0 0 0],
    [z (-1) 0 0 0, z 0 0 0 0, z 0 0 0 0, z 0 0 0 1]],
   [[z 0 0 0 0, z 0 0 0 0, z 0 0 (-1) 0, z 0 0 0 0],
    [z 0 1 0 0, z 0 0 0 0, z 0 0 1 0, z 1 0 0 0],
    [z 0 0 1 0, z 0 0 0 0, z 0 0 0 0, z 0 0 0 0],
    [z 1 0 0 0, z 1 0 0 0, z 0 0 0 1, z 0 0 0 0]]]

/-- Irreducibility certificate: entry `4a+b` lists pairs `(c, w)` with `Σ c·ρ(w) = 5·E_ab`.
The 16 words are the increasing products `t_{i₁} ⋯ t_{i_k}` (`i₁ < ⋯ < i_k`). -/
def irrCert : List (List (Z8 × List Nat)) :=
  [[(z 1 0 1 0, []), (z 0 1 0 (-2), [0]), (z 0 2 0 (-2), [1]), (z 0 0 0 (-4), [2]), (z 0 2 0 (-2), [3]), (z (-2) 0 1 0, [0,1]), (z (-2) 0 3 0, [0,2]), (z (-2) 0 0 0, [0,3]), (z 1 0 (-1) 0, [1,3]), (z 0 0 0 (-2), [0,1,2]), (z 0 0 0 (-1), [0,1,3]), (z 0 2 0 0, [0,2,3]), (z 0 4 0 0, [1,2,3]), (z (-3) 0 (-2) 0, [0,1,2,3])],
   [(z 1 0 (-1) 0, []), (z 0 (-1) 0 2, [0]), (z 0 0 0 (-1), [1]), (z 0 0 0 2, [2]), (z 0 1 0 2, [3]), (z 0 0 (-1) 0, [0,1]), (z 2 0 (-1) 0, [0,2]), (z 2 0 (-2) 0, [0,3]), (z 2 0 1 0, [1,2]), (z 1 0 0 0, [1,3]), (z 1 0 (-2) 0, [2,3]), (z 0 (-3) 0 2, [0,1,2]), (z 0 0 0 3, [0,1,3]), (z 0 0 0 3, [0,2,3]), (z 0 (-2) 0 0, [1,2,3]), (z 2 0 0 0, [0,1,2,3])],
   [(z 0 2 0 2, []), (z 0 0 (-2) 0, [0]), (z 1 0 1 0, [1]), (z (-1) 0 1 0, [3]), (z 0 1 0 0, [0,1]), (z 0 0 0 2, [0,2]), (z 0 2 0 1, [0,3]), (z 0 0 0 4, [1,2]), (z 0 2 0 2, [1,3]), (z 0 4 0 0, [2,3]), (z 2 0 (-3) 0, [0,1,2]), (z (-1) 0 (-2) 0, [0,1,3]), (z (-3) 0 (-2) 0, [0,2,3]), (z 0 2 0 0, [0,1,2,3])],
   [(z 0 2 0 (-1), []), (z (-2) 0 (-3) 0, [0]), (z 0 0 (-3) 0, [1]), (z (-3) 0 (-2) 0, [2]), (z 0 0 (-2) 0, [3]), (z 0 2 0 1, [0,1]), (z 0 4 0 0, [0,2]), (z 0 2 0 0, [0,3]), (z 0 2 0 0, [1,2]), (z 0 1 0 (-2), [1,3]), (z 0 0 0 (-2), [2,3]), (z (-3) 0 (-2) 0, [0,1,2]), (z (-3) 0 0 0, [0,1,3]), (z 2 0 (-3) 0, [1,2,3]), (z 0 0 0 2, [0,1,2,3])],
   [(z 3 0 0 0, []), (z 0 2 0 (-2), [0]), (z 0 1 0 0, [1]), (z 0 0 0 (-2), [2]), (z 0 2 0 (-1), [3]), (z 1 0 1 0, [0,1]), (z 1 0 (-1) 0, [0,3]), (z 2 0 (-3) 0, [1,2]), (z 3 0 (-1) 0, [1,3]), (z 3 0 2 0, [2,3]), (z 0 0 0 (-4), [0,1,2]), (z 0 2 0 (-2), [0,1,3]), (z 0 4 0 0, [0,2,3]), (z 0 2 0 0, [1,2,3])],
   [(z 1 0 0 0, []), (z 0 0 0 (-1), [0]), (z 0 1 0 (-3), [1]), (z 0 3 0 0, [2]), (z 0 1 0 (-1), [3]), (z 1 0 (-1) 0, [0,1]), (z 2 0 1 0, [0,2]), (z 1 0 0 0, [0,3]), (z 0 0 2 0, [1,2]), (z (-1) 0 2 0, [1,3]), (z (-1) 0 (-2) 0, [2,3]), (z 0 0 0 2, [0,1,2]), (z 0 1 0 2, [0,1,3]), (z 0 (-2) 0 0, [0,2,3]), (z 0 (-2) 0 (-3), [1,2,3]), (z 1 0 (-2) 0, [0,1,2,3])],
   [(z 0 1 0 2, []), (z 1 0 1 0, [0]), (z 1 0 3 0, [1]), (z (-2) 0 3 0, [2]), (z 0 0 3 0, [3]), (z 0 2 0 2, [0,1]), (z 0 0 0 4, [0,2]), (z 0 2 0 2, [0,3]), (z 0 0 0 2, [1,2]), (z 0 0 0 1, [1,3]), (z 0 2 0 0, [2,3]), (z (-1) 0 1 0, [0,1,3]), (z 3 0 2 0, [1,2,3]), (z 0 4 0 0, [0,1,2,3])],
   [(z 0 0 0 (-2), []), (z 0 0 (-3) 0, [0]), (z 2 0 0 0, [1]), (z 3 0 (-2) 0, [3]), (z 0 2 0 (-1), [0,1]), (z 0 2 0 0, [0,2]), (z 0 1 0 (-2), [0,3]), (z 0 (-2) 0 0, [1,2]), (z 0 (-1) 0 (-2), [1,3]), (z 0 0 0 (-4), [2,3]), (z (-3) 0 (-2) 0, [0,1,2]), (z 0 0 (-2) 0, [0,1,3]), (z 2 0 (-3) 0, [0,2,3]), (z 2 0 (-3) 0, [1,2,3]), (z 0 0 0 (-2), [0,1,2,3])],
   [(z 0 1 0 3, []), (z 0 0 1 0, [0]), (z 2 0 0 0, [1]), (z 2 0 (-1) 0, [2]), (z 1 0 0 0, [3]), (z 0 (-2) 0 3, [0,1]), (z 0 0 0 2, [0,2]), (z 0 1 0 2, [0,3]), (z 0 3 0 0, [1,2]), (z 0 3 0 2, [1,3]), (z 0 0 0 3, [2,3]), (z 2 0 1 0, [0,1,2]), (z 0 0 2 0, [0,1,3]), (z (-1) 0 2 0, [0,2,3]), (z 1 0 2 0, [1,2,3]), (z 0 (-2) 0 0, [0,1,2,3])],
   [(z 0 1 0 (-2), []), (z 0 0 2 0, [0]), (z 0 0 3 0, [1]), (z (-3) 0 2 0, [2]), (z (-2) 0 3 0, [3]), (z 0 2 0 (-1), [0,1]), (z 0 2 0 0, [0,2]), (z 0 0 0 (-2), [0,3]), (z 0 1 0 0, [1,2]), (z 0 (-1) 0 (-2), [1,3]), (z 0 0 0 (-4), [2,3]), (z (-2) 0 (-1) 0, [0,1,2]), (z (-3) 0 0 0, [0,1,3]), (z 1 0 1 0, [1,2,3]), (z 0 2 0 (-2), [0,1,2,3])],
   [(z 0 0 1 0, []), (z 0 (-2) 0 1, [0]), (z 0 (-2) 0 3, [1]), (z 0 (-3) 0 0, [2]), (z 0 (-3) 0 1, [3]), (z (-2) 0 0 0, [0,1]), (z (-2) 0 (-1) 0, [0,2]), (z (-1) 0 0 0, [0,3]), (z (-2) 0 1 0, [1,2]), (z 0 0 2 0, [1,3]), (z 1 0 2 0, [2,3]), (z 0 0 0 (-2), [0,1,2]), (z 0 (-3) 0 (-2), [0,1,3]), (z 0 (-2) 0 0, [0,2,3]), (z 0 0 0 3, [1,2,3]), (z (-1) 0 2 0, [0,1,2,3])],
   [(z 2 0 2 0, []), (z 0 1 0 (-1), [0]), (z 0 (-2) 0 0, [2]), (z 0 1 0 1, [3]), (z 0 0 4 0, [0,1]), (z 1 0 2 0, [0,2]), (z 2 0 2 0, [0,3]), (z 2 0 0 0, [1,2]), (z 4 0 0 0, [1,3]), (z 2 0 1 0, [2,3]), (z 0 (-2) 0 (-3), [0,1,2]), (z 0 3 0 0, [0,2,3]), (z 0 3 0 (-2), [1,2,3]), (z 0 0 2 0, [0,1,2,3])],
   [(z 0 2 0 1, []), (z (-1) 0 1 0, [0]), (z (-1) 0 (-2) 0, [1]), (z (-3) 0 (-2) 0, [2]), (z 0 0 (-2) 0, [3]), (z 0 2 0 2, [0,1]), (z 0 4 0 0, [0,2]), (z 0 2 0 2, [0,3]), (z 0 2 0 0, [1,2]), (z 0 1 0 0, [1,3]), (z 0 0 0 2, [2,3]), (z 1 0 1 0, [0,1,3]), (z 2 0 (-3) 0, [1,2,3]), (z 0 0 0 4, [0,1,2,3])],
   [(z 0 (-2) 0 (-1), []), (z 1 0 1 0, [0]), (z 1 0 0 0, [1]), (z 1 0 2 0, [2]), (z 2 0 2 0, [3]), (z 0 1 0 0, [0,1]), (z 0 (-2) 0 0, [0,2]), (z 0 (-2) 0 1, [0,3]), (z 0 (-2) 0 (-3), [1,2]), (z 0 (-3) 0 0, [1,3]), (z 0 (-3) 0 0, [2,3]), (z (-1) 0 2 0, [0,1,2]), (z 0 0 1 0, [0,1,3]), (z 2 0 1 0, [0,2,3]), (z 0 0 2 0, [1,2,3]), (z 0 0 0 (-2), [0,1,2,3])],
   [(z 2 0 0 0, []), (z 0 (-2) 0 2, [0]), (z 0 0 0 1, [1]), (z 0 (-2) 0 0, [2]), (z 0 (-1) 0 2, [3]), (z (-1) 0 1 0, [0,1]), (z (-1) 0 (-1) 0, [0,3]), (z 3 0 2 0, [1,2]), (z 2 0 (-1) 0, [1,3]), (z 2 0 (-3) 0, [2,3]), (z 0 (-4) 0 0, [0,1,2]), (z 0 (-2) 0 2, [0,1,3]), (z 0 0 0 4, [0,2,3]), (z 0 0 0 2, [1,2,3])],
   [(z 3 0 (-2) 0, []), (z 0 1 0 2, [0]), (z 0 (-1) 0 2, [1]), (z 0 0 0 4, [2]), (z 0 0 0 2, [3]), (z 3 0 0 0, [0,1]), (z 2 0 (-3) 0, [0,2]), (z 2 0 0 0, [0,3]), (z 2 0 (-3) 0, [1,2]), (z 0 0 (-3) 0, [1,3]), (z 0 0 0 2, [0,1,2]), (z 0 2 0 1, [0,1,3]), (z 0 2 0 0, [0,2,3]), (z 0 (-2) 0 0, [1,2,3]), (z 3 0 2 0, [0,1,2,3])]]


/-- Generators of the basic spin representation for each cover: `T5` for `Ŝ_5`, `i·T5` for `S̃_5`. -/
def gens : Cover → List Mat
  | .hat => T5
  | .tilde => T5.map (msmul Z8.I)

/-- The certificate for the cover `c`: for `S̃_5` the word `w` gets the extra factor `(-i)^{|w|}`,
since `ρ̃(w) = i^{|w|} ρ(w)`. -/
def certFor : Cover → List (List (Z8 × List Nat))
  | .hat => irrCert
  | .tilde => irrCert.map (fun l => l.map (fun p => (Z8.mul p.1 (Z8.pow Z8.negI p.2.length), p.2)))

def CertOK (d : Nat) (T : List Mat) (N : Z8) (cert : List (List (Z8 × List Nat))) : Prop :=
  N ≠ Z8.zero ∧ ∀ a, a < d → ∀ b, b < d →
    (∀ p ∈ cert.getD (a * d + b) [], ∀ i ∈ p.2, i < T.length) ∧
    lincomb d T (cert.getD (a * d + b) []) = msmul N (unitMat d a b)

instance (d : Nat) (T : List Mat) (N : Z8) (cert : List (List (Z8 × List Nat))) :
    Decidable (CertOK d T N cert) := by unfold CertOK; infer_instance

theorem spans_of_certOK {d : Nat} {T : List Mat} {N : Z8} {cert : List (List (Z8 × List Nat))}
    (h : CertOK d T N cert) : SpansMatrices d T :=
  fun a ha b hb => ⟨N, h.1, cert.getD (a * d + b) [], (h.2 a ha b hb).1, (h.2 a ha b hb).2⟩

/-- Schur's relations hold (both covers). -/
theorem spinRep_hat : IsSpinRep .hat 5 4 (gens .hat) := by decide +kernel
theorem spinRep_tilde : IsSpinRep .tilde 5 4 (gens .tilde) := by decide +kernel

theorem spinRep (c : Cover) : IsSpinRep c 5 4 (gens c) := by
  cases c
  · exact spinRep_hat
  · exact spinRep_tilde

/-- The certificate checks: `5·E_ab` is a `ℤ[ζ]`-combination of 16 words. -/
theorem certOK_hat : CertOK 4 (gens .hat) (Z8.ofInt 5) (certFor .hat) := by decide +kernel
theorem certOK_tilde : CertOK 4 (gens .tilde) (Z8.ofInt 5) (certFor .tilde) := by decide +kernel

/-- Irreducibility (both covers). -/
theorem spans (c : Cover) : SpansMatrices 4 (gens c) := by
  cases c
  · exact spans_of_certOK certOK_hat
  · exact spans_of_certOK certOK_tilde

/-- `t_1 t_2` lies over the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` (i.e. `(1 2 3)`), an even permutation. -/
theorem t1t2_perm : wordPerm 5 [0, 1] = [1, 2, 0, 3, 4] := by decide
theorem t1t2_even : IsEven (wordPerm 5 [0, 1]) := by decide

/-- The character values at `t_1 t_2`: `-2` for `Ŝ_5` and `2` for `S̃_5`. -/
theorem chi_t1t2_hat : trace (eval 4 (gens .hat) [0, 1]) = Z8.ofInt (-2) := by decide +kernel
theorem chi_t1t2_tilde : trace (eval 4 (gens .tilde) [0, 1]) = Z8.ofInt 2 := by decide +kernel

theorem normSq_t1t2 (c : Cover) : normSq (trace (eval 4 (gens c) [0, 1])) = Z8.ofInt 4 := by
  cases c
  · rw [chi_t1t2_hat]; decide
  · rw [chi_t1t2_tilde]; decide

/-- `χ(z) = tr(-I) = -4 = -χ(1)`: the character is a spin character, of degree 4. -/
theorem chi_z : trace (mneg (ident 4)) = Z8.ofInt (-4) ∧ trace (ident 4) = Z8.ofInt 4 := by decide

/-- `ρ(z) = -I ≠ I = ρ(1)`, so `z ≠ 1` in the presented group. -/
theorem z_ne_one : mneg (ident 4) ≠ ident 4 := by decide

theorem bound_five : boundSq 5 = 1 := by decide

/-! ## 6. The refutation -/

/-- **The conjecture is false for `n = 5`**, for either double cover `c` of `S_5`: the basic spin
character `χ` (degree 4, irreducible) has `|χ(t_1 t_2)|² = 4 > 1 = (2^{⌊5/4⌋-1})²`, where
`t_1 t_2` lies over the even permutation `(1 2 3)`. -/
theorem conjecture_00000001753_false (c : Cover) : ¬ Claim c 5 := by
  intro h
  have h4 := h 4 (gens c) (spinRep c) (spans c) [0, 1] (by decide) t1t2_even 4 (normSq_t1t2 c)
  rw [bound_five] at h4
  exact absurd h4 (by decide)

theorem conjecture_00000001753_false_both : ¬ Claim .hat 5 ∧ ¬ Claim .tilde 5 :=
  ⟨conjecture_00000001753_false .hat, conjecture_00000001753_false .tilde⟩

/-! ## 7. The projection to `S_5` and a lower bound for the presented group -/

/-- `t_i ↦ (i i+1)`, `z ↦ 1` respects Schur's relations (Coxeter relations of `S_5`), so the
projection of the presented group onto `S_5` is well defined. -/
theorem perm_relations :
    (∀ i, i < 4 → wordPerm 5 [i, i] = List.range 5) ∧
    (∀ i, i < 3 → wordPerm 5 [i, i + 1, i, i + 1, i, i + 1] = List.range 5) ∧
    (∀ j, j < 4 → ∀ i, i < j - 1 → wordPerm 5 [i, j, i, j] = List.range 5) := by decide

/-- One reduced word for each of the 120 permutations of `S_5`. -/
def permWords : List (List Nat) :=
  [[], [0], [1], [2], [3], [0,1], [0,2], [0,3], [1,0], [1,2],
   [1,3], [2,1], [2,3], [3,2], [0,1,0], [0,1,2], [0,1,3], [0,2,1], [0,2,3], [0,3,2],
   [1,0,2], [1,0,3], [1,2,1], [1,2,3], [1,3,2], [2,1,0], [2,1,3], [2,3,2], [3,2,1], [0,1,0,2],
   [0,1,0,3], [0,1,2,1], [0,1,2,3], [0,1,3,2], [0,2,1,0], [0,2,1,3], [0,2,3,2], [0,3,2,1], [1,0,2,1], [1,0,2,3],
   [1,0,3,2], [1,2,1,0], [1,2,1,3], [1,2,3,2], [1,3,2,1], [2,1,0,3], [2,1,3,2], [2,3,2,1], [3,2,1,0], [0,1,0,2,1],
   [0,1,0,2,3], [0,1,0,3,2], [0,1,2,1,0], [0,1,2,1,3], [0,1,2,3,2], [0,1,3,2,1], [0,2,1,0,3], [0,2,1,3,2], [0,2,3,2,1], [0,3,2,1,0],
   [1,0,2,1,0], [1,0,2,1,3], [1,0,2,3,2], [1,0,3,2,1], [1,2,1,0,3], [1,2,1,3,2], [1,2,3,2,1], [1,3,2,1,0], [2,1,0,3,2], [2,1,3,2,1],
   [2,3,2,1,0], [0,1,0,2,1,0], [0,1,0,2,1,3], [0,1,0,2,3,2], [0,1,0,3,2,1], [0,1,2,1,0,3], [0,1,2,1,3,2], [0,1,2,3,2,1], [0,1,3,2,1,0], [0,2,1,0,3,2],
   [0,2,1,3,2,1], [0,2,3,2,1,0], [1,0,2,1,0,3], [1,0,2,1,3,2], [1,0,2,3,2,1], [1,0,3,2,1,0], [1,2,1,0,3,2], [1,2,1,3,2,1], [1,2,3,2,1,0], [2,1,0,3,2,1],
   [2,1,3,2,1,0], [0,1,0,2,1,0,3], [0,1,0,2,1,3,2], [0,1,0,2,3,2,1], [0,1,0,3,2,1,0], [0,1,2,1,0,3,2], [0,1,2,1,3,2,1], [0,1,2,3,2,1,0], [0,2,1,0,3,2,1], [0,2,1,3,2,1,0],
   [1,0,2,1,0,3,2], [1,0,2,1,3,2,1], [1,0,2,3,2,1,0], [1,2,1,0,3,2,1], [1,2,1,3,2,1,0], [2,1,0,3,2,1,0], [0,1,0,2,1,0,3,2], [0,1,0,2,1,3,2,1], [0,1,0,2,3,2,1,0], [0,1,2,1,0,3,2,1],
   [0,1,2,1,3,2,1,0], [0,2,1,0,3,2,1,0], [1,0,2,1,0,3,2,1], [1,0,2,1,3,2,1,0], [1,2,1,0,3,2,1,0], [0,1,0,2,1,0,3,2,1], [0,1,0,2,1,3,2,1,0], [0,1,2,1,0,3,2,1,0], [1,0,2,1,0,3,2,1,0], [0,1,0,2,1,0,3,2,1,0]]

/-- The 120 words of `permWords` lie over 120 distinct permutations. With `z ≠ 1`
(`z_ne_one`) and `z ↦ 1`, the presented group has at least `2 · 120 = 240` elements. -/
theorem perm_words_distinct :
    permWords.length = 120 ∧ (permWords.map (wordPerm 5)).Nodup ∧
    ∀ w ∈ permWords, ∀ i ∈ w, i < 4 := by decide +kernel

end Spin1753

#print axioms Spin1753.conjecture_00000001753_false
#print axioms Spin1753.conjecture_00000001753_false_both
#print axioms Spin1753.spinRep
#print axioms Spin1753.spans
#print axioms Spin1753.normSq_t1t2
#print axioms Spin1753.t1t2_perm
#print axioms Spin1753.chi_z
#print axioms Spin1753.z_ne_one
#print axioms Spin1753.perm_relations
#print axioms Spin1753.perm_words_distinct
