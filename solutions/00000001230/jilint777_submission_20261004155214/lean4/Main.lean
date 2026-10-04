/-!
# Conjecture 00000001230 is false

The conjecture: the Jacobian (sandpile group) of the grid graph `[m₁] × ⋯ × [mₙ]` is
isomorphic to `⊕_S (ℤ/gcd(S))^{e(S)}`, the sum over subsets `S` of the `mᵢ`.

Everything is defined from scratch (core Lean 4, no Mathlib):

* `gridVerts ms` lists the vertices of `[m₁] × ⋯ × [mₙ]` (tuples with `0 ≤ xᵢ < mᵢ`),
  `adj` is the grid adjacency (L¹ distance one), `lap` the graph Laplacian and
  `redLap` the reduced Laplacian (first vertex `(0,…,0)` is the sink).
* `Coker k M = ℤ^k / M ℤ^k` is the cokernel of an integer `k × k` matrix, as a quotient type.
  `Sandpile ms = Coker (|V|-1) (redLap ms)` is the sandpile group (Jacobian), and
  `Pic ms = Coker |V| (lap ms)` is the full Laplacian cokernel `ℤ^V / im Δ`, and `Pic0` is the
  degree-zero part of `Pic [2,2]` (the Baker–Norine Jacobian `Div⁰/Prin` of the 4-cycle).
* `ZM d = ℤ/dℤ` (canonical representatives; `ZM 0 = ℤ`), `subsetsL ms` the `2ⁿ` sub-lists,
  `gcdL` the gcd of a list (`gcd ∅ = 0`), and `Target ms e = ⊕_S (ℤ/gcd S)^{e(S)}`.
* `IsIso φ`: `φ` is additive and bijective.

Main results:
* `conjecture_00000001230_false : ¬ ClaimV` (vertex-count reading of `[m]`),
* `conjecture_00000001230_false_edges : ¬ ClaimE` (edge-count reading of `[m]`),
* `conjecture_00000001230_false_dim3 : ¬ ClaimV3` (the claim restricted to `n ≥ 3`; cube `[2]³`),
* `no_iso_22`, `no_iso_111_edges`, `no_iso_22_Pic0`, `no_iso_22_Pic` : the explicit failing instances,
* `no_injective_hom_C4`, `no_injective_hom_Q3`, `no_injective_hom_PicC4`, `no_injective_hom_Pic0C4` :
  there is not even an injective additive map into ANY product `∏_{i ∈ ι} ℤ/dᵢ` with every
  `dᵢ ∈ {0,1,2}` (arbitrary index type `ι`: any exponents, any `gcd ∅` convention, infinite sums).
* Sanity: `sandpile_C4_iso_Z4 : Jac([2]×[2]) ≅ ℤ/4` is constructed explicitly, and
  `sandpile_P3_trivial` shows the conjecture's predicate holds for the path `[3]` (e ≡ 0).
-/

namespace Grid1230

/-! ## Grid graphs and Laplacians -/

/-- Vertices of `[m₁] × ⋯ × [mₙ]`: all tuples `(x₁,…,xₙ)` with `xᵢ < mᵢ`, lexicographic order. -/
def gridVerts : List Nat → List (List Nat)
  | [] => [[]]
  | m :: ms => (List.range m).flatMap (fun i => (gridVerts ms).map (fun v => i :: v))

/-- L¹ distance between two tuples. -/
def dist1 : List Nat → List Nat → Nat
  | a :: u, b :: v => (a - b) + (b - a) + dist1 u v
  | _, _ => 0

/-- Grid adjacency (Cartesian product of paths): L¹ distance exactly one. -/
def adj (u v : List Nat) : Bool := dist1 u v == 1

/-- Degree of `u` in the grid graph on `ms`. -/
def deg (ms : List Nat) (u : List Nat) : Nat := ((gridVerts ms).filter (fun w => adj u w)).length

/-- Laplacian entry `Δ(u,v)`. -/
def lapUV (ms : List Nat) (u v : List Nat) : Int :=
  if u = v then (deg ms u : Int) else if adj u v then -1 else 0

/-- Full Laplacian indexed by vertex positions. -/
def lap (ms : List Nat) (i j : Nat) : Int :=
  lapUV ms ((gridVerts ms).getD i []) ((gridVerts ms).getD j [])

/-- Reduced Laplacian: delete row and column of the sink (vertex 0 = `(0,…,0)`). -/
def redLap (ms : List Nat) (i j : Nat) : Int :=
  lapUV ms ((gridVerts ms).tail.getD i []) ((gridVerts ms).tail.getD j [])

/-! ## Cokernels -/

/-- `∑_{j<n} f j`. -/
def sumTo : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

theorem sumTo_add (n : Nat) (f g : Nat → Int) :
    sumTo n (fun j => f j + g j) = sumTo n f + sumTo n g := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih]; omega

theorem sumTo_neg (n : Nat) (f : Nat → Int) : sumTo n (fun j => - f j) = - sumTo n f := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih]; omega

theorem sumTo_zero (n : Nat) : sumTo n (fun _ => 0) = 0 := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih]; omega

theorem sumTo_congr (n : Nat) (f g : Nat → Int) (h : ∀ j, j < n → f j = g j) :
    sumTo n f = sumTo n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

/-- Integer vectors of length `k`. -/
abbrev Vec (k : Nat) := Fin k → Int

/-- Matrix–vector product `(M z)_i = ∑_{j<k} M i j * z j`. -/
def app (k : Nat) (M : Nat → Nat → Int) (z : Vec k) (i : Nat) : Int :=
  sumTo k (fun j => if h : j < k then M i j * z ⟨j, h⟩ else 0)

theorem app_add (k : Nat) (M : Nat → Nat → Int) (z w : Vec k) (i : Nat) :
    app k M (fun j => z j + w j) i = app k M z i + app k M w i := by
  unfold app
  rw [← sumTo_add]
  apply sumTo_congr
  intro j hj
  simp [hj, Int.mul_add]

theorem app_neg (k : Nat) (M : Nat → Nat → Int) (z : Vec k) (i : Nat) :
    app k M (fun j => - z j) i = - app k M z i := by
  unfold app
  rw [← sumTo_neg]
  apply sumTo_congr
  intro j hj
  simp [hj, Int.mul_neg]

theorem app_zero (k : Nat) (M : Nat → Nat → Int) (i : Nat) :
    app k M (fun _ => 0) i = 0 := by
  unfold app
  exact (sumTo_congr k _ _ (fun j hj => by simp [hj])).trans (sumTo_zero k)

/-- `x ≡ y` iff `x - y` lies in the column space `M ℤ^k`. -/
def Rel (k : Nat) (M : Nat → Nat → Int) (x y : Vec k) : Prop :=
  ∃ z : Vec k, ∀ i : Fin k, x i - y i = app k M z i.val

def cokerSetoid (k : Nat) (M : Nat → Nat → Int) : Setoid (Vec k) where
  r := Rel k M
  iseqv := {
    refl := fun x => ⟨fun _ => 0, fun i => by rw [app_zero]; omega⟩
    symm := fun ⟨z, hz⟩ => ⟨fun j => - z j, fun i => by rw [app_neg, ← hz i]; omega⟩
    trans := fun ⟨z, hz⟩ ⟨w, hw⟩ =>
      ⟨fun j => z j + w j, fun i => by rw [app_add, ← hz i, ← hw i]; omega⟩ }

/-- The cokernel `ℤ^k / M ℤ^k`. -/
def Coker (k : Nat) (M : Nat → Nat → Int) : Type := Quotient (cokerSetoid k M)

instance (k : Nat) (M : Nat → Nat → Int) : Add (Coker k M) where
  add := Quotient.lift₂ (s₁ := cokerSetoid k M) (s₂ := cokerSetoid k M)
    (fun x y => (Quotient.mk (cokerSetoid k M) (fun j => x j + y j) : Coker k M)) (by
    intro x y x' y' ⟨z, hz⟩ ⟨w, hw⟩
    apply Quotient.sound
    exact ⟨fun j => z j + w j, fun i => by dsimp only; rw [app_add, ← hz i, ← hw i]; omega⟩)

instance (k : Nat) (M : Nat → Nat → Int) : Zero (Coker k M) where
  zero := Quotient.mk (cokerSetoid k M) (fun _ => 0)

/-- The class of a vector in the cokernel. -/
def mkC (k : Nat) (M : Nat → Nat → Int) (x : Vec k) : Coker k M := Quotient.mk (cokerSetoid k M) x

theorem coker_add_mk (k : Nat) (M : Nat → Nat → Int) (x y : Vec k) :
    mkC k M x + mkC k M y = mkC k M (fun j => x j + y j) := rfl

theorem coker_zero_def (k : Nat) (M : Nat → Nat → Int) :
    (0 : Coker k M) = mkC k M (fun _ => 0) := rfl

theorem mkC_eq (k : Nat) (M : Nat → Nat → Int) (x y : Vec k) :
    mkC k M x = mkC k M y ↔ Rel k M x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- `4[x] = 0` in the cokernel iff `4x ∈ M ℤ^k`. -/
theorem four_eq (k : Nat) (M : Nat → Nat → Int) (x : Vec k)
    (h : Rel k M (fun j => (x j + x j) + (x j + x j)) (fun _ => 0)) :
    (mkC k M x + mkC k M x) + (mkC k M x + mkC k M x) = 0 :=
  (mkC_eq k M _ _).2 h

/-- `2[x] ≠ 0` in the cokernel iff `2x ∉ M ℤ^k`. -/
theorem two_ne (k : Nat) (M : Nat → Nat → Int) (x : Vec k)
    (h : ¬ Rel k M (fun j => x j + x j) (fun _ => 0)) : mkC k M x + mkC k M x ≠ 0 :=
  fun h' => h ((mkC_eq k M _ _).1 h')

/-- The sandpile group (Jacobian) `ℤ^{V∖{s}} / Δ̃ ℤ^{V∖{s}}` of the grid graph on `ms`. -/
def Sandpile (ms : List Nat) : Type := Coker ((gridVerts ms).length - 1) (redLap ms)

instance (ms : List Nat) : Add (Sandpile ms) := inferInstanceAs (Add (Coker _ _))
instance (ms : List Nat) : Zero (Sandpile ms) := inferInstanceAs (Zero (Coker _ _))

/-- The full Laplacian cokernel `ℤ^V / Δ ℤ^V` (≅ ℤ ⊕ Jacobian for connected graphs). -/
def Pic (ms : List Nat) : Type := Coker (gridVerts ms).length (lap ms)

instance (ms : List Nat) : Add (Pic ms) := inferInstanceAs (Add (Coker _ _))
instance (ms : List Nat) : Zero (Pic ms) := inferInstanceAs (Zero (Coker _ _))

/-! ## The groups `ℤ/d` and the conjectured decomposition -/

/-- `ℤ/dℤ` via canonical representatives `a % d = a` (so `ZM 0 = ℤ`, `ZM d = {0,…,d-1}`). -/
def ZM (d : Nat) : Type := { a : Int // a % (d : Int) = a }

instance (d : Nat) : Add (ZM d) where
  add x y := ⟨(x.val + y.val) % (d : Int), Int.emod_emod _ _⟩

instance (d : Nat) : Zero (ZM d) where
  zero := ⟨0, Int.zero_emod _⟩

theorem ZM.ext {d : Nat} {x y : ZM d} (h : x.val = y.val) : x = y := Subtype.ext h

/-- Pointwise structure on products `∏_{i ∈ ι} ℤ/dᵢ`. -/
def Prod' (ι : Type) (d : ι → Nat) : Type := (i : ι) → ZM (d i)

instance (ι : Type) (d : ι → Nat) : Add (Prod' ι d) where
  add x y := fun i => x i + y i

instance (ι : Type) (d : ι → Nat) : Zero (Prod' ι d) where
  zero := fun _ => 0

/-- All `2ⁿ` sub-lists (subsets of positions) of a list. -/
def subsetsL : List Nat → List (List Nat)
  | [] => [[]]
  | m :: ms => subsetsL ms ++ (subsetsL ms).map (fun S => m :: S)

/-- gcd of a list, with `gcd ∅ = 0`. -/
def gcdL (S : List Nat) : Nat := S.foldr Nat.gcd 0

/-- Modulus attached to the `k`-th subset. -/
def modOf (ms : List Nat) (k : Nat) : Nat := gcdL ((subsetsL ms).getD k [])

/-- Index set of `⊕_S (ℤ/gcd S)^{e(S)}`: pairs (subset number `k`, copy `c < e k`). -/
def Idx (ms : List Nat) (e : Nat → Nat) : Type := Σ k : Fin (subsetsL ms).length, Fin (e k.val)

/-- The conjectured group `⊕_S (ℤ/gcd S)^{e(S)}` (a finite sum, so a product). -/
def Target (ms : List Nat) (e : Nat → Nat) : Type := Prod' (Idx ms e) (fun i => modOf ms i.1.val)

instance (ms : List Nat) (e : Nat → Nat) : Add (Target ms e) := inferInstanceAs (Add (Prod' _ _))
instance (ms : List Nat) (e : Nat → Nat) : Zero (Target ms e) := inferInstanceAs (Zero (Prod' _ _))

/-! ## Isomorphisms -/

def IsHom {A B : Type} [Add A] [Add B] (φ : A → B) : Prop := ∀ a b, φ (a + b) = φ a + φ b
def Injective {A B : Type} (φ : A → B) : Prop := ∀ a b, φ a = φ b → a = b
def Surjective {A B : Type} (φ : A → B) : Prop := ∀ b, ∃ a, φ a = b
/-- A group isomorphism: an additive bijection. -/
def IsIso {A B : Type} [Add A] [Add B] (φ : A → B) : Prop := IsHom φ ∧ Injective φ ∧ Surjective φ

/-- The conjecture, `[m]` = path on `m` vertices: for every grid there are exponents `e`
with `Jac([m₁]×⋯×[mₙ]) ≅ ⊕_S (ℤ/gcd S)^{e(S)}`. -/
def ClaimV : Prop :=
  ∀ ms : List Nat, (∀ m ∈ ms, 1 ≤ m) →
    ∃ e : Nat → Nat, ∃ φ : Sandpile ms → Target ms e, IsIso φ

/-- The conjecture, `[m]` = path with `m` edges (`m+1` vertices). -/
def ClaimE : Prop :=
  ∀ ms : List Nat, ∃ e : Nat → Nat, ∃ φ : Sandpile (ms.map (· + 1)) → Target ms e, IsIso φ

/-- The conjecture restricted to dimension `n ≥ 3` (vertex-count reading). -/
def ClaimV3 : Prop :=
  ∀ ms : List Nat, 3 ≤ ms.length → (∀ m ∈ ms, 1 ≤ m) →
    ∃ e : Nat → Nat, ∃ φ : Sandpile ms → Target ms e, IsIso φ

/-! ## The obstruction: "4x = 0 ⇒ 2x = 0" in every `∏ ℤ/dᵢ` with `dᵢ ∈ {0,1,2}` -/

def Small (d : Nat) : Prop := d = 0 ∨ d = 1 ∨ d = 2

theorem zm_four (d : Nat) (hd : Small d) (x : ZM d) (h : (x + x) + (x + x) = 0) :
    x + x = 0 := by
  have hv := congrArg Subtype.val h
  apply ZM.ext
  show (x.val + x.val) % (d : Int) = 0
  have hx := x.property
  change ((x.val + x.val) % (d : Int) + (x.val + x.val) % (d : Int)) % (d : Int) = 0 at hv
  rcases hd with rfl | rfl | rfl
  · simp only [Int.ofNat_zero, Int.emod_zero] at hv ⊢; omega
  · omega
  · omega

theorem zm_cancel (d : Nat) (hd : Small d) (x : ZM d) (h : x + x = x) : x = 0 := by
  have hv := congrArg Subtype.val h
  apply ZM.ext
  show x.val = 0
  have hx := x.property
  change (x.val + x.val) % (d : Int) = x.val at hv
  rcases hd with rfl | rfl | rfl
  · simp only [Int.ofNat_zero, Int.emod_zero] at hv hx; omega
  · omega
  · omega

theorem prod_four (ι : Type) (d : ι → Nat) (hd : ∀ i, Small (d i)) (x : Prod' ι d)
    (h : (x + x) + (x + x) = 0) : x + x = 0 := by
  funext i
  exact zm_four (d i) (hd i) (x i) (congrFun h i)

theorem prod_cancel (ι : Type) (d : ι → Nat) (hd : ∀ i, Small (d i)) (x : Prod' ι d)
    (h : x + x = x) : x = 0 := by
  funext i
  exact zm_cancel (d i) (hd i) (x i) (congrFun h i)

/-- Abstract transfer: if `G` has `g` with `4g = 0`, `2g ≠ 0`, then no injective additive map
`G → ∏ ℤ/dᵢ` with all `dᵢ ∈ {0,1,2}` exists. -/
theorem no_injective_hom {G : Type} [Add G] [Zero G] (hz : (0 : G) + 0 = 0)
    (g : G) (h4 : (g + g) + (g + g) = 0) (h2 : g + g ≠ 0)
    (ι : Type) (d : ι → Nat) (hd : ∀ i, Small (d i))
    (φ : G → Prod' ι d) (hφ : IsHom φ) (hinj : Injective φ) : False := by
  have h0 : φ 0 = 0 := by
    apply prod_cancel ι d hd
    rw [← hφ, hz]
  apply h2
  apply hinj
  rw [h0, hφ]
  apply prod_four ι d hd
  rw [← hφ, ← hφ, h4, h0]

/-! ## The 2 × 2 grid (the 4-cycle) -/

/-- Explicit reduced Laplacian of `[2]×[2]` (non-sink vertices `(0,1),(1,0),(1,1)`). -/
def T22 : Nat → Nat → Int
  | 0, 0 => 2 | 0, 1 => 0 | 0, 2 => -1
  | 1, 0 => 0 | 1, 1 => 2 | 1, 2 => -1
  | 2, 0 => -1 | 2, 1 => -1 | 2, 2 => 2
  | _, _ => 0

theorem gridVerts_22 : gridVerts [2, 2] = [[0,0], [0,1], [1,0], [1,1]] := by decide

theorem redLap_22 : ∀ i, i < 3 → ∀ j, j < 3 → redLap [2, 2] i j = T22 i j := by decide

theorem app_22 (z : Vec 3) (i : Nat) (hi : i < 3) :
    app 3 (redLap [2, 2]) z i = T22 i 0 * z 0 + T22 i 1 * z 1 + T22 i 2 * z 2 := by
  unfold app
  simp only [sumTo]
  rw [redLap_22 i hi 0 (by decide), redLap_22 i hi 1 (by decide), redLap_22 i hi 2 (by decide)]
  simp

/-- The sandpile group of `[2]×[2]` is `Coker 3 (redLap [2,2])` on the nose. -/
theorem sandpile_22_def : Sandpile [2, 2] = Coker 3 (redLap [2, 2]) := rfl

/-- `e₀`, the chip at vertex `(0,1)`. -/
def e0 : Vec 3 := fun j => if j.val = 0 then 1 else 0

def g22 : Coker 3 (redLap [2, 2]) := mkC 3 (redLap [2, 2]) e0

theorem coker_zero_add (k : Nat) (M : Nat → Nat → Int) : (0 : Coker k M) + 0 = 0 := by
  rw [coker_zero_def, coker_add_mk, mkC_eq]
  exact ⟨fun _ => 0, fun i => by rw [app_zero]; simp⟩

/-- `4 e₀ = Δ̃ (3,1,2)`, so `4 g = 0`. -/
theorem g22_four : (g22 + g22) + (g22 + g22) = 0 := by
  apply four_eq
  refine ⟨fun j => if j.val = 0 then 3 else if j.val = 1 then 1 else 2, ?_⟩
  intro ⟨i, hi⟩
  rw [app_22 _ i hi]
  simp only [e0]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

/-- `2 e₀ ∉ Δ̃ ℤ³`, so `2 g ≠ 0`. -/
theorem g22_two : g22 + g22 ≠ 0 := by
  refine two_ne 3 (redLap [2, 2]) e0 ?_
  intro ⟨z, hz⟩
  have h0 := hz ⟨0, by decide⟩
  have h1 := hz ⟨1, by decide⟩
  have h2 := hz ⟨2, by decide⟩
  rw [app_22 _ _ (by decide)] at h0 h1 h2
  simp [e0, T22] at h0 h1 h2
  omega

/-- **Main lemma (n = 2).** `Jac([2]×[2])` has no injective additive map into any
`∏_{i∈ι} ℤ/dᵢ` with `dᵢ ∈ {0,1,2}`, for any index type `ι`. -/
theorem no_injective_hom_C4 (ι : Type) (d : ι → Nat) (hd : ∀ i, Small (d i))
    (φ : Sandpile [2, 2] → Prod' ι d) (hφ : IsHom φ) : ¬ Injective φ := fun hinj =>
  no_injective_hom (G := Coker 3 (redLap [2, 2])) (coker_zero_add _ _) g22 g22_four g22_two
    ι d hd φ hφ hinj

/-- Every modulus `gcd S`, `S ⊆ {2,2}`, is `0` or `2`. -/
theorem modOf_22 : ∀ k, k < (subsetsL [2, 2]).length → Small (modOf [2, 2] k) := by
  intro k hk
  have : (subsetsL [2, 2]).length = 4 := by decide
  rw [this] at hk
  unfold Small
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide

/-- Every modulus `gcd S`, `S ⊆ {1,1}`, is `0` or `1`. -/
theorem modOf_11 : ∀ k, k < (subsetsL [1, 1]).length → Small (modOf [1, 1] k) := by
  intro k hk
  have : (subsetsL [1, 1]).length = 4 := by decide
  rw [this] at hk
  unfold Small
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide

/-- **Disproof (vertex-count reading).** -/
theorem conjecture_00000001230_false : ¬ ClaimV := by
  intro hc
  obtain ⟨e, φ, hφ, hinj, _⟩ := hc [2, 2] (by decide)
  exact no_injective_hom_C4 (Idx [2, 2] e) (fun i => modOf [2, 2] i.1.val)
    (fun i => modOf_22 i.1.val i.1.isLt) φ hφ hinj

/-- **Disproof (edge-count reading):** `[1]×[1]` (one edge each way) is again the 4-cycle. -/
theorem conjecture_00000001230_false_edges : ¬ ClaimE := by
  intro hc
  obtain ⟨e, φ, hφ, hinj, _⟩ := hc [1, 1]
  exact no_injective_hom_C4 (Idx [1, 1] e) (fun i => modOf [1, 1] i.1.val)
    (fun i => modOf_11 i.1.val i.1.isLt) φ hφ hinj

/-- The explicit failing instance: no exponents `e` and no isomorphism at all. -/
theorem no_iso_22 (e : Nat → Nat) (φ : Sandpile [2, 2] → Target [2, 2] e) : ¬ IsIso φ :=
  fun ⟨hφ, hinj, _⟩ => no_injective_hom_C4 (Idx [2, 2] e) (fun i => modOf [2, 2] i.1.val)
    (fun i => modOf_22 i.1.val i.1.isLt) φ hφ hinj

/-! ## The full Laplacian cokernel `ℤ^V / Δ ℤ^V` of the 4-cycle -/

def U22 : Nat → Nat → Int
  | 0, 0 => 2 | 0, 1 => -1 | 0, 2 => -1 | 0, 3 => 0
  | 1, 0 => -1 | 1, 1 => 2 | 1, 2 => 0 | 1, 3 => -1
  | 2, 0 => -1 | 2, 1 => 0 | 2, 2 => 2 | 2, 3 => -1
  | 3, 0 => 0 | 3, 1 => -1 | 3, 2 => -1 | 3, 3 => 2
  | _, _ => 0

theorem lap_22 : ∀ i, i < 4 → ∀ j, j < 4 → lap [2, 2] i j = U22 i j := by decide

theorem lapp_22 (z : Vec 4) (i : Nat) (hi : i < 4) :
    app 4 (lap [2, 2]) z i = U22 i 0 * z 0 + U22 i 1 * z 1 + U22 i 2 * z 2 + U22 i 3 * z 3 := by
  unfold app
  simp only [sumTo]
  rw [lap_22 i hi 0 (by decide), lap_22 i hi 1 (by decide), lap_22 i hi 2 (by decide),
    lap_22 i hi 3 (by decide)]
  simp

/-- The degree-zero divisor `(0,1) − (0,0)`. -/
def d01 : Vec 4 := fun j => if j.val = 1 then 1 else if j.val = 0 then -1 else 0

def p22 : Coker 4 (lap [2, 2]) := mkC 4 (lap [2, 2]) d01

theorem p22_four : (p22 + p22) + (p22 + p22) = 0 := by
  apply four_eq
  refine ⟨fun j => if j.val = 1 then 3 else if j.val = 2 then 1 else if j.val = 3 then 2 else 0, ?_⟩
  intro ⟨i, hi⟩
  rw [lapp_22 _ i hi]
  simp only [d01]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem p22_two : p22 + p22 ≠ 0 := by
  refine two_ne 4 (lap [2, 2]) d01 ?_
  intro ⟨z, hz⟩
  have h0 : (-2 : Int) = (2) * z 0 + (-1) * z 1 + (-1) * z 2 + (0) * z 3 := by
    have := hz ⟨0, by decide⟩
    rw [lapp_22 _ _ (by decide)] at this
    exact this
  have h1 : (2 : Int) = (-1) * z 0 + (2) * z 1 + (0) * z 2 + (-1) * z 3 := by
    have := hz ⟨1, by decide⟩
    rw [lapp_22 _ _ (by decide)] at this
    exact this
  have h2 : (0 : Int) = (-1) * z 0 + (0) * z 1 + (2) * z 2 + (-1) * z 3 := by
    have := hz ⟨2, by decide⟩
    rw [lapp_22 _ _ (by decide)] at this
    exact this
  have h3 : (0 : Int) = (0) * z 0 + (-1) * z 1 + (-1) * z 2 + (2) * z 3 := by
    have := hz ⟨3, by decide⟩
    rw [lapp_22 _ _ (by decide)] at this
    exact this
  omega

/-- Robustness: also `ℤ^V/Δℤ^V` (and hence its degree-zero part, which contains `p22`)
has no injective additive map into any `∏ ℤ/dᵢ` with `dᵢ ∈ {0,1,2}`. -/
theorem no_injective_hom_PicC4 (ι : Type) (d : ι → Nat) (hd : ∀ i, Small (d i))
    (φ : Pic [2, 2] → Prod' ι d) (hφ : IsHom φ) : ¬ Injective φ := fun hinj =>
  no_injective_hom (G := Coker 4 (lap [2, 2])) (coker_zero_add _ _) p22 p22_four p22_two
    ι d hd φ hφ hinj


/-! ## The Baker–Norine Jacobian `Pic⁰ = Div⁰ / Prin` of the 4-cycle -/

/-- Degree `∑ᵥ x(v)` of a divisor class; well defined since every column of `Δ` sums to `0`. -/
def degC : Coker 4 (lap [2, 2]) → Int :=
  @Quotient.lift _ _ (cokerSetoid 4 (lap [2, 2])) (fun x => x 0 + x 1 + x 2 + x 3) (by
    intro x y ⟨z, hz⟩
    have h0 : x 0 - y 0 = (2) * z 0 + (-1) * z 1 + (-1) * z 2 + (0) * z 3 := by
      have := hz ⟨0, by decide⟩
      rw [lapp_22 _ _ (by decide)] at this
      exact this
    have h1 : x 1 - y 1 = (-1) * z 0 + (2) * z 1 + (0) * z 2 + (-1) * z 3 := by
      have := hz ⟨1, by decide⟩
      rw [lapp_22 _ _ (by decide)] at this
      exact this
    have h2 : x 2 - y 2 = (-1) * z 0 + (0) * z 1 + (2) * z 2 + (-1) * z 3 := by
      have := hz ⟨2, by decide⟩
      rw [lapp_22 _ _ (by decide)] at this
      exact this
    have h3 : x 3 - y 3 = (0) * z 0 + (-1) * z 1 + (-1) * z 2 + (2) * z 3 := by
      have := hz ⟨3, by decide⟩
      rw [lapp_22 _ _ (by decide)] at this
      exact this
    show x 0 + x 1 + x 2 + x 3 = y 0 + y 1 + y 2 + y 3
    omega)

theorem degC_add (a b : Coker 4 (lap [2, 2])) : degC (a + b) = degC a + degC b := by
  induction a using Quotient.inductionOn with | h x => ?_
  induction b using Quotient.inductionOn with | h y => ?_
  show (x 0 + y 0) + (x 1 + y 1) + (x 2 + y 2) + (x 3 + y 3)
    = (x 0 + x 1 + x 2 + x 3) + (y 0 + y 1 + y 2 + y 3)
  omega

/-- `Pic⁰(C₄)`: divisor classes of degree zero (the Jacobian in the sense of Baker–Norine). -/
def Pic0 : Type := { q : Coker 4 (lap [2, 2]) // degC q = 0 }

instance : Add Pic0 where
  add a b := ⟨a.1 + b.1, by rw [degC_add, a.2, b.2]; rfl⟩

instance : Zero Pic0 where
  zero := ⟨0, rfl⟩

/-- The class of `(0,1) − (0,0)` lies in `Pic⁰`. -/
def q22 : Pic0 := ⟨p22, rfl⟩

theorem no_injective_hom_Pic0C4 (ι : Type) (d : ι → Nat) (hd : ∀ i, Small (d i))
    (φ : Pic0 → Prod' ι d) (hφ : IsHom φ) : ¬ Injective φ := fun hinj =>
  no_injective_hom (G := Pic0) (Subtype.ext (coker_zero_add 4 (lap [2, 2]))) q22
    (Subtype.ext p22_four) (fun h => p22_two (congrArg Subtype.val h)) ι d hd φ hφ hinj


/-- The `[2]×[2]` instance of the conjecture also fails if "Jacobian" means `Pic⁰` or `ℤ^V/Δℤ^V`. -/
theorem no_iso_22_Pic0 (e : Nat → Nat) (φ : Pic0 → Target [2, 2] e) : ¬ IsIso φ :=
  fun ⟨hφ, hinj, _⟩ => no_injective_hom_Pic0C4 (Idx [2, 2] e) (fun i => modOf [2, 2] i.1.val)
    (fun i => modOf_22 i.1.val i.1.isLt) φ hφ hinj

theorem no_iso_22_Pic (e : Nat → Nat) (φ : Pic [2, 2] → Target [2, 2] e) : ¬ IsIso φ :=
  fun ⟨hφ, hinj, _⟩ => no_injective_hom_PicC4 (Idx [2, 2] e) (fun i => modOf [2, 2] i.1.val)
    (fun i => modOf_22 i.1.val i.1.isLt) φ hφ hinj

/-! ## Sanity checks: the definitions are the right ones -/

/-- `Jac([2]×[2]) ≅ ℤ/4` explicitly: `x ↦ 3x₀ + x₁ + 2x₂ mod 4`
(`(3,1,2)` is the first row of `adj Δ̃`; it annihilates every column of `Δ̃` mod 4). -/
def phi4 : Coker 3 (redLap [2, 2]) → ZM 4 :=
  @Quotient.lift _ _ (cokerSetoid 3 (redLap [2, 2]))
    (fun x => (⟨(3 * x 0 + x 1 + 2 * x 2) % 4, Int.emod_emod _ _⟩ : ZM 4)) (by
    intro x y ⟨z, hz⟩
    apply ZM.ext
    have h0 := hz 0
    have h1 := hz 1
    have h2 := hz 2
    rw [app_22 _ _ (by decide)] at h0 h1 h2
    simp [T22] at h0 h1 h2
    show (3 * x 0 + x 1 + 2 * x 2) % 4 = (3 * y 0 + y 1 + 2 * y 2) % 4
    omega)

theorem phi4_iso : IsIso phi4 := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    apply ZM.ext
    show (3 * (x 0 + y 0) + (x 1 + y 1) + 2 * (x 2 + y 2)) % 4
      = ((3 * x 0 + x 1 + 2 * x 2) % 4 + (3 * y 0 + y 1 + 2 * y 2) % 4) % 4
    omega
  · intro a b h
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    have hv := congrArg Subtype.val h
    change (3 * x 0 + x 1 + 2 * x 2) % 4 = (3 * y 0 + y 1 + 2 * y 2) % 4 at hv
    apply Quotient.sound
    -- z = adj(Δ̃)(x - y) / 4
    have ⟨q, hq⟩ : ∃ q, 3 * (x 0 - y 0) + (x 1 - y 1) + 2 * (x 2 - y 2) = 4 * q :=
      ⟨(3 * (x 0 - y 0) + (x 1 - y 1) + 2 * (x 2 - y 2)) / 4, by omega⟩
    have ⟨r, hr⟩ : ∃ r, (x 0 - y 0) - (x 1 - y 1) = 2 * r :=
      ⟨((x 0 - y 0) - (x 1 - y 1)) / 2, by omega⟩
    refine ⟨fun j => if j.val = 0 then q else if j.val = 1 then q - r
      else r + (x 1 - y 1) + (x 2 - y 2), ?_⟩
    intro i
    rw [app_22 _ i.val i.isLt]
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      rcases i with ⟨i, hi⟩
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    rcases hi with rfl | rfl | rfl
    · simp [T22]; omega
    · simp [T22]; omega
    · simp [T22]; omega
  · intro b
    refine ⟨Quotient.mk (cokerSetoid 3 (redLap [2, 2])) (fun j => if j.val = 0 then 3 * b.val else 0), ?_⟩
    apply ZM.ext
    have hb : b.val % 4 = b.val := b.property
    show (3 * (3 * b.val) + 0 + 2 * 0) % 4 = b.val
    omega

/-- **Sanity check:** the sandpile group of the 4-cycle `[2]×[2]` is `ℤ/4`. -/
theorem sandpile_C4_iso_Z4 : ∃ φ : Sandpile [2, 2] → ZM 4, IsIso φ := ⟨phi4, phi4_iso⟩

theorem p3_iso : ∃ e : Nat → Nat, ∃ φ : Coker 2 (redLap [3]) → Target [3] e, IsIso φ := by
  refine ⟨fun _ => 0, fun _ => fun i => Fin.elim0 i.2, ?_, ?_, ?_⟩
  · intro a b; funext i; exact Fin.elim0 i.2
  · intro a b _
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    apply Quotient.sound
    -- reduced Laplacian of the path 0-1-2 with sink 0 is [[2,-1],[-1,1]], inverse [[1,1],[1,2]]
    have hL : ∀ i, i < 2 → ∀ j, j < 2 → redLap [3] i j =
        (if i = 0 ∧ j = 0 then 2 else if i = 1 ∧ j = 1 then 1 else -1) := by decide
    refine ⟨fun j => if j.val = 0 then (x 0 - y 0) + (x 1 - y 1)
      else (x 0 - y 0) + 2 * (x 1 - y 1), ?_⟩
    intro ⟨i, hi⟩
    unfold app
    simp only [sumTo]
    rw [hL i hi 0 (by decide), hL i hi 1 (by decide)]
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · simp
      omega
    · simp
      omega
  · intro b; exact ⟨Quotient.mk (cokerSetoid 2 (redLap [3])) (fun _ => 0),
      funext fun i => Fin.elim0 i.2⟩

/-- Non-vacuity of the predicate: the path `[3]` (a tree, n = 1) has trivial Jacobian, and the
conjectured form holds with `e ≡ 0` (the empty sum). -/
theorem sandpile_P3_trivial : ∃ e : Nat → Nat, ∃ φ : Sandpile [3] → Target [3] e, IsIso φ :=
  p3_iso

/-! ## Dimension three: the cube `[2]×[2]×[2]` -/

def T222 : Nat → Nat → Int
  | 0, 0 => 3 | 0, 2 => -1 | 0, 4 => -1
  | 1, 1 => 3 | 1, 2 => -1 | 1, 5 => -1
  | 2, 0 => -1 | 2, 1 => -1 | 2, 2 => 3 | 2, 6 => -1
  | 3, 3 => 3 | 3, 4 => -1 | 3, 5 => -1
  | 4, 0 => -1 | 4, 3 => -1 | 4, 4 => 3 | 4, 6 => -1
  | 5, 1 => -1 | 5, 3 => -1 | 5, 5 => 3 | 5, 6 => -1
  | 6, 2 => -1 | 6, 4 => -1 | 6, 5 => -1 | 6, 6 => 3
  | _, _ => 0

theorem redLap_222 : ∀ i, i < 7 → ∀ j, j < 7 → redLap [2, 2, 2] i j = T222 i j := by decide

theorem app_222 (z : Vec 7) (i : Nat) (hi : i < 7) :
    app 7 (redLap [2, 2, 2]) z i = T222 i 0 * z 0 + T222 i 1 * z 1 + T222 i 2 * z 2 +
      T222 i 3 * z 3 + T222 i 4 * z 4 + T222 i 5 * z 5 + T222 i 6 * z 6 := by
  unfold app
  simp only [sumTo]
  rw [redLap_222 i hi 0 (by decide), redLap_222 i hi 1 (by decide), redLap_222 i hi 2 (by decide),
    redLap_222 i hi 3 (by decide), redLap_222 i hi 4 (by decide), redLap_222 i hi 5 (by decide),
    redLap_222 i hi 6 (by decide)]
  simp

/-- `2 e₂`, twice the chip at vertex `(0,1,1)`. -/
def f2 : Vec 7 := fun j => if j.val = 2 then 2 else 0

def g222 : Coker 7 (redLap [2, 2, 2]) := mkC 7 (redLap [2, 2, 2]) f2

/-- `8 e₂ = Δ̃ (3,3,6,2,3,3,4)`. -/
theorem g222_four : (g222 + g222) + (g222 + g222) = 0 := by
  apply four_eq
  refine ⟨fun j => [3, 3, 6, 2, 3, 3, 4].getD j.val 0, ?_⟩
  intro ⟨i, hi⟩
  rw [app_222 _ i hi]
  simp only [f2]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `4 e₂ ∉ Δ̃ ℤ⁷`. -/
theorem g222_two : g222 + g222 ≠ 0 := by
  refine two_ne 7 (redLap [2, 2, 2]) f2 ?_
  intro ⟨z, hz⟩
  have h0 : (0 : Int) = (3) * z 0 + (0) * z 1 + (-1) * z 2 + (0) * z 3 + (-1) * z 4 + (0) * z 5 + (0) * z 6 := by
    have := hz ⟨0, by decide⟩
    rw [app_222 _ _ (by decide)] at this
    exact this
  have h1 : (0 : Int) = (0) * z 0 + (3) * z 1 + (-1) * z 2 + (0) * z 3 + (0) * z 4 + (-1) * z 5 + (0) * z 6 := by
    have := hz ⟨1, by decide⟩
    rw [app_222 _ _ (by decide)] at this
    exact this
  have h2 : (4 : Int) = (-1) * z 0 + (-1) * z 1 + (3) * z 2 + (0) * z 3 + (0) * z 4 + (0) * z 5 + (-1) * z 6 := by
    have := hz ⟨2, by decide⟩
    rw [app_222 _ _ (by decide)] at this
    exact this
  have h3 : (0 : Int) = (0) * z 0 + (0) * z 1 + (0) * z 2 + (3) * z 3 + (-1) * z 4 + (-1) * z 5 + (0) * z 6 := by
    have := hz ⟨3, by decide⟩
    rw [app_222 _ _ (by decide)] at this
    exact this
  have h4 : (0 : Int) = (-1) * z 0 + (0) * z 1 + (0) * z 2 + (-1) * z 3 + (3) * z 4 + (0) * z 5 + (-1) * z 6 := by
    have := hz ⟨4, by decide⟩
    rw [app_222 _ _ (by decide)] at this
    exact this
  have h5 : (0 : Int) = (0) * z 0 + (-1) * z 1 + (0) * z 2 + (-1) * z 3 + (0) * z 4 + (3) * z 5 + (-1) * z 6 := by
    have := hz ⟨5, by decide⟩
    rw [app_222 _ _ (by decide)] at this
    exact this
  have h6 : (0 : Int) = (0) * z 0 + (0) * z 1 + (-1) * z 2 + (0) * z 3 + (-1) * z 4 + (-1) * z 5 + (3) * z 6 := by
    have := hz ⟨6, by decide⟩
    rw [app_222 _ _ (by decide)] at this
    exact this
  omega

theorem no_injective_hom_Q3 (ι : Type) (d : ι → Nat) (hd : ∀ i, Small (d i))
    (φ : Sandpile [2, 2, 2] → Prod' ι d) (hφ : IsHom φ) : ¬ Injective φ := fun hinj =>
  no_injective_hom (G := Coker 7 (redLap [2, 2, 2])) (coker_zero_add _ _) g222 g222_four g222_two
    ι d hd φ hφ hinj

theorem modOf_222 : ∀ k, k < (subsetsL [2, 2, 2]).length → Small (modOf [2, 2, 2] k) := by
  intro k hk
  have : (subsetsL [2, 2, 2]).length = 8 := by decide
  rw [this] at hk
  unfold Small
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem modOf_111 : ∀ k, k < (subsetsL [1, 1, 1]).length → Small (modOf [1, 1, 1] k) := by
  intro k hk
  have : (subsetsL [1, 1, 1]).length = 8 := by decide
  rw [this] at hk
  unfold Small
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Disproof in dimension `n ≥ 3`** (in case the claim is read as excluding `n = 2`). -/
theorem conjecture_00000001230_false_dim3 : ¬ ClaimV3 := by
  intro hc
  obtain ⟨e, φ, hφ, hinj, _⟩ := hc [2, 2, 2] (by decide) (by decide)
  exact no_injective_hom_Q3 (Idx [2, 2, 2] e) (fun i => modOf [2, 2, 2] i.1.val)
    (fun i => modOf_222 i.1.val i.1.isLt) φ hφ hinj

/-- Edge-count reading in dimension 3: `[1]×[1]×[1]` is the cube. -/
theorem no_iso_111_edges (e : Nat → Nat) (φ : Sandpile ([1, 1, 1].map (· + 1)) → Target [1, 1, 1] e) :
    ¬ IsIso φ :=
  fun ⟨hφ, hinj, _⟩ => no_injective_hom_Q3 (Idx [1, 1, 1] e) (fun i => modOf [1, 1, 1] i.1.val)
    (fun i => modOf_111 i.1.val i.1.isLt) φ hφ hinj

end Grid1230

#print axioms Grid1230.conjecture_00000001230_false
#print axioms Grid1230.conjecture_00000001230_false_edges
#print axioms Grid1230.conjecture_00000001230_false_dim3
#print axioms Grid1230.no_iso_22
#print axioms Grid1230.no_iso_111_edges
#print axioms Grid1230.no_injective_hom_C4
#print axioms Grid1230.no_injective_hom_PicC4
#print axioms Grid1230.no_injective_hom_Pic0C4
#print axioms Grid1230.no_iso_22_Pic0
#print axioms Grid1230.no_iso_22_Pic
#print axioms Grid1230.no_injective_hom_Q3
#print axioms Grid1230.sandpile_C4_iso_Z4
#print axioms Grid1230.sandpile_P3_trivial
