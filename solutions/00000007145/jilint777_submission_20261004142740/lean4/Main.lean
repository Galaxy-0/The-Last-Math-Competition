/-!
# Conjecture 00000007145: a 3-dimensional polytope with a non-Hamiltonian graph

The conjecture says that non-Hamiltonian graphs of 4-dimensional polytopes exist
and that *the minimal dimension of such examples is four*.  The second clause is
false: the rhombic dodecahedron

  `conv {(±2,0,0), (0,±2,0), (0,0,±2), (±1,±1,±1)} ⊂ ℝ³`

is a 3-dimensional polytope whose graph (1-skeleton) has no Hamiltonian cycle.
The 8 vertices `(±1,±1,±1)` are pairwise non-adjacent, and 8 > 14/2.

Everything is defined from scratch (core Lean only):

* points are integer vectors (`List Int`), a polytope is given by its vertex list;
* `IsVertex d V p`: some linear functional is maximised over `V` exactly at `p`;
* `Adj d V p q`: some linear functional is maximised over `V` exactly at `{p, q}`,
  i.e. the segment `[p, q]` is an edge (a 1-dimensional face) of `conv V`;
* `FullDim d V`: `d + 1` points of `V` are affinely independent (nonzero determinant),
  so `conv V` is `d`-dimensional;
* `HamCycle d V cyc`: `cyc` lists every vertex exactly once, has length `≥ 3`,
  and cyclically consecutive vertices are adjacent.
-/

namespace PolytopeHam

/-! ## Vectors -/

/-- A point (or linear functional) in `ℤ^d`, as a list of coordinates. -/
abbrev Pt := List Int

/-- Dot product (missing coordinates count as `0`). -/
def dot : Pt → Pt → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- Vector sum (missing coordinates count as `0`). -/
def vadd : Pt → Pt → Pt
  | a :: as, b :: bs => (a + b) :: vadd as bs
  | [], v => v
  | u, [] => u

def vsub (u v : Pt) : Pt := List.zipWith (· - ·) u v

def smul (k : Int) (v : Pt) : Pt := v.map (k * ·)

/-- `Σ mᵢ wᵢ` for a list of pairs `(mᵢ, wᵢ)` with natural weights. -/
def lincomb : List (Nat × Pt) → Pt
  | [] => []
  | e :: t => vadd (smul e.1 e.2) (lincomb t)

@[simp] theorem dot_nil_left (v : Pt) : dot [] v = 0 := by cases v <;> rfl
@[simp] theorem dot_nil_right (v : Pt) : dot v [] = 0 := by cases v <;> rfl

theorem dot_vadd : ∀ (c u v : Pt), dot c (vadd u v) = dot c u + dot c v
  | [], u, v => by simp
  | _ :: _, [], v => by simp [vadd]
  | _ :: _, _ :: _, [] => by simp [vadd]
  | x :: c, a :: u, b :: v => by
    show x * (a + b) + dot c (vadd u v) = (x * a + dot c u) + (x * b + dot c v)
    rw [dot_vadd c u v, Int.mul_add]; omega

theorem dot_smul (k : Int) : ∀ (c v : Pt), dot c (smul k v) = k * dot c v
  | [], v => by simp
  | _ :: _, [] => by simp [smul]
  | x :: c, b :: v => by
    show x * (k * b) + dot c (smul k v) = k * (x * b + dot c v)
    rw [dot_smul k c v, Int.mul_add, Int.mul_left_comm]

theorem dot_lincomb (c : Pt) : ∀ cert : List (Nat × Pt),
    dot c (lincomb cert) = (cert.map fun e => (e.1 : Int) * dot c e.2).sum
  | [] => by simp [lincomb]
  | e :: t => by simp [lincomb, dot_vadd, dot_smul, dot_lincomb c t]

/-! ## Determinants and dimension -/

/-- Determinant of an `n × n` matrix (list of rows) by Laplace expansion along the first row. -/
def detN : Nat → List (List Int) → Int
  | 0, _ => 1
  | _ + 1, [] => 0
  | n + 1, r :: rs => ((List.range (n + 1)).map fun j =>
      (if j % 2 = 0 then (1 : Int) else -1) * r.getD j 0 * detN n (rs.map (·.eraseIdx j))).sum

def det (M : List (List Int)) : Int := detN M.length M

example : det [[1, 2], [3, 4]] = -2 := by decide
example : det [[2, 0, 1], [1, 3, 2], [1, 1, 2]] = 6 := by decide
example : det [[1, 2, 3], [4, 5, 6], [7, 8, 9]] = 0 := by decide

/-- `conv V ⊂ ℝ^d` is `d`-dimensional: there are `d + 1` affinely independent points
`p, b₁, …, b_d` in `V`, i.e. `det (b₁ - p, …, b_d - p) ≠ 0`. -/
def FullDim (d : Nat) (V : List Pt) : Prop :=
  ∃ p ∈ V, ∃ B : List Pt, (∀ b ∈ B, b ∈ V) ∧ B.length = d ∧ det (B.map (vsub · p)) ≠ 0

/-! ## Vertices and edges of `conv V` -/

/-- `p` is a vertex of `conv V`: a linear functional `c` attains its maximum over `V`
only at `p`. -/
def IsVertex (d : Nat) (V : List Pt) (p : Pt) : Prop :=
  p ∈ V ∧ ∃ c : Pt, c.length = d ∧ ∀ q ∈ V, q ≠ p → dot c q < dot c p

/-- `[p, q]` is an edge of `conv V` (for `V` a list of vertices): a linear functional
`c` attains its maximum over `V` exactly at `p` and `q`. -/
def Adj (d : Nat) (V : List Pt) (p q : Pt) : Prop :=
  p ∈ V ∧ q ∈ V ∧ p ≠ q ∧
    ∃ c : Pt, c.length = d ∧ dot c p = dot c q ∧ ∀ r ∈ V, r ≠ p → r ≠ q → dot c r < dot c p

theorem Adj.symm {d V p q} : Adj d V p q → Adj d V q p := by
  rintro ⟨hp, hq, hne, c, hc, heq, hlt⟩
  exact ⟨hq, hp, Ne.symm hne, c, hc, heq.symm, fun r hr h1 h2 => heq ▸ hlt r hr h2 h1⟩

/-- A (vertex-described) convex polytope of dimension `d`: `conv V ⊂ ℝ^d` where every listed
point is a vertex and the hull is full-dimensional. -/
structure Polytope where
  d : Nat
  V : List Pt
  coords : ∀ p ∈ V, p.length = d
  nodup : V.Nodup
  allVertices : ∀ p ∈ V, IsVertex d V p
  fullDim : FullDim d V

/-! ## Hamiltonian cycles -/

/-- `Path R [x₀, …, xₙ]`: `R xᵢ xᵢ₊₁` for all consecutive entries. -/
def Path {α : Type} (R : α → α → Prop) : List α → Prop
  | a :: b :: t => R a b ∧ Path R (b :: t)
  | _ => True

instance decPath {α : Type} (R : α → α → Prop) [DecidableRel R] : ∀ l, Decidable (Path R l)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | a :: b :: t =>
    have := decPath R (b :: t)
    inferInstanceAs (Decidable (R a b ∧ Path R (b :: t)))

theorem Path.mono {α : Type} {R R' : α → α → Prop} (h : ∀ x y, R x y → R' x y) :
    ∀ l, Path R l → Path R' l
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: b :: t, ⟨h1, h2⟩ => ⟨h _ _ h1, Path.mono h (b :: t) h2⟩

theorem Path.of_append {α : Type} {R : α → α → Prop} :
    ∀ (l m : List α), Path R (l ++ m) → Path R l
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | _ :: b :: t, m, ⟨h1, h2⟩ => ⟨h1, Path.of_append (b :: t) m h2⟩

/-- A Hamiltonian cycle `v₀ v₁ … v_{n-1} v₀` of the graph of `conv V`: the list `cyc`
contains every vertex exactly once, `n ≥ 3`, and `vᵢ ~ vᵢ₊₁` (indices mod `n`). -/
def HamCycle (d : Nat) (V : List Pt) (cyc : List Pt) : Prop :=
  cyc.Nodup ∧ (∀ x, x ∈ cyc ↔ x ∈ V) ∧ 3 ≤ cyc.length ∧ Path (Adj d V) (cyc ++ cyc.take 1)

/-- The graph of the polytope is Hamiltonian. -/
def Polytope.Hamiltonian (P : Polytope) : Prop := ∃ cyc, HamCycle P.d P.V cyc

/-! ## The conjecture's minimality clause -/

/-- "Non-Hamiltonian examples of 4-dimensional polytope graphs exist, and the minimal
dimension of the examples is four."  Charitably, degenerate polytopes of dimension
`0, 1` (one or two vertices, no cycle at all) are not counted as examples. -/
def MinDimIsFour : Prop :=
  (∃ P : Polytope, P.d = 4 ∧ ¬ P.Hamiltonian) ∧
    ∀ P : Polytope, 2 ≤ P.d → ¬ P.Hamiltonian → 4 ≤ P.d

/-- The weakest consequence of the minimality clause: all 3-polytopes are Hamiltonian. -/
def AllThreePolytopesHamiltonian : Prop := ∀ P : Polytope, P.d = 3 → P.Hamiltonian

theorem minDimIsFour_imp : MinDimIsFour → AllThreePolytopesHamiltonian := by
  intro h P hd
  apply Classical.byContradiction
  intro hP
  have := h.2 P (by omega) hP
  omega

/-! ## Certificates -/

/-- Certificate that `[p, q]` is an edge, with the exposing functional `c`. -/
def EdgeCertOK (d : Nat) (V : List Pt) (p q c : Pt) : Prop :=
  p ∈ V ∧ q ∈ V ∧ p ≠ q ∧ c.length = d ∧ dot c p = dot c q ∧
    ∀ r ∈ V, r ≠ p → r ≠ q → dot c r < dot c p

instance (d V p q c) : Decidable (EdgeCertOK d V p q c) := by
  unfold EdgeCertOK; infer_instance

theorem adj_of_edgeCert {d V p q c} (h : EdgeCertOK d V p q c) : Adj d V p q :=
  ⟨h.1, h.2.1, h.2.2.1, c, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Certificate that `[p, q]` is NOT an edge: `k (p + q) = Σ mᵢ wᵢ` with natural weights,
`Σ mᵢ = 2k`, `k > 0`, and all `wᵢ ∈ V \ {p, q}`.  Geometrically, the midpoint of `[p, q]` is
a convex combination of the other vertices. -/
def CertOK (V : List Pt) (p q : Pt) (k : Nat) (cert : List (Nat × Pt)) : Prop :=
  0 < k ∧ (∀ e ∈ cert, e.2 ∈ V ∧ e.2 ≠ p ∧ e.2 ≠ q) ∧ (cert.map Prod.fst).sum = 2 * k ∧
    lincomb cert = smul k (vadd p q)

instance (V p q k cert) : Decidable (CertOK V p q k cert) := by
  unfold CertOK; infer_instance

theorem weighted_le (c : Pt) (t : Int) : ∀ cert : List (Nat × Pt), (∀ e ∈ cert, dot c e.2 < t) →
    (cert.map fun e => (e.1 : Int) * dot c e.2).sum + ((cert.map Prod.fst).sum : Nat)
      ≤ ((cert.map Prod.fst).sum : Nat) * t
  | [], _ => by simp
  | (m, w) :: rest, h => by
    have h1 : dot c w + 1 ≤ t := h (m, w) (by simp)
    have ih := weighted_le c t rest (fun e he => h e (by simp [he]))
    have h2 : (m : Int) * (dot c w + 1) ≤ m * t :=
      Int.mul_le_mul_of_nonneg_left h1 (Int.ofNat_nonneg m)
    rw [Int.mul_add, Int.mul_one] at h2
    simp only [List.map_cons, List.sum_cons, Int.natCast_add, Int.add_mul]
    omega

/-- **Non-edge lemma.**  A convex-combination certificate rules out every exposing functional. -/
theorem not_adj_of_cert {d V p q k cert} (h : CertOK V p q k cert) : ¬ Adj d V p q := by
  rintro ⟨_, _, _, c, _, heq, hlt⟩
  obtain ⟨hk, hmem, hsum, hcomb⟩ := h
  have h1 := weighted_le c (dot c p) cert
    (fun e he => hlt e.2 (hmem e he).1 (hmem e he).2.1 (hmem e he).2.2)
  rw [← dot_lincomb, hcomb, dot_smul, dot_vadd, hsum, ← heq] at h1
  have h2 : ((2 * k : Nat) : Int) * dot c p = 2 * ((k : Int) * dot c p) := by
    rw [Int.natCast_mul, Int.mul_assoc]; rfl
  rw [h2, Int.mul_add] at h1
  have : (0 : Int) < k := by omega
  generalize (k : Int) * dot c p = y at h1
  push_cast at h1
  omega

/-! ## The independence criterion for non-Hamiltonicity -/

theorem path_count {α : Type} (R : α → α → Prop) (P : α → Bool)
    (hind : ∀ x y, R x y → ¬ (P x = true ∧ P y = true)) :
    ∀ l : List α, Path R l →
      l.countP P ≤ l.countP (fun x => !P x) + 1 ∧
      (∀ a t, l = a :: t → P a = false → l.countP P ≤ l.countP (fun x => !P x))
  | [], _ => by simp
  | [a], _ => by
    refine ⟨?_, ?_⟩
    · cases h : P a <;> simp [h]
    · intro b t hl hb; cases hl; simp [hb]
  | a :: b :: t, ⟨hab, hp⟩ => by
    have ih := path_count R P hind (b :: t) hp
    have e1 : (a :: b :: t).countP P = (b :: t).countP P + (if P a = true then 1 else 0) :=
      List.countP_cons
    have e2 : (a :: b :: t).countP (fun x => !P x) =
        (b :: t).countP (fun x => !P x) + (if (!P a) = true then 1 else 0) := List.countP_cons
    have hA1 : P a = false → (a :: b :: t).countP P ≤ (a :: b :: t).countP (fun x => !P x) := by
      intro ha
      rw [e1, e2]
      simp only [ha, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      have := ih.1
      omega
    refine ⟨?_, ?_⟩
    · cases ha : P a
      · have := hA1 ha; omega
      · have hb : P b = false := by
          cases hb' : P b
          · rfl
          · exact absurd ⟨ha, hb'⟩ (hind a b hab)
        have := ih.2 b t rfl hb
        rw [e1, e2]
        simp only [ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        omega
    · intro a' t' hl ha'
      cases hl
      exact hA1 ha'

theorem perm_of_nodup {α : Type} [DecidableEq α] : ∀ {l l' : List α}, l.Nodup → l'.Nodup → (∀ x, x ∈ l ↔ x ∈ l') →
    l.Perm l'
  | [], l', _, _, h => by
    cases l' with
    | nil => exact List.Perm.nil
    | cons b t => exact absurd ((h b).2 (by simp)) (by simp)
  | a :: t, l', hn, hn', h => by
    have ha : a ∈ l' := (h a).1 (by simp)
    have hn1 := List.nodup_cons.1 hn
    have hp := perm_of_nodup hn1.2 (hn'.erase a) (fun x => by
      rw [hn'.mem_erase_iff]
      constructor
      · intro hx
        exact ⟨fun e => hn1.1 (e ▸ hx), (h x).1 (by simp [hx])⟩
      · rintro ⟨hxa, hx⟩
        have := (h x).2 hx
        simp at this
        rcases this with e | e
        · exact absurd e hxa
        · exact e)
    exact (hp.cons a).trans (List.perm_cons_erase ha).symm

/-- **Independence criterion.**  If more than half of the vertices are pairwise
non-adjacent (marked by `P`), there is no Hamiltonian cycle. -/
theorem no_hamCycle (d : Nat) (V : List Pt) (P : Pt → Bool) (hV : V.Nodup)
    (hind : ∀ x y, P x = true → P y = true → ¬ Adj d V x y)
    (hbig : V.countP (fun x => !P x) < V.countP P) : ¬ ∃ cyc, HamCycle d V cyc := by
  rintro ⟨cyc, hnd, hmem, hlen, hpath⟩
  have hperm := perm_of_nodup hnd hV hmem
  have e1 := hperm.countP_eq P
  have e2 := hperm.countP_eq (fun x => !P x)
  have hind' : ∀ x y, Adj d V x y → ¬ (P x = true ∧ P y = true) :=
    fun x y h hxy => hind x y hxy.1 hxy.2 h
  have key : cyc.countP P ≤ cyc.countP (fun x => !P x) := by
    match cyc, hlen, hpath with
    | a :: b :: u, _, hpath =>
      have hp' : Path (Adj d V) (a :: b :: (u ++ [a])) := by simpa using hpath
      cases ha : P a
      · have hc : Path (Adj d V) (a :: b :: u) :=
          Path.of_append (a :: b :: u) [a] (by simpa using hp')
        exact (path_count _ P hind' _ hc).2 a _ rfl ha
      · have hb : P b = false := by
          cases hb' : P b
          · rfl
          · exact absurd ⟨ha, hb'⟩ (hind' a b hp'.1)
        have := (path_count _ P hind' _ hp'.2).2 b _ rfl hb
        simp only [List.countP_cons, List.countP_append, List.countP_nil] at this ⊢
        simp only [ha, hb, Bool.not_true, Bool.not_false] at this ⊢
        simp at this ⊢
        omega
  omega

/-! ## The rhombic dodecahedron -/

/-- The 14 vertices: 6 "octahedral" ones `(±2,0,0), …` and 8 "cubical" ones `(±1,±1,±1)`. -/
def rd : List Pt :=
  [[2,0,0], [-2,0,0], [0,2,0], [0,-2,0], [0,0,2], [0,0,-2],
   [1,1,1], [1,1,-1], [1,-1,1], [1,-1,-1], [-1,1,1], [-1,1,-1], [-1,-1,1], [-1,-1,-1]]

/-- The cubical vertices. -/
def cube : List Pt :=
  [[1,1,1], [1,1,-1], [1,-1,1], [1,-1,-1], [-1,1,1], [-1,1,-1], [-1,-1,1], [-1,-1,-1]]

def isCube (p : Pt) : Bool := cube.contains p

/-- Every point `p` is the unique maximiser of the functional `x ↦ ⟨p, x⟩`. -/
theorem rd_vertex_cert : ∀ p ∈ rd, p.length = 3 ∧ ∀ q ∈ rd, q ≠ p → dot p q < dot p p := by
  decide

/-- Affine independence of `(0,0,-2), (2,0,0), (0,2,0), (0,0,2)`. -/
theorem rd_fullDim : FullDim 3 rd :=
  ⟨[0,0,-2], by decide, [[2,0,0], [0,2,0], [0,0,2]], by decide, rfl, by decide⟩

/-- The rhombic dodecahedron as a 3-dimensional polytope. -/
def RD : Polytope where
  d := 3
  V := rd
  coords p hp := (rd_vertex_cert p hp).1
  nodup := by decide
  allVertices p hp := ⟨hp, p, (rd_vertex_cert p hp).1, (rd_vertex_cert p hp).2⟩
  fullDim := rd_fullDim

theorem RD_dim : RD.d = 3 := rfl

/-- The 24 edges `(cubical vertex s, octahedral vertex a, exposing functional c)`. -/
def rdEdges : List (Pt × Pt × Pt) := [
  ([1,1,1], [2,0,0], [2,1,1]),
  ([1,1,1], [0,2,0], [1,2,1]),
  ([1,1,1], [0,0,2], [1,1,2]),
  ([1,1,-1], [2,0,0], [2,1,-1]),
  ([1,1,-1], [0,2,0], [1,2,-1]),
  ([1,1,-1], [0,0,-2], [1,1,-2]),
  ([1,-1,1], [2,0,0], [2,-1,1]),
  ([1,-1,1], [0,-2,0], [1,-2,1]),
  ([1,-1,1], [0,0,2], [1,-1,2]),
  ([1,-1,-1], [2,0,0], [2,-1,-1]),
  ([1,-1,-1], [0,-2,0], [1,-2,-1]),
  ([1,-1,-1], [0,0,-2], [1,-1,-2]),
  ([-1,1,1], [-2,0,0], [-2,1,1]),
  ([-1,1,1], [0,2,0], [-1,2,1]),
  ([-1,1,1], [0,0,2], [-1,1,2]),
  ([-1,1,-1], [-2,0,0], [-2,1,-1]),
  ([-1,1,-1], [0,2,0], [-1,2,-1]),
  ([-1,1,-1], [0,0,-2], [-1,1,-2]),
  ([-1,-1,1], [-2,0,0], [-2,-1,1]),
  ([-1,-1,1], [0,-2,0], [-1,-2,1]),
  ([-1,-1,1], [0,0,2], [-1,-1,2]),
  ([-1,-1,-1], [-2,0,0], [-2,-1,-1]),
  ([-1,-1,-1], [0,-2,0], [-1,-2,-1]),
  ([-1,-1,-1], [0,0,-2], [-1,-1,-2])
]

/-- The 67 non-edges `(p, q, k, certificate)`. -/
def rdNonEdges : List (Pt × Pt × Nat × List (Nat × Pt)) := [
  ([2,0,0], [-2,0,0], 1, [(1, [0,2,0]), (1, [0,-2,0])]),
  ([2,0,0], [0,2,0], 1, [(1, [1,1,1]), (1, [1,1,-1])]),
  ([2,0,0], [0,-2,0], 1, [(1, [1,-1,1]), (1, [1,-1,-1])]),
  ([2,0,0], [0,0,2], 1, [(1, [1,1,1]), (1, [1,-1,1])]),
  ([2,0,0], [0,0,-2], 1, [(1, [1,1,-1]), (1, [1,-1,-1])]),
  ([2,0,0], [-1,1,1], 1, [(1, [0,2,0]), (1, [1,-1,1])]),
  ([2,0,0], [-1,1,-1], 1, [(1, [0,2,0]), (1, [1,-1,-1])]),
  ([2,0,0], [-1,-1,1], 1, [(1, [0,-2,0]), (1, [1,1,1])]),
  ([2,0,0], [-1,-1,-1], 1, [(1, [0,-2,0]), (1, [1,1,-1])]),
  ([-2,0,0], [0,2,0], 1, [(1, [-1,1,1]), (1, [-1,1,-1])]),
  ([-2,0,0], [0,-2,0], 1, [(1, [-1,-1,1]), (1, [-1,-1,-1])]),
  ([-2,0,0], [0,0,2], 1, [(1, [-1,1,1]), (1, [-1,-1,1])]),
  ([-2,0,0], [0,0,-2], 1, [(1, [-1,1,-1]), (1, [-1,-1,-1])]),
  ([-2,0,0], [1,1,1], 1, [(1, [0,2,0]), (1, [-1,-1,1])]),
  ([-2,0,0], [1,1,-1], 1, [(1, [0,2,0]), (1, [-1,-1,-1])]),
  ([-2,0,0], [1,-1,1], 1, [(1, [0,-2,0]), (1, [-1,1,1])]),
  ([-2,0,0], [1,-1,-1], 1, [(1, [0,-2,0]), (1, [-1,1,-1])]),
  ([0,2,0], [0,-2,0], 1, [(1, [2,0,0]), (1, [-2,0,0])]),
  ([0,2,0], [0,0,2], 1, [(1, [1,1,1]), (1, [-1,1,1])]),
  ([0,2,0], [0,0,-2], 1, [(1, [1,1,-1]), (1, [-1,1,-1])]),
  ([0,2,0], [1,-1,1], 1, [(1, [2,0,0]), (1, [-1,1,1])]),
  ([0,2,0], [1,-1,-1], 1, [(1, [2,0,0]), (1, [-1,1,-1])]),
  ([0,2,0], [-1,-1,1], 1, [(1, [-2,0,0]), (1, [1,1,1])]),
  ([0,2,0], [-1,-1,-1], 1, [(1, [-2,0,0]), (1, [1,1,-1])]),
  ([0,-2,0], [0,0,2], 1, [(1, [1,-1,1]), (1, [-1,-1,1])]),
  ([0,-2,0], [0,0,-2], 1, [(1, [1,-1,-1]), (1, [-1,-1,-1])]),
  ([0,-2,0], [1,1,1], 1, [(1, [2,0,0]), (1, [-1,-1,1])]),
  ([0,-2,0], [1,1,-1], 1, [(1, [2,0,0]), (1, [-1,-1,-1])]),
  ([0,-2,0], [-1,1,1], 1, [(1, [-2,0,0]), (1, [1,-1,1])]),
  ([0,-2,0], [-1,1,-1], 1, [(1, [-2,0,0]), (1, [1,-1,-1])]),
  ([0,0,2], [0,0,-2], 1, [(1, [2,0,0]), (1, [-2,0,0])]),
  ([0,0,2], [1,1,-1], 1, [(1, [2,0,0]), (1, [-1,1,1])]),
  ([0,0,2], [1,-1,-1], 1, [(1, [2,0,0]), (1, [-1,-1,1])]),
  ([0,0,2], [-1,1,-1], 1, [(1, [-2,0,0]), (1, [1,1,1])]),
  ([0,0,2], [-1,-1,-1], 1, [(1, [-2,0,0]), (1, [1,-1,1])]),
  ([0,0,-2], [1,1,1], 1, [(1, [2,0,0]), (1, [-1,1,-1])]),
  ([0,0,-2], [1,-1,1], 1, [(1, [2,0,0]), (1, [-1,-1,-1])]),
  ([0,0,-2], [-1,1,1], 1, [(1, [-2,0,0]), (1, [1,1,-1])]),
  ([0,0,-2], [-1,-1,1], 1, [(1, [-2,0,0]), (1, [1,-1,-1])]),
  ([1,1,1], [1,1,-1], 1, [(1, [2,0,0]), (1, [0,2,0])]),
  ([1,1,1], [1,-1,1], 1, [(1, [2,0,0]), (1, [0,0,2])]),
  ([1,1,1], [1,-1,-1], 1, [(1, [1,1,-1]), (1, [1,-1,1])]),
  ([1,1,1], [-1,1,1], 1, [(1, [0,2,0]), (1, [0,0,2])]),
  ([1,1,1], [-1,1,-1], 1, [(1, [1,1,-1]), (1, [-1,1,1])]),
  ([1,1,1], [-1,-1,1], 1, [(1, [1,-1,1]), (1, [-1,1,1])]),
  ([1,1,1], [-1,-1,-1], 1, [(1, [2,0,0]), (1, [-2,0,0])]),
  ([1,1,-1], [1,-1,1], 1, [(1, [1,1,1]), (1, [1,-1,-1])]),
  ([1,1,-1], [1,-1,-1], 1, [(1, [2,0,0]), (1, [0,0,-2])]),
  ([1,1,-1], [-1,1,1], 1, [(1, [1,1,1]), (1, [-1,1,-1])]),
  ([1,1,-1], [-1,1,-1], 1, [(1, [0,2,0]), (1, [0,0,-2])]),
  ([1,1,-1], [-1,-1,1], 1, [(1, [2,0,0]), (1, [-2,0,0])]),
  ([1,1,-1], [-1,-1,-1], 1, [(1, [1,-1,-1]), (1, [-1,1,-1])]),
  ([1,-1,1], [1,-1,-1], 1, [(1, [2,0,0]), (1, [0,-2,0])]),
  ([1,-1,1], [-1,1,1], 1, [(1, [1,1,1]), (1, [-1,-1,1])]),
  ([1,-1,1], [-1,1,-1], 1, [(1, [2,0,0]), (1, [-2,0,0])]),
  ([1,-1,1], [-1,-1,1], 1, [(1, [0,-2,0]), (1, [0,0,2])]),
  ([1,-1,1], [-1,-1,-1], 1, [(1, [1,-1,-1]), (1, [-1,-1,1])]),
  ([1,-1,-1], [-1,1,1], 1, [(1, [2,0,0]), (1, [-2,0,0])]),
  ([1,-1,-1], [-1,1,-1], 1, [(1, [1,1,-1]), (1, [-1,-1,-1])]),
  ([1,-1,-1], [-1,-1,1], 1, [(1, [1,-1,1]), (1, [-1,-1,-1])]),
  ([1,-1,-1], [-1,-1,-1], 1, [(1, [0,-2,0]), (1, [0,0,-2])]),
  ([-1,1,1], [-1,1,-1], 1, [(1, [-2,0,0]), (1, [0,2,0])]),
  ([-1,1,1], [-1,-1,1], 1, [(1, [-2,0,0]), (1, [0,0,2])]),
  ([-1,1,1], [-1,-1,-1], 1, [(1, [-1,1,-1]), (1, [-1,-1,1])]),
  ([-1,1,-1], [-1,-1,1], 1, [(1, [-1,1,1]), (1, [-1,-1,-1])]),
  ([-1,1,-1], [-1,-1,-1], 1, [(1, [-2,0,0]), (1, [0,0,-2])]),
  ([-1,-1,1], [-1,-1,-1], 1, [(1, [-2,0,0]), (1, [0,-2,0])])
]

theorem rd_edges_ok : ∀ e ∈ rdEdges, EdgeCertOK 3 rd e.1 e.2.1 e.2.2 := by decide

theorem rd_nonedges_ok : ∀ e ∈ rdNonEdges, CertOK rd e.1 e.2.1 e.2.2.1 e.2.2.2 := by
  decide +kernel

/-- Every pair of distinct vertices is covered by one of the two tables. -/
theorem rd_cover : ∀ p ∈ rd, ∀ q ∈ rd, p ≠ q →
    (∃ e ∈ rdEdges, (e.1 = p ∧ e.2.1 = q) ∨ (e.1 = q ∧ e.2.1 = p)) ∨
    (∃ e ∈ rdNonEdges, (e.1 = p ∧ e.2.1 = q) ∨ (e.1 = q ∧ e.2.1 = p)) := by
  decide +kernel

/-- **The graph of the rhombic dodecahedron**: exactly the 24 listed edges. -/
theorem rd_adj_iff (p q : Pt) :
    Adj 3 rd p q ↔ ∃ e ∈ rdEdges, (e.1 = p ∧ e.2.1 = q) ∨ (e.1 = q ∧ e.2.1 = p) := by
  constructor
  · intro h
    rcases rd_cover p h.1 q h.2.1 h.2.2.1 with h' | ⟨e, he, hpq⟩
    · exact h'
    · have hn := not_adj_of_cert (d := 3) (rd_nonedges_ok e he)
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1 h2; exact absurd h hn
      · subst h1 h2; exact absurd h.symm hn
  · rintro ⟨e, he, hpq⟩
    have ha := adj_of_edgeCert (rd_edges_ok e he)
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2; exact ha
    · subst h1 h2; exact ha.symm

/-- Every edge joins a cubical and an octahedral vertex (the graph is bipartite). -/
theorem rd_edges_bipartite : ∀ e ∈ rdEdges, isCube e.1 = true ∧ isCube e.2.1 = false := by
  decide

/-- The 8 cubical vertices are pairwise non-adjacent. -/
theorem cube_independent : ∀ x y, isCube x = true → isCube y = true → ¬ Adj 3 rd x y := by
  intro x y hx hy h
  obtain ⟨e, he, hxy⟩ := (rd_adj_iff x y).1 h
  have hb := rd_edges_bipartite e he
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1 h2; rw [hb.2] at hy; exact Bool.false_ne_true hy
  · subst h1 h2; rw [hb.2] at hx; exact Bool.false_ne_true hx

theorem rd_counts : rd.countP isCube = 8 ∧ rd.countP (fun x => !isCube x) = 6 := by decide

/-- **The rhombic dodecahedron has a non-Hamiltonian graph.** -/
theorem RD_not_hamiltonian : ¬ RD.Hamiltonian :=
  no_hamCycle 3 rd isCube (by decide) cube_independent (by rw [rd_counts.1, rd_counts.2]; decide)

/-- A 3-dimensional polytope with a non-Hamiltonian graph. -/
theorem exists_nonHamiltonian_3polytope : ∃ P : Polytope, P.d = 3 ∧ ¬ P.Hamiltonian :=
  ⟨RD, rfl, RD_not_hamiltonian⟩

/-! ## Main result -/

theorem not_allThreePolytopesHamiltonian : ¬ AllThreePolytopesHamiltonian :=
  fun h => RD_not_hamiltonian (h RD rfl)

/-- **Conjecture 00000007145 is false**: the minimal dimension of a polytope with a
non-Hamiltonian graph is not four (it is at most three). -/
theorem conjecture_00000007145_false : ¬ MinDimIsFour :=
  fun h => not_allThreePolytopesHamiltonian (minDimIsFour_imp h)

/-- Whatever reading one takes of the lower range of dimensions (even counting only
dimension 3), some example has dimension `< 4`. -/
theorem conjecture_00000007145_false' :
    ¬ ∀ P : Polytope, ¬ P.Hamiltonian → 4 ≤ P.d :=
  fun h => absurd (h RD RD_not_hamiltonian) (by decide)

/-! ## The first clause holds: a 4-dimensional example (pyramid over `RD`) -/

def lift (p : Pt) : Pt := p ++ [0]

def apex : Pt := [0, 0, 0, 1]

def pyr : List Pt := rd.map lift ++ [apex]

def cube4 : List Pt := cube.map lift

def isCube4 (p : Pt) : Bool := cube4.contains p

theorem pyr_vertex_cert : ∀ p ∈ pyr, p.length = 4 ∧ ∀ q ∈ pyr, q ≠ p → dot p q < dot p p := by
  decide

theorem pyr_fullDim : FullDim 4 pyr :=
  ⟨[0,0,-2,0], by decide, [[2,0,0,0], [0,2,0,0], [0,0,2,0], [0,0,0,1]], by decide, rfl,
    by decide⟩

/-- The pyramid over the rhombic dodecahedron, a 4-dimensional polytope. -/
def Pyr : Polytope where
  d := 4
  V := pyr
  coords p hp := (pyr_vertex_cert p hp).1
  nodup := by decide
  allVertices p hp := ⟨hp, p, (pyr_vertex_cert p hp).1, (pyr_vertex_cert p hp).2⟩
  fullDim := pyr_fullDim

/-- Lifted non-edge certificates for the 28 pairs of cubical vertices of the pyramid. -/
theorem pyr_cube_nonedges : ∀ x ∈ cube4, ∀ y ∈ cube4, x ≠ y →
    ∃ e ∈ rdNonEdges, ((lift e.1 = x ∧ lift e.2.1 = y) ∨ (lift e.1 = y ∧ lift e.2.1 = x)) ∧
      CertOK pyr (lift e.1) (lift e.2.1) e.2.2.1 (e.2.2.2.map fun w => (w.1, lift w.2)) := by
  decide +kernel

theorem cube4_independent : ∀ x y, isCube4 x = true → isCube4 y = true → ¬ Adj 4 pyr x y := by
  intro x y hx hy h
  have hx' : x ∈ cube4 := by simpa [isCube4] using hx
  have hy' : y ∈ cube4 := by simpa [isCube4] using hy
  obtain ⟨e, _, hxy, hc⟩ := pyr_cube_nonedges x hx' y hy' h.2.2.1
  have hn := not_adj_of_cert (d := 4) hc
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hn; exact hn h
  · rw [h1, h2] at hn; exact hn h.symm

theorem Pyr_not_hamiltonian : ¬ Pyr.Hamiltonian :=
  no_hamCycle 4 pyr isCube4 (by decide) cube4_independent (by decide)

/-- The first clause of the conjecture is true (so the conjunction fails only through
its minimality clause). -/
theorem exists_nonHamiltonian_4polytope : ∃ P : Polytope, P.d = 4 ∧ ¬ P.Hamiltonian :=
  ⟨Pyr, rfl, Pyr_not_hamiltonian⟩

/-! ## Non-vacuity: a Hamiltonian polytope (the octahedron) -/

def oct : List Pt := [[1,0,0], [0,1,0], [0,0,1], [-1,0,0], [0,-1,0], [0,0,-1]]

theorem oct_vertex_cert : ∀ p ∈ oct, p.length = 3 ∧ ∀ q ∈ oct, q ≠ p → dot p q < dot p p := by
  decide

def Oct : Polytope where
  d := 3
  V := oct
  coords p hp := (oct_vertex_cert p hp).1
  nodup := by decide
  allVertices p hp := ⟨hp, p, (oct_vertex_cert p hp).1, (oct_vertex_cert p hp).2⟩
  fullDim := ⟨[0,0,-1], by decide, [[1,0,0], [0,1,0], [0,0,1]], by decide, rfl, by decide⟩

/-- The cycle `x⁺ y⁺ z⁺ x⁻ y⁻ z⁻ x⁺`, with exposing functional `p + q` for each edge. -/
theorem Oct_hamiltonian : Oct.Hamiltonian := by
  refine ⟨oct, by decide, fun _ => Iff.rfl, by decide, ?_⟩
  have h : Path (fun p q => EdgeCertOK 3 oct p q (vadd p q)) (oct ++ oct.take 1) := by decide
  exact Path.mono (fun _ _ hc => adj_of_edgeCert hc) _ h

/-- The octahedron's graph is not complete: `[x⁺, x⁻]` is not an edge. -/
theorem oct_nonedge : ¬ Adj 3 oct [1,0,0] [-1,0,0] :=
  not_adj_of_cert (k := 1) (cert := [(1, [0,1,0]), (1, [0,-1,0])]) (by decide)

end PolytopeHam

#print axioms PolytopeHam.not_adj_of_cert
#print axioms PolytopeHam.no_hamCycle
#print axioms PolytopeHam.rd_adj_iff
#print axioms PolytopeHam.RD_not_hamiltonian
#print axioms PolytopeHam.exists_nonHamiltonian_3polytope
#print axioms PolytopeHam.conjecture_00000007145_false
#print axioms PolytopeHam.conjecture_00000007145_false'
#print axioms PolytopeHam.exists_nonHamiltonian_4polytope
#print axioms PolytopeHam.Oct_hamiltonian
