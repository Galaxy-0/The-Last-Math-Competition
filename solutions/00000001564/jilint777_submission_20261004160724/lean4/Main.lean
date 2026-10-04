/-!
# Conjecture 00000001564: minimal vertex number of cs-neighborly polytopes

The conjecture: "A cs-neighborly polytope is centrally symmetric and has support
points in every direction.  Conjecture: the minimal number of vertices of a
k-dimensional cs-neighborly polytope is 2^{k+1}; and the extremal bodies are
the Hanner polytopes."

We refute the first clause.  The k-dimensional cross-polytope
`conv {±e₁, …, ±e_k}` has only `2k < 2^{k+1}` vertices, is centrally symmetric,
satisfies the statement's own definition, and is cs-neighborly in the strongest
possible (Grünbaum) sense: *every* set of its vertices that contains no
antipodal pair is the vertex set of a face.  We check this for k = 1, 2, 3, 4.

## Model

* A point of `ℤ^k` is a list of `k` integers (`Pt`); `dot` is the scalar product.
* A polytope is given by its list of vertices `V` (`conv V`).  `ConvexPosition V`
  says that the list has no repetitions and every listed point is a vertex of
  `conv V`, i.e. the unique maximizer over `V` of some linear functional
  (an exposed point).  Then `conv V` has exactly `V.length` vertices.
* `S ⊆ V` is the vertex set of a face of `conv V` iff `S` is exactly the set of
  maximizers over `V` of some linear functional (`IsFace`).
* `FullDim k V` is a certificate that the affine hull of `V` is `k`-dimensional:
  points `a, b₁, …, b_k ∈ V` and functionals `f₁, …, f_k` with
  `fᵢ(b_j − a) ≠ 0 ↔ i = j`.  `fullDim_linIndep` proves that the vectors
  `b_j − a` are then linearly independent (over `ℤ`; the same argument works
  verbatim over `ℝ`).

All witnesses are integral; integral functionals are in particular real
functionals, so every predicate below implies its real-coefficient analogue.
Restricting the universally quantified conjecture to lattice polytopes only
weakens it, so refuting the restriction refutes the conjecture.
-/

namespace CsNeighborly

/-- A point of `ℤ^k`, as a list of coordinates. -/
abbrev Pt := List Int

/-- Scalar product. -/
def dot : Pt → Pt → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

def neg (p : Pt) : Pt := p.map (fun x => -x)
def add (p q : Pt) : Pt := List.zipWith (· + ·) p q
def sub (p q : Pt) : Pt := List.zipWith (· - ·) p q
def smul (t : Int) (p : Pt) : Pt := p.map (fun x => t * x)
def zero (k : Nat) : Pt := List.replicate k 0

/-- Sum of a list of points of `ℤ^k`. -/
def vsum (k : Nat) : List Pt → Pt
  | [] => zero k
  | p :: ps => add p (vsum k ps)

/-- Linear combination `Σ λⱼ pⱼ` in `ℤ^k`. -/
def combo (k : Nat) : List Int → List Pt → Pt
  | l :: ls, p :: ps => add (smul l p) (combo k ls ps)
  | _, _ => zero k

/-! ## Polytopes, vertices, faces -/

/-- `v` is a vertex of `conv V`: the unique maximizer over `V` of a functional. -/
def IsVertex (V : List Pt) (v : Pt) : Prop :=
  v ∈ V ∧ ∃ c : Pt, ∀ q ∈ V, q ≠ v → dot c q < dot c v

/-- `V` is the vertex list of `conv V`; then `conv V` has `V.length` vertices. -/
def ConvexPosition (V : List Pt) : Prop :=
  V.Nodup ∧ ∀ v ∈ V, IsVertex V v

/-- `S` is the vertex set of a (nonempty, exposed) face of `conv V`: the set of
maximizers over `V` of some functional `c` with maximum value `m` is exactly `S`. -/
def IsFace (V S : List Pt) : Prop :=
  S ≠ [] ∧ (∀ s ∈ S, s ∈ V) ∧
    ∃ c : Pt, ∃ m : Int, ∀ q ∈ V, dot c q ≤ m ∧ (q ∈ S ↔ dot c q = m)

/-- Central symmetry (about the origin). -/
def CentSymm (V : List Pt) : Prop := ∀ v ∈ V, neg v ∈ V

/-- No two points of `S` are antipodal. -/
def NoAntipodal (S : List Pt) : Prop := ∀ u ∈ S, ∀ v ∈ S, u ≠ neg v

/-- Affine dimension `≥ k` certificate (see module doc and `fullDim_linIndep`). -/
def FullDim (k : Nat) (V : List Pt) : Prop :=
  ∃ a : Pt, ∃ B F : List Pt, a ∈ V ∧ (∀ b ∈ B, b ∈ V) ∧ B.length = k ∧ F.length = k ∧
    ∀ i, i < k → ∀ j, j < k →
      (dot (F.getD i []) (sub (B.getD j []) a) ≠ 0 ↔ i = j)

/-- A `k`-dimensional polytope in `ℝ^k` with integral vertex list `V`. -/
def IsPolytopeOfDim (k : Nat) (V : List Pt) : Prop :=
  V ≠ [] ∧ (∀ v ∈ V, v.length = k) ∧ ConvexPosition V ∧ FullDim k V

/-! ## Notions of cs-neighborliness -/

/-- The statement's own definition: centrally symmetric, with a support point
(a point of `V` maximizing the functional) in every direction `c`. -/
def StatementCsNeighborly (V : List Pt) : Prop :=
  CentSymm V ∧ ∀ c : Pt, ∃ v ∈ V, ∀ q ∈ V, dot c q ≤ dot c v

/-- Grünbaum's cs-`j`-neighborliness: every set of at most `j` vertices with no
antipodal pair is the vertex set of a face.  (`j = 2`: any two non-antipodal
vertices span an edge.) -/
def CsNeighborlyUpTo (j : Nat) (V : List Pt) : Prop :=
  CentSymm V ∧ ∀ S : List Pt, S ≠ [] → (∀ s ∈ S, s ∈ V) → S.length ≤ j →
    NoAntipodal S → IsFace V S

/-- The strongest form: every nonempty set of vertices with no antipodal pair is
the vertex set of a face. -/
def CsNeighborlyFull (V : List Pt) : Prop :=
  CentSymm V ∧ ∀ S : List Pt, S ≠ [] → (∀ s ∈ S, s ∈ V) → NoAntipodal S → IsFace V S

theorem full_upTo {V : List Pt} (h : CsNeighborlyFull V) (j : Nat) :
    CsNeighborlyUpTo j V :=
  ⟨h.1, fun S hS hsub _ hna => h.2 S hS hsub hna⟩

/-- Every nonempty finite point set has a support point in every direction. -/
theorem support_exists : ∀ (V : List Pt), V ≠ [] → ∀ c : Pt,
    ∃ v ∈ V, ∀ q ∈ V, dot c q ≤ dot c v
  | [], h, _ => absurd rfl h
  | [p], _, c => ⟨p, by simp, fun q hq => by simp at hq; subst hq; exact Int.le_refl _⟩
  | p :: p' :: ps, _, c => by
    obtain ⟨v, hv, hmax⟩ := support_exists (p' :: ps) (by simp) c
    by_cases hle : dot c p ≤ dot c v
    · refine ⟨v, List.mem_cons_of_mem _ hv, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hle
      · exact hmax q hq
    · refine ⟨p, List.mem_cons_self .., fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Int.le_refl _
      · have := hmax q hq; omega

/-- The statement's own "definition" is satisfied by every nonempty centrally
symmetric polytope. -/
theorem statement_def_of_cs {V : List Pt} (hne : V ≠ []) (hcs : CentSymm V) :
    StatementCsNeighborly V :=
  ⟨hcs, support_exists V hne⟩

/-! ## Decidable checks with explicit witnesses -/

/-- All sublists of a list (one for each subset of positions). -/
def subs {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (subs xs).map (x :: ·) ++ subs xs

theorem filter_mem_subs {α : Type} (p : α → Bool) : ∀ V : List α, V.filter p ∈ subs V
  | [] => by simp [subs]
  | x :: xs => by
    have ih := filter_mem_subs p xs
    by_cases hx : p x = true
    · simp only [List.filter_cons, hx, if_true, subs]
      exact List.mem_append_left _ (List.mem_map_of_mem ih)
    · simp only [List.filter_cons, hx, subs]
      exact List.mem_append_right _ ih

theorem getD_of_lt {α : Type} (l : List α) (d : α) (i : Nat) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The maximizer set of `c` over `V` is exactly `S` (value `dot c s₀`). -/
def faceCheck (V S : List Pt) (c : Pt) : Prop :=
  ∀ q ∈ V, dot c q ≤ dot c (S.headD []) ∧ (q ∈ S ↔ dot c q = dot c (S.headD []))

instance (V S : List Pt) (c : Pt) : Decidable (faceCheck V S c) := by
  unfold faceCheck; infer_instance

instance (S : List Pt) : Decidable (NoAntipodal S) := by
  unfold NoAntipodal; infer_instance

theorem isFace_of_check {V S : List Pt} (c : Pt) (hS : S ≠ []) (hsub : ∀ s ∈ S, s ∈ V)
    (h : faceCheck V S c) : IsFace V S :=
  ⟨hS, hsub, c, _, h⟩

/-- Faces depend only on the membership predicate of `S`, so it suffices to check
the sublists of `V` (one per subset of the vertex set). -/
theorem full_of_sublists (k : Nat) (V : List Pt) (hcs : CentSymm V)
    (h : ∀ S ∈ subs V, S ≠ [] → NoAntipodal S → faceCheck V S (vsum k S)) :
    CsNeighborlyFull V := by
  refine ⟨hcs, fun S hS hsub hna => ?_⟩
  let S' := V.filter (fun q => decide (q ∈ S))
  have hmem : ∀ q, q ∈ S' ↔ q ∈ S := by
    intro q; simp only [S', List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hsub q h, h⟩⟩
  have hS' : S' ≠ [] := by
    intro h0
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil S hS
    have := (hmem s).2 hs
    rw [h0] at this; simp at this
  have hna' : NoAntipodal S' := fun u hu v hv => hna u ((hmem u).1 hu) v ((hmem v).1 hv)
  have hsl : S' ∈ subs V := filter_mem_subs _ V
  obtain ⟨_, _, c, m, hc⟩ :=
    isFace_of_check (V := V) (S := S') _ hS' (fun s hs => hsub s ((hmem s).1 hs))
      (h S' hsl hS' hna')
  exact ⟨hS, hsub, c, m, fun q hq => ⟨(hc q hq).1, (hmem q).symm.trans (hc q hq).2⟩⟩

/-- Vertex check with the functional `c = v` itself. -/
def vertexCheck (V : List Pt) : Prop := ∀ v ∈ V, ∀ q ∈ V, q ≠ v → dot v q < dot v v

instance (V : List Pt) : Decidable (vertexCheck V) := by
  unfold vertexCheck; infer_instance

theorem convexPosition_of_check {V : List Pt} (hnd : V.Nodup) (h : vertexCheck V) :
    ConvexPosition V :=
  ⟨hnd, fun v hv => ⟨hv, v, h v hv⟩⟩

/-- Decidable form of `FullDim` for given witnesses. -/
def fullDimCheck (k : Nat) (V : List Pt) (a : Pt) (B F : List Pt) : Prop :=
  a ∈ V ∧ (∀ b ∈ B, b ∈ V) ∧ B.length = k ∧ F.length = k ∧
    ∀ i, i < k → ∀ j, j < k → (dot (F.getD i []) (sub (B.getD j []) a) ≠ 0 ↔ i = j)

instance (k : Nat) (V : List Pt) (a : Pt) (B F : List Pt) :
    Decidable (fullDimCheck k V a B F) := by
  unfold fullDimCheck; infer_instance

theorem fullDim_of_check {k V a B F} (h : fullDimCheck k V a B F) : FullDim k V :=
  ⟨a, B, F, h⟩

/-! ## The cross-polytope -/

/-- The unit vector `e_i` of `ℤ^k`. -/
def unit (k i : Nat) : Pt := (List.range k).map (fun j => if j = i then 1 else 0)

/-- Vertex list of the `k`-dimensional cross-polytope: `e₀, −e₀, e₁, −e₁, …`. -/
def cross (k : Nat) : List Pt :=
  (List.range k).flatMap (fun i => [unit k i, neg (unit k i)])

/-- Dimension certificate for the cross-polytope:
`a = −e₀`, `b_j = e_j`, `f₀ = e₀ − e₁ − ⋯ − e_{k−1}`, `f_i = e_i` for `i ≥ 1`. -/
def crossA (k : Nat) : Pt := neg (unit k 0)
def crossB (k : Nat) : List Pt := (List.range k).map (unit k)
def crossF (k : Nat) : List Pt :=
  (List.range k).map (fun i =>
    if i = 0 then (List.range k).map (fun j => if j = 0 then 1 else -1) else unit k i)

example : cross 3 = [[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]] := by decide

/-- All facts about the cross-polytope of dimension `k`, as one decidable bundle. -/
def CrossFacts (k : Nat) : Prop :=
  (cross k).length = 2 * k ∧ (cross k).Nodup ∧ (∀ v ∈ cross k, v.length = k) ∧
    CentSymm (cross k) ∧ vertexCheck (cross k) ∧
    fullDimCheck k (cross k) (crossA k) (crossB k) (crossF k) ∧
    ∀ S ∈ subs (cross k), S ≠ [] → NoAntipodal S → faceCheck (cross k) S (vsum k S)

instance (k : Nat) : Decidable (CentSymm (cross k)) := by unfold CentSymm; infer_instance
instance (k : Nat) : Decidable (CrossFacts k) := by unfold CrossFacts; infer_instance

theorem crossFacts_1 : CrossFacts 1 := by decide
theorem crossFacts_2 : CrossFacts 2 := by decide
theorem crossFacts_3 : CrossFacts 3 := by decide
set_option maxRecDepth 10000 in
theorem crossFacts_4 : CrossFacts 4 := by decide +kernel

/-- From the decidable bundle to the mathematical statements. -/
theorem cross_props {k : Nat} (hk : 1 ≤ k) (h : CrossFacts k) :
    IsPolytopeOfDim k (cross k) ∧ CentSymm (cross k) ∧ CsNeighborlyFull (cross k) ∧
      StatementCsNeighborly (cross k) ∧ (cross k).length = 2 * k := by
  obtain ⟨hlen, hnd, hl, hcs, hv, hfd, hf⟩ := h
  have hne : cross k ≠ [] := by
    intro h0; rw [h0] at hlen; simp at hlen; omega
  exact ⟨⟨hne, hl, convexPosition_of_check hnd hv, fullDim_of_check hfd⟩, hcs,
    full_of_sublists k _ hcs hf, statement_def_of_cs hne hcs, hlen⟩

/-! ## The conjecture -/

/-- "The minimal number of vertices of a `k`-dimensional polytope that is
centrally symmetric and `N`-neighborly is `n`": it is attained, and it is a
lower bound.  (For `V` in convex position, `conv V` has `V.length` vertices.) -/
def MinVerticesIs (N : List Pt → Prop) (k n : Nat) : Prop :=
  (∃ V, IsPolytopeOfDim k V ∧ CentSymm V ∧ N V ∧ V.length = n) ∧
    ∀ V, IsPolytopeOfDim k V → CentSymm V → N V → n ≤ V.length

/-- The first clause of the conjecture, for a notion `N` of cs-neighborliness. -/
def MinClause (N : List Pt → Prop) : Prop := ∀ k, 1 ≤ k → MinVerticesIs N k (2 ^ (k + 1))

/-- Even the bare lower-bound half of the clause fails, for every `k = 1,2,3,4`
and every notion `N` that the cross-polytope satisfies. -/
theorem not_min_at {N : List Pt → Prop} {k : Nat} (hk : 1 ≤ k) (h : CrossFacts k)
    (hN : N (cross k)) (hlt : 2 * k < 2 ^ (k + 1)) : ¬ MinVerticesIs N k (2 ^ (k + 1)) := by
  intro hmin
  obtain ⟨hP, hcs, _, _, hlen⟩ := cross_props hk h
  have := hmin.2 _ hP hcs hN
  omega

theorem fails_k1 {N : List Pt → Prop} (hN : N (cross 1)) : ¬ MinVerticesIs N 1 4 :=
  not_min_at (by decide) crossFacts_1 hN (by decide)
theorem fails_k2 {N : List Pt → Prop} (hN : N (cross 2)) : ¬ MinVerticesIs N 2 8 :=
  not_min_at (by decide) crossFacts_2 hN (by decide)
theorem fails_k3 {N : List Pt → Prop} (hN : N (cross 3)) : ¬ MinVerticesIs N 3 16 :=
  not_min_at (by decide) crossFacts_3 hN (by decide)
theorem fails_k4 {N : List Pt → Prop} (hN : N (cross 4)) : ¬ MinVerticesIs N 4 32 :=
  not_min_at (by decide) crossFacts_4 hN (by decide)

/-- The k-cross-polytope (k = 1..4) satisfies every reading of cs-neighborly. -/
theorem cross_all_readings (k : Nat) (hk : 1 ≤ k) (h : CrossFacts k) :
    StatementCsNeighborly (cross k) ∧ CsNeighborlyFull (cross k) ∧
      ∀ j, CsNeighborlyUpTo j (cross k) := by
  obtain ⟨_, _, hfull, hst, _⟩ := cross_props hk h
  exact ⟨hst, hfull, full_upTo hfull⟩

/-- **Main theorem (statement's own definition).** -/
theorem conjecture_00000001564_false : ¬ MinClause StatementCsNeighborly :=
  fun h => fails_k3 (cross_props (by decide) crossFacts_3).2.2.2.1 (h 3 (by decide))

/-- **Main theorem (Grünbaum's cs-neighborliness, every neighborliness level `j`,
including `j = 2`: non-antipodal vertices are adjacent).** -/
theorem conjecture_00000001564_false_grunbaum (j : Nat) :
    ¬ MinClause (CsNeighborlyUpTo j) :=
  fun h => fails_k3 ((cross_all_readings 3 (by decide) crossFacts_3).2.2 j) (h 3 (by decide))

/-- **Main theorem (strongest cs-neighborliness).** -/
theorem conjecture_00000001564_false_full : ¬ MinClause CsNeighborlyFull :=
  fun h => fails_k3 (cross_props (by decide) crossFacts_3).2.2.1 (h 3 (by decide))

/-- The clause fails at each of `k = 1, 2, 3, 4` separately, under every reading. -/
theorem fails_each_k :
    (¬ MinVerticesIs StatementCsNeighborly 1 4 ∧ ¬ MinVerticesIs CsNeighborlyFull 1 4) ∧
    (¬ MinVerticesIs StatementCsNeighborly 2 8 ∧ ¬ MinVerticesIs CsNeighborlyFull 2 8) ∧
    (¬ MinVerticesIs StatementCsNeighborly 3 16 ∧ ¬ MinVerticesIs CsNeighborlyFull 3 16) ∧
    (¬ MinVerticesIs StatementCsNeighborly 4 32 ∧ ¬ MinVerticesIs CsNeighborlyFull 4 32) :=
  ⟨⟨fails_k1 (cross_props (by decide) crossFacts_1).2.2.2.1,
      fails_k1 (cross_props (by decide) crossFacts_1).2.2.1⟩,
    ⟨fails_k2 (cross_props (by decide) crossFacts_2).2.2.2.1,
      fails_k2 (cross_props (by decide) crossFacts_2).2.2.1⟩,
    ⟨fails_k3 (cross_props (by decide) crossFacts_3).2.2.2.1,
      fails_k3 (cross_props (by decide) crossFacts_3).2.2.1⟩,
    ⟨fails_k4 (cross_props (by decide) crossFacts_4).2.2.2.1,
      fails_k4 (cross_props (by decide) crossFacts_4).2.2.1⟩⟩

/-- Reading with `k` as the neighborliness parameter (cs-`k`-neighborly polytopes of
any dimension `d`): the octahedron is cs-3-neighborly with 6 < 2^4 vertices. -/
theorem conjecture_00000001564_false_param :
    ¬ ∀ k, 1 ≤ k → ∀ d V, IsPolytopeOfDim d V → CsNeighborlyUpTo k V →
      2 ^ (k + 1) ≤ V.length := by
  intro h
  obtain ⟨hP, _, hfull, _, hlen⟩ := cross_props (by decide) crossFacts_3
  have := h 3 (by decide) 3 _ hP (full_upTo hfull 3)
  omega

/-- The same for *any* notion `N` of cs-neighborliness that the octahedron satisfies. -/
theorem conjecture_00000001564_false_any (N : List Pt → Prop) (hN : N (cross 3)) :
    ¬ MinClause N :=
  fun h => fails_k3 hN (h 3 (by decide))

/-- The conjecture is a conjunction with a second clause about Hanner polytopes;
whatever that clause is, the conjunction is false. -/
theorem conjecture_00000001564_conjunction_false (Hanner : Prop) :
    ¬ (MinClause StatementCsNeighborly ∧ Hanner) ∧
    ¬ (MinClause CsNeighborlyFull ∧ Hanner) ∧
    ∀ j, ¬ (MinClause (CsNeighborlyUpTo j) ∧ Hanner) :=
  ⟨fun h => conjecture_00000001564_false h.1, fun h => conjecture_00000001564_false_full h.1,
    fun j h => conjecture_00000001564_false_grunbaum j h.1⟩

/-! ## The dimension certificate is sound -/

theorem dot_add : ∀ (f p q : Pt), p.length = q.length →
    dot f (add p q) = dot f p + dot f q
  | [], _, _, _ => by simp [dot]
  | _ :: _, [], [], _ => rfl
  | a :: f, b :: p, c :: q, h1 => by
    have ih := dot_add f p q (by simpa using h1)
    simp only [add, List.zipWith_cons_cons, dot] at *
    rw [ih, Int.mul_add]; omega
  | _ :: _, [], _ :: _, h1 => by simp at h1
  | _ :: _, _ :: _, [], h1 => by simp at h1

theorem dot_smul : ∀ (f p : Pt) (t : Int), dot f (smul t p) = t * dot f p
  | [], _, _ => by simp [dot]
  | _ :: _, [], _ => by simp [dot, smul]
  | a :: f, b :: p, t => by
    have := dot_smul f p t
    simp only [smul, List.map_cons, dot] at *
    rw [this, Int.mul_add, Int.mul_left_comm]

theorem dot_zero : ∀ (f : Pt) (k : Nat), dot f (zero k) = 0
  | [], _ => by simp [dot]
  | _ :: _, 0 => rfl
  | a :: f, k + 1 => by
    simp only [zero, List.replicate_succ, dot]; rw [← zero, dot_zero f k]; simp

theorem length_smul (t : Int) (p : Pt) : (smul t p).length = p.length := by simp [smul]

theorem length_combo (k : Nat) : ∀ (l : List Int) (P : List Pt), (∀ p ∈ P, p.length = k) →
    (combo k l P).length = k
  | [], _, _ => by simp [combo, zero]
  | _ :: _, [], _ => by simp [combo, zero]
  | t :: l, p :: P, h => by
    simp only [combo, add, List.length_zipWith, length_smul]
    rw [length_combo k l P (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      h p (List.mem_cons_self ..)]
    simp

/-- `f(Σ λⱼ pⱼ) = Σ λⱼ f(pⱼ)`. -/
theorem dot_combo (k : Nat) (f : Pt) :
    ∀ (l : List Int) (P : List Pt), (∀ p ∈ P, p.length = k) →
      dot f (combo k l P) = ((l.zip P).map (fun x => x.1 * dot f x.2)).foldr (· + ·) 0
  | [], _, _ => by simp [combo, dot_zero]
  | _ :: _, [], _ => by simp [combo, dot_zero]
  | t :: l, p :: P, h => by
    have hp := h p (List.mem_cons_self ..)
    have hP : ∀ q ∈ P, q.length = k := fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [combo]
    rw [dot_add _ _ _ (by rw [length_smul, hp, length_combo k l P hP]), dot_smul,
      dot_combo k f l P hP]
    simp

theorem foldr_single (g : Nat → Int) : ∀ (n i : Nat), i < n → (∀ j, j < n → j ≠ i → g j = 0) →
    ((List.range n).map g).foldr (· + ·) 0 = g i
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, hi, hz => by
    rw [List.range_succ, List.map_append, List.foldr_append]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Int.add_zero]
    by_cases hin : i = n
    · subst hin
      have : ((List.range i).map g).foldr (· + ·) (g i) =
          ((List.range i).map g).foldr (· + ·) 0 + g i := by
        generalize (List.range i).map g = L
        induction L with
        | nil => simp
        | cons x L ih => simp only [List.foldr_cons, ih]; omega
      rw [this]
      have h0 : ∀ m, m ≤ i → ((List.range m).map g).foldr (· + ·) 0 = 0 := by
        intro m hm
        induction m with
        | zero => simp
        | succ m ih =>
          rw [List.range_succ, List.map_append, List.foldr_append]
          simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            Int.add_zero]
          rw [hz m (by omega) (by omega)]; simpa using ih (by omega)
      rw [h0 i (Nat.le_refl _)]; simp
    · rw [hz n (Nat.lt_succ_self _) (fun h => hin h.symm)]
      exact foldr_single g n i (by omega) (fun j hj hji => hz j (by omega) hji)

/-- Soundness of `FullDim`: the vectors `b_j − a` are linearly independent, i.e.
`Σ λⱼ (b_j − a) = 0` forces every `λᵢ = 0`.  Hence `conv V` has dimension `≥ k`. -/
theorem fullDim_linIndep {k : Nat} (a : Pt) (B F : List Pt) (hB : B.length = k)
    (hF : F.length = k) (hlenB : ∀ b ∈ B, b.length = k) (ha : a.length = k)
    (hbi : ∀ i, i < k → ∀ j, j < k →
      (dot (F.getD i []) (sub (B.getD j []) a) ≠ 0 ↔ i = j))
    (l : List Int) (hl : l.length = k)
    (h0 : combo k l (B.map (fun b => sub b a)) = zero k) :
    ∀ i, i < k → l.getD i 0 = 0 := by
  intro i hi
  have hsub : ∀ p ∈ B.map (fun b => sub b a), p.length = k := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    simp [sub, hlenB b hb, ha]
  have key := dot_combo k (F.getD i []) l _ hsub
  rw [h0, dot_zero] at key
  -- rewrite the sum as a sum over indices
  have hzip : (l.zip (B.map (fun b => sub b a))).map
      (fun x => x.1 * dot (F.getD i []) x.2) =
      (List.range k).map (fun j => l.getD j 0 * dot (F.getD i []) (sub (B.getD j []) a)) := by
    apply List.ext_getElem
    · simp [hl, hB]
    · intro n _ h2
      simp only [List.length_range, List.length_map] at h2
      simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
      rw [getD_of_lt l 0 n (by omega), getD_of_lt B [] n (by omega)]
  rw [hzip, foldr_single _ k i hi] at key
  · have hne := (hbi i hi i hi).2 rfl
    rcases Int.mul_eq_zero.mp key.symm with h | h
    · exact h
    · exact absurd h hne
  · intro j hj hji
    have : dot (F.getD i []) (sub (B.getD j []) a) = 0 := by
      have := (hbi i hi j hj).1
      by_cases hd : dot (F.getD i []) (sub (B.getD j []) a) = 0
      · exact hd
      · exact absurd (this hd) (fun h => hji h.symm)
    rw [this, Int.mul_zero]

/-- `FullDim k V` (with all points in `ℤ^k`) yields `a ∈ V` and `b₁, …, b_k ∈ V`
with `b_j − a` linearly independent: the affine hull of `V` is all of `ℝ^k`. -/
theorem fullDim_sound {k : Nat} {V : List Pt} (hl : ∀ v ∈ V, v.length = k)
    (h : FullDim k V) : ∃ a ∈ V, ∃ B : List Pt, (∀ b ∈ B, b ∈ V) ∧ B.length = k ∧
      ∀ l : List Int, l.length = k → combo k l (B.map (fun b => sub b a)) = zero k →
        ∀ i, i < k → l.getD i 0 = 0 := by
  obtain ⟨a, B, F, ha, hB, hBl, hFl, hbi⟩ := h
  exact ⟨a, ha, B, hB, hBl, fun l hll h0 =>
    fullDim_linIndep a B F hBl hFl (fun b hb => hl b (hB b hb)) (hl a ha) hbi l hll h0⟩

/-! ## Non-vacuity -/

/-- A centrally symmetric hexagon: a cs polygon in convex position, 2-dimensional,
which is NOT cs-neighborly (the non-antipodal vertices (2,1), (−1,1) span no edge;
the vertex (1,2) lies between them). -/
def hexagon : List Pt := [[2,1],[1,2],[-1,1],[-2,-1],[-1,-2],[1,-1]]

theorem hexagon_polytope : IsPolytopeOfDim 2 hexagon ∧ CentSymm hexagon := by
  refine ⟨⟨by decide, by decide, convexPosition_of_check (by decide) (by decide),
    fullDim_of_check (a := [2,1]) (B := [[1,2],[-1,1]]) (F := [[0,1],[1,1]]) (by decide)⟩,
    by unfold CentSymm; decide⟩

theorem hexagon_not_csNeighborly : ¬ CsNeighborlyUpTo 2 hexagon := by
  rintro ⟨_, h⟩
  obtain ⟨_, _, c, m, hc⟩ := h [[2,1],[-1,1]] (by decide) (by decide) (by decide) (by decide)
  have e1 : dot c [2,1] = m := (hc [2,1] (by decide)).2.mp (by decide)
  have e2 : dot c [-1,1] = m := (hc [-1,1] (by decide)).2.mp (by decide)
  have l3 : dot c [1,2] ≤ m := (hc [1,2] (by decide)).1
  have n3 : dot c [1,2] ≠ m := fun h' => absurd ((hc [1,2] (by decide)).2.mpr h') (by decide)
  have l4 : dot c [-2,-1] ≤ m := (hc [-2,-1] (by decide)).1
  have n4 : dot c [-2,-1] ≠ m :=
    fun h' => absurd ((hc [-2,-1] (by decide)).2.mpr h') (by decide)
  rcases c with _ | ⟨x, _ | ⟨y, c⟩⟩ <;> simp [dot] at e1 e2 l3 n3 l4 n4 <;> omega

theorem dot_sub_self : ∀ (f p : Pt), dot f (sub p p) = 0
  | [], _ => by simp [dot]
  | _ :: _, [] => rfl
  | a :: f, x :: p => by
    have := dot_sub_self f p
    simp only [sub, List.zipWith_cons_cons, dot] at *
    rw [this, Int.sub_self, Int.mul_zero, Int.add_zero]

theorem two_le_length {V : List Pt} {a b : Pt} (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) :
    2 ≤ V.length := by
  match V, ha, hb with
  | [], ha, _ => simp at ha
  | [x], ha, hb =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | _ :: _ :: _, _, _ => simp

/-- A *true* instance of `MinVerticesIs`: in dimension 1 the minimum is `2`
(under each reading), so the predicate is not vacuous. -/
theorem true_min_k1 :
    MinVerticesIs StatementCsNeighborly 1 2 ∧ MinVerticesIs CsNeighborlyFull 1 2 := by
  have lb : ∀ V, IsPolytopeOfDim 1 V → 2 ≤ V.length := by
    rintro V ⟨_, _, _, a, B, F, ha, hB, hBl, _, hbi⟩
    have h00 := (hbi 0 (by decide) 0 (by decide)).2 rfl
    have hb0 : B.getD 0 [] ∈ B := by
      rw [getD_of_lt B [] 0 (by omega)]; exact List.getElem_mem _
    refine two_le_length (hB _ hb0) ha (fun he => h00 ?_)
    rw [he, dot_sub_self]
  obtain ⟨hP, hcs, hfull, hst, hlen⟩ := cross_props (by decide) crossFacts_1
  exact ⟨⟨⟨cross 1, hP, hcs, hst, hlen⟩, fun V hV _ _ => lb V hV⟩,
    ⟨⟨cross 1, hP, hcs, hfull, hlen⟩, fun V hV _ _ => lb V hV⟩⟩

/-- The hexagon satisfies the statement's own definition but not Grünbaum's:
the two notions really differ. -/
theorem hexagon_statement_def : StatementCsNeighborly hexagon :=
  statement_def_of_cs (by decide) hexagon_polytope.2

/-- A point set NOT in convex position (an interior point). -/
theorem not_convexPosition : ¬ ConvexPosition [[1,0],[-1,0],[0,0]] := by
  rintro ⟨_, h⟩
  obtain ⟨_, c, hc⟩ := h [0,0] (by decide)
  have h1 := hc [1,0] (by decide) (by decide)
  have h2 := hc [-1,0] (by decide) (by decide)
  rcases c with _ | ⟨x, c⟩
  · simp [dot] at h1
  · rcases c with _ | ⟨y, c⟩ <;> simp [dot] at h1 h2 <;> omega

/-! ## Hanner polytopes: vertex counts (combinatorial shadow)

Hanner polytopes are generated from the segment `[−1,1]` by Cartesian products
(vertex numbers multiply, dimensions add) and free sums (vertex numbers add,
dimensions add).  `HannerCount d v` records the pairs (dimension, vertex number)
that arise.  We show `2d ≤ v ≤ 2^d`; in particular no Hanner polytope has
`2^{d+1}` vertices, so the two clauses of the conjecture are incompatible. -/

inductive HannerCount : Nat → Nat → Prop
  | segment : HannerCount 1 2
  | prod {d₁ v₁ d₂ v₂} : HannerCount d₁ v₁ → HannerCount d₂ v₂ → HannerCount (d₁ + d₂) (v₁ * v₂)
  | sum {d₁ v₁ d₂ v₂} : HannerCount d₁ v₁ → HannerCount d₂ v₂ → HannerCount (d₁ + d₂) (v₁ + v₂)

theorem hanner_bounds {d v : Nat} (h : HannerCount d v) : 1 ≤ d ∧ 2 * d ≤ v ∧ v ≤ 2 ^ d := by
  induction h with
  | segment => decide
  | @prod d₁ v₁ d₂ v₂ _ _ ih₁ ih₂ =>
    obtain ⟨a1, b1, c1⟩ := ih₁
    obtain ⟨a2, b2, c2⟩ := ih₂
    refine ⟨by omega, ?_, ?_⟩
    · have m1 : d₁ * 1 ≤ d₁ * d₂ := Nat.mul_le_mul_left d₁ a2
      have m2 : 1 * d₂ ≤ d₁ * d₂ := Nat.mul_le_mul_right d₂ a1
      have hm : 2 * d₁ * (2 * d₂) = (2 * 2) * (d₁ * d₂) := Nat.mul_mul_mul_comm 2 d₁ 2 d₂
      have hb : 2 * d₁ * (2 * d₂) ≤ v₁ * v₂ := Nat.mul_le_mul b1 b2
      rw [hm] at hb
      simp only [Nat.mul_one, Nat.one_mul] at m1 m2
      generalize d₁ * d₂ = t at *
      generalize v₁ * v₂ = w at *
      omega
    · rw [Nat.pow_add]; exact Nat.mul_le_mul c1 c2
  | @sum d₁ v₁ d₂ v₂ _ _ ih₁ ih₂ =>
    obtain ⟨a1, b1, c1⟩ := ih₁
    obtain ⟨a2, b2, c2⟩ := ih₂
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.pow_add]
    have p1 : 2 ≤ 2 ^ d₁ := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) a1; simpa using this
    have p2 : 2 ≤ 2 ^ d₂ := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) a2; simpa using this
    -- x + y ≤ x * y for x, y ≥ 2
    have : 2 ^ d₁ + 2 ^ d₂ ≤ 2 ^ d₁ * 2 ^ d₂ := by
      generalize 2 ^ d₁ = x at p1 ⊢
      generalize 2 ^ d₂ = y at p2 ⊢
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 2 := ⟨x - 2, by omega⟩
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 2 := ⟨y - 2, by omega⟩
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      omega
    omega

theorem no_hanner_with_2pow_succ {d v : Nat} (h : HannerCount d v) : v ≠ 2 ^ (d + 1) := by
  have ⟨_, _, h3⟩ := hanner_bounds h
  have : 2 ^ d < 2 ^ (d + 1) := Nat.pow_lt_pow_succ (by decide)
  omega

/-- The cube (`d` products of segments) and the cross-polytope (`d` free sums)
are Hanner, with `2^d` and `2d` vertices; e.g. in dimension 3: 8 and 6. -/
theorem cube3 : HannerCount 3 8 := .prod (.prod .segment .segment) .segment
theorem cross3 : HannerCount 3 6 := .sum (.sum .segment .segment) .segment

end CsNeighborly

#print axioms CsNeighborly.crossFacts_3
#print axioms CsNeighborly.crossFacts_4
#print axioms CsNeighborly.cross_props
#print axioms CsNeighborly.conjecture_00000001564_false
#print axioms CsNeighborly.conjecture_00000001564_false_grunbaum
#print axioms CsNeighborly.conjecture_00000001564_false_full
#print axioms CsNeighborly.conjecture_00000001564_false_param
#print axioms CsNeighborly.conjecture_00000001564_conjunction_false
#print axioms CsNeighborly.fails_each_k
#print axioms CsNeighborly.fullDim_linIndep
#print axioms CsNeighborly.fullDim_sound
#print axioms CsNeighborly.hexagon_not_csNeighborly
#print axioms CsNeighborly.true_min_k1
#print axioms CsNeighborly.conjecture_00000001564_false_any
#print axioms CsNeighborly.not_convexPosition
#print axioms CsNeighborly.hanner_bounds
#print axioms CsNeighborly.no_hanner_with_2pow_succ
