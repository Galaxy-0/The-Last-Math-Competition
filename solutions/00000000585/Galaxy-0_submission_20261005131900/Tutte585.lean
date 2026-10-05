import Std

/-!
Conjecture 00000000585. Finite undirected multigraphs, including loops.
The Tutte polynomial is defined by its standard rank-subset expansion.
`Connected` is genuine undirected graph connectivity; rank is |V|-components.
A finite cut algorithm decides genuine graph connectivity; its correctness
is proved. Classical reasoning appears in that proof, not in the algorithm.
No axiom, sorry, graph-rank oracle, or positivity assumption is introduced.
-/
namespace Tutte585

abbrev Edge (n : Nat) := Fin n × Fin n

structure Graph where
  vertexCount : Nat
  edges : List (Edge vertexCount)

/-- List positions label edges, so parallel edges remain distinct. -/
inductive Connected {n : Nat} (es : List (Edge n)) : Fin n → Fin n → Prop
  | refl (v) : Connected es v v
  | edge {u v} : (u, v) ∈ es → Connected es u v
  | symm {u v} : Connected es u v → Connected es v u
  | trans {u v w} : Connected es u v → Connected es v w → Connected es u w

theorem connected_nil_iff {n : Nat} {u v : Fin n} :
    Connected ([] : List (Edge n)) u v ↔ u = v := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | edge h => simp at h
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    subst v
    exact Connected.refl u

/-- Enumerate all positional subsets of a list. -/
def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as => subsets as ++ (subsets as).map (fun s => a :: s)

theorem filter_mem_subsets {α : Type} (xs : List α) (p : α → Bool) :
    xs.filter p ∈ subsets xs := by
  induction xs with
  | nil => simp [subsets]
  | cons a as ih =>
    cases hp : p a <;> simp [hp, subsets, ih]

/-- A finite cut test. Closure means an edge cannot cross the cut. -/
def CutConnected {n : Nat} (es : List (Edge n)) (u v : Fin n) : Prop :=
  ∀ s ∈ subsets (List.finRange n),
    (∀ e ∈ es, (e.1 ∈ s ↔ e.2 ∈ s)) → (u ∈ s → v ∈ s)

instance {n : Nat} (es : List (Edge n)) (u v : Fin n) :
    Decidable (CutConnected es u v) := by
  unfold CutConnected
  infer_instance

theorem connected_preserves_cut {n : Nat} {es : List (Edge n)}
    {u v : Fin n} (s : List (Fin n))
    (hs : ∀ e ∈ es, (e.1 ∈ s ↔ e.2 ∈ s)) (h : Connected es u v) :
    u ∈ s ↔ v ∈ s := by
  induction h with
  | refl => exact Iff.rfl
  | edge he => exact hs _ he
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The finite cut algorithm decides the actual inductively defined relation. -/
theorem connected_iff_cut {n : Nat} (es : List (Edge n)) (u v : Fin n) :
    Connected es u v ↔ CutConnected es u v := by
  constructor
  · intro h s _ hs hu
    exact (connected_preserves_cut s hs h).mp hu
  · intro h
    classical
    let s := (List.finRange n).filter (fun w => decide (Connected es u w))
    have mem_s (w : Fin n) : w ∈ s ↔ Connected es u w := by
      simp [s]
    have hs : s ∈ subsets (List.finRange n) := filter_mem_subsets _ _
    have closed : ∀ e ∈ es, (e.1 ∈ s ↔ e.2 ∈ s) := by
      intro e he
      rw [mem_s, mem_s]
      constructor
      · intro hu
        exact Connected.trans hu (Connected.edge he)
      · intro hv
        exact Connected.trans hv (Connected.symm (Connected.edge he))
    exact (mem_s v).mp (h s hs closed ((mem_s u).mpr (Connected.refl u)))

instance {n : Nat} (es : List (Edge n)) (u v : Fin n) :
    Decidable (Connected es u v) :=
  decidable_of_iff (CutConnected es u v) (connected_iff_cut es u v).symm

/-- Each connected component contributes its unique least vertex. -/
def componentCount {n : Nat} (es : List (Edge n)) : Nat := by
  exact ((List.finRange n).filter fun v =>
    decide (∀ w : Fin n, Connected es v w → v.val ≤ w.val)).length

/-- Standard graphic rank, including isolated vertices in the component count. -/
def rank {n : Nat} (es : List (Edge n)) : Nat :=
  n - componentCount es

theorem componentCount_nil (n : Nat) :
    componentCount ([] : List (Edge n)) = n := by
  simp only [componentCount, connected_nil_iff]
  have hfilter : (List.finRange n).filter (fun _ => true) = List.finRange n :=
    List.filter_eq_self.mpr (by simp)
  simpa using congrArg List.length hfilter

theorem rank_nil (n : Nat) : rank ([] : List (Edge n)) = 0 := by
  simp [rank, componentCount_nil]

/-- Sum over all positional edge subsets, without identifying parallel edges. -/
def subsetSum {α : Type} (f : List α → Nat) : List α → Nat
  | [] => f []
  | e :: es => subsetSum f es + subsetSum (fun a => f (e :: a)) es

theorem empty_term_le {α : Type} (es : List α) (f : List α → Nat) :
    f [] ≤ subsetSum f es := by
  induction es generalizing f with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
    exact Nat.le_trans (ih f) (Nat.le_add_right _ _)

/-- The standard Tutte rank expansion evaluated at natural x,y >= 1.
For smaller inputs this natural-valued definition is not asserted to agree
with the integer polynomial. Only x=q+1,y=q-1 with q>=2 is used below. -/
def tutte (G : Graph) (x y : Nat) : Nat :=
  subsetSum (fun a =>
    (x - 1) ^ (rank G.edges - rank a) *
    (y - 1) ^ (a.length - rank a)) G.edges

theorem positive_power (q k : Nat) (hq : 0 < q) : 0 < q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simpa [Nat.pow_succ] using Nat.mul_pos ih hq

/-- Stronger than the prime-power assertion: every integer q >= 2 works. -/
theorem tutte_lower_bound (G : Graph) (q : Nat) :
    q ^ rank G.edges ≤ tutte G (q + 1) (q - 1) := by
  have h := empty_term_le G.edges (fun a =>
    ((q + 1) - 1) ^ (rank G.edges - rank a) *
    ((q - 1) - 1) ^ (a.length - rank a))
  simpa [tutte, rank_nil] using h

theorem tutte_positive (G : Graph) (q : Nat) (hq : 2 ≤ q) :
    0 < tutte G (q + 1) (q - 1) := by
  have hq' : 0 < q := by omega
  exact Nat.lt_of_lt_of_le (positive_power q _ hq') (tutte_lower_bound G q)

/-- Explicit rectangle of color-word codes, with no repetitions. -/
def rectangle : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | a + 1, b => rectangle a b ++ (List.range b).map (fun j => (a, j))

theorem rectangle_length (a b : Nat) : (rectangle a b).length = a * b := by
  induction a with
  | zero => simp [rectangle]
  | succ a ih => simp [rectangle, ih, Nat.succ_mul]

/-- Enumerate each selected edge subset with its Boolean positional mask,
and then enumerate its decorations. The mask distinguishes parallel edges. -/
def enumerate {α β : Type} (f : List α → List β) :
    List α → List (List Bool × β)
  | [] => (f []).map (fun b => ([], b))
  | e :: es =>
      (enumerate f es).map (fun z => (false :: z.1, z.2)) ++
      (enumerate (fun a => f (e :: a)) es).map
        (fun z => (true :: z.1, z.2))

theorem enumerate_length {α β : Type} (es : List α) (f : List α → List β) :
    (enumerate f es).length = subsetSum (fun a => (f a).length) es := by
  induction es generalizing f with
  | nil => simp [enumerate, subsetSum]
  | cons e es ih => simp [enumerate, subsetSum, ih]

/-- A rectangle code is in its exact two finite bounds. -/
theorem mem_rectangle (a b i j : Nat) :
    (i, j) ∈ rectangle a b ↔ i < a ∧ j < b := by
  induction a with
  | zero => simp [rectangle]
  | succ a ih =>
    simp only [rectangle, List.mem_append, ih, List.mem_map, List.mem_range,
      Prod.mk.injEq]
    constructor
    · intro h
      rcases h with h | ⟨k, hk, hki, hkj⟩
      · omega
      · omega
    · intro h
      by_cases hi : i < a
      · exact Or.inl ⟨hi, h.2⟩
      · right
        refine ⟨j, h.2, ?_, rfl⟩
        omega

theorem nodup_map_injective {α β : Type} (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) {xs : List α}
    (hx : xs.Nodup) : (xs.map f).Nodup := by
  apply List.pairwise_map.mpr
  exact hx.imp (fun {a b} hab heq => hab (hf a b heq))

/-- Distinct positions in the rectangle encode distinct pairs. -/
theorem rectangle_nodup (a b : Nat) : (rectangle a b).Nodup := by
  induction a with
  | zero => simp [rectangle]
  | succ a ih =>
    apply List.nodup_append.mpr
    refine ⟨ih, ?_, ?_⟩
    · exact nodup_map_injective _ (by
        intro i j h
        exact (Prod.mk.inj h).2) (List.nodup_range (n := b))
    · intro z hz w hw hzw
      subst w
      obtain ⟨i, hi, hzi⟩ := List.mem_map.mp hw
      subst z
      have h := (mem_rectangle a b a i).mp hz
      omega

/-- Positional masks make different branches disjoint. -/
theorem enumerate_nodup {α β : Type} (es : List α) (f : List α → List β)
    (hf : ∀ a, (f a).Nodup) : (enumerate f es).Nodup := by
  induction es generalizing f with
  | nil =>
    exact nodup_map_injective _ (by
      intro a b h
      exact (Prod.mk.inj h).2) (hf [])
  | cons e es ih =>
    apply List.nodup_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact nodup_map_injective _ (by
        intro a b h
        have h₁ := List.cons.inj (Prod.mk.inj h).1
        exact Prod.ext h₁.2 (Prod.mk.inj h).2) (ih f hf)
    · exact nodup_map_injective _ (by
        intro a b h
        have h₁ := List.cons.inj (Prod.mk.inj h).1
        exact Prod.ext h₁.2 (Prod.mk.inj h).2)
        (ih (fun a => f (e :: a)) (fun a => hf (e :: a)))
    · intro z hz w hw hzw
      subst w
      obtain ⟨a, ha, hza⟩ := List.mem_map.mp hz
      obtain ⟨b, hb, hzb⟩ := List.mem_map.mp hw
      have h := hza.trans hzb.symm
      have hhead := (List.cons.inj (Prod.mk.inj h).1).1
      cases hhead

/-- Codes for the finite decorated-subgraph count. For a subset A, the two
coordinates encode words over alphabets of q and q-2 colors of lengths
r(E)-r(A) and |A|-r(A), respectively. Base-0 words follow 0^0=1. -/
def countedObjects (G : Graph) (q : Nat) :
    List (List Bool × (Nat × Nat)) :=
  enumerate (fun a => rectangle
    (q ^ (rank G.edges - rank a))
    ((q - 2) ^ (a.length - rank a))) G.edges

theorem effective_count (G : Graph) (q : Nat) :
    (countedObjects G q).length = tutte G (q + 1) (q - 1) := by
  simp [countedObjects, enumerate_length, rectangle_length, tutte, Nat.sub_sub]

theorem countedObjects_nodup (G : Graph) (q : Nat) :
    (countedObjects G q).Nodup :=
  enumerate_nodup G.edges _ (fun _ => rectangle_nodup _ _)

/-- The complete positivity and finite counting assertion. -/
theorem conjecture_00000000585 (G : Graph) (q : Nat) (hq : 2 ≤ q) :
    0 < tutte G (q + 1) (q - 1) ∧
    (countedObjects G q).length = tutte G (q + 1) (q - 1) ∧
    (countedObjects G q).Nodup :=
  ⟨tutte_positive G q hq, effective_count G q, countedObjects_nodup G q⟩

#print axioms conjecture_00000000585
end Tutte585
