/-!
# Conjecture 00000001289: the "nim graph" Q_⊕(n) cannot have diameter 2^n - 1 and
# chromatic number 2^n

The conjecture: the nim graph `Q_⊕(n)` of the hypercube (vertex set the `2^n` vertices of
the `n`-cube, identified with `{0, …, 2^n - 1}` via binary expansion, edges "given by ⊕")
has diameter `2^n - 1` and chromatic number `2^n`.

The edge rule is not specified precisely, so we prove the strongest possible statement:
**no** simple graph on `N ≥ 3` vertices has diameter `N - 1` and chromatic number `N`
(`no_graph_diam_chi`). Indeed, chromatic number `N` forces the graph to be complete
(`adj_of_chromatic`), and a complete graph has diameter `≤ 1`. With `N = 2^n` the
conjecture therefore fails for every `n ≥ 2` and for every choice of the edge set
(`claimAt_false`, `conjecture_00000001289_false`). We also compute the two natural
concrete readings (hypercube: `χ = 2`, `diam = n`; complete graph: `χ = 2^n`, `diam = 1`),
check non-vacuity, and cross-check `n = 2` over all 64 labelled graphs on 4 vertices.

Everything is defined from scratch in core Lean 4 (no Mathlib): graphs are Boolean
adjacency functions on `ℕ` restricted to `{0, …, N-1}`; colourings, walks, distances and
the diameter are the textbook notions.
-/

namespace NimGraph

/-- A graph: Boolean adjacency on `ℕ`; only vertices `< N` are used. -/
abbrev Graph := Nat → Nat → Bool

/-- Simple graph on the vertex set `{0, …, N-1}`: symmetric and loopless. -/
def IsSimple (G : Graph) (N : Nat) : Prop :=
  ∀ u, u < N → ∀ v, v < N → G u v = G v u ∧ G u u = false

/-- `col` is a proper colouring of `G` with colours `{0, …, c-1}`. -/
def IsProperColoring (G : Graph) (N c : Nat) (col : Nat → Nat) : Prop :=
  (∀ u, u < N → col u < c) ∧
    ∀ u, u < N → ∀ v, v < N → G u v = true → col u ≠ col v

/-- `G` has a proper `c`-colouring. -/
def Colorable (G : Graph) (N c : Nat) : Prop := ∃ col, IsProperColoring G N c col

/-- `χ(G) = c`: `c` is the least number of colours of a proper colouring. -/
def ChromaticNumberEq (G : Graph) (N c : Nat) : Prop :=
  Colorable G N c ∧ ∀ k, k < c → ¬ Colorable G N k

/-- `WalkFrom G N u [w₁, …, w_k] v`: `u, w₁, …, w_k` is a walk of length `k` in `G`
(consecutive vertices adjacent, all `wᵢ < N`) ending at `w_k = v` (`u = v` if `k = 0`). -/
def WalkFrom (G : Graph) (N : Nat) : Nat → List Nat → Nat → Prop
  | u, [], v => u = v
  | u, w :: ws, v => w < N ∧ G u w = true ∧ WalkFrom G N w ws v

/-- There is a walk of length `≤ k` from `u` to `v`, i.e. `dist(u, v) ≤ k`. -/
def WalkLe (G : Graph) (N u v k : Nat) : Prop :=
  ∃ ws : List Nat, ws.length ≤ k ∧ WalkFrom G N u ws v

/-- `dist(u, v) = d`: shortest walk length. -/
def DistEq (G : Graph) (N u v d : Nat) : Prop :=
  WalkLe G N u v d ∧ ∀ k, k < d → ¬ WalkLe G N u v k

/-- `diam(G) = D`: all distances are `≤ D` (in particular `G` is connected) and some
pair is at distance exactly `D`. A disconnected graph has no finite diameter. -/
def DiameterEq (G : Graph) (N D : Nat) : Prop :=
  (∀ u, u < N → ∀ v, v < N → WalkLe G N u v D) ∧
    ∃ u, u < N ∧ ∃ v, v < N ∧ DistEq G N u v D

/-- Executable reachability within `k` steps (used only for decidability). -/
def reach (G : Graph) (N : Nat) : Nat → Nat → Nat → Bool
  | 0, u, v => u == v
  | k + 1, u, v => reach G N k u v || (List.range N).any (fun w => G u w && reach G N k w v)

/-- `reach` decides `WalkLe`. -/
theorem reach_iff (G : Graph) (N : Nat) :
    ∀ k u v, reach G N k u v = true ↔ WalkLe G N u v k
  | 0, u, v => by
    simp only [reach, beq_iff_eq, WalkLe]
    constructor
    · intro h; exact ⟨[], Nat.le_refl _, h⟩
    · rintro ⟨ws, hl, hw⟩
      cases ws with
      | nil => exact hw
      | cons w ws => simp at hl
  | k + 1, u, v => by
    simp only [reach, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true]
    rw [reach_iff G N k u v]
    constructor
    · rintro (⟨ws, hl, hw⟩ | ⟨w, hw, hG, hr⟩)
      · exact ⟨ws, Nat.le_succ_of_le hl, hw⟩
      · obtain ⟨ws, hl, hws⟩ := (reach_iff G N k w v).1 hr
        exact ⟨w :: ws, by simp; omega, hw, hG, hws⟩
    · rintro ⟨ws, hl, hw⟩
      cases ws with
      | nil => exact Or.inl ⟨[], Nat.zero_le _, hw⟩
      | cons w ws =>
        obtain ⟨hwN, hG, hws⟩ := hw
        refine Or.inr ⟨w, hwN, hG, (reach_iff G N k w v).2 ⟨ws, ?_, hws⟩⟩
        simp at hl; omega

instance (G : Graph) (N u v k : Nat) : Decidable (WalkLe G N u v k) :=
  decidable_of_iff _ (reach_iff G N k u v)

instance (G : Graph) (N u v d : Nat) : Decidable (DistEq G N u v d) := by
  unfold DistEq; infer_instance

instance (G : Graph) (N D : Nat) : Decidable (DiameterEq G N D) := by
  unfold DiameterEq; infer_instance

instance (G : Graph) (N : Nat) : Decidable (IsSimple G N) := by
  unfold IsSimple; infer_instance


/-! ## Well-definedness -/

theorem chromatic_unique {G : Graph} {N a b : Nat}
    (ha : ChromaticNumberEq G N a) (hb : ChromaticNumberEq G N b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd ha.1 (hb.2 a h)
  · exact h
  · exact absurd hb.1 (ha.2 b h)

theorem diameter_unique {G : Graph} {N a b : Nat}
    (ha : DiameterEq G N a) (hb : DiameterEq G N b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · obtain ⟨u, hu, v, hv, -, hfar⟩ := hb.2
    exact absurd (ha.1 u hu v hv) (hfar a h)
  · exact h
  · obtain ⟨u, hu, v, hv, -, hfar⟩ := ha.2
    exact absurd (hb.1 u hu v hv) (hfar b h)

theorem colorable_self {G : Graph} {N : Nat} (hs : IsSimple G N) : Colorable G N N := by
  refine ⟨fun w => w, fun u hu => hu, fun u hu v hv huv heq => ?_⟩
  subst heq
  rw [(hs u hu u hu).2] at huv
  exact Bool.false_ne_true huv

/-! ## The key lemma -/

theorem adj_of_chromatic {G : Graph} {N : Nat} (hs : IsSimple G N)
    (hc : ChromaticNumberEq G N N) :
    ∀ u, u < N → ∀ v, v < N → u ≠ v → G u v = true := by
  intro u hu v hv huv
  cases hG : G u v with
  | true => rfl
  | false =>
    exfalso
    apply hc.2 (N - 1) (by omega)
    refine ⟨fun w => if w = v then (if u < v then u else u - 1)
              else (if w < v then w else w - 1), ?_, ?_⟩
    · intro w hw
      simp only
      repeat' split
      all_goals omega
    · intro a ha b hb hab
      have hab' : a ≠ b := by
        intro h; subst h; rw [(hs a ha a ha).2] at hab; exact Bool.false_ne_true hab
      have h1 : a = v → b ≠ u := by
        intro h1 h2; subst h1; subst h2
        rw [(hs a ha b hb).1, hG] at hab; exact Bool.false_ne_true hab
      have h2 : b = v → a ≠ u := by
        intro h1 h2; subst h1; subst h2; rw [hG] at hab; exact Bool.false_ne_true hab
      simp only
      repeat' split
      all_goals omega

theorem walkLe_one_of_complete {G : Graph} {N : Nat}
    (hcomp : ∀ u, u < N → ∀ v, v < N → u ≠ v → G u v = true) :
    ∀ u, u < N → ∀ v, v < N → WalkLe G N u v 1 := by
  intro u hu v hv
  by_cases h : u = v
  · exact ⟨[], Nat.zero_le _, h⟩
  · exact ⟨[v], Nat.le_refl _, hv, hcomp u hu v hv h, rfl⟩

theorem diameter_le_one {G : Graph} {N D : Nat}
    (hcomp : ∀ u, u < N → ∀ v, v < N → u ≠ v → G u v = true)
    (hD : DiameterEq G N D) : D ≤ 1 := by
  obtain ⟨u, hu, v, hv, -, hfar⟩ := hD.2
  refine Nat.le_of_not_lt fun h => hfar 1 h ?_
  exact walkLe_one_of_complete hcomp u hu v hv

/-- **General lemma.** A simple graph on `N` vertices with chromatic number `N`
is complete, hence has diameter at most `1`. -/
theorem diameter_le_one_of_chromatic {G : Graph} {N D : Nat} (hs : IsSimple G N)
    (hc : ChromaticNumberEq G N N) (hD : DiameterEq G N D) : D ≤ 1 :=
  diameter_le_one (adj_of_chromatic hs hc) hD

/-- No simple graph on `N ≥ 3` vertices has diameter `N - 1` and chromatic number `N`. -/
theorem no_graph_diam_chi (N : Nat) (hN : 3 ≤ N) (G : Graph) (hs : IsSimple G N) :
    ¬ (DiameterEq G N (N - 1) ∧ ChromaticNumberEq G N N) := by
  rintro ⟨hD, hc⟩
  have := diameter_le_one_of_chromatic hs hc hD
  omega

/-! ## The conjecture -/

/-- The clause of conjecture 00000001289 for a single `n`: the graph `G = Q_⊕(n)` on
the `2^n` hypercube vertices `{0, …, 2^n - 1}` has diameter `2^n - 1` and chromatic
number `2^n`. -/
def ClaimAt (G : Graph) (n : Nat) : Prop :=
  DiameterEq G (2 ^ n) (2 ^ n - 1) ∧ ChromaticNumberEq G (2 ^ n) (2 ^ n)

/-- Conjecture 00000001289 for a family `Q n = Q_⊕(n)`: the clause holds for every `n ≥ 1`. -/
def NimClaim (Q : Nat → Graph) : Prop := ∀ n, 1 ≤ n → ClaimAt (Q n) n

/-- For every `n ≥ 2` and **every** simple graph on `2^n` vertices the clause fails. -/
theorem claimAt_false (n : Nat) (hn : 2 ≤ n) (G : Graph) (hs : IsSimple G (2 ^ n)) :
    ¬ ClaimAt G n := by
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  exact no_graph_diam_chi (2 ^ n) (by simp at h4; omega) G hs

/-- **Conjecture 00000001289 is false**, whatever simple graph `Q_⊕(n)` is taken to be
on the `2^n` vertices of the hypercube: the clause already fails at `n = 2`. -/
theorem conjecture_00000001289_false (Q : Nat → Graph) (hQ : IsSimple (Q 2) (2 ^ 2)) :
    ¬ NimClaim Q :=
  fun h => claimAt_false 2 (Nat.le_refl _) (Q 2) hQ (h 2 (by decide))

/-! ## Pigeonhole and the complete ("all `u ⊕ v ≠ 0`") reading -/

theorem pigeonhole : ∀ (N k : Nat) (f : Nat → Nat), (∀ i, i < N → f i < k) →
    (∀ i, i < N → ∀ j, j < N → i ≠ j → f i ≠ f j) → N ≤ k
  | 0, _, _, _, _ => Nat.zero_le _
  | N + 1, k, f, hlt, hinj => by
    have hN := hlt N (Nat.lt_succ_self N)
    have key := pigeonhole N (k - 1) (fun i => if f i < f N then f i else f i - 1)
      (by
        intro i hi
        have := hlt i (by omega)
        have := hinj i (by omega) N (Nat.lt_succ_self N) (by omega)
        simp only; split <;> omega)
      (by
        intro i hi j hj hij
        have := hinj i (by omega) j (by omega) hij
        have := hinj i (by omega) N (Nat.lt_succ_self N) (by omega)
        have := hinj j (by omega) N (Nat.lt_succ_self N) (by omega)
        simp only; split <;> split <;> omega)
    omega

theorem xor_eq_zero {u v : Nat} (h : u ^^^ v = 0) : u = v := by
  have : u ^^^ (u ^^^ v) = v := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [h, Nat.xor_zero] at this
  exact this

/-- Reading (K): `u ~ v` iff `u ⊕ v ≠ 0`, i.e. the Cayley graph of `(ℤ/2)^n` with all
nonzero elements as generators (the complete graph). -/
def nimComplete : Graph := fun u v => (u ^^^ v) != 0

theorem nimComplete_simple (N : Nat) : IsSimple nimComplete N := by
  intro u _ v _
  refine ⟨by simp only [nimComplete, Nat.xor_comm], by simp [nimComplete]⟩

theorem nimComplete_adj {u v : Nat} (h : u ≠ v) : nimComplete u v = true := by
  simp only [nimComplete, bne_iff_ne, ne_eq]
  exact fun h' => h (xor_eq_zero h')

theorem nimComplete_chi (N : Nat) : ChromaticNumberEq nimComplete N N := by
  refine ⟨colorable_self (nimComplete_simple N), fun k hk ⟨col, hlt, hprop⟩ => ?_⟩
  have := pigeonhole N k col hlt
    (fun i hi j hj hij => hprop i hi j hj (nimComplete_adj hij))
  omega

theorem nimComplete_diam (N : Nat) (hN : 2 ≤ N) : DiameterEq nimComplete N 1 := by
  refine ⟨walkLe_one_of_complete fun u _ v _ h => nimComplete_adj h, 0, by omega, 1, hN,
    walkLe_one_of_complete (fun u _ v _ h => nimComplete_adj h) 0 (by omega) 1 hN, ?_⟩
  intro k hk ⟨ws, hl, hw⟩
  have : ws = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst this
  simp [WalkFrom] at hw

/-! ## The hypercube reading -/

/-- `x` is a power of two. -/
def isPow2 (x : Nat) : Bool := x != 0 && (x &&& (x - 1)) == 0

/-- Reading (H): `u ~ v` iff `u ⊕ v` is a power of two, i.e. `u, v` differ in exactly one
bit: the hypercube graph `Q_n` (Cayley graph of `(ℤ/2)^n` with the unit vectors). -/
def hypercube : Graph := fun u v => isPow2 (u ^^^ v)

theorem hypercube_simple (N : Nat) : IsSimple hypercube N := by
  intro u _ v _
  refine ⟨by simp only [hypercube, Nat.xor_comm], by simp [hypercube, isPow2]⟩

/-- Parity of the number of one-bits (`fuel` bounds the recursion). -/
def bitParity : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, x => (x % 2 + bitParity fuel (x / 2)) % 2

theorem hypercube_chi_two (n : Nat) (hn : 1 ≤ n)
    (hcol : IsProperColoring hypercube (2 ^ n) 2 (bitParity n)) :
    ChromaticNumberEq hypercube (2 ^ n) 2 := by
  refine ⟨⟨_, hcol⟩, fun k hk ⟨col, hlt, hprop⟩ => ?_⟩
  have h2 : 2 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hn; simpa using this
  have h01 := hprop 0 (by omega) 1 (by omega) (by decide)
  have := hlt 0 (by omega)
  have := hlt 1 (by omega)
  omega

theorem hypercube2_chi : ChromaticNumberEq hypercube (2 ^ 2) 2 :=
  hypercube_chi_two 2 (by decide) (by unfold IsProperColoring; decide)

theorem hypercube3_chi : ChromaticNumberEq hypercube (2 ^ 3) 2 :=
  hypercube_chi_two 3 (by decide) (by unfold IsProperColoring; decide)

theorem hypercube2_diam : DiameterEq hypercube (2 ^ 2) 2 := by decide

theorem hypercube3_diam : DiameterEq hypercube (2 ^ 3) 3 := by decide

/-- The hypercube reading refutes the conjecture at `n = 2`: `χ = 2 ≠ 4`, `diam = 2 ≠ 3`. -/
theorem hypercube_reading_false : ¬ NimClaim (fun _ => hypercube) := by
  intro h
  obtain ⟨hD, hc⟩ := h 2 (by decide)
  have := chromatic_unique hc hypercube2_chi
  have := diameter_unique hD hypercube2_diam
  simp at *

theorem complete_reading_false : ¬ NimClaim (fun _ => nimComplete) := by
  intro h
  obtain ⟨hD, -⟩ := h 2 (by decide)
  have := diameter_unique hD (nimComplete_diam 4 (by decide))
  simp at this

/-! ## Non-vacuity -/

/-- The path `0 - 1 - 2 - 3`. -/
def path4 : Graph := fun u v => u + 1 == v || v + 1 == u

/-- On four vertices each conjunct alone is satisfiable: the path has diameter `3`,
the complete graph has chromatic number `4`. -/
theorem nonvacuous_four :
    IsSimple path4 4 ∧ DiameterEq path4 4 3 ∧ ChromaticNumberEq nimComplete 4 4 :=
  ⟨by decide, by decide, nimComplete_chi 4⟩

/-- At `n = 1` the clause is satisfied (by `Q_1 = K_2`, under both readings), so the
predicates are not vacuous and the conjecture first fails at `n = 2`. -/
theorem claimAt_one : ClaimAt hypercube 1 ∧ ClaimAt nimComplete 1 := by
  refine ⟨⟨by decide, ?_⟩, ⟨nimComplete_diam 2 (by decide), nimComplete_chi 2⟩⟩
  exact hypercube_chi_two 1 (by decide) (by unfold IsProperColoring; decide)

/-! ## Cross-check: all 64 labelled graphs on 4 vertices -/

/-- The six pairs of `{0,1,2,3}`. -/
def pairs4 : List (Nat × Nat) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

/-- The graph on `{0,1,2,3}` whose edge set is encoded by the bits of `m < 64`. -/
def graphOfMask (m : Nat) : Graph := fun u v =>
  (List.range 6).any fun i =>
    m.testBit i && (match pairs4[i]? with
      | some (a, b) => (a == u && b == v) || (a == v && b == u)
      | none => false)

/-- All maps `{0,1,2,3} → {0,1,2}` as lists. -/
def colorings3 : List (List Nat) :=
  [0,1,2].flatMap fun a => [0,1,2].flatMap fun b => [0,1,2].flatMap fun c =>
    [0,1,2].map fun d => [a, b, c, d]

def properL (G : Graph) (l : List Nat) : Bool :=
  (List.range 4).all fun u => (List.range 4).all fun v => !G u v || l.getD u 0 != l.getD v 0

theorem colorable_of_properL {G : Graph} {l : List Nat} (hl : l ∈ colorings3)
    (hp : properL G l = true) : Colorable G 4 3 := by
  have hbound : ∀ u, l.getD u 0 < 3 := by
    intro u
    simp only [colorings3, List.mem_flatMap, List.mem_map, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hl
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hl
    have : ∀ x, x = 0 ∨ x = 1 ∨ x = 2 → x < 3 := by omega
    match u with
    | 0 => exact this a ha
    | 1 => exact this b hb
    | 2 => exact this c hc
    | 3 => exact this d hd
    | _ + 4 => simp
  refine ⟨fun u => l.getD u 0, fun u _ => hbound u, fun u hu v hv huv => ?_⟩
  simp only [properL, List.all_eq_true, List.mem_range] at hp
  have := hp u hu v hv
  rw [huv] at this
  simpa using this

/-- Decidable statement checked over all 64 masks: each graph on `{0,1,2,3}` has a proper
3-colouring or has all distances `≤ 2`. -/
theorem all_masks : ∀ m, m < 64 →
    (colorings3.any fun l => properL (graphOfMask m) l) = true ∨
      ∀ u, u < 4 → ∀ v, v < 4 → WalkLe (graphOfMask m) 4 u v 2 := by
  decide

theorem all_masks_fail (m : Nat) (hm : m < 64) :
    ¬ (DiameterEq (graphOfMask m) 4 3 ∧ ChromaticNumberEq (graphOfMask m) 4 4) := by
  rintro ⟨hD, hc⟩
  rcases all_masks m hm with h | h
  · simp only [List.any_eq_true] at h
    obtain ⟨l, hl, hp⟩ := h
    exact hc.2 3 (by decide) (colorable_of_properL hl hp)
  · obtain ⟨u, hu, v, hv, -, hfar⟩ := hD.2
    exact hfar 2 (by decide) (h u hu v hv)

end NimGraph

#print axioms NimGraph.conjecture_00000001289_false
#print axioms NimGraph.no_graph_diam_chi
#print axioms NimGraph.claimAt_false
#print axioms NimGraph.hypercube_reading_false
#print axioms NimGraph.complete_reading_false
#print axioms NimGraph.nonvacuous_four
#print axioms NimGraph.claimAt_one
#print axioms NimGraph.hypercube3_diam
#print axioms NimGraph.hypercube3_chi
#print axioms NimGraph.all_masks_fail
