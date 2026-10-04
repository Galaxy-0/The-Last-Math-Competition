/-!
# Conjecture 00000001685: even subdivisions of `K_{3,3}` are not Pfaffian

The conjecture says that the minimal families of nonplanar Pfaffian graphs are the
Möbius ladders `M_{2k}` and the even subdivisions of `K_{3,3}`.  In particular every even
subdivision of `K_{3,3}` would be a (nonplanar) Pfaffian graph.  This clause is false:
`K_{3,3}` itself (and the proper even subdivision `S`, one edge subdivided twice) has no
Pfaffian orientation.

Everything is defined from scratch (core Lean only):
* a graph is a vertex count `n` and an edge list; a perfect matching is an edge subset
  (bit mask) covering every vertex exactly once; `PMs G` lists all of them;
* an orientation is a list of Booleans, one per edge;
* `term G os M` is the Pfaffian term `sgn(π) ∏ a_{π(2k-1)π(2k)}` of the matching `M`,
  i.e. the sign of the permutation `t₁ h₁ t₂ h₂ …` (tail/head of the oriented edges);
* `Pf G os = Σ_M term G os M` and `IsPfaffian G` means `|Pf| = #perfect matchings` for some
  orientation (the "counting by signed cancellation" of the conjecture).  `IsPfaffian'` is
  Kasteleyn's form (all terms equal) and implies `IsPfaffian`.

The proof is the classical parity obstruction (`not_pfaffian_of_invariant`, proved for all
graphs): reversing an edge flips exactly the terms of the matchings through it, so if every
edge lies in an even number of perfect matchings the parity of the number of negative terms
does not depend on the orientation; for `K_{3,3}` it is odd (3 of 6), while a Pfaffian
orientation would make it `0` or `6`.
-/

namespace Pfaffian

/-! ## Graphs, perfect matchings, orientations -/

/-- A finite graph on the vertex set `{0, …, n-1}` given by its list of edges.
Assumption: every edge endpoint is `< n` (true for every graph used below: `K33`, `S`,
`mobius r`, and the graphs produced by `subdivide2`). -/
structure Graph where
  n : Nat
  edges : List (Nat × Nat)
deriving DecidableEq, Repr

/-- The sub-list of edges selected by the bit mask `M` (bit `i` = edge number `i`). -/
def sel : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | e :: es, M => if M % 2 = 1 then e :: sel es (M / 2) else sel es (M / 2)

/-- `M` is a perfect matching: every vertex `v < n` lies on exactly one selected edge.
(Faithful when all edge endpoints are `< n`, see `Graph`.) -/
def isPM (G : Graph) (M : Nat) : Bool :=
  (List.range G.n).all fun v => ((sel G.edges M).countP fun e => e.1 == v || e.2 == v) == 1

/-- All perfect matchings, as edge masks `M < 2^|E|`. -/
def PMs (G : Graph) : List Nat := (List.range (2 ^ G.edges.length)).filter (isPM G)

def numPM (G : Graph) : Nat := (PMs G).length

/-- Orient the edges: entry `true` keeps `(a,b)` as `a → b`, `false` reverses it. -/
def orientL : List (Nat × Nat) → List Bool → List (Nat × Nat)
  | [], _ => []
  | e :: es, [] => e :: orientL es []
  | e :: es, b :: bs => (if b then e else (e.2, e.1)) :: orientL es bs

/-- `t₁ h₁ t₂ h₂ …` for a list of oriented edges `tᵢ → hᵢ`. -/
def word : List (Nat × Nat) → List Nat
  | [] => []
  | (a, b) :: r => a :: b :: word r

def inversions : List Nat → Nat
  | [] => 0
  | x :: r => r.countP (fun y => y < x) + inversions r

/-- Parity of the permutation `t₁ h₁ t₂ h₂ …` attached to the matching `M`. -/
def par (G : Graph) (os : List Bool) (M : Nat) : Nat :=
  inversions (word (sel (orientL G.edges os) M)) % 2

/-- The Pfaffian term `sgn(π) · ∏ a_{π(2k-1) π(2k)}` of the matching `M`. -/
def term (G : Graph) (os : List Bool) (M : Nat) : Int := if par G os M = 0 then 1 else -1

/-- Pfaffian of the skew adjacency matrix of the orientation `os`. -/
def Pf (G : Graph) (os : List Bool) : Int := ((PMs G).map (term G os)).sum

/-- Pfaffian orientation: the signed sum counts the perfect matchings. -/
def IsPfaffianOrientation (G : Graph) (os : List Bool) : Prop :=
  os.length = G.edges.length ∧ (Pf G os).natAbs = numPM G

/-- Kasteleyn's form: all perfect matchings have the same sign. -/
def IsSameSignOrientation (G : Graph) (os : List Bool) : Prop :=
  os.length = G.edges.length ∧ ∀ M ∈ PMs G, ∀ M' ∈ PMs G, term G os M = term G os M'

def IsPfaffian (G : Graph) : Prop := ∃ os, IsPfaffianOrientation G os

def IsPfaffian' (G : Graph) : Prop := ∃ os, IsSameSignOrientation G os

/-! ## The graphs -/

def K33 : Graph := ⟨6, [(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]⟩

/-- Möbius ladder with `r` rungs (`2r` vertices): the cycle `0 … 2r-1` plus rungs `i — i+r`. -/
def mobius (r : Nat) : Graph :=
  ⟨2 * r, (List.range (2 * r)).map (fun i => (i, (i + 1) % (2 * r))) ++
          (List.range r).map (fun i => (i, i + r))⟩

/-- Replace edge number `i = uv` by the path `u — n — n+1 — v` (two new vertices). -/
def subdivide2 (G : Graph) (i : Nat) : Graph :=
  let e := G.edges.getD i (0, 0)
  ⟨G.n + 2, G.edges.eraseIdx i ++ [(e.1, G.n), (G.n, G.n + 1), (G.n + 1, e.2)]⟩

/-- Even subdivisions of `K_{3,3}`: obtained by repeatedly subdividing an edge twice. -/
inductive EvenSubdivisionK33 : Graph → Prop
  | base : EvenSubdivisionK33 K33
  | step (G : Graph) (i : Nat) : EvenSubdivisionK33 G → i < G.edges.length →
      EvenSubdivisionK33 (subdivide2 G i)

/-! ## The parity invariant -/

/-- Number of selected edges whose orientation is reversed. -/
def flips : List (Nat × Nat) → List Bool → Nat → Nat
  | [], _, _ => 0
  | _ :: es, [], M => flips es [] (M / 2)
  | _ :: es, b :: bs, M => (if M % 2 = 1 ∧ b = false then 1 else 0) + flips es bs (M / 2)

def noLoops (es : List (Nat × Nat)) : Bool := es.all fun e => e.1 != e.2

/-- Every edge lies in an even number of the matchings in `L`. -/
def allEven : List (Nat × Nat) → List Nat → Bool
  | [], _ => true
  | _ :: es, L => (L.countP fun M => M % 2 == 1) % 2 == 0 && allEven es (L.map (· / 2))

theorem word_perm (es : List (Nat × Nat)) (os : List Bool) (M : Nat) :
    (word (sel (orientL es os) M)).Perm (word (sel es M)) := by
  induction es generalizing os M with
  | nil => cases os <;> simp [orientL, sel, word]
  | cons e es ih =>
    obtain ⟨a, c⟩ := e
    cases os with
    | nil =>
      by_cases h : M % 2 = 1
      · simp only [orientL, sel, h, if_true, word]
        exact List.Perm.cons _ (List.Perm.cons _ (ih [] _))
      · simp only [orientL, sel, h, if_false]; exact ih [] _
    | cons b bs =>
      by_cases h : M % 2 = 1
      · cases b
        · simp only [orientL, sel, h, if_true, word, Bool.false_eq_true, if_false]
          exact (List.Perm.cons _ (List.Perm.cons _ (ih bs _))).trans (List.Perm.swap _ _ _)
        · simp only [orientL, sel, h, if_true, word]
          exact List.Perm.cons _ (List.Perm.cons _ (ih bs _))
      · simp only [orientL, sel, h, if_false]; exact ih bs _

theorem flips_nil (es : List (Nat × Nat)) (M : Nat) : flips es [] M = 0 := by
  induction es generalizing M with
  | nil => rfl
  | cons e es ih => simp [flips, ih]

/-- Reversing the selected edges changes the parity by the number of reversals. -/
theorem par_flips (es : List (Nat × Nat)) (hl : noLoops es = true) (os : List Bool) (M : Nat) :
    (inversions (word (sel (orientL es os) M)) + inversions (word (sel es M))
      + flips es os M) % 2 = 0 := by
  induction es generalizing os M with
  | nil => cases os <;> simp [orientL, sel, word, inversions, flips]
  | cons e es ih =>
    obtain ⟨a, c⟩ := e
    simp only [noLoops, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hl
    have hac : a ≠ c := hl.1
    have hl' : noLoops es = true := hl.2
    cases os with
    | nil =>
      have := ih hl' [] (M / 2)
      rw [flips_nil] at this ⊢
      by_cases h : M % 2 = 1
      · simp only [orientL, sel, h, if_true, word, inversions, List.countP_cons]
        have hp := (word_perm es [] (M / 2))
        rw [hp.countP_eq, hp.countP_eq]
        omega
      · simp only [orientL, sel, h, if_false]; omega
    | cons b bs =>
      have := ih hl' bs (M / 2)
      have hp := (word_perm es bs (M / 2))
      by_cases h : M % 2 = 1
      · cases b
        · simp only [orientL, sel, h, if_true, word, inversions, List.countP_cons, flips,
            Bool.false_eq_true, if_false, and_self]
          rw [hp.countP_eq, hp.countP_eq]
          by_cases hlt : a < c
          · have h1 : ¬ c < a := by omega
            simp [hlt, h1]; omega
          · have h1 : c < a := by omega
            simp [hlt, h1]; omega
        · simp only [orientL, sel, h, if_true, word, inversions, List.countP_cons, flips]
          rw [hp.countP_eq, hp.countP_eq]
          simp; omega
      · simp only [orientL, sel, h, if_false, flips]; simp [h]; omega

theorem sum_map_zero (L : List Nat) : (L.map (fun _ => (0 : Nat))).sum = 0 := by
  induction L with
  | nil => rfl
  | cons M L ih => simp only [List.map_cons, List.sum_cons, ih]

theorem sum_map_flips_even (es : List (Nat × Nat)) (os : List Bool) (L : List Nat)
    (h : allEven es L = true) : (L.map (flips es os)).sum % 2 = 0 := by
  induction es generalizing os L with
  | nil =>
    have hz : flips [] os = fun _ => 0 := by funext M; rfl
    rw [hz, sum_map_zero]
  | cons e es ih =>
    simp only [allEven, Bool.and_eq_true, beq_iff_eq] at h
    cases os with
    | nil =>
      have hz : flips (e :: es) [] = fun _ => 0 := by funext M; exact flips_nil _ M
      rw [hz, sum_map_zero]
    | cons b bs =>
      have key : ∀ L : List Nat, (L.map (flips (e :: es) (b :: bs))).sum =
          (if b = false then L.countP (fun M => M % 2 == 1) else 0) +
          ((L.map (· / 2)).map (flips es bs)).sum := by
        intro L
        induction L with
        | nil => simp
        | cons M L ihL =>
          rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ihL,
            List.countP_cons]
          show (if M % 2 = 1 ∧ b = false then 1 else 0) + flips es bs (M / 2) + _ = _
          cases b <;> by_cases hM : M % 2 = 1 <;> simp [hM] <;> omega
      rw [key]
      have := ih bs _ h.2
      cases b
      · rw [if_pos rfl]; omega
      · rw [if_neg (by decide)]; omega

/-- `Σ term = |L| - 2 · Σ par` -/
theorem sum_terms (G : Graph) (os : List Bool) (L : List Nat) :
    (L.map (term G os)).sum = (L.length : Int) - 2 * ((L.map (par G os)).sum : Nat) := by
  induction L with
  | nil => simp
  | cons M L ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, term]
    have : par G os M < 2 := Nat.mod_lt _ (by decide)
    by_cases h : par G os M = 0
    · simp [h]; omega
    · have h1 : par G os M = 1 := by omega
      simp [h1]; omega

theorem sum_par_le (G : Graph) (os : List Bool) (L : List Nat) :
    (L.map (par G os)).sum ≤ L.length := by
  induction L with
  | nil => simp
  | cons M L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have : par G os M < 2 := Nat.mod_lt _ (by decide)
    omega

/-- Summing `par_flips` over a list of matchings. -/
theorem sum_par_congr (G : Graph) (hl : noLoops G.edges = true) (os : List Bool) (L : List Nat) :
    ((L.map (par G os)).sum + (L.map (par G [])).sum + (L.map (flips G.edges os)).sum) % 2
      = 0 := by
  induction L with
  | nil => simp
  | cons M L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := par_flips G.edges hl os M
    have h0 : orientL G.edges [] = G.edges := by
      generalize G.edges = es
      induction es with
      | nil => rfl
      | cons e es ihe => simp [orientL, ihe]
    simp only [par, h0] at ih ⊢
    omega

/-- **Obstruction.** If the graph has no loops, an even number of perfect matchings,
every edge lies in an even number of them, and the reference orientation has an odd number
of negative terms, then the graph has no Pfaffian orientation. -/
theorem not_pfaffian_of_invariant (G : Graph) (hl : noLoops G.edges = true)
    (hE : allEven G.edges (PMs G) = true) (hN : numPM G % 2 = 0)
    (hodd : ((PMs G).map (par G [])).sum % 2 = 1) : ¬ IsPfaffian G := by
  rintro ⟨os, _, habs⟩
  have hs := sum_terms G os (PMs G)
  have hle := sum_par_le G os (PMs G)
  have hc := sum_par_congr G hl os (PMs G)
  have hf := sum_map_flips_even G.edges os (PMs G) hE
  unfold Pf at habs
  unfold numPM at hN habs
  rw [hs] at habs
  generalize ((PMs G).map (par G os)).sum = S at *
  generalize (PMs G).length = N at *
  omega

theorem same_sign_pfaffian (G : Graph) (os : List Bool) :
    IsSameSignOrientation G os → IsPfaffianOrientation G os := by
  rintro ⟨hlen, hall⟩
  refine ⟨hlen, ?_⟩
  unfold Pf numPM
  cases hP : PMs G with
  | nil => simp
  | cons M₀ L =>
    have hc : ∀ M ∈ PMs G, term G os M = term G os M₀ :=
      fun M hM => hall M hM M₀ (by rw [hP]; simp)
    rw [hP] at hc
    have key : ∀ L' : List Nat, (∀ M ∈ L', term G os M = term G os M₀) →
        (L'.map (term G os)).sum = L'.length * term G os M₀ := by
      intro L' h'
      induction L' with
      | nil => simp
      | cons M L' ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [h' M (by simp), ih (fun M hM => h' M (by simp [hM]))]
        push_cast; rw [Int.add_mul, Int.one_mul, Int.add_comm]
    rw [key _ hc]
    unfold term
    split <;> simp <;> omega

theorem not_pfaffian'_of_not_pfaffian (G : Graph) : ¬ IsPfaffian G → ¬ IsPfaffian' G :=
  fun h ⟨os, hos⟩ => h ⟨os, same_sign_pfaffian G os hos⟩

/-! ## Computations -/

theorem PMs_K33 : PMs K33 = [84, 98, 140, 161, 266, 273] := by decide +kernel

def S : Graph := subdivide2 K33 0

theorem PMs_S : PMs S = [554, 561, 582, 645, 1360, 1416] := by decide +kernel

theorem K33_not_pfaffian : ¬ IsPfaffian K33 := by
  apply not_pfaffian_of_invariant
  · decide
  · rw [PMs_K33]; decide
  · unfold numPM; rw [PMs_K33]; decide
  · rw [PMs_K33]; decide

theorem S_not_pfaffian : ¬ IsPfaffian S := by
  apply not_pfaffian_of_invariant
  · decide
  · rw [PMs_S]; decide
  · unfold numPM; rw [PMs_S]; decide
  · rw [PMs_S]; decide

theorem PMs_M6 : PMs (mobius 3) = [21, 42, 82, 164, 265, 448] := by decide +kernel

/-- The Möbius ladder with 3 rungs (`M_6` in the vertex-count convention, isomorphic to
`K_{3,3}`) is not Pfaffian. -/
theorem M6_not_pfaffian : ¬ IsPfaffian (mobius 3) := by
  apply not_pfaffian_of_invariant
  · decide
  · rw [PMs_M6]; decide
  · unfold numPM; rw [PMs_M6]; decide
  · rw [PMs_M6]; decide

/-! ## Non-vacuity: some graphs are Pfaffian -/

theorem PMs_K4 : PMs (mobius 2) = [5, 10, 48] := by decide +kernel
theorem PMs_M8 : PMs (mobius 4) = [85, 170, 836, 1672, 2338, 3089, 3840] := by decide +kernel

/-- `K_4` (= Möbius ladder with 2 rungs, planar) is Pfaffian. -/
theorem K4_pfaffian : IsPfaffian (mobius 2) :=
  ⟨[true, true, true, false, true, false], by decide, by unfold Pf numPM; rw [PMs_K4]; decide⟩

/-- The Wagner graph `V_8` (Möbius ladder with 4 rungs, nonplanar) is Pfaffian. -/
theorem M8_pfaffian : IsPfaffian (mobius 4) :=
  ⟨[true, true, true, true, true, true, true, false, true, false, true, false], by decide,
    by unfold Pf numPM; rw [PMs_M8]; decide⟩

/-! ## Cross-check with the matrix Pfaffian (expansion along the first row) -/

/-- Skew adjacency entry `a_{ij}` of an oriented edge list. -/
def skew (D : List (Nat × Nat)) (i j : Nat) : Int :=
  if D.contains (i, j) then 1 else if D.contains (j, i) then -1 else 0

/-- `(j, rest without j, (-1)^position)` for every element `j` of a list. -/
def splits : List Nat → List (Nat × List Nat × Int)
  | [] => []
  | j :: r => (j, r, 1) :: (splits r).map (fun x => (x.1, j :: x.2.1, -x.2.2))

/-- Pfaffian of the principal submatrix on the index list `vs`, by
`Pf(A) = Σ_j (-1)^j a_{1j} Pf(A_{\hat 1 \hat j})` (with `fuel` bounding the depth). -/
def pfAux (a : Nat → Nat → Int) : Nat → List Nat → Int
  | 0, _ => 1
  | _ + 1, [] => 1
  | f + 1, i :: rest => ((splits rest).map fun x => x.2.2 * a i x.1 * pfAux a f x.2.1).sum

def pfMat (G : Graph) (os : List Bool) : Int :=
  pfAux (skew (orientL G.edges os)) G.n (List.range G.n)

theorem pfMat_K33 : pfMat K33 [] = Pf K33 [] ∧ Pf K33 [] = 0 := by
  unfold Pf; rw [PMs_K33]; decide

theorem pfMat_M8 :
    pfMat (mobius 4) [true, true, true, true, true, true, true, false, true, false, true, false]
      = Pf (mobius 4) [true, true, true, true, true, true, true, false, true, false, true, false]
    := by unfold Pf; rw [PMs_M8]; decide

/-! ## The conjecture -/

/-- `S` (one edge of `K_{3,3}` subdivided twice) is a proper even subdivision of `K_{3,3}`. -/
theorem S_even_subdivision : EvenSubdivisionK33 S ∧ S ≠ K33 :=
  ⟨EvenSubdivisionK33.step K33 0 EvenSubdivisionK33.base (by decide), by decide⟩

theorem numPM_K33 : numPM K33 = 6 := by unfold numPM; rw [PMs_K33]; rfl
theorem numPM_S : numPM S = 6 := by unfold numPM; rw [PMs_S]; rfl

/-- The clause "the even subdivisions of `K_{3,3}` form a family of (nonplanar, minimal, …)
Pfaffian graphs": `Q` stands for any additional property attributed to the family. -/
def EvenSubdivisionClause (Q : Graph → Prop) : Prop :=
  ∀ G, EvenSubdivisionK33 G → Q G ∧ IsPfaffian G

/-- Same clause, with Kasteleyn's "all perfect matchings have the same sign" definition. -/
def EvenSubdivisionClause' (Q : Graph → Prop) : Prop :=
  ∀ G, EvenSubdivisionK33 G → Q G ∧ IsPfaffian' G

theorem conjecture_00000001685_false (Q : Graph → Prop) : ¬ EvenSubdivisionClause Q :=
  fun h => K33_not_pfaffian (h K33 EvenSubdivisionK33.base).2

theorem conjecture_00000001685_false' (Q : Graph → Prop) : ¬ EvenSubdivisionClause' Q :=
  fun h => not_pfaffian'_of_not_pfaffian K33 K33_not_pfaffian (h K33 EvenSubdivisionK33.base).2

/-- Also false if "even subdivision" is meant to exclude `K_{3,3}` itself. -/
theorem conjecture_00000001685_false_proper (Q : Graph → Prop) :
    ¬ ∀ G, EvenSubdivisionK33 G → G ≠ K33 → Q G ∧ IsPfaffian G :=
  fun h => S_not_pfaffian (h S S_even_subdivision.1 S_even_subdivision.2).2

/-- The whole conjecture is a conjunction containing the clause; `R` is everything else. -/
theorem conjecture_00000001685_conjunction_false (Q : Graph → Prop) (R : Prop) :
    ¬ (EvenSubdivisionClause Q ∧ R) :=
  fun h => conjecture_00000001685_false Q h.1

/-- Möbius part, vertex-count convention (`M_{2k}` has `2k` vertices, `k ≥ 3` rungs). -/
theorem mobius_clause_false_vertex_convention (Q : Graph → Prop) :
    ¬ ∀ k, 3 ≤ k → Q (mobius k) ∧ IsPfaffian (mobius k) :=
  fun h => M6_not_pfaffian (h 3 (by decide)).2


/-! ## Obstruction reading (minimal NON-Pfaffian families, as in Little's theorem) -/

/-- If the families were read as minimal *non*-Pfaffian obstructions, the Möbius clause
fails in the rung-count convention (`M_{2k}` = `mobius (2*k)`, `2k` rungs): at `k = 2` it
is the Wagner graph `V_8 = mobius 4`, which is Pfaffian. -/
theorem obstruction_reading_false (Q : Graph → Prop) :
    ¬ ∀ k, 2 ≤ k → Q (mobius (2 * k)) ∧ ¬ IsPfaffian (mobius (2 * k)) :=
  fun h => (h 2 (by decide)).2 M8_pfaffian

/-- Same, vertex-count convention (`M_{2k}` = `mobius k`, `2k` vertices): at `k = 4`
it is `V_8`, which is Pfaffian. -/
theorem obstruction_reading_false_vertex_convention (Q : Graph → Prop) :
    ¬ ∀ k, 3 ≤ k → Q (mobius k) ∧ ¬ IsPfaffian (mobius k) :=
  fun h => (h 4 (by decide)).2 M8_pfaffian

end Pfaffian

#print axioms Pfaffian.not_pfaffian_of_invariant
#print axioms Pfaffian.K33_not_pfaffian
#print axioms Pfaffian.S_not_pfaffian
#print axioms Pfaffian.M6_not_pfaffian
#print axioms Pfaffian.K4_pfaffian
#print axioms Pfaffian.M8_pfaffian
#print axioms Pfaffian.pfMat_K33
#print axioms Pfaffian.pfMat_M8
#print axioms Pfaffian.S_even_subdivision
#print axioms Pfaffian.conjecture_00000001685_false
#print axioms Pfaffian.conjecture_00000001685_false'
#print axioms Pfaffian.conjecture_00000001685_false_proper
#print axioms Pfaffian.conjecture_00000001685_conjunction_false
#print axioms Pfaffian.mobius_clause_false_vertex_convention
#print axioms Pfaffian.obstruction_reading_false
#print axioms Pfaffian.obstruction_reading_false_vertex_convention
