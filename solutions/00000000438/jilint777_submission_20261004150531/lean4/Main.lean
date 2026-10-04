/-!
# Conjecture 00000000438: primitive elements of NSym versus Eulerian numbers

The conjecture claims that the primitive Lie algebra of the Hopf algebra **Sym** of
noncommutative symmetric functions has `n`-th homogeneous dimension equal to the
Eulerian number `A(n,1)`.  We refute this dimension clause at `n = 3`:
the degree-3 primitive space has dimension `2`, while `A(3,1) = 4`
(permutations with one descent / ascent) or `A(3,1) = 1` (1-based convention,
OEIS A008292).

**Model.** NSym is the free associative algebra on `S_1, S_2, …` (`deg S_k = k`);
its degree-`n` part has basis `S^I = S_{i₁} ⋯ S_{iₗ}`, `I` a composition of `n`.
The coproduct is the algebra map with `Δ S_k = Σ_{i+j=k} S_i ⊗ S_j` (`S_0 = 1`).
A composition is a `List Nat` (`[]` is the unit `1`), a basis tensor `S^J ⊗ S^K` is
the pair `(J, K)`, and a tensor is a formal integer combination of such pairs
(`Tens`, a list of terms), compared coefficientwise (`coeffT`).  `deltaS I` computes
`Δ S^I` as the product `Δ S_{i₁} ⋯ Δ S_{iₗ}` in the tensor-square algebra,
where `(J,K)·(J',K') = (J++J', K++K')`.

An element `x = Σ_{I ⊨ n} x(I) S^I` of degree `n` is given by its coefficient
function `x : Comp → Int` (only the values on `comps n` are used).  It is
primitive when `Δ x − x ⊗ 1 − 1 ⊗ x = 0`, i.e. when every coefficient of
`Σ_I x(I) (Δ S^I − S^I ⊗ 1 − 1 ⊗ S^I)` vanishes (`IsPrimitive`).
`PrimDim n m` says that the primitive space has dimension `m`: there are `m`
linearly independent primitives and every `m + 1` primitives are linearly
dependent.  We work with integer coefficients; linear (in)dependence over `ℤ`
and over `ℚ` coincide (clear denominators), so this is the dimension over `ℚ`.
-/

namespace NSym

/-- A composition: a list of positive integers (`[]` stands for the unit `S^∅ = 1`). -/
abbrev Comp := List Nat

/-- Compositions of `m` (with fuel `f ≥ m`): first part `i+1`, then a composition of `m-1-i`. -/
def compsF : Nat → Nat → List Comp
  | _, 0 => [[]]
  | 0, _+1 => []
  | f+1, m+1 => (List.range (m+1)).flatMap (fun i => (compsF f (m - i)).map (fun c => (i+1) :: c))

/-- The compositions of `n`, indexing the basis `S^I` of `NSym_n`. -/
def comps (n : Nat) : List Comp := compsF n n

/-- Sanity check: `comps n` lists `2^(n-1)` distinct compositions of `n` (positive parts
summing to `n`), for `1 ≤ n ≤ 8`. -/
theorem comps_valid : ∀ n ∈ [1,2,3,4,5,6,7,8], (comps n).length = 2 ^ (n - 1) ∧ (comps n).Nodup ∧
    ∀ I ∈ comps n, I.sum = n ∧ ∀ i ∈ I, 0 < i := by decide +kernel

/-- Formal integer combinations of basis tensors `S^J ⊗ S^K`, encoded as `(J, K)`. -/
abbrev Tens := List ((Comp × Comp) × Int)

/-- Product in `NSym ⊗ NSym`: `(S^J ⊗ S^K)(S^J' ⊗ S^K') = S^{JJ'} ⊗ S^{KK'}`. -/
def tmul (s t : Tens) : Tens :=
  s.flatMap (fun p => t.map (fun q => ((p.1.1 ++ q.1.1, p.1.2 ++ q.1.2), p.2 * q.2)))

/-- `S_j` as a composition (`S_0 = 1` is the empty composition). -/
def gen (j : Nat) : Comp := if j = 0 then [] else [j]

/-- `Δ S_i = Σ_{j=0}^{i} S_j ⊗ S_{i-j}`. -/
def deltaGen (i : Nat) : Tens := (List.range (i+1)).map (fun j => ((gen j, gen (i - j)), 1))

/-- `Δ S^I = Δ S_{i₁} ⋯ Δ S_{iₗ}` (the coproduct is an algebra morphism). -/
def deltaS : Comp → Tens
  | [] => [(([], []), 1)]
  | i :: I => tmul (deltaGen i) (deltaS I)

/-- Coefficient of the basis tensor `k = (J, K)` in a formal combination. -/
def coeffT (t : Tens) (k : Comp × Comp) : Int := (t.map (fun p => if p.1 = k then p.2 else 0)).sum

/-- `Δ S^I − S^I ⊗ 1 − 1 ⊗ S^I`. -/
def defectS (I : Comp) : Tens := deltaS I ++ [((I, []), -1), (([], I), -1)]


/-! ## Primitive elements -/

/-- Coefficient function of an element `Σ_I x(I) S^I`. -/
abbrev Elt := Comp → Int

/-- Coefficient of `k` in `Δ x − x ⊗ 1 − 1 ⊗ x` for `x = Σ_{I ⊨ n} x(I) S^I`. -/
def primDefect (n : Nat) (x : Elt) (k : Comp × Comp) : Int :=
  ((comps n).map (fun I => x I * coeffT (defectS I) k)).sum

/-- `x` (in degree `n`) is primitive: `Δ x = x ⊗ 1 + 1 ⊗ x`. -/
def IsPrimitive (n : Nat) (x : Elt) : Prop := ∀ k : Comp × Comp, primDefect n x k = 0

/-- `Σ cᵢ bᵢ`. -/
def lincomb : List Int → List Elt → Elt
  | c :: cs, b :: bs => fun I => c * b I + lincomb cs bs I
  | _, _ => fun _ => 0

/-- Linear independence (over `ℤ`, equivalently over `ℚ`) in `NSym_n`. -/
def Indep (n : Nat) (B : List Elt) : Prop :=
  ∀ cs : List Int, cs.length = B.length → (∀ I ∈ comps n, lincomb cs B I = 0) → ∀ c ∈ cs, c = 0

/-- The degree-`n` primitive space has dimension `m`. -/
def PrimDim (n m : Nat) : Prop :=
  (∃ B : List Elt, B.length = m ∧ (∀ b ∈ B, IsPrimitive n b) ∧ Indep n B) ∧
  (∀ B : List Elt, B.length = m + 1 → (∀ b ∈ B, IsPrimitive n b) → ¬ Indep n B)

theorem coeffT_eq_zero_of_not_mem (t : Tens) (k : Comp × Comp) (h : k ∉ t.map Prod.fst) :
    coeffT t k = 0 := by
  induction t with
  | nil => simp [coeffT]
  | cons p t ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have h1 : p.1 ≠ k := fun e => h.1 e.symm
    have := ih h.2
    simp only [coeffT, List.map_cons, List.sum_cons] at this ⊢
    simp [h1, this]

/-- Sanity check: `Δ S_2 = S_2 ⊗ 1 + S_1 ⊗ S_1 + 1 ⊗ S_2` and `Δ S^{(2,1)}` has the six
expected terms. -/
theorem deltaS_examples :
    deltaS [2] = [(([], [2]), 1), (([1], [1]), 1), (([2], []), 1)] ∧
    deltaS [2,1] = [(([], [2,1]), 1), (([1], [2]), 1), (([1], [1,1]), 1), (([1,1], [1]), 1),
      (([2], [1]), 1), (([2,1], []), 1)] := by decide

theorem comps_three : comps 3 = [[1,1,1], [1,2], [2,1], [3]] := by decide

def keys3 : List (Comp × Comp) := (comps 3).flatMap (fun I => (defectS I).map Prod.fst)

def fv (k : Comp × Comp) : Int × Int × Int × Int :=
  (coeffT (defectS [3]) k, coeffT (defectS [2,1]) k, coeffT (defectS [1,2]) k,
    coeffT (defectS [1,1,1]) k)

theorem fv_table : ∀ k ∈ keys3, fv k = (0,0,0,0) ∨ fv k = (1,1,1,0) ∨ fv k = (0,1,1,3) := by
  decide

theorem fv_21 : fv ([2], [1]) = (1,1,1,0) := by decide
theorem fv_111 : fv ([1,1], [1]) = (0,1,1,3) := by decide

theorem fv_not_mem (k : Comp × Comp) (hk : k ∉ keys3) : fv k = (0,0,0,0) := by
  have aux : ∀ I ∈ comps 3, coeffT (defectS I) k = 0 := by
    intro I hI
    apply coeffT_eq_zero_of_not_mem
    intro hm
    exact hk (List.mem_flatMap.mpr ⟨I, hI, hm⟩)
  simp only [comps_three, List.mem_cons, List.mem_nil_iff, or_false] at aux
  simp [fv, aux]

theorem primDefect_three (x : Elt) (k : Comp × Comp) :
    primDefect 3 x k = x [3] * (fv k).1 + x [2,1] * (fv k).2.1 + x [1,2] * (fv k).2.2.1 +
      x [1,1,1] * (fv k).2.2.2 := by
  simp only [primDefect, comps_three, fv, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

/-- **Primitives of degree 3.** `x = a S_3 + b S_{21} + c S_{12} + d S_{111}` is primitive
iff `a + b + c = 0` and `b + c + 3d = 0`. -/
theorem isPrimitive_three_iff (x : Elt) :
    IsPrimitive 3 x ↔ (x [3] + x [2,1] + x [1,2] = 0 ∧ x [2,1] + x [1,2] + 3 * x [1,1,1] = 0) := by
  constructor
  · intro h
    have h1 := h ([2], [1])
    have h2 := h ([1,1], [1])
    rw [primDefect_three, fv_21] at h1
    rw [primDefect_three, fv_111] at h2
    simp at h1 h2
    omega
  · intro ⟨h1, h2⟩ k
    rw [primDefect_three]
    by_cases hk : k ∈ keys3
    · rcases fv_table k hk with e | e | e <;> rw [e] <;> simp <;> omega
    · rw [fv_not_mem k hk]; simp


/-! ## Explicit primitives -/

def ofList (l : List (Comp × Int)) : Elt := fun I => (l.map (fun p => if p.1 = I then p.2 else 0)).sum

/-- The power sum `Ψ_3 = 3 S_3 − S_{21} − 2 S_{12} + S_{111}` (Newton: `3 S_3 = S_2 Ψ_1 + S_1 Ψ_2 + Ψ_3`). -/
def psi3 : Elt := ofList [([3], 3), ([2,1], -1), ([1,2], -2), ([1,1,1], 1)]
/-- The commutator `[S_2, S_1] = S_{21} − S_{12}`. -/
def comm21 : Elt := ofList [([2,1], 1), ([1,2], -1)]

theorem psi3_vals : psi3 [3] = 3 ∧ psi3 [2,1] = -1 ∧ psi3 [1,2] = -2 ∧ psi3 [1,1,1] = 1 := by decide
theorem comm21_vals : comm21 [3] = 0 ∧ comm21 [2,1] = 1 ∧ comm21 [1,2] = -1 ∧ comm21 [1,1,1] = 0 := by
  decide

theorem psi3_prim : IsPrimitive 3 psi3 := by
  rw [isPrimitive_three_iff]; have := psi3_vals; omega

theorem comm21_prim : IsPrimitive 3 comm21 := by
  rw [isPrimitive_three_iff]; have := comm21_vals; omega

theorem indep_psi3_comm21 : Indep 3 [psi3, comm21] := by
  intro cs hlen h
  match cs, hlen with
  | [c1, c2], _ =>
    have e1 := h [3] (by decide)
    have e2 := h [2,1] (by decide)
    simp only [lincomb] at e1 e2
    have := psi3_vals; have := comm21_vals
    simp only [*] at e1 e2
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    omega

theorem indep_psi3 : Indep 3 [psi3] := by
  intro cs hlen h
  match cs, hlen with
  | [c1], _ =>
    have e1 := h [3] (by decide)
    simp only [lincomb] at e1
    have := psi3_vals
    simp only [*] at e1
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    omega

/-- Any three integer vectors in `ℤ²` satisfy a nontrivial integer linear relation. -/
theorem dep3 (d1 d2 d3 b1 b2 b3 : Int) : ∃ c1 c2 c3 : Int, ¬ (c1 = 0 ∧ c2 = 0 ∧ c3 = 0) ∧
    c1 * d1 + c2 * d2 + c3 * d3 = 0 ∧ c1 * b1 + c2 * b2 + c3 * b3 = 0 := by
  by_cases h : d1 * b2 - d2 * b1 = 0
  · by_cases hd : d1 = 0
    · subst hd
      by_cases hb : b1 = 0
      · subst hb
        exact ⟨1, 0, 0, by omega, by omega, by omega⟩
      · refine ⟨b2, -b1, 0, by omega, ?_, ?_⟩
        · simp only [Int.mul_zero, Int.zero_mul, Int.neg_mul, Int.mul_neg, Int.mul_comm] at h ⊢; omega
        · simp only [Int.neg_mul, Int.mul_neg, Int.mul_comm, Int.zero_mul]; omega
    · refine ⟨d2, -d1, 0, by omega, ?_, ?_⟩
      · simp only [Int.neg_mul, Int.mul_neg, Int.mul_comm, Int.zero_mul]; omega
      · simp only [Int.neg_mul, Int.mul_neg, Int.mul_comm, Int.zero_mul] at h ⊢; omega
  · refine ⟨d2 * b3 - d3 * b2, -(d1 * b3 - d3 * b1), d1 * b2 - d2 * b1, by omega, ?_, ?_⟩
    · simp only [Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]; omega
    · simp only [Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]; omega

/-- Any three primitive elements of degree 3 are linearly dependent (explicit relation). -/
theorem three_dep (x y z : Elt) (hx : IsPrimitive 3 x) (hy : IsPrimitive 3 y)
    (hz : IsPrimitive 3 z) : ∃ c1 c2 c3 : Int, ¬ (c1 = 0 ∧ c2 = 0 ∧ c3 = 0) ∧
      ∀ I ∈ comps 3, c1 * x I + c2 * y I + c3 * z I = 0 := by
  rw [isPrimitive_three_iff] at hx hy hz
  obtain ⟨c1, c2, c3, hne, h1, h2⟩ :=
    dep3 (x [1,1,1]) (y [1,1,1]) (z [1,1,1]) (x [2,1]) (y [2,1]) (z [2,1])
  refine ⟨c1, c2, c3, hne, ?_⟩
  have ex : x [3] = 3 * x [1,1,1] := by omega
  have ey : y [3] = 3 * y [1,1,1] := by omega
  have ez : z [3] = 3 * z [1,1,1] := by omega
  have fx : x [1,2] = - x [2,1] - 3 * x [1,1,1] := by omega
  have fy : y [1,2] = - y [2,1] - 3 * y [1,1,1] := by omega
  have fz : z [1,2] = - z [2,1] - 3 * z [1,1,1] := by omega
  intro I hI
  rw [comps_three] at hI
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hI
  rcases hI with rfl | rfl | rfl | rfl
  · exact h1
  · rw [fx, fy, fz]
    simp only [Int.mul_sub, Int.mul_neg, Int.mul_left_comm _ 3]
    omega
  · exact h2
  · rw [ex, ey, ez]
    simp only [Int.mul_left_comm _ 3]
    omega

theorem lincomb_replicate_zero (k : Nat) (B : List Elt) (I : Comp) :
    lincomb (List.replicate k 0) B I = 0 := by
  induction k generalizing B with
  | zero => cases B <;> simp [lincomb]
  | succ k ih =>
    cases B with
    | nil => simp [lincomb]
    | cons b B => simp [List.replicate_succ, lincomb, ih]

theorem not_indep_of_three (x y z : Elt) (rest : List Elt) (hx : IsPrimitive 3 x)
    (hy : IsPrimitive 3 y) (hz : IsPrimitive 3 z) : ¬ Indep 3 (x :: y :: z :: rest) := by
  intro hind
  obtain ⟨c1, c2, c3, hne, hrel⟩ := three_dep x y z hx hy hz
  have hall := hind (c1 :: c2 :: c3 :: List.replicate rest.length 0) (by simp) (by
    intro I hI
    simp only [lincomb, lincomb_replicate_zero]
    have := hrel I hI
    omega)
  apply hne
  refine ⟨hall c1 (by simp), hall c2 (by simp), hall c3 (by simp)⟩

/-- **The degree-3 primitive space of NSym has dimension 2.** -/
theorem primDim_three : PrimDim 3 2 := by
  refine ⟨⟨[psi3, comm21], rfl, ?_, indep_psi3_comm21⟩, ?_⟩
  · intro b hb
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl
    · exact psi3_prim
    · exact comm21_prim
  · intro B hlen hprim
    match B, hlen with
    | [x, y, z], _ =>
      exact not_indep_of_three x y z [] (hprim x (by simp)) (hprim y (by simp)) (hprim z (by simp))

/-- The dimension is unique: `PrimDim 3 m` forces `m = 2`. -/
theorem primDim_three_unique (m : Nat) (h : PrimDim 3 m) : m = 2 := by
  obtain ⟨⟨B, hlen, hprim, hind⟩, hmax⟩ := h
  match m, hlen, hmax with
  | 0, _, hmax =>
    exact absurd indep_psi3 (hmax [psi3] rfl (by simp [psi3_prim]))
  | 1, _, hmax =>
    exact absurd indep_psi3_comm21
      (hmax [psi3, comm21] rfl (by simp [psi3_prim, comm21_prim]))
  | 2, _, _ => rfl
  | k + 3, hlen, _ =>
    match B, hlen with
    | x :: y :: z :: rest, _ =>
      exact absurd hind (not_indep_of_three x y z rest (hprim x (by simp))
        (hprim y (by simp)) (hprim z (by simp)))


/-! ## Eulerian numbers -/

/-- Insert `a` at every position of a list. -/
def insertAll (a : Nat) : List Nat → List (List Nat)
  | [] => [[a]]
  | b :: l => (a :: b :: l) :: (insertAll a l).map (b :: ·)

/-- All permutations of `[1, …, n]` (as lists). -/
def perms : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (perms n).flatMap (insertAll (n + 1))

def descents : List Nat → Nat
  | a :: b :: l => (if b < a then 1 else 0) + descents (b :: l)
  | _ => 0

def ascents : List Nat → Nat
  | a :: b :: l => (if a < b then 1 else 0) + ascents (b :: l)
  | _ => 0

/-- `A(n,k)`: permutations with `k` descents (Concrete Mathematics convention). -/
def eulerDes0 (n k : Nat) : Nat := (perms n).countP (fun p => descents p == k)
/-- `A(n,k)`, 1-based (OEIS A008292): permutations with `k` ascending runs (`k-1` descents). -/
def eulerDes1 (n k : Nat) : Nat := (perms n).countP (fun p => descents p + 1 == k)
/-- Ascent versions of the two conventions. -/
def eulerAsc0 (n k : Nat) : Nat := (perms n).countP (fun p => ascents p == k)
def eulerAsc1 (n k : Nat) : Nat := (perms n).countP (fun p => ascents p + 1 == k)

theorem perms_three : perms 3 = [[3,2,1],[2,3,1],[2,1,3],[3,1,2],[1,3,2],[1,2,3]] := by decide

theorem perms_three_complete : ∀ a ∈ [0,1,2,3], ∀ b ∈ [0,1,2,3], ∀ c ∈ [0,1,2,3],
    ([a, b, c] ∈ perms 3 ↔ (1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c)) := by decide

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `perms n` lists `n!` distinct lists, each a permutation of `[1, …, n]`. -/
theorem perms_valid : ∀ n ∈ [0,1,2,3,4,5], (perms n).length = fact n ∧ (perms n).Nodup ∧
    ∀ p ∈ perms n, p.length = n ∧ ∀ i ∈ List.range n, (i + 1) ∈ p := by decide +kernel


theorem eulerian_three : eulerDes0 3 1 = 4 ∧ eulerDes1 3 1 = 1 ∧ eulerAsc0 3 1 = 4 ∧ eulerAsc1 3 1 = 1 := by
  decide

/-- The value 2 is never an Eulerian number `A(m,1)` for `m ≤ 6`, under any of the
four conventions (so no index shift can rescue the clause at degree 3 in this range). -/
theorem eulerian_ne_two : ∀ m ∈ [0,1,2,3,4,5,6],
    eulerDes0 m 1 ≠ 2 ∧ eulerDes1 m 1 ≠ 2 ∧ eulerAsc0 m 1 ≠ 2 ∧ eulerAsc1 m 1 ≠ 2 := by
  decide +kernel

/-! ## The conjecture's dimension clause and its refutation -/

/-- The clause: for every `n ≥ 1`, the degree-`n` primitive space of NSym has dimension `A(n,1)`. -/
def DimClause (A : Nat → Nat → Nat) : Prop := ∀ n, 1 ≤ n → PrimDim n (A n 1)

theorem dimClause_false_of (A : Nat → Nat → Nat) (hA : A 3 1 ≠ 2) : ¬ DimClause A := by
  intro h
  exact hA (primDim_three_unique _ (h 3 (by decide)))

theorem conjecture_00000000438_false :
    ¬ DimClause eulerDes0 ∧ ¬ DimClause eulerDes1 ∧ ¬ DimClause eulerAsc0 ∧
      ¬ DimClause eulerAsc1 := by
  obtain ⟨h1, h2, h3, h4⟩ := eulerian_three
  exact ⟨dimClause_false_of _ (by omega), dimClause_false_of _ (by omega),
    dimClause_false_of _ (by omega), dimClause_false_of _ (by omega)⟩

/-- Robust form: in degree 3 the dimension is 2, which differs from `A(m,1)` for every
`m ≤ 6` and every convention. -/
theorem conjecture_00000000438_false_degree3 :
    PrimDim 3 2 ∧ (∀ m, PrimDim 3 m → m = 2) ∧
    ∀ m ∈ [0,1,2,3,4,5,6], ¬ PrimDim 3 (eulerDes0 m 1) ∧ ¬ PrimDim 3 (eulerDes1 m 1) ∧
      ¬ PrimDim 3 (eulerAsc0 m 1) ∧ ¬ PrimDim 3 (eulerAsc1 m 1) := by
  refine ⟨primDim_three, primDim_three_unique, ?_⟩
  intro m hm
  obtain ⟨h1, h2, h3, h4⟩ := eulerian_ne_two m hm
  exact ⟨fun h => h1 (primDim_three_unique _ h), fun h => h2 (primDim_three_unique _ h),
    fun h => h3 (primDim_three_unique _ h), fun h => h4 (primDim_three_unique _ h)⟩

end NSym

#print axioms NSym.isPrimitive_three_iff
#print axioms NSym.primDim_three
#print axioms NSym.primDim_three_unique
#print axioms NSym.eulerian_three
#print axioms NSym.eulerian_ne_two
#print axioms NSym.conjecture_00000000438_false
#print axioms NSym.conjecture_00000000438_false_degree3
