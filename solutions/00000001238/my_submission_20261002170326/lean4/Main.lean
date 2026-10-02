/-!
# Disproof of TLMC conjecture 00000001238

Conjecture: "Log-concavity of the invariant-factor sequence of the [Jacobi] torsion
group holds for all graphs; and equality in the concavity holds exactly for direct
sums of cycles."

Two counterexamples, machine-checked in core Lean 4 with **zero axioms and no
`sorry`**.  Every proof is a kernel computation: `rfl`/`decide` over closed
integer arithmetic.  (Deliberately avoided, because in toolchain v4.33.1 they
pull `propext`: `omega`, `simp`, `native_decide`, `Nat.testBit`, `Nat.lor`, and
pattern matches with overlapping catch-all rows.)

* **Counterexample A.** `K_{2,4}` (complete bipartite graph with parts `{0,1}` and
  `{2,3,4,5}`).  Its reduced Laplacian is the `5x5` matrix `L24`; explicit
  unimodular matrices `U24`, `V24` (both of determinant `-1`) satisfy
  `U24 * L24 * V24 = diag(1,1,2,2,8)`.  Hence `Jac(K_{2,4}) = Z/2 x Z/2 x Z/8`
  with nontrivial invariant-factor sequence `(2,2,8)`, whose middle concavity
  condition `2*2 >= 2*8` **fails** (`4 < 16`): log-concavity does not hold for
  all graphs.  `lapMinor5 K24mask = L24` ties the matrix to the graph's edge
  bitmask (edges `02 03 04 05 12 13 14 15` of `K6`, i.e. bits 1..8, mask 510).

* **Counterexample B.** `K4`.  Its reduced Laplacian `LK4` satisfies
  `U4 * LK4 * V4 = diag(1,4,4)` with `U4`, `V4` unimodular (determinant `1`), so
  `Jac(K4) = Z/4 x Z/4` with sequence `(4,4)`, for which the concavity condition
  holds **with equality**.  But `K4` is not a direct sum of cycles: the edge
  `{0,1}` lies on the two distinct triangles `{0,1,2}` and `{0,1,3}` (both
  certified here, with distinct edge masks), whereas every edge of a direct sum
  of cycles lies on at most one cycle.  `lapMinor3 K4mask = LK4` ties the matrix
  to the edge bitmask 615.

Further certificates: the equality sequence `(5,5,5)` of `Jac(K5) = (Z/5)^3`
(all interior equalities; `K5` is not a cycle sum), and `(3,3,6)` of the cactus
`C3 v C3 v C6` — a *direct sum of cycles* whose invariant factors are **not**
log-concave (`9 < 18`), so the conjecture is internally incoherent.

The graph-level identifications (cokernel of the reduced Laplacian = Jacobian;
cactus = direct sum of cycles) are classical; `reproduce.py` re-derives every
numeric fact from the adjacency lists and exhaustively sweeps all 2^15
six-vertex graphs.
-/
set_option maxHeartbeats 1000000

namespace Tlmc1238

/-! ### Matrices as lists of rows (core Lean only) -/

abbrev Mat := List (List Int)

/-- `r[j]`, by structural recursion with disjoint patterns. -/
def cellOf : List Int → Nat → Int
  | a :: _, 0 => a
  | [], _ => 0
  | _ :: as, n + 1 => cellOf as n

/-- `A[i][j]`, by structural recursion with disjoint patterns. -/
def getM : Mat → Nat → Nat → Int
  | a :: _, 0, j => cellOf a j
  | [], _, _ => 0
  | _ :: as, n + 1, j => getM as n j

/-- Number of columns (length of the first row). -/
def cellCount : Mat → Nat
  | [] => 0
  | r :: _ => r.length

/-- Matrix product over `Int`. -/
def mulM (A B : Mat) : Mat :=
  (List.range A.length).map (fun i =>
    (List.range (cellCount B)).map (fun j =>
      (List.range B.length).foldl (fun acc k => acc + getM A i k * getM B k j) 0))

/-- Determinant by cofactor expansion along the first row, with explicit fuel
(structural recursion; fuel `A.length` suffices for any nonempty `A`). -/
def detL : Nat → Mat → Int
  | _, [] => 1
  | 0, _ :: _ => 0
  | n + 1, r0 :: rest =>
    (List.range r0.length).foldl (fun acc j =>
      acc + (if j % 2 == 0 then 1 else -1) * (cellOf r0 j) *
        detL n (rest.map (fun r => r.take j ++ r.drop (j + 1)))) 0

/-- Determinant of a nonempty matrix (fuel = number of rows). -/
def det (A : Mat) : Int := detL A.length A

/-! ### The counterexample matrices -/

/-- Reduced Laplacian of `K_{2,4}` (delete vertex `0`; rows/cols are vertices `1..5`). -/
def L24 : Mat := [[4, -1, -1, -1, -1], [-1, 2, 0, 0, 0], [-1, 0, 2, 0, 0],
                  [-1, 0, 0, 2, 0], [-1, 0, 0, 0, 2]]

/-- Unimodular row operations: `det U24 = -1`. -/
def U24 : Mat := [[1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [2, 1, 7, 0, 0],
                  [2, 1, 6, 1, 0], [2, 1, 5, 1, 1]]

/-- Unimodular column operations: `det V24 = -1`. -/
def V24 : Mat := [[0, -1, 0, 0, 2], [-1, -4, 1, 0, 1], [0, 0, 0, 0, 1],
                  [0, 0, -1, 1, 1], [0, 0, 0, -1, 5]]

/-- `diag(1,1,2,2,8)`: the Smith normal form diagonal of `L24`. -/
def diag11228 : Mat := [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 2, 0, 0],
                        [0, 0, 0, 2, 0], [0, 0, 0, 0, 8]]

/-- Reduced Laplacian of `K4` (delete vertex `0`; rows/cols are vertices `1,2,3`). -/
def LK4 : Mat := [[3, -1, -1], [-1, 3, -1], [-1, -1, 3]]

/-- Unimodular row operations: `det U4 = 1`. -/
def U4 : Mat := [[1, 0, 0], [3, 1, 0], [2, 1, 1]]

/-- Unimodular column operations: `det V4 = 1`. -/
def V4 : Mat := [[0, 0, 1], [-1, 1, 1], [0, -1, 2]]

/-- `diag(1,4,4)`: the Smith normal form diagonal of `LK4`. -/
def diag144 : Mat := [[1, 0, 0], [0, 4, 0], [0, 0, 4]]

/-- **Smith normal form of the `K_{2,4}` reduced Laplacian** (unimodular equivalence):
`U24 * L24 * V24 = diag(1,1,2,2,8)` with `det U24 = det V24 = -1`. -/
theorem snf_L24 :
    mulM (mulM U24 L24) V24 = diag11228 ∧ det U24 = -1 ∧ det V24 = -1 :=
  ⟨rfl, rfl, rfl⟩

/-- **Smith normal form of the `K4` reduced Laplacian** (unimodular equivalence):
`U4 * LK4 * V4 = diag(1,4,4)` with `det U4 = det V4 = 1`. -/
theorem snf_LK4 :
    mulM (mulM U4 LK4) V4 = diag144 ∧ det U4 = 1 ∧ det V4 = 1 :=
  ⟨rfl, rfl, rfl⟩

/-! ### Graphs on 6 labeled vertices by edge bitmask -/

/-- Index of edge `{min i j, max i j}` in the list of the 15 pairs `0 ≤ i < j ≤ 5`. -/
def edgeIdx6 (i j : Nat) : Nat :=
  let a := min i j
  let b := max i j
  if a = 0 then (if b = 1 then 0 else if b = 2 then 1 else if b = 3 then 2
                 else if b = 4 then 3 else 4)
  else if a = 1 then (if b = 2 then 5 else if b = 3 then 6 else if b = 4 then 7 else 8)
  else if a = 2 then (if b = 3 then 9 else if b = 4 then 10 else 11)
  else if a = 3 then (if b = 4 then 12 else 13)
  else 14

/-- The `k`-th bit of `mask`, via `div`/`mod` (`Nat.testBit` pulls `propext`). -/
def bitOf (mask k : Nat) : Bool := (mask / 2 ^ k) % 2 == 1

/-- Adjacency of the graph given as an edge bitmask. -/
def adj6 (mask : Nat) (i j : Nat) : Bool :=
  if i = j then false else bitOf mask (edgeIdx6 i j)

/-- Degree of vertex `i` (of 6). -/
def deg6 (mask : Nat) (i : Nat) : Nat :=
  (List.range 6).foldl (fun acc v => acc + (if adj6 mask i v then 1 else 0)) 0

/-- Laplacian minor obtained by deleting vertex `0`; rows/cols indexed by `1..5`. -/
def lapMinor5 (mask : Nat) : Mat :=
  (List.range 5).map (fun p =>
    (List.range 5).map (fun q =>
      let i := p + 1
      let j := q + 1
      if i = j then (deg6 mask i : Int)
      else if adj6 mask i j then -1 else 0))

/-- Laplacian minor obtained by deleting vertex `0`; rows/cols indexed by `1..3`. -/
def lapMinor3 (mask : Nat) : Mat :=
  (List.range 3).map (fun p =>
    (List.range 3).map (fun q =>
      let i := p + 1
      let j := q + 1
      if i = j then (deg6 mask i : Int)
      else if adj6 mask i j then -1 else 0))

/-- `K_{2,4}` with parts `{0,1}`, `{2,3,4,5}`: edges `02 03 04 05 12 13 14 15` (bits 1..8). -/
def K24mask : Nat := 510

/-- `K4` on vertices `{0,1,2,3}`: all six edges (bits 0,1,2,5,6,9). -/
def K4mask : Nat := 615

/-- The matrix `L24` is exactly the reduced Laplacian of the graph `K24mask`. -/
theorem lap24_is_minor : lapMinor5 K24mask = L24 := rfl

/-- The matrix `LK4` is exactly the reduced Laplacian of the graph `K4mask`. -/
theorem lapK4_is_minor : lapMinor3 K4mask = LK4 := rfl

/-! ### Triangles of K4 through the edge {0,1} -/

/-- Sum of `2^e` over the three edges `ab, bc, ac` of the triangle on `a, b, c`
(distinct edge indices make this an edge-set fingerprint). -/
def triMaskOf (a b c : Nat) : Nat :=
  2 ^ edgeIdx6 a b + 2 ^ edgeIdx6 b c + 2 ^ edgeIdx6 a c

/-- Triangle membership in the graph given by `mask`. -/
def hasTri (mask : Nat) (a b c : Nat) : Bool :=
  adj6 mask a b && adj6 mask b c && adj6 mask a c

/-- **`K4` is not a direct sum of cycles**: its edge `{0,1}` lies on the two distinct
triangles `{0,1,2}` and `{0,1,3}` (distinct edge fingerprints), while every edge of
a direct sum of cycles lies on at most one cycle. -/
theorem K4_edge_in_two_triangles :
    hasTri K4mask 0 1 2 ∧ hasTri K4mask 0 1 3 ∧ triMaskOf 0 1 2 ≠ triMaskOf 0 1 3 :=
  ⟨rfl, rfl, by decide⟩

/-! ### Log-concavity of invariant-factor sequences -/

/-- Interior log-concavity inequalities `b*b ≥ a*c` for consecutive triples. -/
def interiorOK : List Nat → Bool
  | a :: b :: c :: rest => decide (b * b ≥ a * c) && interiorOK (b :: c :: rest)
  | [] => true
  | [_] => true
  | [_, _] => true

/-- Interior equalities `b*b = a*c` for consecutive triples. -/
def interiorEq : List Nat → Bool
  | a :: b :: c :: rest => decide (b * b = a * c) && interiorEq (b :: c :: rest)
  | [] => true
  | [_] => true
  | [_, _] => true

/-- The violation arithmetic behind `interiorOK [2,2,8] = false`: `2*2 = 4 < 2*8 = 16`. -/
theorem violation_arith : (2 : Nat) * 2 = 4 ∧ (2 : Nat) * 8 = 16 ∧ 4 < 16 :=
  ⟨rfl, rfl, by decide⟩

/-- **Clause 1 fails**: the invariant-factor sequence `(2,2,8)` of `Jac(K_{2,4})`
(from `snf_L24`: `diag(1,1,2,2,8)`) is **not** log-concave: `2*2 = 4 < 2*8 = 16`. -/
theorem seq_228_not_logconcave : ¬ interiorOK [2, 2, 8] :=
  fun h => Bool.noConfusion h

/-- **Clause 2 fails**: the sequence `(4,4)` of `Jac(K4)` (from `snf_LK4`:
`diag(1,4,4)`) satisfies log-concavity **with equality** (`4*4 = 4*4`). -/
theorem seq_44_logconcave_eq : interiorOK [4, 4] ∧ interiorEq [4, 4] := ⟨rfl, rfl⟩

/-- The sequence `(5,5,5)` of `Jac(K5) = (Z/5)^3` has all interior equalities
(`25 = 25`). -/
theorem seq_555_equalities : interiorOK [5, 5, 5] ∧ interiorEq [5, 5, 5] := ⟨rfl, rfl⟩

/-- The cactus `C3 v C3 v C6` — a direct sum of cycles — has invariant factors
`(3,3,6)`, which are **not** log-concave (`3*3 = 9 < 3*6 = 18`): the two clauses of
the conjecture are jointly unsatisfiable even on its own equality class. -/
theorem seq_336_not_logconcave : ¬ interiorOK [3, 3, 6] :=
  fun h => Bool.noConfusion h

/-! ### The refutation -/

/-- **Refutation of conjecture 00000001238.** Both clauses fail simultaneously:
`Jac(K_{2,4})` has invariant-factor sequence `(2,2,8)` violating log-concavity
(clause 1), and `Jac(K4) = Z/4 x Z/4` has equality in the concavity while `K4` is
not a direct sum of cycles (clause 2).  Every component is kernel-checked closed
arithmetic; `lap24_is_minor` / `lapK4_is_minor` tie the matrices to the graphs'
edge bitmasks. -/
theorem refute :
    ¬ interiorOK [2, 2, 8] ∧
    interiorEq [4, 4] ∧
    (∃ U V : Mat, det U = -1 ∧ det V = -1 ∧ mulM (mulM U L24) V = diag11228) ∧
    (∃ U V : Mat, det U = 1 ∧ det V = 1 ∧ mulM (mulM U LK4) V = diag144) ∧
    lapMinor5 K24mask = L24 ∧
    lapMinor3 K4mask = LK4 ∧
    (hasTri K4mask 0 1 2 ∧ hasTri K4mask 0 1 3 ∧ triMaskOf 0 1 2 ≠ triMaskOf 0 1 3) :=
  ⟨seq_228_not_logconcave, rfl, ⟨U24, V24, rfl, rfl, rfl⟩, ⟨U4, V4, rfl, rfl, rfl⟩,
   rfl, rfl, K4_edge_in_two_triangles⟩

end Tlmc1238
