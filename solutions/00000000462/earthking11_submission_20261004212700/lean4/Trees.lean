/-
  The circulant graph `C_n(1,2)` and its spanning trees, by exhaustive enumeration.

  `Main.lean` formalises the sequence `τ` through its exact closed form
  `τ(n) = n·(L(2n) + 2·(−1)^(n+1))/5` and proves the recurrence and the algebraic
  obstruction.  This file closes the remaining gap between that closed form and
  the conjecture's own object: it defines the graph `C_n(1,2)`, defines what a
  spanning tree of it is, enumerates them, and certifies that the enumeration
  agrees with the closed form for `n = 5, 6, 7`.

  For general `n` the identification of the closed form with the spanning-tree
  count rests on the matrix-tree theorem and the unit-root product, which are
  classical and are proved in full in `main.tex` §I.
-/
import Main

namespace Tlmc462

set_option maxRecDepth 1000000

/-! ## The graph `C_n(1,2)` -/

/-- The unordered edge set of the circulant graph `C_n(1,2)`: the pairs `i < j`
with `j - i ∈ {1, 2, n-1, n-2}`, i.e. `j - i ≡ ±1` or `±2 (mod n)`.  For
`n ≥ 5` the four distances are distinct, so each edge is listed once. -/
def edgesC (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i =>
    (List.range n).filterMap fun j =>
      if i < j then
        (let d := j - i
         if d == 1 || d == 2 || d == n - 1 || d == n - 2 then some (i, j) else none)
      else none

/-- `adj S u v` : some edge of `S` joins `u` and `v`. -/
def adj (S : List (Nat × Nat)) (u v : Nat) : Bool :=
  S.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

/-- The vertices reachable from `0` in at most `k` rounds, where one round adds
every vertex adjacent to an already reachable one. -/
def reachFrom (n : Nat) (S : List (Nat × Nat)) : Nat → List Nat
  | 0 => [0]
  | k + 1 =>
    let acc := reachFrom n S k
    (List.range n).filter fun v => acc.contains v || acc.any (fun u => adj S u v)

/-- `S` connects all `n` vertices. -/
def connected (n : Nat) (S : List (Nat × Nat)) : Bool :=
  (reachFrom n S n).length == n

/-! ## Spanning trees by enumeration -/

/-- All sublists of a list (the powerset). -/
def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => let r := sublists xs; r ++ r.map (fun ys => x :: ys)

/-- A spanning tree of `C_n(1,2)` is a set of `n-1` edges connecting all `n`
vertices.  The edge count and connectivity together force acyclicity. -/
def isSpanningTree (n : Nat) (S : List (Nat × Nat)) : Bool :=
  if S.length == n - 1 then connected n S else false

/-- **The conjecture's own object**: the list of all spanning trees of
`C_n(1,2)`, obtained by exhaustive enumeration of all subgraphs. -/
def spanningTrees (n : Nat) : List (List (Nat × Nat)) :=
  (sublists (edgesC n)).filter (isSpanningTree n)

/-- `C_5(1,2)` has ten edges: it is `K_5`. -/
theorem edgesC_5 : (edgesC 5).length = 10 := rfl

/-- `C_6(1,2)` has twelve edges. -/
theorem edgesC_6 : (edgesC 6).length = 12 := rfl

/-- `C_7(1,2)` has fourteen edges. -/
theorem edgesC_7 : (edgesC 7).length = 14 := rfl

set_option maxHeartbeats 0 in
/-- `C_5(1,2) = K_5` has `5³ = 125` spanning trees (Cayley), by enumeration. -/
theorem trees_5 : (spanningTrees 5).length = 125 := rfl

set_option maxHeartbeats 0 in
/-- `C_6(1,2)` has `384` spanning trees, by enumeration of all `2¹²`
subgraphs. -/
theorem trees_6 : (spanningTrees 6).length = 384 := rfl

set_option maxHeartbeats 0 in
/-- `C_7(1,2)` has `1183` spanning trees, by enumeration of all `2¹⁴`
subgraphs. -/
theorem trees_7 : (spanningTrees 7).length = 1183 := rfl

/-! ## The closed form agrees with the enumeration

`tau_5`, `tau_6`, `tau_7` in `Main.lean` certify the closed-form values
`125, 384, 1183`; the three theorems below certify that the *actual* spanning
tree enumeration produces the same numbers. -/

/-- The closed form and the true spanning-tree count agree at `n = 5`. -/
theorem tau_eq_trees_5 : tau 5 = ((spanningTrees 5).length : Int) := by
  rw [tau_5, trees_5]
  rfl

/-- The closed form and the true spanning-tree count agree at `n = 6`. -/
theorem tau_eq_trees_6 : tau 6 = ((spanningTrees 6).length : Int) := by
  rw [tau_6, trees_6]
  rfl

/-- The closed form and the true spanning-tree count agree at `n = 7`. -/
theorem tau_eq_trees_7 : tau 7 = ((spanningTrees 7).length : Int) := by
  rw [tau_7, trees_7]
  rfl

/-- **The bridge, made explicit.**  For `n = 5, 6, 7` the sequence `τ` defined by
the closed form in `Main.lean` is exactly the number of spanning trees of
`C_n(1,2)`, certified by exhaustive enumeration of the graph's subgraphs.  This
is the finite-range kernel-checked counterpart of the matrix-tree computation in
`main.tex` §I, which supplies the general `n`. -/
theorem tau_matches_spanningTrees :
    tau 5 = ((spanningTrees 5).length : Int)
      ∧ tau 6 = ((spanningTrees 6).length : Int)
      ∧ tau 7 = ((spanningTrees 7).length : Int) :=
  ⟨tau_eq_trees_5, tau_eq_trees_6, tau_eq_trees_7⟩

end Tlmc462
