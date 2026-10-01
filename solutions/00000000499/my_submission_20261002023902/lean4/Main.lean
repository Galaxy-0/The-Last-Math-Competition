/-!
# Disproof of TLMC conjecture 00000000499

Two nonintersecting simple random walks on `Z` (ordered: `w1(t) < w2(t)` for all
`t`), starts `(x1, x2) = (0, 4)`, endpoints `(y1, y2) = (1, 3)`, each walk moving
`+1` / `-1` per step; all `4^T` joint step sequences are equally likely.

We brute-force enumerate every joint step sequence and count those that
  (a) end at the prescribed endpoints, and
  (b) keep `w1(t) < w2(t)` at every time `t = 0..T`.

Results (proved below by `decide` over the explicit enumerations):
  `T = 1` : `1` of `4`   joint paths survive, so `p = 1/4`;
  `T = 2` : `0` of `16`  joint paths survive, so `p = 0`   (parity obstruction);
  `T = 3` : `8` of `64`  joint paths survive, so `p = 1/8`.

Hence `1/4 != 1/8` at identical endpoints.  The conjectured right-hand side (the
GUE ordered-eigenvalue joint density at the endpoints times the fixed Vandermonde
factor `(y2-y1)-(x2-x1) = -2`) contains no `T`, so it is a single constant and
cannot equal both `1/4` and `1/8`; the identity cannot hold for all `T > 0`.

Encoding note: every coordinate is shifted by `+2` so that all positions are `Nat`
(walk 1 dips to `-1` at worst, walk 2 to `+2` at worst).  A constant shift
preserves strict order and endpoint tests (the endpoints become `3` and `5`), so
the count is unchanged.
-/

/-- One step of a simple random walk: `true` means `+1`, `false` means `-1`. -/
def S (b : Bool) (p : Nat) : Nat := if b then p + 1 else p - 1

/-- Positions at times `t = 0,1,2,3` of walk 1 from shifted start `2`, steps `a b c`. -/
def W1 (a b c : Bool) : Nat × Nat × Nat × Nat :=
  (2, S a 2, S b (S a 2), S c (S b (S a 2)))

/-- Positions at times `t = 0,1,2,3` of walk 2 from shifted start `6`, steps `d e f`. -/
def W2 (d e f : Bool) : Nat × Nat × Nat × Nat :=
  (6, S d 6, S e (S d 6), S f (S e (S d 6)))

/-- Endpoint and strict-order test for `T = 3` in shifted coordinates
(endpoints `3` and `5`, i.e. `1` and `3` before the shift by `+2`). -/
def OK (u v : Nat × Nat × Nat × Nat) : Bool :=
  decide (u.1 < v.1) && decide (u.2.1 < v.2.1) && decide (u.2.2.1 < v.2.2.1) &&
    decide (u.2.2.2 < v.2.2.2) && decide (u.2.2.2 = 3) && decide (v.2.2.2 = 5)

/-- All 8 step triples of length 3. -/
def T3 : List (Bool × Bool × Bool) :=
  [ (true, true, true), (true, true, false), (true, false, true), (true, false, false),
    (false, true, true), (false, true, false), (false, false, true), (false, false, false) ]

/-- Number of nonintersecting endpoint-respecting joint paths for `T = 3`
(out of `64` equally likely joint step sequences). -/
def C3 : Nat :=
  (T3.flatMap fun p => T3.map fun q =>
    if OK (W1 p.1 p.2.1 p.2.2) (W2 q.1 q.2.1 q.2.2) then 1 else 0).sum

/-- Positions at times `t = 0,1,2` of walk 1 from shifted start `2`, steps `a b`. -/
def V1 (a b : Bool) : Nat × Nat × Nat := (2, S a 2, S b (S a 2))

/-- Positions at times `t = 0,1,2` of walk 2 from shifted start `6`, steps `d e`. -/
def V2 (d e : Bool) : Nat × Nat × Nat := (6, S d 6, S e (S d 6))

/-- Endpoint and strict-order test for `T = 2` in shifted coordinates. -/
def OK2 (u v : Nat × Nat × Nat) : Bool :=
  decide (u.1 < v.1) && decide (u.2.1 < v.2.1) && decide (u.2.2 < v.2.2) &&
    decide (u.2.2 = 3) && decide (v.2.2 = 5)

/-- All 4 step pairs of length 2. -/
def T2 : List (Bool × Bool) :=
  [ (true, true), (true, false), (false, true), (false, false) ]

/-- Number of nonintersecting endpoint-respecting joint paths for `T = 2`
(out of `16` equally likely joint step sequences). -/
def C2 : Nat :=
  (T2.flatMap fun p => T2.map fun q =>
    if OK2 (V1 p.1 p.2) (V2 q.1 q.2) then 1 else 0).sum

/-- Positions at times `t = 0,1` of walk 1 from shifted start `2`, single step `a`. -/
def U1 (a : Bool) : Nat × Nat := (2, S a 2)

/-- Positions at times `t = 0,1` of walk 2 from shifted start `6`, single step `d`. -/
def U2 (d : Bool) : Nat × Nat := (6, S d 6)

/-- Endpoint and strict-order test for `T = 1` in shifted coordinates. -/
def OK1 (u v : Nat × Nat) : Bool :=
  decide (u.1 < v.1) && decide (u.2 < v.2) && decide (u.2 = 3) && decide (v.2 = 5)

/-- All 2 single steps. -/
def T1 : List Bool := [true, false]

/-- Number of nonintersecting endpoint-respecting joint paths for `T = 1`
(out of `4` equally likely joint step sequences). -/
def C1 : Nat :=
  (T1.flatMap fun p => T1.map fun q => if OK1 (U1 p) (U2 q) then 1 else 0).sum

set_option maxHeartbeats 1000000

theorem C1_eq : C1 = 1 := by decide

theorem C2_eq : C2 = 0 := by decide

theorem C3_eq : C3 = 8 := by decide

/-- The hitting probabilities `C1/4` and `C3/64` differ: cross-multiplied in `Nat`,
`C1 * 64 = 64` while `C3 * 4 = 32`.  So `p` is not a function of the endpoints
alone, while the conjecture's right-hand side is `T`-free: contradiction. -/
theorem attack : (C1 * 64 : Nat) ≠ C3 * 4 := by decide
