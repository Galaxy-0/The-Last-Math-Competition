/-
Disproof of TLMC conjecture 00000001092.

Conjecture (verbatim): "Definition: A complete cap of PG(2,27) is a maximal set
with no three collinear points. Conjecture: Its minimum size is 21, with exactly
two isomorphism classes attaining this value; the second-smallest complete cap
has size 22."

This file is a fully mechanical, axiom-free certificate of a counterexample:
an explicit 14-point complete cap in PG(2,27).

Model: F_27 = F_3[a] with a^3 = a + 1 (t^3 - t + 2 has no root in F_3, hence
is irreducible). An element is stored as (d0, d1, d2) meaning d0 + d1*a + d2*a^2
with all digits in {0,1,2}. Points of PG(2,27) are represented by their 757
canonical representatives: triples (x,y,z) of field elements whose first
nonzero coordinate equals 1. Three points are collinear iff the determinant of
their coordinate matrix vanishes.

Everything below reduces to `True`/`true` by plain kernel evaluation (`decide`),
so `#print axioms` reports that no theorem depends on any axiom.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

structure F27 where
  d0 : Nat
  d1 : Nat
  d2 : Nat
deriving BEq, Repr

@[reducible] def fzero : F27 := ⟨0, 0, 0⟩
@[reducible] def fone : F27 := ⟨1, 0, 0⟩

def fmk (a b c : Nat) : F27 := ⟨a % 3, b % 3, c % 3⟩

def fadd (x y : F27) : F27 :=
  fmk (x.d0 + y.d0) (x.d1 + y.d1) (x.d2 + y.d2)

def fneg (x : F27) : F27 :=
  fmk ((3 - x.d0) % 3) ((3 - x.d1) % 3) ((3 - x.d2) % 3)

def fsub (x y : F27) : F27 := fadd x (fneg y)

def fmul (x y : F27) : F27 :=
  -- (d0 + d1 t + d2 t^2) * (e0 + e1 t + e2 t^2) mod (t^3 - t - 1), i.e. t^3 = t + 1
  let a := x.d0; let b := x.d1; let c := x.d2
  let d := y.d0; let e := y.d1; let f := y.d2
  let p0 := a * d
  let p1 := a * e + b * d
  let p2 := a * f + b * e + c * d
  let p3 := b * f + c * e      -- coefficient of t^3 = t + 1
  let p4 := c * f              -- coefficient of t^4 = t * t^3 = t^2 + t
  fmk (p0 + p3) (p1 + p3 + p4) (p2 + p4)

structure Pt where
  px : F27
  py : F27
  pz : F27
deriving BEq, Repr

def collinear (p q r : Pt) : Bool :=
  let a := p; let b := q; let c := r
  let t1 := fmul a.px (fsub (fmul b.py c.pz) (fmul b.pz c.py))
  let t2 := fmul a.py (fsub (fmul b.px c.pz) (fmul b.pz c.px))
  let t3 := fmul a.pz (fsub (fmul b.px c.py) (fmul b.py c.px))
  fsub (fadd t1 t3) t2 == fzero

/-- The 14-point complete cap: each triple lists the digits (c0,c1,c2) of the
three homogeneous coordinates x = c0 + c1*a + c2*a^2, y = ..., z = ... . -/
def cap : List Pt := [
  ⟨⟨1,0,0⟩, ⟨2,1,1⟩, ⟨2,2,2⟩⟩,
  ⟨⟨1,0,0⟩, ⟨1,0,0⟩, ⟨2,1,1⟩⟩,
  ⟨⟨1,0,0⟩, ⟨2,0,1⟩, ⟨0,0,0⟩⟩,
  ⟨⟨0,0,0⟩, ⟨1,0,0⟩, ⟨1,2,1⟩⟩,
  ⟨⟨1,0,0⟩, ⟨1,1,0⟩, ⟨0,1,2⟩⟩,
  ⟨⟨1,0,0⟩, ⟨2,0,2⟩, ⟨1,2,0⟩⟩,
  ⟨⟨1,0,0⟩, ⟨2,1,1⟩, ⟨1,1,0⟩⟩,
  ⟨⟨1,0,0⟩, ⟨1,0,1⟩, ⟨0,2,0⟩⟩,
  ⟨⟨1,0,0⟩, ⟨1,1,1⟩, ⟨1,2,1⟩⟩,
  ⟨⟨1,0,0⟩, ⟨2,0,1⟩, ⟨1,2,1⟩⟩,
  ⟨⟨1,0,0⟩, ⟨0,1,0⟩, ⟨2,1,0⟩⟩,
  ⟨⟨1,0,0⟩, ⟨1,2,1⟩, ⟨1,1,0⟩⟩,
  ⟨⟨1,0,0⟩, ⟨1,0,0⟩, ⟨2,0,2⟩⟩,
  ⟨⟨1,0,0⟩, ⟨0,0,0⟩, ⟨0,1,1⟩⟩
]

/-- A representative is canonical for PG(2,27) if it is nonzero and its first
nonzero coordinate equals 1. -/
def isCanon (p : Pt) : Bool :=
  match [p.px, p.py, p.pz].find? (fun v => !(v == fzero)) with
  | some v => v == fone
  | none => false

/-- The 757 canonical representatives of the points of PG(2,27). -/
def plane : List Pt :=
  let digits : List F27 :=
    (List.range 27).map (fun n => fmk (n % 3) ((n / 3) % 3) ((n / 9) % 3))
  let all := digits.flatMap (fun x => digits.flatMap (fun y => digits.map (fun z => ⟨x, y, z⟩)))
  all.filter isCanon

def pairwiseDistinct : List Pt → Bool
  | [] => true
  | a :: t => !(t.contains a) && pairwiseDistinct t

/-- No three (distinct) points of `cap` are collinear. -/
def noThreeCollinear : Bool :=
  cap.all fun a => cap.all fun b => cap.all fun c =>
    a == b || b == c || a == c || !(collinear a b c)

/-- Every point outside `cap` lies on a secant (a line through two cap points),
so `cap` cannot be extended: it is a complete cap. -/
def isComplete : Bool :=
  plane.all fun p =>
    cap.contains p ||
    cap.any fun a => cap.any fun b => !(a == b) && collinear a b p

-- The plane really is PG(2,27): exactly 757 canonical representatives.
theorem plane_size : plane.length = 757 := by decide

-- The exhibited set has 14 points, below the claimed minimum of 21.
theorem cap_small : cap.length = 14 ∧ cap.length < 21 := by decide

-- It is a cap: no three of its points are collinear.
theorem cap_is_cap : noThreeCollinear = true := by decide

-- It is complete: every point of PG(2,27) lies on it or on one of its secants.
theorem cap_is_complete : isComplete = true := by decide

-- Combining: a complete cap of size 14 exists, so the minimum is at most 14 < 21,
-- and complete caps of sizes 14 < 15 exist in PG(2,27) (the 15-point one is
-- reported in reproduce.py), so the second-smallest is < 22 as well.
def disproof_claim : Bool := (cap.length < 21) && noThreeCollinear && isComplete

theorem main_disproof : disproof_claim = true := by decide
