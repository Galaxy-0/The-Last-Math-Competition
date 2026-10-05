import Tutte585
open Tutte585

def emptyGraph : Graph := ⟨0, []⟩
def oneLoop : Graph := ⟨1, [(⟨0, by decide⟩, ⟨0, by decide⟩)]⟩
def oneEdge : Graph := ⟨2, [(⟨0, by decide⟩, ⟨1, by decide⟩)]⟩
def parallelPair : Graph := ⟨2,
  [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨0, by decide⟩, ⟨1, by decide⟩)]⟩
def triangle : Graph := ⟨3,
  [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩),
   (⟨2, by decide⟩, ⟨0, by decide⟩)]⟩

example : tutte emptyGraph 3 1 = 1 := by decide
example : tutte oneLoop 3 1 = 1 := by decide
example : tutte oneLoop 4 2 = 2 := by decide
example : tutte oneEdge 3 1 = 3 := by decide
example : tutte parallelPair 3 1 = 4 := by decide
example : tutte triangle 3 1 = 13 := by decide
example : (countedObjects triangle 2).length = 13 := by decide
example : (countedObjects parallelPair 3).Nodup := countedObjects_nodup _ _

#eval (countedObjects triangle 2).length
#print axioms conjecture_00000000585
