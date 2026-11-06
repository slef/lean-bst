module

public import RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor

/-- One off-path occurrence. Equal source subtrees may retain different
physical layouts and repair credits at different occurrences. -/
structure Entry (α : Type) where
  source : Frame α
  shape : Tree
  credit : Nat

namespace Entry

def slot {α : Type} (weight : α → ℝ) (e : Entry α) : Tree × ℝ :=
  (e.shape, frameMass weight e.source)
def lowerBlock {α : Type} (e : Entry α) : List α := Recursive.lowerBlock e.source
def upperBlock {α : Type} (e : Entry α) : List α := Recursive.upperBlock e.source

/-- Restore this source separator around the remaining heavy path. -/
def wrap {α : Type} (e : Entry α) (child : Tree) : Tree :=
  match e.source with
  | .left _ _ => .node child e.shape
  | .right _ _ => .node e.shape child

end Entry

def lower {α : Type} : List (Entry α) → List (Entry α)
  | [] => []
  | e :: es => match e.source with
    | .left _ _ => lower es
    | .right _ _ => lower es ++ [e]

def upper {α : Type} : List (Entry α) → List (Entry α)
  | [] => []
  | e :: es => match e.source with
    | .left _ _ => e :: upper es
    | .right _ _ => upper es

/-- Physical fringes describe occurrences, without imposing construction
history or assuming a height bound. -/
structure PathValid {α : Type} (weight : α → ℝ) (es : List (Entry α)) (p : Stacks) : Prop where
  pair : p.Valid
  lower : p.lower.decode.fringe = (History.lower es).map (Entry.slot weight) ++ [(.nil, 0)]
  upper : p.upper.decode.mirror.fringe = [(.nil, 0)] ++ (History.upper es).map (Entry.slot weight)

/-- A recursive representation with arbitrary valid stack histories. The
potential is the sum over actual path and payload occurrences. -/
inductive Layout {α : Type} (weight : α → ℝ) : LabelledTree α → Tree → Nat → Prop where
  | nil : Layout weight .nil .nil 0
  | path {t : LabelledTree α} {es : List (Entry α)} {p : Stacks}
      (positive : Positive weight t) (nonempty : t ≠ .nil)
      (context : es.map Entry.source = (extract weight t).context)
      (valid : PathValid weight es p)
      (children : ∀ e ∈ es, Layout weight (framePayload e.source) e.shape e.credit) :
      Layout weight t p.tree (p.potential + (es.map Entry.credit).sum)

end RotationBST.HeavyPath.Recursive.History
