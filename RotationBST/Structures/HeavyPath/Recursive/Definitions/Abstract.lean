module

public import RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Recursive
open Paired LabelledCursor

/-- Off-path frames in physical inorder order on each side of the endpoint. -/
def lowerFrames {α : Type} : List (Frame α) → List (Frame α)
  | [] => []
  | .left _ _ :: cs => lowerFrames cs
  | f@(.right _ _) :: cs => lowerFrames cs ++ [f]

def upperFrames {α : Type} : List (Frame α) → List (Frame α)
  | [] => []
  | f@(.left _ _) :: cs => f :: upperFrames cs
  | .right _ _ :: cs => upperFrames cs

def lowerBlock {α : Type} (frame : Frame α) : List α :=
  (framePayload frame).inorder ++ [frameKey frame]

def upperBlock {α : Type} (frame : Frame α) : List α :=
  frameKey frame :: (framePayload frame).inorder

/-- A property of every occurrence, retaining its rank even when labels repeat. -/
def RanksSatisfy {α : Type} (P : Nat → α → Prop) (offset : Nat) (xs : List α) : Prop :=
  ∀ before x after, xs = before ++ x :: after → P (offset + before.length) x

/-- Fuel bounds the number of recursively nested heavy paths. The zero case
retains the original subtree. With at least one unit per original node and
positive weights, every nonempty recursive call takes the paired branch. -/
noncomputable def rebuildFuel {α : Type} (weight : α → ℝ) : Nat → LabelledTree α → Tree
  | 0, t => t.erase
  | _ + 1, .nil => .nil
  | n + 1, t@(.node _ _ _) =>
      match (extract weight t).focus with
      | .node .nil _ .nil => (Stacks.buildWith weight (rebuildFuel weight n)
          (extract weight t).context Stacks.empty).tree
      | _ => t.erase

noncomputable def rebuild {α : Type} (weight : α → ℝ) (t : LabelledTree α) : Tree :=
  rebuildFuel weight t.erase.size t

/-- The outermost pair, with all off-path payloads recursively rebuilt. -/
noncomputable def rootPair {α : Type} (weight : α → ℝ) (t : LabelledTree α) : Stacks :=
  Stacks.buildWith weight (rebuild weight) (extract weight t).context Stacks.empty

/-- A full recursive paired layout: every nonempty source path is represented
by its Chocolate pair, and each off-path source subtree has another full
layout in its corresponding opaque payload. No depth estimate is assumed. -/
inductive Layout {α : Type} (weight : α → ℝ) : LabelledTree α → Tree → Prop where
  | nil : Layout weight .nil .nil
  | path {t : LabelledTree α} {payload : LabelledTree α → Tree}
      (positive : Positive weight t) (nonempty : t ≠ .nil)
      (terminal : ∃ x, (extract weight t).focus = .node .nil x .nil)
      (children : ∀ frame ∈ (extract weight t).context,
        Layout weight (framePayload frame) (payload (framePayload frame))) :
      Layout weight t (Stacks.buildWith weight payload (extract weight t).context Stacks.empty).tree

end RotationBST.HeavyPath.Recursive
