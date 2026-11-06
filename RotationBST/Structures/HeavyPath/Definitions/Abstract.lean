module

public import RotationBST.Models.Labelled.Cursor.Definitions.Abstract
public import RotationBST.Models.Labelled.Ordering.Definitions.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section
namespace RotationBST.HeavyPath
open LabelledCursor

/-- Analysis weights belong to labelled nodes; no additional tree shape is
introduced. Inorder ranks can be used as the labels of an ordinary BST. -/
def mass {α : Type} (weight : α → ℝ) : LabelledTree α → ℝ
  | .nil => 0
  | .node l x r => mass weight l + weight x + mass weight r

def Nonnegative {α : Type} (weight : α → ℝ) : LabelledTree α → Prop
  | .nil => True
  | .node l x r => Nonnegative weight l ∧ 0 ≤ weight x ∧ Nonnegative weight r

def Positive {α : Type} (weight : α → ℝ) : LabelledTree α → Prop
  | .nil => True
  | .node l x r => Positive weight l ∧ 0 < weight x ∧ Positive weight r

/-- A node's solid edge goes to its heavier child; ties go left. -/
def LeftHeavy {α : Type} (weight : α → ℝ) (l r : LabelledTree α) : Prop :=
  mass weight r ≤ mass weight l

/-- Frames run from the endpoint back toward the root, as in the existing
labelled cursor. Every selected edge must obey the canonical heavy choice. -/
def SolidContext {α : Type} (weight : α → ℝ) : LabelledTree α → List (Frame α) → Prop
  | _, [] => True
  | t, .left x r :: cs => LeftHeavy weight t r ∧ SolidContext weight (.node t x r) cs
  | t, .right l x :: cs => ¬ LeftHeavy weight l t ∧ SolidContext weight (.node l x t) cs

/-- Weight removed from the active path by a frame: its separator node plus
its off-path subtree. These charges partition the original node mass. -/
def frameMass {α : Type} (weight : α → ℝ) : Frame α → ℝ
  | .left x r => weight x + mass weight r
  | .right l x => mass weight l + weight x

def frameKey {α : Type} : Frame α → α
  | .left x _ => x
  | .right _ x => x

/-- Path separators smaller than the endpoint, in endpoint-to-root order. -/
def lowerKeys {α : Type} : List (Frame α) → List α
  | [] => []
  | .left _ _ :: cs => lowerKeys cs
  | .right _ x :: cs => x :: lowerKeys cs

/-- Path separators larger than the endpoint, in endpoint-to-root order. -/
def upperKeys {α : Type} : List (Frame α) → List α
  | [] => []
  | .left x _ :: cs => x :: upperKeys cs
  | .right _ _ :: cs => upperKeys cs

def extend {α : Type} (cursor : Config α) (frame : Frame α) : Config α :=
  ⟨cursor.focus, cursor.context ++ [frame]⟩

/-- Extract one maximal solid path. If the selected child is empty, the
current node is its endpoint. Positive node weights make that endpoint a
leaf; zero-weight off-path subtrees are retained without being discarded. -/
noncomputable def extract {α : Type} (weight : α → ℝ) : LabelledTree α → Config α := by
  classical
  exact fun t => match t with
  | .nil => ⟨.nil, []⟩
  | .node l x r =>
      if LeftHeavy weight l r then
        if l = .nil then ⟨.node l x r, []⟩
        else extend (extract weight l) (.left x r)
      else
        if r = .nil then ⟨.node l x r, []⟩
        else extend (extract weight r) (.right l x)

/-- A particular original node occurrence, with its total edge depth and
number of dotted (non-heavy) edges recorded separately. -/
inductive Path {α : Type} (weight : α → ℝ) : LabelledTree α → α → Nat → Nat → Prop where
  | root (l r : LabelledTree α) (x : α) : Path weight (.node l x r) x 0 0
  | leftSolid {l r : LabelledTree α} {x y : α} {lights depth : Nat}
      (found : Path weight l y lights depth) (heavy : LeftHeavy weight l r) :
      Path weight (.node l x r) y lights (depth + 1)
  | leftLight {l r : LabelledTree α} {x y : α} {lights depth : Nat}
      (found : Path weight l y lights depth) (heavy : ¬ LeftHeavy weight l r) :
      Path weight (.node l x r) y (lights + 1) (depth + 1)
  | rightSolid {l r : LabelledTree α} {x y : α} {lights depth : Nat}
      (found : Path weight r y lights depth) (heavy : ¬ LeftHeavy weight l r) :
      Path weight (.node l x r) y lights (depth + 1)
  | rightLight {l r : LabelledTree α} {x y : α} {lights depth : Nat}
      (found : Path weight r y lights depth) (heavy : LeftHeavy weight l r) :
      Path weight (.node l x r) y (lights + 1) (depth + 1)

end RotationBST.HeavyPath
