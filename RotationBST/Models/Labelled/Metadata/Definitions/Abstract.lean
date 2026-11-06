module

public import RotationBST.Models.Rotation.Abstract
public import Mathlib.Logic.Function.Basic

@[expose] public section
namespace RotationBST.Metadata

/-- Render the payload attached to each physical key. The total function is a
semantic representation: only the tree's finite key interval is stored. -/
def label {α : Type} (data : Nat → α) : Tree → Nat → LabelledTree (Nat × α)
  | .nil, _ => .nil
  | .node l r, lo => .node (label data l lo) (lo + l.size, data (lo + l.size))
      (label data r (lo + l.size + 1))

/-- A labelled node carrying a given key and payload. This is structural
membership; access permission must additionally identify the current cursor. -/
inductive At {α : Type} : LabelledTree (Nat × α) → Nat → α → Prop where
  | root (l r : LabelledTree (Nat × α)) (x : Nat) (value : α) : At (.node l (x, value) r) x value
  | left {l r : LabelledTree (Nat × α)} {entry : Nat × α} {x : Nat} {value : α} :
      At l x value → At (.node l entry r) x value
  | right {l r : LabelledTree (Nat × α)} {entry : Nat × α} {x : Nat} {value : α} :
      At r x value → At (.node l entry r) x value

/-- Replace exactly one node's payload, leaving its key and both children fixed.
The contextual cases describe the location; they do not grant free navigation. -/
inductive Write {α : Type} : LabelledTree (Nat × α) → Nat → α → LabelledTree (Nat × α) → Prop where
  | root (l r : LabelledTree (Nat × α)) (x : Nat) (old value : α) :
      Write (.node l (x, old) r) x value (.node l (x, value) r)
  | left {l l' r : LabelledTree (Nat × α)} {entry : Nat × α} {x : Nat} {value : α} :
      Write l x value l' → Write (.node l entry r) x value (.node l' entry r)
  | right {l r r' : LabelledTree (Nat × α)} {entry : Nat × α} {x : Nat} {value : α} :
      Write r x value r' → Write (.node l entry r) x value (.node l entry r')

end RotationBST.Metadata
