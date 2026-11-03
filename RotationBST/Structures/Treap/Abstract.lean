module

public import RotationBST.Models.Geometric.Definitions.Abstract
public import RotationBST.Models.Rotation.Abstract
public import Mathlib.Data.Finset.Max

@[expose] public section
namespace RotationBST.Geometric

/-- First touch at or after `time`; infinity means that the key is never touched
again. These priorities depend on the future and are used only offline. -/
def nextTouch (P : Finset Point) (time key : Nat) : WithTop Nat :=
  ((P.filter fun p => p.1 = key ∧ time ≤ p.2).image Prod.snd).min

/-- A treap on consecutive inorder ranks. Each subtree root has minimum
priority in its interval. Equal priorities impose no extra tie-breaking rule. -/
def Heap {α : Type} [LE α] (priority : Nat → α) : Tree → Nat → Prop
  | .nil, _ => True
  | .node l r, lo =>
      (∀ x < l.size + 1 + r.size, priority (lo + l.size) ≤ priority (lo + x)) ∧
      Heap priority l lo ∧ Heap priority r (lo + l.size + 1)

/-- No other point on the current row lies between `a` and `b`. -/
def RowAdjacent (P : Finset Point) (time a b : Nat) : Prop :=
  ∀ x, (x, time) ∈ P → min a b ≤ x → x ≤ max a b → x = a

end RotationBST.Geometric
