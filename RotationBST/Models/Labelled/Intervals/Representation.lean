module

public import RotationBST.Models.Labelled.Intervals.Definitions.Abstract
public import RotationBST.Models.Pointer.Routing.Correctness
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.IntervalMetadata

theorem label_erase (tree : Tree) (lo : Nat) : (label tree lo).erase = tree := by
  induction tree generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [label, LabelledTree.erase, il, ir]

theorem label_plug_at (cs : List Pointer.Frame) (tree : Tree) (lo key : Nat) (bounds : Bounds)
    (atNode : Metadata.At (label tree (lo + Pointer.offset cs)) key bounds) :
    Metadata.At (label (Pointer.plug cs tree) lo) key bounds := by
  induction cs generalizing tree with
  | nil => simpa only [Pointer.plug, Pointer.offset, Nat.add_zero] using atNode
  | cons frame cs ih =>
    cases frame with
    | left r => exact ih (.node tree r) (.left atNode)
    | right l =>
      apply ih (.node l tree)
      apply Metadata.At.right
      simpa only [Pointer.offset, Nat.add_assoc] using atNode

/-- The routing interval is physically present at the cursor's labelled node. -/
theorem view_at (v : Pointer.Routing.View) (cursor : Pointer.Config) (valid : v.Valid cursor) :
    Metadata.At (label cursor.tree 0) v.key ⟨v.low, v.high⟩ := by
  rcases cursor with ⟨focus, cs⟩
  rcases v with ⟨low, key, high⟩
  change low = Pointer.offset cs ∧ (Pointer.Config.mk focus cs).key? = some key ∧ high = low + focus.size at valid
  rcases valid with ⟨rfl, keyAt, rfl⟩
  cases focus with
  | nil => simp [Pointer.Config.key?] at keyAt
  | node l r =>
    have root : Pointer.offset cs + l.size = key := Option.some.inj keyAt
    subst key
    apply label_plug_at
    simpa only [Nat.zero_add, label] using (Metadata.At.root (label l (Pointer.offset cs))
      (label r (Pointer.offset cs + l.size + 1)) (Pointer.offset cs + l.size)
      (Bounds.mk (Pointer.offset cs) (Pointer.offset cs + (Tree.node l r).size)))

/-- Interval maintenance needs one rotation and exactly two node-field writes. -/
theorem Update.writes {s t : LabelledTree (Nat × Bounds)} (update : Update s t) :
    ∃ rotated first x bx y byBounds, LabelledTree.Rotate s rotated ∧
      Metadata.Write rotated x bx first ∧ Metadata.Write first y byBounds t := by
  induction update with
  | right a b c x y bx byBounds =>
    exact ⟨_, _, x, ⟨bx.low, byBounds.high⟩, y, ⟨x + 1, byBounds.high⟩, .right,
      .root _ _ _ _ _, .right (.root _ _ _ _ _)⟩
  | left a b c x y bx byBounds =>
    exact ⟨_, _, y, ⟨bx.low, byBounds.high⟩, x, ⟨bx.low, y⟩, .left,
      .root _ _ _ _ _, .left (.root _ _ _ _ _)⟩
  | inLeft _ ih =>
    obtain ⟨rotated, first, x, bx, y, byBounds, rotation, one, two⟩ := ih
    exact ⟨_, _, x, bx, y, byBounds, .inLeft rotation, .left one, .left two⟩
  | inRight _ ih =>
    obtain ⟨rotated, first, x, bx, y, byBounds, rotation, one, two⟩ := ih
    exact ⟨_, _, x, bx, y, byBounds, .inRight rotation, .right one, .right two⟩

/-- These local updates preserve the complete interval annotation after a
rotation at any depth; no ancestor or descendant field recomputation is needed. -/
theorem label_rotate {s t : Tree} (rotation : Rotate s t) (lo : Nat) :
    Update (label s lo) (label t lo) := by
  induction rotation generalizing lo with
  | right =>
    simp only [label, Tree.size, Nat.add_assoc]
    exact Update.right _ _ _ _ _ _ _
  | left =>
    simp only [label, Tree.size, Nat.add_assoc]
    exact Update.left _ _ _ _ _ _ _
  | inLeft rotation ih =>
    simp only [label, rotation.size_eq, Tree.size]
    exact .inLeft (ih lo)
  | inRight rotation ih =>
    simp only [label, rotation.size_eq, Tree.size]
    exact .inRight (ih _)

end RotationBST.IntervalMetadata
