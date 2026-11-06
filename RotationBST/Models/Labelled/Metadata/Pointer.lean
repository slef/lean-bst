module

public import RotationBST.Models.Labelled.Metadata.Representation
public import RotationBST.Models.Labelled.Cursor.Map.Basic

@[expose] public section
namespace RotationBST.Metadata

theorem label_map {α : Type} (data : Nat → α) (tree : Tree) (lo : Nat) :
    label data tree lo = (tree.labelFrom lo).map (fun key => (key, data key)) := by
  induction tree generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [label, Tree.labelFrom, LabelledTree.map, il, ir]

theorem label_inorder {α : Type} (data : Nat → α) (tree : Tree) (lo : Nat) :
    (label data tree lo).inorder = (List.range' lo tree.size).map (fun key => (key, data key)) := by
  rw [label_map, LabelledTree.inorder_map, Representation.Bridge.inorder_label]

/-- Following links and rotating physical nodes preserve every key-associated
payload, in the finite labelled-cursor representation. -/
theorem perform_label {α : Type} (data : Nat → α) {op : Multifinger.Opcode}
    {s t : LabelledCursor.Config (Nat × α)} (execution : LabelledCursor.perform op s = some t)
    (stored : s.tree = label data s.erase.tree 0) : t.tree = label data t.erase.tree 0 := by
  have same := LabelledCursor.perform_inorder execution
  have size : s.erase.tree.size = t.erase.tree.size := by
    simpa only [Representation.Bridge.inorder_length, LabelledCursor.erase_tree] using
      congrArg List.length same
  apply Representation.Bridge.ext
  · rw [label_erase, LabelledCursor.erase_tree]
  · rw [← same, stored, label_inorder, label_inorder, size]

end RotationBST.Metadata
