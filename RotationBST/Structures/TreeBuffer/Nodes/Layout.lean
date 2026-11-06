module

public import RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract
public import RotationBST.Models.Labelled.Cursor.Map.Basic
public import RotationBST.Models.Labelled.Intervals.Representation

@[expose] public section
namespace RotationBST.TreeBuffer.Nodes

theorem label_routing {α : Type} (data : Nat → α) (tree : Tree) (lo : Nat) :
    (label data tree lo).map Entry.routing = IntervalMetadata.label tree lo := by
  induction tree generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [label, LabelledTree.map, Entry.routing, IntervalMetadata.label, il, ir]

theorem label_payload {α : Type} (data : Nat → α) (tree : Tree) (lo : Nat) :
    (label data tree lo).map Entry.payload = Metadata.label data tree lo := by
  induction tree generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [label, LabelledTree.map, Entry.payload, Metadata.label, il, ir]

theorem label_erase {α : Type} (data : Nat → α) (tree : Tree) (lo : Nat) :
    (label data tree lo).erase = tree := by
  have erased := congrArg LabelledTree.erase (label_routing data tree lo)
  simpa only [LabelledTree.erase_map, IntervalMetadata.label_erase] using erased

theorem root_layout {α : Type} (data : Nat → α) (tree : Tree) :
    Routing ⟨label data tree 0, []⟩ ∧ Stored data ⟨label data tree 0, []⟩ := by
  constructor
  · change (label data tree 0).map Entry.routing =
      IntervalMetadata.label ((label data tree 0).map Entry.routing).erase 0
    rw [label_routing, IntervalMetadata.label_erase]
  · change (label data tree 0).map Entry.payload = Metadata.label data (label data tree 0).erase 0
    rw [label_payload, label_erase]

end RotationBST.TreeBuffer.Nodes
