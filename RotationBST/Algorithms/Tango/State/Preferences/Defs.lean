module

public import RotationBST.Algorithms.Tango.State.Canonical.Defs
public import RotationBST.Algorithms.Tango.Preferences.Updates.Abstract

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- In a reference marking, each node has at most one preferred child.
This is a condition on the fixed reference shape, not on auxiliary BST shapes. -/
def PathMarked : MarkedTree → Prop
  | .nil => True
  | .node l r cl cr => PathMarked l ∧ PathMarked r ∧ (cl = true ∨ cr = true)

/-- Set a reference node's preference, using its inorder rank. Out-of-range
ranks have no effect. `true` selects the left child. -/
def setPreference : MarkedTree → Nat → Bool → MarkedTree
  | .nil, _, _ => .nil
  | .node l r cl cr, key, next =>
      if key < l.tree.size then .node (setPreference l key next) r cl cr
      else if key = l.tree.size then .node l r (!next) next
      else .node l (setPreference r (key - l.tree.size - 1) next) cl cr

/-- Apply a log of reference preference changes in order. Log keys are absolute
inorder ranks in this reference tree; the old preference is recorded for audit. -/
def applyPreferences : MarkedTree → List PreferenceUpdate → MarkedTree
  | s, [] => s
  | s, update :: rest => applyPreferences (s.setPreference update.key update.next) rest

end RotationBST.Tango.MarkedTree
