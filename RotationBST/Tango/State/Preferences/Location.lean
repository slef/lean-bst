module

public import RotationBST.Tango.State.Preferences.Lookup.Proofs

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- A rank-based preference update changes only the two marks at one node. -/
theorem setPreference_context (s : MarkedTree) (key : Nat) (next : Bool)
    (valid : key < s.tree.size) :
    ∃ fs : List Context.Frame, ∃ l r : MarkedTree, ∃ cl cr : Bool,
      s = Context.plug fs (.node l r cl cr) ∧
      s.setPreference key next = Context.plug fs (.node l r (!next) next) := by
  obtain ⟨fs, l, r, cl, cr, _, source, target⟩ := locateKey_spec s key next valid
  exact ⟨fs, l, r, cl, cr, source, target⟩

end RotationBST.Tango.MarkedTree
