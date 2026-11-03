module

public import RotationBST.Algorithms.Tango.State.Preferences.Structure
public import RotationBST.Algorithms.Tango.State.Preferences.Lookup.Defs
public import RotationBST.Algorithms.Tango.State.Context.Localization

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- A rank-based preference update changes only the two marks at one node. -/
theorem locateKey_spec (s : MarkedTree) (key : Nat) (next : Bool)
    (valid : key < s.tree.size) :
    ∃ fs : List Context.Frame, ∃ l r : MarkedTree, ∃ cl cr : Bool,
      s.locateKey key = some (.node l r cl cr, fs) ∧
      s = Context.plug fs (.node l r cl cr) ∧
      s.setPreference key next = Context.plug fs (.node l r (!next) next) := by
  induction s generalizing key with
  | nil => simp [tree, Tree.size] at valid
  | node l r cl cr il ir =>
    by_cases left : key < l.tree.size
    · obtain ⟨fs, a, b, ca, cb, found, source, target⟩ := il key left
      refine ⟨fs ++ [.left r cl cr], a, b, ca, cb, ?_, ?_, ?_⟩
      · simp [locateKey, left, found]
      · rw [Context.plug_append]
        change MarkedTree.node l r cl cr = .node (Context.plug fs (.node a b ca cb)) r cl cr
        rw [← source]
      · rw [setPreference, ite_eq_left left, Context.plug_append]
        change MarkedTree.node (l.setPreference key next) r cl cr =
          .node (Context.plug fs (.node a b (!next) next)) r cl cr
        rw [target]
    · by_cases root : key = l.tree.size
      · exact ⟨[], l, r, cl, cr, by simp [locateKey, root], rfl, by simp [setPreference, root, Context.plug]⟩
      · have right : key - l.tree.size - 1 < r.tree.size := by
          simp only [tree, Tree.size] at valid
          omega
        obtain ⟨fs, a, b, ca, cb, found, source, target⟩ := ir _ right
        refine ⟨fs ++ [.right l cr cl], a, b, ca, cb, ?_, ?_, ?_⟩
        · simp [locateKey, left, root, found]
        · rw [Context.plug_append]
          change MarkedTree.node l r cl cr = .node l (Context.plug fs (.node a b ca cb)) cl cr
          rw [← source]
        · rw [setPreference, ite_eq_right left, ite_eq_right root, Context.plug_append]
          change MarkedTree.node l (r.setPreference (key - l.tree.size - 1) next) cl cr =
            .node l (Context.plug fs (.node a b (!next) next)) cl cr
          rw [target]

end RotationBST.Tango.MarkedTree
