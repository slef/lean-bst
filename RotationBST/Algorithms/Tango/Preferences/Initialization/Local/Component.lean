module

public import RotationBST.Algorithms.Tango.Preferences.Initialization.Local.Bounds
public import RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Initialization
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Initialization
open MarkedTree Context

/-- A first join at a component root is paid by the height of its own
reference subtree. No ancestor component is silently included in this bound. -/
theorem root_component_charge (s l r : MarkedTree) (next : Bool)
    (paths : (MarkedTree.node l r true true).PathMarked)
    (same : s.nesting = (MarkedTree.node l r true true).nesting) :
    (s.setMarksInPath [] l r true true next).1.nesting =
      (MarkedTree.node l r (!next) next).nesting ∧
      Rotations s.tree (s.setMarksInPath [] l r true true next).1.tree
        (s.setMarksInPath [] l r true true next).2 ∧
      ((s.setMarksInPath [] l r true true next).2 : ℝ) +
        (s.setMarksInPath [] l r true true next).1.potential - s.potential ≤
          localCredit (.node l.tree r.tree) l.tree.size := by
  obtain ⟨nested, rotations, bound⟩ := setMarksInPath_initial_spec s []
    (by simp) l r next same
  have nextPaths : (MarkedTree.node l r (!next) next).PathMarked := by
    cases next <;> simpa [PathMarked] using paths
  have size := region_size_le_height (MarkedTree.node l r (!next) next) nextPaths
  have logarithm := Splay.Updates.log_nat_mono size
  refine ⟨nested, rotations, ?_⟩
  simp only [plug, tree] at bound logarithm
  simp only [localCredit, heightAt, lt_self_iff_false, ite_false, ite_true]
  linarith

end RotationBST.Tango.Initialization
