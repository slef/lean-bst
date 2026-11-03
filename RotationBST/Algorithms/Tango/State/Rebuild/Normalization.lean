module

public import RotationBST.Algorithms.Tango.State.Rebuild.Defs
public import RotationBST.Algorithms.Tango.State.Fringe

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region

/-- Canonicalize marks on empty edges within the root component. Marks below a
component boundary are retained verbatim. -/
def normalizeRoot : MarkedTree → MarkedTree
  | .nil => .nil
  | .node l r cl cr => .node
      (if cl then l else normalizeRoot l) (if cr then r else normalizeRoot r)
      (cl || decide (l = .nil)) (cr || decide (r = .nil))

theorem normalizeRoot_tree (s : MarkedTree) : s.normalizeRoot.tree = s.tree := by
  induction s with
  | nil => rfl
  | node l r cl cr il ir => cases cl <;> cases cr <;> simp [normalizeRoot, tree, il, ir]

theorem normalizeRoot_region (s : MarkedTree) : s.normalizeRoot.region = s.region := by
  induction s with
  | nil => rfl
  | node l r cl cr il ir =>
    cases cl <;> cases cr <;> cases l <;> cases r <;>
      simp_all [normalizeRoot, region, tree]

theorem normalizeRoot_fringe (s : MarkedTree) : s.normalizeRoot.fringe = s.fringe := by
  induction s with
  | nil => rfl
  | node l r cl cr il ir =>
    cases cl <;> cases cr <;> cases l <;> cases r <;>
      simp_all [normalizeRoot, fringe]

theorem shape_nil_iff (s : MarkedTree) : shape s.region = .nil ↔ s = .nil := by
  cases s <;> simp [region, shape]

/-- Reconstruction from a component's own shape and fringe only canonicalizes
irrelevant marks on empty edges. Attached marked subtrees are kept exactly. -/
theorem fill_shape_fringe (s : MarkedTree) (rest : List MarkedTree) :
    fill (shape s.region) (s.fringe ++ rest) = (s.normalizeRoot, rest) := by
  induction s generalizing rest with
  | nil => rfl
  | node l r cl cr il ir =>
    cases cl <;> cases cr <;>
      simp [region, shape, fringe, fill, normalizeRoot, List.append_assoc, il, ir, shape_nil_iff]

end RotationBST.Tango.MarkedTree
