module

public import RotationBST.Tango.State.Context.Abstract

@[expose] public section
namespace RotationBST.Tango.Context

/-- Fringe slots preceding the focus within one ancestor frame. -/
def Frame.before : Frame → List MarkedTree
  | .left _ _ _ => []
  | .right l _ cl => if cl then [l] else l.fringe

/-- Fringe slots following the focus within one ancestor frame. -/
def Frame.after : Frame → List MarkedTree
  | .left r _ cr => if cr then [r] else r.fringe
  | .right _ _ _ => []

/-- Prefix slots contributed by an unmarked context, in inorder. Its length is
the active-rank offset of the focused subtree. -/
def before : List Frame → List MarkedTree
  | [] => []
  | f :: fs => before fs ++ f.before

/-- Suffix slots contributed by an unmarked context. -/
def after : List Frame → List MarkedTree
  | [] => []
  | f :: fs => f.after ++ after fs

end RotationBST.Tango.Context
