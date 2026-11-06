module

import RotationBST.Audit.Check
public import RotationBST.Models.Pointer.Mirror.AbstractBridge

@[expose] public section
namespace RotationBST.Pointer.Mirror.Results

theorem tree_involution (t : Tree) : t.mirror.mirror = t := Tree.mirror_mirror t
theorem tree_size (t : Tree) : t.mirror.size = t.size := Tree.mirror_size t
theorem frame_involution (f : Frame) : f.mirror.mirror = f := Frame.mirror_mirror f
theorem config_involution (c : Config) : c.mirror.mirror = c := Config.mirror_mirror c
theorem plug (cs : List Frame) (t : Tree) :
    (Pointer.plug cs t).mirror = Pointer.plug (cs.map Frame.mirror) t.mirror := mirror_plug cs t
theorem config_tree (c : Config) : c.mirror.tree = c.tree.mirror := Config.mirror_tree c
theorem step {a b : Config} (h : Step a b) : Step a.mirror b.mirror := h.mirror
theorem trace {a b : Config} {k : Nat} (h : Trace a b k) : Trace a.mirror b.mirror k := h.mirror

end RotationBST.Pointer.Mirror.Results

/-- info: abstract audit passed for `RotationBST.Pointer.Mirror.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Pointer.Mirror.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract]
