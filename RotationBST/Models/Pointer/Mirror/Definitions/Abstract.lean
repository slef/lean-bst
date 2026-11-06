module

public import RotationBST.Models.Pointer.Machine.Abstract

@[expose] public section
namespace RotationBST

def Tree.mirror : Tree → Tree
  | .nil => .nil
  | .node l r => .node r.mirror l.mirror

namespace Pointer

def Frame.mirror : Frame → Frame
  | .left r => .right r.mirror
  | .right l => .left l.mirror

def Config.mirror (c : Config) : Config :=
  ⟨c.focus.mirror, c.context.map Frame.mirror⟩

end Pointer
end RotationBST
