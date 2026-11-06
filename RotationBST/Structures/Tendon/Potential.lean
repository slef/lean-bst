module

public import RotationBST.Structures.BSTDeque.Potential
public import RotationBST.Structures.Tendon.Representation

@[expose] public section
namespace RotationBST.Tendon.State

/-- The two deque components partition the reference path, so their combined
potential is linear in that path's length, even after arbitrary updates. -/
theorem potential_le_length {d : State} {cs : List Pointer.Frame} (rep : d.Represents cs) :
    d.potential ≤ 32 * cs.length := by
  have lower := d.lower.potential_le_size
  have upper := d.upper.potential_le_size
  have sizes := represents_size rep
  have partition := path_length cs
  dsimp only [potential]
  omega

end RotationBST.Tendon.State
