module

public import RotationBST.Models.Region.Fringe

@[expose] public section
namespace RotationBST.Arboral.Region
open Pointer.Lazy.Skeleton

private def chain : Nat → Tree
  | 0 => .nil
  | n + 1 => .node .nil (chain n)

private theorem chain_size (n : Nat) : (chain n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, Tree.size, ih, Nat.add_comm]

private def normalize : Region → Region
  | .hole t => .hole (chain t.size)
  | .node l r => .node (normalize l) (normalize r)

private theorem normalize_size (s : Region) : (normalize s).tree.size = s.tree.size := by
  induction s with
  | hole t => exact chain_size _
  | node l r il ir => simp only [normalize, tree, Tree.size, il, ir]

private theorem normalize_keys (s : Region) (lo : Nat) : (normalize s).keys lo = s.keys lo := by
  induction s generalizing lo with
  | hole t => rfl
  | node l r il ir => simp only [normalize, keys, normalize_size, il, ir]

private theorem normalize_fringe (s : Region) :
    (normalize s).fringe = s.fringe.map (fun t => chain t.size) := by
  induction s with
  | hole t => rfl
  | node l r il ir => simp only [normalize, fringe, List.map_append, il, ir]

/-- Absolute active key ranks depend on fringe sizes, not on the binary shapes
inside the attached subtrees. -/
theorem keys_of_fringe_sizes {s t : Region}
    (same : s.fringe.map Tree.size = t.fringe.map Tree.size) (lo : Nat) : s.keys lo = t.keys lo := by
  have mapped := congrArg (List.map chain) same
  simp only [List.map_map, Function.comp_def] at mapped
  have hf : (normalize s).fringe = (normalize t).fringe := by
    rw [normalize_fringe, normalize_fringe, mapped]
  simpa only [normalize_keys] using (same_of_fringe hf lo).2.1

end RotationBST.Arboral.Region
