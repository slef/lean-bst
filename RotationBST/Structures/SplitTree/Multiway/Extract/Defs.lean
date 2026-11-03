module

public import RotationBST.Structures.SplitTree.Multiway.Edges.Defs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway

/-- A root with at least two keys can lose one key without shrinking its height. -/
def Wide : Multiway → Prop
  | .three _ _ _ | .four _ _ _ _ => True
  | _ => False

def firstChild : Multiway → Multiway
  | .nil => .nil
  | .two a _ | .three a _ _ | .four a _ _ _ => a

/-- Contract a minimal root before descending. Its binary representation is
unchanged, but its multiway height drops by one. -/
def rootMerge : Multiway → Option Multiway
  | .two (.two a b) (.two c d) => some (.four a b c d)
  | _ => none

/-- Extract from the first child, then rotate its minimum past this parent.
The supplied recursive operation handles the nonempty child. -/
def descendFirst (recur : Multiway → Multiway × Nat) : Multiway → Multiway × Nat
  | .nil => (.nil, 0)
  | .two l r =>
      if l = .nil then (r, 0)
      else let result := recur l; (.two result.1 r, result.2 + 1)
  | .three l m r =>
      if l = .nil then (.two m r, 0)
      else let result := recur l; (.three result.1 m r, result.2 + 1)
  | .four a b c d =>
      if a = .nil then (.three b c d, 1)
      else let result := recur a; (.four result.1 b c d, result.2 + 2)

/-- Fuel counts available multiway nodes. Root contraction consumes two nodes;
every descent visits a strictly smaller subtree. -/
def extractMinAux : Nat → Multiway → Multiway × Nat
  | 0, t => (t, 0)
  | fuel + 1, t =>
      match t.rootMerge with
      | some contracted => extractMinAux fuel contracted
      | none =>
          let prepared := t.repairFirst
          let result := descendFirst (extractMinAux fuel) prepared.1
          (result.1, prepared.2 + result.2)

/-- Expose and remove the minimum key, retaining a multiway representation of
the remaining keys and returning the exact number of binary rotations. -/
def extractMin (t : Multiway) : Multiway × Nat := extractMinAux (t.nodes + 1) t

end RotationBST.Geometric.Split.Multiway
