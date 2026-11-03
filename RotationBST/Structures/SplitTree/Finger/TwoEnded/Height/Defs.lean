module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Defs
public import RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded

/-- A structural alternative to side-size balance. Equal-height 2–3–4 trees
may have very different sizes, but their logarithmic sizes stay comparable. -/
def State.HeightValid (state : State) : Prop :=
  state.left.Valid ∧ state.right.Valid ∧
    state.left.height ≤ state.right.height + 1 ∧ state.right.height ≤ state.left.height + 1

/-- Keep the original separating root and give each of its balanced binary
pieces the appropriate endpoint view. No median search is needed. -/
def fromRoot (height : Nat) (t : Multiway) : State × Nat :=
  let parts := Multiway.Partition.children height t
  (⟨parts.1, parts.2⟩, conversionCost parts.1.tree + maximumCost parts.2.tree)

/-- Keep an already height-balanced root unchanged. Otherwise join its two
balanced sides and establish the endpoint views around the joined tree's root. -/
def rebalance (state : State) : State × Nat :=
  if state.left.height ≤ state.right.height + 1 ∧ state.right.height ≤ state.left.height + 1 then
    (state, 0)
  else
    let joined := Multiway.Join.compact state.left.height state.right.height state.left.tree state.right.tree
    let result := fromRoot joined.height joined.tree
    (result.1, conversionCost state.left.tree + maximumCost state.right.tree + joined.cost + result.2)

end RotationBST.SplitTree.Multiway.Finger.TwoEnded
