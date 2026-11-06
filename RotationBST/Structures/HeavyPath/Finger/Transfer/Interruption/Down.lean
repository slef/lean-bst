module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Interruption.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Top.Invariant
public import RotationBST.Bounds.StaticTree.Trace.Mirror
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Transfer.Interruption
open PopTart PopTart.Chocolate

/-- Transfer an exposed child while guarding the whole physical tree through
both local rotations and the recursive push into the opposite stack. -/
theorem downLeft_within {p : Pair} {a b : Tree} {oldCharge : ℝ}
    (exposed : p.lower.top = .leaf (Tree.node a b).mirror oldCharge)
    (lowerCharge upperCharge : ℝ) :
    Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.tree x + 24)
      ⟨p.tree, []⟩ ⟨(p.downLeft a b lowerCharge upperCharge).tree, []⟩ p.downLeftCost := by
  let new : WeightedTree := .leaf b upperCharge
  have push := Chocolate.Interruption.Results.push_within p.upper new
  have nonempty : (p.upper.push new).decode.tree ≠ .nil := by
    intro empty
    have size := push.finish.1
    change (p.upper.push new).decode.tree.size = (Tree.node new.tree p.upper.decode.tree).size at size
    rw [empty] at size
    simp only [Tree.size] at size
    omega
  have embedded := StaticTree.Trace.within_embed
    [.right (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.tree.mirror]
    (by decide : 1 ≤ 4) push (by intro h; cases h) nonempty
  have short := StaticTree.Trace.within_size_depth (expose_left_trace exposed lowerCharge)
  have exposeBound : p.leftExposeCost ≤ 4 := by
    unfold Pair.leftExposeCost
    cases p.lower.topTail <;> norm_num
  have first : Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 1 * Tree.depth p.tree x + 4)
      ⟨p.tree, []⟩
      ⟨.node (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.tree.mirror
        (.node b p.upper.decode.tree), []⟩ p.leftExposeCost :=
    short.weaken (by
      intro t bound
      exact ⟨bound.1, fun x => by have h := bound.2 x; change Tree.depth t x ≤ Tree.depth p.tree x + p.leftExposeCost at h; omega⟩)
  have last : Pointer.TraceWithin (fun t =>
      t.size = (Tree.node (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.tree.mirror
        (.node b p.upper.decode.tree)).size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth
        (.node (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.tree.mirror
          (.node b p.upper.decode.tree)) x + 8)
      ⟨.node (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.tree.mirror
        (.node b p.upper.decode.tree), []⟩
      ⟨(p.downLeft a b lowerCharge upperCharge).tree, []⟩ (p.upper.pushCost + 2) := by
    convert embedded using 1 <;>
      simp only [Pointer.plug, Pair.downLeft, Pair.tree, new, WeightedTree.tree,
        WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, List.length_cons, List.length_nil]
    omega
  have composed := StaticTree.Trace.within_append (a := ⟨p.tree, []⟩)
    (b := ⟨.node (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.tree.mirror
      (.node b p.upper.decode.tree), []⟩) (f := 1) (u := 4) (v := 8)
    (by decide : 1 ≤ 4) first last
  simpa only [Nat.mul_one, Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc, Pair.downLeftCost,
    Pointer.Config.tree, Pointer.plug] using composed

/-- The right transfer reflects the same depth and exact-cost certificate. -/
theorem downRight_within {p : Pair} {a b : Tree} {oldCharge : ℝ}
    (exposed : p.upper.top = .leaf (.node a b) oldCharge)
    (lowerCharge upperCharge : ℝ) :
    Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.tree x + 24)
      ⟨p.tree, []⟩ ⟨(p.downRight a b lowerCharge upperCharge).tree, []⟩ p.downRightCost := by
  have reflected : p.flip.lower.top = .leaf (Tree.node b.mirror a.mirror).mirror oldCharge := by
    simpa only [Pair.flip, Tree.mirror, Tree.mirror_mirror] using exposed
  have result := StaticTree.Trace.within_mirror_depth
    (a := ⟨p.flip.tree, []⟩) (constant := 24) (by decide : 1 ≤ 4)
    (downLeft_within reflected upperCharge lowerCharge)
  simpa only [Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug,
    Pair.downRight, Pair.downRightCost, flip_tree, Tree.mirror_mirror, Tree.mirror_size,
    List.map_nil] using result

end RotationBST.HeavyPath.Finger.Transfer.Interruption
