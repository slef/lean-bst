module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Top.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open PopTart PopTart.WeightedTree PopTart.Chocolate

private theorem pushed_nonempty (stack : Layer) (new : WeightedTree) :
    (stack.push new).decode.tree ≠ .nil := by
  obtain ⟨_, _, rotations⟩ := (Chocolate.Results.push_trace stack new).rotations
  have size := rotations.size_eq
  simp only [Pointer.Config.tree, Pointer.plug] at size
  intro empty
  rw [empty] at size
  simp only [Tree.size] at size
  omega

/-- Two rotations suffice even when an inverted-path separator stands between
the represented root and the exposed child payload. All descents are charged. -/
theorem expose_left_trace {p : Pair} {a b : Tree} {oldCharge : ℝ}
    (exposed : p.lower.top = .leaf (Tree.node a b).mirror oldCharge) (newCharge : ℝ) :
    Pointer.Trace ⟨p.tree, []⟩
      ⟨.node (p.lower.replaceTop (.leaf a.mirror newCharge)).decode.tree.mirror
        (.node b p.upper.decode.tree), []⟩ p.leftExposeCost := by
  cases tail : p.lower.topTail with
  | none =>
    have oldTree : p.lower.decode.tree.mirror = .node a b := by
      rw [decode_top p.lower, tail, exposed]
      simp only [Option.elim, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror_mirror]
    have newTree : (p.lower.replaceTop (.leaf a.mirror newCharge)).decode.tree.mirror = a := by
      rw [replaceTop_decode, tail]
      simp only [Option.elim, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror_mirror]
    rw [Pair.tree, oldTree, newTree, Pair.leftExposeCost, tail]
    change Pointer.Trace _ _ 2
    exact .step .downLeft (.step .rotateLeftChild .refl)
  | some suffix =>
    have oldTree : p.lower.decode.tree.mirror = .node suffix.tree.mirror (.node a b) := by
      rw [decode_top p.lower, tail, exposed]
      simp only [Option.elim, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror, Tree.mirror_mirror]
    have newTree : (p.lower.replaceTop (.leaf a.mirror newCharge)).decode.tree.mirror = .node suffix.tree.mirror a := by
      rw [replaceTop_decode, tail]
      simp only [Option.elim, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror, Tree.mirror_mirror]
    rw [Pair.tree, oldTree, newTree, Pair.leftExposeCost, tail]
    change Pointer.Trace _ _ 4
    exact .step .downLeft (.step .downRight (.step .rotateRightChild (.step .rotateLeftChild .refl)))

theorem downLeft_trace {p : Pair} {a b : Tree} {oldCharge : ℝ}
    (exposed : p.lower.top = .leaf (Tree.node a b).mirror oldCharge) (lowerCharge upperCharge : ℝ) :
    Pointer.Trace ⟨p.tree, []⟩ ⟨(p.downLeft a b lowerCharge upperCharge).tree, []⟩ p.downLeftCost := by
  let new : WeightedTree := .leaf b upperCharge
  have push := Chocolate.Results.push_trace p.upper new
  have inner := push.inContext (by intro h; cases h) (pushed_nonempty p.upper new)
    [.right (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.tree.mirror]
  have result := (expose_left_trace exposed lowerCharge).append inner
  convert result using 1 <;>
    simp only [Pair.downLeft, Pair.tree, Pair.downLeftCost, new, Pointer.plug,
      WeightedTree.tree,
      List.length_cons, List.length_nil]
  omega

theorem downLeft_valid {p : Pair} (valid : p.Valid) (a b : Tree)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    (p.downLeft a b lowerCharge upperCharge).Valid :=
  ⟨replaceTop_valid valid.1 (.leaf _ _) lowerNonnegative,
    (Chocolate.Results.push valid.2 (.leaf _ _) upperNonnegative []).1⟩

theorem downLeft_amortized {p : Pair} (valid : p.Valid) (a b : Tree)
    (lowerCharge : ℝ) {upperCharge : ℝ} (upperNonnegative : 0 ≤ upperCharge) :
    p.downLeftCost + (p.downLeft a b lowerCharge upperCharge).potential ≤ 26 + p.potential := by
  have push := (Chocolate.Results.push valid.2 (.leaf b upperCharge) upperNonnegative []).2.2.2.2
  have unchanged := replaceTop_potential valid.1 (.leaf a.mirror lowerCharge)
  have localCost : p.leftExposeCost ≤ 4 := by
    unfold Pair.leftExposeCost
    cases p.lower.topTail <;> norm_num
  simp only [Pair.downLeftCost, Pair.downLeft, Pair.potential]
  omega

theorem downLeft_mass {p : Pair} (valid : p.Valid) {a b : Tree} {oldCharge : ℝ}
    (exposed : p.lower.top = .leaf (Tree.node a b).mirror oldCharge)
    (lowerCharge : ℝ) {upperCharge : ℝ} (upperNonnegative : 0 ≤ upperCharge) :
    (p.downLeft a b lowerCharge upperCharge).mass + oldCharge = p.mass + lowerCharge + upperCharge := by
  have lower := replaceTop_mass p.lower (.leaf a.mirror lowerCharge)
  rw [exposed] at lower
  have upper := (Chocolate.Results.push valid.2 (.leaf b upperCharge) upperNonnegative []).2.2.1
  simp only [WeightedTree.mass] at lower upper
  change (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.mass +
      (p.upper.push (.leaf b upperCharge)).decode.mass + oldCharge =
    p.lower.decode.mass + p.upper.decode.mass + lowerCharge + upperCharge
  linarith

theorem downLeft_root_key {p : Pair} {a b : Tree} {oldCharge : ℝ}
    (exposed : p.lower.top = .leaf (Tree.node a b).mirror oldCharge) (lowerCharge upperCharge : ℝ) :
    (Pointer.Config.mk (p.downLeft a b lowerCharge upperCharge).tree []).key? =
      some (p.lower.decode.tree.mirror.size - b.size - 1) := by
  have sizes := replaceTop_size p.lower (.leaf a.mirror lowerCharge)
  rw [exposed] at sizes
  change (p.lower.replaceTop (.leaf a.mirror lowerCharge)).decode.tree.size +
    (Tree.node a b).mirror.size = p.lower.decode.tree.size + a.mirror.size at sizes
  simp only [Tree.mirror_size, Tree.size] at sizes
  simp only [Pointer.Config.key?, Pair.downLeft, Pair.tree, Pointer.offset, Nat.zero_add, Tree.mirror_size]
  congr 1
  omega

end RotationBST.HeavyPath.Finger
