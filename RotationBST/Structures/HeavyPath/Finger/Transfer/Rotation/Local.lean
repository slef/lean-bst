module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Transfer.Rotation
open PopTart PopTart.Chocolate PopTart.WeightedTree

private theorem popped_nonempty {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) : stack.decode.tree ≠ .nil := by
  obtain ⟨_, _, rotations⟩ := (Chocolate.Results.pop_trace popped).rotations
  have sizes := rotations.size_eq
  simp only [Pointer.Config.tree, Pointer.plug, Tree.size] at sizes
  intro empty
  rw [empty, Tree.size] at sizes
  omega

/-- Merge the first two opaque occurrences, using the popped separator as
their root. A following ancestor may require one additional rotation. -/
theorem collect_front {stack rest : Layer} {a b : Tree} {firstCharge secondCharge : ℝ}
    (popped : stack.pop = some (.leaf a firstCharge, rest))
    (stored : rest.top = .leaf b secondCharge) (newCharge : ℝ) :
    ∃ cost, Pointer.Trace ⟨stack.decode.tree, []⟩
      ⟨(rest.replaceTop (.leaf (.node a b) newCharge)).decode.tree, []⟩ cost ∧
      cost ≤ stack.popCost + 2 := by
  have pop := Chocolate.Results.pop_trace popped
  change Pointer.Trace ⟨stack.decode.tree, []⟩ ⟨.node a rest.decode.tree, []⟩ stack.popCost at pop
  cases tail : rest.topTail with
  | none =>
    have oldTree : rest.decode.tree = b := by
      rw [decode_top, tail, stored]
      rfl
    have newTree : (rest.replaceTop (.leaf (.node a b) newCharge)).decode.tree = .node a b := by
      rw [replaceTop_decode, tail]
      rfl
    rw [oldTree] at pop
    refine ⟨stack.popCost, ?_, by omega⟩
    rw [newTree]
    exact pop
  | some suffix =>
    have oldTree : rest.decode.tree = .node b suffix.tree := by
      rw [decode_top, tail, stored]
      rfl
    have newTree : (rest.replaceTop (.leaf (.node a b) newCharge)).decode.tree = .node (.node a b) suffix.tree := by
      rw [replaceTop_decode, tail]
      rfl
    rw [oldTree] at pop
    have rotate : Pointer.Trace ⟨.node a (.node b suffix.tree), []⟩
        ⟨.node (.node a b) suffix.tree, []⟩ 2 :=
      .step .downRight (.step .rotateRightChild .refl)
    refine ⟨stack.popCost + 2, ?_, le_rfl⟩
    rw [newTree]
    exact pop.append rotate

/-- Perform the recursive join inside the collected front occurrence. -/
theorem merge_front {stack rest : Layer} {a b shape : Tree} {firstCharge secondCharge : ℝ}
    (popped : stack.pop = some (.leaf a firstCharge, rest))
    (stored : rest.top = .leaf b secondCharge) (newCharge : ℝ)
    (nonempty : shape ≠ .nil) {joinCost : Nat}
    (join : Pointer.Trace ⟨.node a b, []⟩ ⟨shape, []⟩ joinCost) :
    ∃ cost, Pointer.Trace ⟨stack.decode.tree, []⟩
      ⟨(rest.replaceTop (.leaf shape newCharge)).decode.tree, []⟩ cost ∧
      cost ≤ stack.popCost + joinCost + 4 := by
  obtain ⟨collectCost, collect, collectBound⟩ := collect_front popped stored newCharge
  let prepared := rest.replaceTop (.leaf (.node a b) newCharge)
  have top : prepared.top = .leaf (.node a b) newCharge := replaceTop_top _ _
  have inner : Pointer.Trace ⟨prepared.top.tree, []⟩ ⟨shape, []⟩ joinCost := by
    simpa only [top, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree] using join
  obtain ⟨insideCost, insideBound, inside⟩ := Chocolate.Top.Results.replaceTop_lift prepared
    (.leaf shape newCharge) (by rw [top]; intro h; cases h) nonempty inner
  change Pointer.Trace ⟨prepared.decode.tree, []⟩
    ⟨((rest.replaceTop _).replaceTop _).decode.tree, []⟩ insideCost at inside
  rw [replaceTop_replaceTop] at inside
  exact ⟨_, collect.append inside, by omega⟩

theorem rotateLeft_trace {p : Pair} {rest : Layer} {a b shape : Tree} {firstCharge secondCharge : ℝ}
    (popped : p.upper.pop = some (.leaf a firstCharge, rest))
    (stored : rest.top = .leaf b secondCharge) (newCharge : ℝ)
    (nonempty : shape ≠ .nil) {joinCost : Nat}
    (join : Pointer.Trace ⟨.node a b, []⟩ ⟨shape, []⟩ joinCost) :
    ∃ cost, Pointer.Trace ⟨p.tree, []⟩
      ⟨(Pair.mk p.lower (rest.replaceTop (.leaf shape newCharge))).tree, []⟩ cost ∧
      cost ≤ p.upper.popCost + joinCost + 6 := by
  obtain ⟨innerCost, inner, innerBound⟩ := merge_front popped stored newCharge nonempty join
  have resultNonempty : (rest.replaceTop (.leaf shape newCharge)).decode.tree ≠ .nil := by
    rw [replaceTop_decode]
    cases rest.topTail with
    | none => exact nonempty
    | some suffix => intro h; cases h
  have trace := inner.inContext (popped_nonempty popped) resultNonempty [.right p.lower.decode.tree.mirror]
  refine ⟨innerCost + 2, ?_, by omega⟩
  convert trace using 1 <;>
    simp only [Pair.tree, Pointer.plug, List.length_cons, List.length_nil]
  omega

theorem rotateRight_trace {p : Pair} {rest : Layer} {a b shape : Tree} {firstCharge secondCharge : ℝ}
    (popped : p.lower.pop = some (.leaf b.mirror firstCharge, rest))
    (stored : rest.top = .leaf a.mirror secondCharge) (newCharge : ℝ)
    (nonempty : shape ≠ .nil) {joinCost : Nat}
    (join : Pointer.Trace ⟨.node a b, []⟩ ⟨shape, []⟩ joinCost) :
    ∃ cost, Pointer.Trace ⟨p.tree, []⟩
      ⟨(Pair.mk (rest.replaceTop (.leaf shape.mirror newCharge)) p.upper).tree, []⟩ cost ∧
      cost ≤ p.lower.popCost + joinCost + 6 := by
  have mirrorNonempty : shape.mirror ≠ .nil := by
    intro empty
    apply nonempty
    have eq := congrArg Tree.mirror empty
    simpa only [Tree.mirror_mirror, Tree.mirror] using eq
  have mirroredJoin : Pointer.Trace ⟨.node b.mirror a.mirror, []⟩ ⟨shape.mirror, []⟩ joinCost := by
    simpa only [Pointer.Config.mirror, Tree.mirror, List.map_nil] using join.mirror
  obtain ⟨cost, trace, bound⟩ := rotateLeft_trace (p := p.flip) popped stored newCharge mirrorNonempty mirroredJoin
  refine ⟨cost, ?_, bound⟩
  simpa only [Pointer.Config.mirror, Pair.flip, Pair.tree, Tree.mirror,
    Tree.mirror_mirror, List.map_nil] using trace.mirror

end RotationBST.HeavyPath.Finger.Transfer.Rotation
