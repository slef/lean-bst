module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Interruption.Up
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Transfer.Interruption
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
theorem collect_front_within {stack rest : Layer} {a b : Tree} {firstCharge secondCharge : ℝ}
    (popped : stack.pop = some (.leaf a firstCharge, rest))
    (stored : rest.top = .leaf b secondCharge) (newCharge : ℝ) :
    ∃ cost, Pointer.TraceWithin (fun t => t.size = stack.decode.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth stack.decode.tree x + 10) ⟨stack.decode.tree, []⟩
      ⟨(rest.replaceTop (.leaf (.node a b) newCharge)).decode.tree, []⟩ cost ∧
      cost ≤ stack.popCost + 2 := by
  have pop := Chocolate.Interruption.Results.pop_within popped
  change Pointer.TraceWithin (fun t => t.size = stack.decode.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth stack.decode.tree x + 8)
      ⟨stack.decode.tree, []⟩ ⟨.node a rest.decode.tree, []⟩ stack.popCost at pop
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
    exact pop.weaken (by
      intro t bound
      exact ⟨bound.1, fun x => by have h := bound.2 x; omega⟩)
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
    have result := StaticTree.Trace.within_append (a := ⟨stack.decode.tree, []⟩)
      (b := ⟨.node a (.node b suffix.tree), []⟩) (f := 4) (u := 8) (v := 2)
      (by decide : 1 ≤ 1) pop
      (by simpa only [Nat.one_mul] using StaticTree.Trace.within_size_depth rotate)
    exact result

/-- Perform the recursive join inside the collected front occurrence. -/
theorem merge_front_within {stack rest : Layer} {a b shape : Tree} {firstCharge secondCharge : ℝ}
    (popped : stack.pop = some (.leaf a firstCharge, rest))
    (stored : rest.top = .leaf b secondCharge) (newCharge : ℝ)
    (nonempty : shape ≠ .nil) {joinCost : Nat}
    (join : Pointer.TraceWithin (fun t => t.size = (Tree.node a b).size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth (.node a b) x + 16)
      ⟨.node a b, []⟩ ⟨shape, []⟩ joinCost) :
    ∃ cost, Pointer.TraceWithin (fun t => t.size = stack.decode.tree.size ∧
      ∀ x, Tree.depth t x ≤ 16 * Tree.depth stack.decode.tree x + 56) ⟨stack.decode.tree, []⟩
      ⟨(rest.replaceTop (.leaf shape newCharge)).decode.tree, []⟩ cost ∧
      cost ≤ stack.popCost + joinCost + 4 := by
  obtain ⟨collectCost, collect, collectBound⟩ := collect_front_within popped stored newCharge
  let prepared := rest.replaceTop (.leaf (.node a b) newCharge)
  have top : prepared.top = .leaf (.node a b) newCharge := replaceTop_top _ _
  have inner : Pointer.TraceWithin (fun t => t.size = prepared.top.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth prepared.top.tree x + 16)
      ⟨prepared.top.tree, []⟩ ⟨shape, []⟩ joinCost := by
    simpa only [top, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree] using join
  obtain ⟨insideCost, insideBound, inside⟩ := Chocolate.replaceTop_within prepared
    (.leaf shape newCharge) (by decide : 1 ≤ 4) (by rw [top]; intro h; cases h) nonempty inner
  change Pointer.TraceWithin (fun t => t.size = prepared.decode.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth prepared.decode.tree x + 16)
      ⟨prepared.decode.tree, []⟩
    ⟨((rest.replaceTop _).replaceTop _).decode.tree, []⟩ insideCost at inside
  rw [replaceTop_replaceTop] at inside
  have result := StaticTree.Trace.within_append (a := ⟨stack.decode.tree, []⟩)
    (b := ⟨prepared.decode.tree, []⟩) (f := 4) (u := 10) (v := 16)
    (by decide : 1 ≤ 4) collect inside
  exact ⟨_, result, by omega⟩

theorem rotateLeft_within {p : Pair} {rest : Layer} {a b shape : Tree} {firstCharge secondCharge : ℝ}
    (popped : p.upper.pop = some (.leaf a firstCharge, rest))
    (stored : rest.top = .leaf b secondCharge) (newCharge : ℝ)
    (nonempty : shape ≠ .nil) {joinCost : Nat}
    (join : Pointer.TraceWithin (fun t => t.size = (Tree.node a b).size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth (.node a b) x + 16)
      ⟨.node a b, []⟩ ⟨shape, []⟩ joinCost) :
    ∃ cost, Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 16 * Tree.depth p.tree x + 56) ⟨p.tree, []⟩
      ⟨(Pair.mk p.lower (rest.replaceTop (.leaf shape newCharge))).tree, []⟩ cost ∧
      cost ≤ p.upper.popCost + joinCost + 6 := by
  obtain ⟨innerCost, inner, innerBound⟩ := merge_front_within popped stored newCharge nonempty join
  have resultNonempty : (rest.replaceTop (.leaf shape newCharge)).decode.tree ≠ .nil := by
    rw [replaceTop_decode]
    cases rest.topTail with
    | none => exact nonempty
    | some suffix => intro h; cases h
  have trace := StaticTree.Trace.within_embed [.right p.lower.decode.tree.mirror]
    (by decide : 1 ≤ 16) inner (popped_nonempty popped) resultNonempty
  refine ⟨innerCost + 2, ?_, by omega⟩
  convert trace using 1 <;>
    simp only [Pair.tree, Pointer.plug, List.length_cons, List.length_nil]
  omega

theorem rotateRight_within {p : Pair} {rest : Layer} {a b shape : Tree} {firstCharge secondCharge : ℝ}
    (popped : p.lower.pop = some (.leaf b.mirror firstCharge, rest))
    (stored : rest.top = .leaf a.mirror secondCharge) (newCharge : ℝ)
    (nonempty : shape ≠ .nil) {joinCost : Nat}
    (join : Pointer.TraceWithin (fun t => t.size = (Tree.node a b).size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth (.node a b) x + 16)
      ⟨.node a b, []⟩ ⟨shape, []⟩ joinCost) :
    ∃ cost, Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 16 * Tree.depth p.tree x + 56) ⟨p.tree, []⟩
      ⟨(Pair.mk (rest.replaceTop (.leaf shape.mirror newCharge)) p.upper).tree, []⟩ cost ∧
      cost ≤ p.lower.popCost + joinCost + 6 := by
  have mirrorNonempty : shape.mirror ≠ .nil := by
    intro empty
    apply nonempty
    have eq := congrArg Tree.mirror empty
    simpa only [Tree.mirror_mirror, Tree.mirror] using eq
  have mirroredJoin : Pointer.TraceWithin (fun t => t.size = (Tree.node b.mirror a.mirror).size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth (.node b.mirror a.mirror) x + 16)
      ⟨.node b.mirror a.mirror, []⟩ ⟨shape.mirror, []⟩ joinCost := by
    simpa only [Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug, Tree.mirror, Tree.mirror_size, List.map_nil] using
      StaticTree.Trace.within_mirror_depth (a := ⟨.node a b, []⟩)
        (constant := 16) (by decide : 1 ≤ 4) join
  obtain ⟨cost, trace, bound⟩ := rotateLeft_within (p := p.flip) popped stored newCharge mirrorNonempty mirroredJoin
  refine ⟨cost, ?_, bound⟩
  have result := StaticTree.Trace.within_mirror_depth (a := ⟨p.flip.tree, []⟩)
    (constant := 56) (by decide : 1 ≤ 16) trace
  simpa only [Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug, Pair.flip, Pair.tree, Tree.mirror,
    Tree.mirror_mirror, Tree.mirror_size, List.map_nil] using result

end RotationBST.HeavyPath.Finger.Transfer.Interruption
