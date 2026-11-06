module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Interruption.Down
public import RotationBST.Models.Pointer.Reversal
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

/-- Pop the parent-side stack and restore the departing finger subtree as
one opaque payload. The reverse exposure charges every pointer instruction. -/
theorem collect_left_within {p : Pair} {a b : Tree} {lowerCharge upperCharge : ℝ}
    (stored : p.lower.top = .leaf a.mirror lowerCharge) {rest : Layer}
    (popped : p.upper.pop = some (.leaf b upperCharge, rest)) (newCharge : ℝ) :
    ∃ cost, Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.tree x + 20) ⟨p.tree, []⟩
      ⟨(Pair.mk (p.lower.replaceTop (.leaf (Tree.node a b).mirror newCharge)) rest).tree, []⟩ cost ∧
      cost ≤ p.upper.popCost + 14 := by
  let q : Pair := ⟨p.lower.replaceTop (.leaf (Tree.node a b).mirror newCharge), rest⟩
  have qTop : q.lower.top = .leaf (Tree.node a b).mirror newCharge := replaceTop_top _ _
  have restored : (q.lower.replaceTop (.leaf a.mirror lowerCharge)).decode = p.lower.decode := by
    change ((p.lower.replaceTop _).replaceTop _).decode = _
    rw [replaceTop_replaceTop, replaceTop_decode, ← stored, ← decode_top]
  obtain ⟨reverseCost, reverseBound, reverseTrace⟩ := (expose_left_trace qTop lowerCharge).reverse
  rw [restored] at reverseTrace
  have exposeBound : q.leftExposeCost ≤ 4 := by
    unfold Pair.leftExposeCost
    cases q.lower.topTail <;> norm_num
  have pop := StaticTree.Trace.within_embed [.right p.lower.decode.tree.mirror]
    (by decide : 1 ≤ 4) (Chocolate.Interruption.Results.pop_within popped)
    (popped_nonempty popped) (by intro h; cases h)
  have prepare : Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.tree x + 8) ⟨p.tree, []⟩
      ⟨.node p.lower.decode.tree.mirror (.node b rest.decode.tree), []⟩ (p.upper.popCost + 2) := by
    convert pop using 1 <;>
      simp only [Pair.tree, Pointer.plug, WeightedTree.tree, WeightedTree.skeleton,
        Pointer.Lazy.Skeleton.tree, List.length_cons, List.length_nil]
    omega
  have result := StaticTree.Trace.within_append (a := ⟨p.tree, []⟩)
    (b := ⟨.node p.lower.decode.tree.mirror (.node b rest.decode.tree), []⟩)
    (f := 4) (u := 8) (v := reverseCost) (by decide : 1 ≤ 1) prepare
    (by simpa only [Nat.one_mul] using StaticTree.Trace.within_size_depth reverseTrace)
  refine ⟨_, result.weaken ?_, by omega⟩
  intro t bound
  refine ⟨bound.1, ?_⟩
  intro x
  have h := bound.2 x
  change Tree.depth t x ≤ (1 * 4) * Tree.depth p.tree x + (1 * 8 + reverseCost) at h
  omega

/-- Execute a supplied join inside the innermost lower payload. -/
theorem join_lower_within {p : Pair} {a b shape : Tree} {charge : ℝ}
    (stored : p.lower.top = .leaf (Tree.node a b).mirror charge)
    (nonempty : shape ≠ .nil) {joinCost : Nat}
    (join : Pointer.TraceWithin (fun t => t.size = (Tree.node a b).size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth (.node a b) x + 16)
      ⟨.node a b, []⟩ ⟨shape, []⟩ joinCost) :
    ∃ cost, Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.tree x + 16) ⟨p.tree, []⟩
      ⟨(Pair.mk (p.lower.replaceTop (.leaf shape.mirror charge)) p.upper).tree, []⟩ cost ∧
      cost ≤ joinCost + 4 := by
  have mirrorNonempty : shape.mirror ≠ .nil := by
    intro empty
    apply nonempty
    have eq := congrArg Tree.mirror empty
    simpa only [Tree.mirror_mirror, Tree.mirror] using eq
  have inner : Pointer.TraceWithin (fun t => t.size = p.lower.top.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.lower.top.tree x + 16)
      ⟨p.lower.top.tree, []⟩ ⟨shape.mirror, []⟩ joinCost := by
    simpa only [stored, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree,
      Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug, Tree.mirror_size, List.map_nil] using
      StaticTree.Trace.within_mirror_depth (a := ⟨.node a b, []⟩)
        (constant := 16) (by decide : 1 ≤ 4) join
  obtain ⟨insideCost, insideBound, inside⟩ := Chocolate.replaceTop_within p.lower
    (.leaf shape.mirror charge) (by decide : 1 ≤ 4) (by rw [stored]; intro h; cases h) mirrorNonempty inner
  have oldNonempty : p.lower.decode.tree.mirror ≠ .nil := by
    rw [decode_top, stored]
    cases p.lower.topTail <;> intro h <;> cases h
  have newNonempty : (p.lower.replaceTop (.leaf shape.mirror charge)).decode.tree.mirror ≠ .nil := by
    rw [replaceTop_decode]
    cases p.lower.topTail with
    | none => simpa only [Option.elim, WeightedTree.tree, WeightedTree.skeleton,
        Pointer.Lazy.Skeleton.tree, Tree.mirror_mirror] using nonempty
    | some tail => intro h; cases h
  have mirrored := StaticTree.Trace.within_mirror_depth
    (a := ⟨p.lower.decode.tree, []⟩) (constant := 16) (by decide : 1 ≤ 4) inside
  have rootTrace : Pointer.TraceWithin (fun t => t.size = p.lower.decode.tree.mirror.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.lower.decode.tree.mirror x + 16)
      ⟨p.lower.decode.tree.mirror, []⟩
      ⟨(p.lower.replaceTop (.leaf shape.mirror charge)).decode.tree.mirror, []⟩ insideCost := by
    simpa only [Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug, List.map_nil] using mirrored
  have result := StaticTree.Trace.within_embed [.left p.upper.decode.tree]
    (by decide : 1 ≤ 4) rootTrace oldNonempty newNonempty
  refine ⟨insideCost + 2, ?_, by omega⟩
  convert result using 1 <;>
    simp only [Pair.tree, Pointer.plug, List.length_cons, List.length_nil]
  omega

theorem upLeft_within {p : Pair} {a b shape : Tree} {lowerCharge upperCharge : ℝ}
    (stored : p.lower.top = .leaf a.mirror lowerCharge) {rest : Layer}
    (popped : p.upper.pop = some (.leaf b upperCharge, rest)) (newCharge : ℝ)
    (nonempty : shape ≠ .nil) {joinCost : Nat}
    (join : Pointer.TraceWithin (fun t => t.size = (Tree.node a b).size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth (.node a b) x + 16)
      ⟨.node a b, []⟩ ⟨shape, []⟩ joinCost) :
    ∃ cost, Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 16 * Tree.depth p.tree x + 96) ⟨p.tree, []⟩
      ⟨(Pair.mk (p.lower.replaceTop (.leaf shape.mirror newCharge)) rest).tree, []⟩ cost ∧
      cost ≤ p.upper.popCost + joinCost + 18 := by
  obtain ⟨collectCost, collect, collectBound⟩ := collect_left_within stored popped newCharge
  obtain ⟨insideCost, inside, insideBound⟩ := join_lower_within
    (p := ⟨p.lower.replaceTop (.leaf (Tree.node a b).mirror newCharge), rest⟩)
    (replaceTop_top _ _) nonempty join
  rw [replaceTop_replaceTop] at inside
  have result := StaticTree.Trace.within_append (a := ⟨p.tree, []⟩)
    (b := ⟨(Pair.mk (p.lower.replaceTop (.leaf (Tree.node a b).mirror newCharge)) rest).tree, []⟩)
    (f := 4) (u := 20) (v := 16) (by decide : 1 ≤ 4) collect inside
  exact ⟨_, result, by omega⟩

theorem upRight_within {p : Pair} {a b shape : Tree} {lowerCharge upperCharge : ℝ}
    (stored : p.upper.top = .leaf b upperCharge) {rest : Layer}
    (popped : p.lower.pop = some (.leaf a.mirror lowerCharge, rest)) (newCharge : ℝ)
    (nonempty : shape ≠ .nil) {joinCost : Nat}
    (join : Pointer.TraceWithin (fun t => t.size = (Tree.node a b).size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth (.node a b) x + 16)
      ⟨.node a b, []⟩ ⟨shape, []⟩ joinCost) :
    ∃ cost, Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 16 * Tree.depth p.tree x + 96) ⟨p.tree, []⟩
      ⟨(Pair.mk rest (p.upper.replaceTop (.leaf shape newCharge))).tree, []⟩ cost ∧
      cost ≤ p.lower.popCost + joinCost + 18 := by
  have mirroredStored : p.flip.lower.top = .leaf b.mirror.mirror upperCharge := by
    simpa only [Pair.flip, Tree.mirror_mirror] using stored
  have mirroredNonempty : shape.mirror ≠ .nil := by
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
  obtain ⟨cost, trace, bound⟩ := upLeft_within mirroredStored popped newCharge mirroredNonempty mirroredJoin
  refine ⟨cost, ?_, bound⟩
  have result := StaticTree.Trace.within_mirror_depth (a := ⟨p.flip.tree, []⟩)
    (constant := 96) (by decide : 1 ≤ 16) trace
  simpa only [Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug, Pair.flip, Pair.tree, Tree.mirror,
    Tree.mirror_mirror, Tree.mirror_size, List.map_nil] using result

end RotationBST.HeavyPath.Finger.Transfer.Interruption
