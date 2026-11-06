module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Interruption.Rotation
public import RotationBST.Models.Pointer.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Transfer.Interruption
open PopTart PopTart.WeightedTree PopTart.Chocolate

private theorem trace_size {s t : Tree} {cost : Nat}
    (trace : Pointer.Trace ⟨s, []⟩ ⟨t, []⟩ cost) : s.size = t.size := by
  obtain ⟨_, _, rotations⟩ := trace.rotations
  exact rotations.size_eq

private theorem mirror_nonempty {t : Tree} (nonempty : t ≠ .nil) : t.mirror ≠ .nil := by
  intro h
  have eq := congrArg Tree.mirror h
  apply nonempty
  simpa only [Tree.mirror_mirror, Tree.mirror] using eq

/-- A physical root exposure inside the first opaque payload can be composed
with the finger transfer. Every entrance and return through the two enclosing
separators is charged, even when an ancestor intervenes. -/
theorem downLeft_exposed_within {p : Pair} (valid : p.Valid) {old a b : Tree} {oldCharge : ℝ}
    (stored : p.lower.top = .leaf old.mirror oldCharge) {exposureCost : Nat}
    (exposure : Pointer.TraceWithin (fun t => t.size = old.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth old x + 10)
      ⟨old, []⟩ ⟨.node a b, []⟩ exposureCost)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ cost, Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 16 * Tree.depth p.tree x + 64) ⟨p.tree, []⟩ ⟨(p.downLeft a b lowerCharge upperCharge).tree, []⟩ cost ∧
      cost + (p.downLeft a b lowerCharge upperCharge).potential ≤ exposureCost + 30 + p.potential ∧
      (p.downLeft a b lowerCharge upperCharge).Valid ∧
      (p.downLeft a b lowerCharge upperCharge).mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk (p.downLeft a b lowerCharge upperCharge).tree []).key? =
        some (p.lower.decode.tree.mirror.size - b.size - 1) ∧
      cost ≤ exposureCost + p.upper.pushCost + 10 := by
  have oldSize := trace_size exposure.trace
  have oldNonempty : old ≠ .nil := by
    intro empty
    rw [empty, Tree.size, Tree.size] at oldSize
    omega
  have oldNN : 0 ≤ oldCharge := by
    have nn := (Chocolate.Top.Results.top_valid valid.1).2
    simpa only [stored, WeightedTree.Nonnegative] using nn
  let new : WeightedTree := .leaf (Tree.node a b).mirror oldCharge
  let q : Pair := ⟨p.lower.replaceTop new, p.upper⟩
  have qValid : q.Valid :=
    ⟨Chocolate.Top.Results.replaceTop_valid valid.1 (.leaf _ _) oldNN, valid.2⟩
  have qTop : q.lower.top = new := Chocolate.Top.Results.replaceTop_top p.lower new
  have qFinal : q.downLeft a b lowerCharge upperCharge = p.downLeft a b lowerCharge upperCharge := by
    simp only [Pair.downLeft, q, Chocolate.Top.Results.replaceTop_replaceTop]
  have qPotential : q.potential = p.potential := by
    simp only [q, Pair.potential, Chocolate.Top.Results.replaceTop_potential valid.1]
  have qMass : q.mass = p.mass := by
    have balance := Chocolate.Top.Results.replaceTop_mass p.lower new
    rw [stored] at balance
    change (p.lower.replaceTop new).decode.mass + oldCharge = p.lower.decode.mass + oldCharge at balance
    change (p.lower.replaceTop new).decode.mass + p.upper.decode.mass = p.lower.decode.mass + p.upper.decode.mass
    linarith
  have qSize : q.lower.decode.tree.mirror.size = p.lower.decode.tree.mirror.size := by
    have balance := Chocolate.Top.Results.replaceTop_size p.lower new
    rw [stored] at balance
    change (p.lower.replaceTop new).decode.tree.size + old.mirror.size =
      p.lower.decode.tree.size + (Tree.node a b).mirror.size at balance
    simp only [Tree.mirror_size] at balance ⊢
    change (p.lower.replaceTop new).decode.tree.size = p.lower.decode.tree.size
    omega
  have mirrored : Pointer.TraceWithin (fun t => t.size = p.lower.top.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.lower.top.tree x + 10)
      ⟨p.lower.top.tree, []⟩ ⟨new.tree, []⟩ exposureCost := by
    simpa only [stored, new, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree,
      Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug, Tree.mirror_size, List.map_nil] using
      StaticTree.Trace.within_mirror_depth (a := ⟨old, []⟩)
        (constant := 10) (by decide : 1 ≤ 4) exposure
  have topNonempty : p.lower.top.tree ≠ .nil := by
    simpa only [stored, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree] using
      mirror_nonempty oldNonempty
  obtain ⟨insideCost, insideBound, inside⟩ := Chocolate.replaceTop_within p.lower new
    (by decide : 1 ≤ 4) topNonempty (by intro h; cases h) mirrored
  have oldLowerNonempty : p.lower.decode.tree.mirror ≠ .nil := by
    rw [Chocolate.Top.Results.decode_top]
    cases p.lower.topTail with
    | none => exact mirror_nonempty topNonempty
    | some tail => intro h; cases h
  have newLowerNonempty : (p.lower.replaceTop new).decode.tree.mirror ≠ .nil := by
    rw [Chocolate.Top.Results.replaceTop_decode]
    cases p.lower.topTail <;> intro h <;> cases h
  have reflected := StaticTree.Trace.within_mirror_depth
    (a := ⟨p.lower.decode.tree, []⟩) (constant := 10) (by decide : 1 ≤ 4) inside
  have rootTrace : Pointer.TraceWithin (fun t => t.size = p.lower.decode.tree.mirror.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.lower.decode.tree.mirror x + 10)
      ⟨p.lower.decode.tree.mirror, []⟩ ⟨(p.lower.replaceTop new).decode.tree.mirror, []⟩ insideCost := by
    simpa only [Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug, List.map_nil] using reflected
  have embedded := StaticTree.Trace.within_embed [.left p.upper.decode.tree]
    (by decide : 1 ≤ 4) rootTrace oldLowerNonempty newLowerNonempty
  have prepare : Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.tree x + 10)
      ⟨p.tree, []⟩ ⟨q.tree, []⟩ (insideCost + 2) := by
    convert embedded using 1 <;>
      simp only [Pair.tree, q, Pointer.plug,
        List.length_cons, List.length_nil]
    omega
  have moved := StaticTree.Trace.within_append (a := ⟨p.tree, []⟩) (b := ⟨q.tree, []⟩)
    (f := 4) (u := 10) (v := 24) (by decide : 1 ≤ 4) prepare
    (downLeft_within qTop lowerCharge upperCharge)
  have bound := Transfer.Results.downLeft_amortized qValid a b lowerCharge upperNonnegative
  have mass := Transfer.Results.downLeft_mass qValid qTop lowerCharge upperNonnegative
  have rank := Transfer.Results.downLeft_root_key qTop lowerCharge upperCharge
  rw [qFinal] at moved bound mass rank
  rw [qPotential] at bound
  rw [qMass] at mass
  rw [qSize] at rank
  refine ⟨_, moved, by omega, Transfer.Results.downLeft_valid valid a b lowerNonnegative upperNonnegative,
    mass, rank, ?_⟩
  have exposeBound : q.leftExposeCost ≤ 4 := by
    unfold Pair.leftExposeCost
    cases q.lower.topTail <;> norm_num
  change insideCost + 2 + (q.leftExposeCost + p.upper.pushCost + 2) ≤
    exposureCost + p.upper.pushCost + 10
  omega

/-- Reflection preserves the complete exposure-and-transfer cost certificate. -/
theorem downRight_exposed_within {p : Pair} (valid : p.Valid) {old a b : Tree} {oldCharge : ℝ}
    (stored : p.upper.top = .leaf old oldCharge) {exposureCost : Nat}
    (exposure : Pointer.TraceWithin (fun t => t.size = old.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth old x + 10)
      ⟨old, []⟩ ⟨.node a b, []⟩ exposureCost)
    {lowerCharge upperCharge : ℝ} (lowerNonnegative : 0 ≤ lowerCharge) (upperNonnegative : 0 ≤ upperCharge) :
    ∃ cost, Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
      ∀ x, Tree.depth t x ≤ 16 * Tree.depth p.tree x + 64) ⟨p.tree, []⟩ ⟨(p.downRight a b lowerCharge upperCharge).tree, []⟩ cost ∧
      cost + (p.downRight a b lowerCharge upperCharge).potential ≤ exposureCost + 30 + p.potential ∧
      (p.downRight a b lowerCharge upperCharge).Valid ∧
      (p.downRight a b lowerCharge upperCharge).mass + oldCharge = p.mass + lowerCharge + upperCharge ∧
      (Pointer.Config.mk (p.downRight a b lowerCharge upperCharge).tree []).key? =
        some (p.lower.decode.tree.mirror.size + a.size + 1) ∧
      cost ≤ exposureCost + p.lower.pushCost + 10 := by
  have reflected : p.flip.lower.top = .leaf old.mirror.mirror oldCharge := by
    simpa only [Pair.flip, Tree.mirror_mirror] using stored
  obtain ⟨cost, trace, bound, _, mass, _, worst⟩ := downLeft_exposed_within (p := p.flip) ⟨valid.2, valid.1⟩
    reflected (by
      simpa only [Pointer.Config.mirror, Pointer.Config.tree, Pointer.plug,
        Tree.mirror, Tree.mirror_size, List.map_nil] using
        StaticTree.Trace.within_mirror_depth (a := ⟨old, []⟩)
          (constant := 10) (by decide : 1 ≤ 4) exposure)
    upperNonnegative lowerNonnegative
  refine ⟨cost, ?_, ?_, Transfer.Results.downRight_valid valid a b lowerNonnegative upperNonnegative, ?_,
    Transfer.Results.downRight_root_key p a b lowerCharge upperCharge, worst⟩
  · have result := StaticTree.Trace.within_mirror_depth (a := ⟨p.flip.tree, []⟩)
      (constant := 64) (by decide : 1 ≤ 16) trace
    simpa only [Pair.downRight, Transfer.Results.flip_tree, Pointer.Config.mirror,
      Pointer.Config.tree, Pointer.plug, List.map_nil, Tree.mirror_mirror, Tree.mirror_size] using result
  · simpa only [Pair.downRight, Transfer.Results.flip_potential] using bound
  · simpa only [Pair.downRight, Transfer.Results.flip_mass, add_assoc, add_comm, add_left_comm] using mass

end RotationBST.HeavyPath.Finger.Transfer.Interruption
