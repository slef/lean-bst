module

import RotationBST.Audit.Check
public import RotationBST.Bounds.StaticTree.Trace.AbstractBridge

@[expose] public section
namespace RotationBST.StaticTree.Trace.Results
open _root_.RotationBST.Tree (depth)

theorem rotate_depth {s t : Tree} (rotation : Rotate s t) (x : Nat) :
    depth t x ≤ depth s x + 1 :=
  RotationBST.StaticTree.Trace.rotate_depth rotation x

theorem rotations_depth {s t : Tree} {cost : Nat} (rotations : Rotations s t cost) (x : Nat) :
    depth t x ≤ depth s x + cost :=
  RotationBST.StaticTree.Trace.rotations_depth rotations x

theorem trace_depth {s t : Pointer.Config} {cost : Nat} (trace : Pointer.Trace s t cost) (x : Nat) :
    depth t.tree x ≤ depth s.tree x + cost :=
  RotationBST.StaticTree.Trace.trace_depth trace x

theorem trace_depth_reverse {s t : Pointer.Config} {cost : Nat} (trace : Pointer.Trace s t cost) (x : Nat) :
    depth s.tree x ≤ depth t.tree x + cost :=
  RotationBST.StaticTree.Trace.trace_depth_reverse trace x

theorem replay_prefix_depth {ops : List Multifinger.Opcode} {s t : Pointer.Config}
    (executed : Multifinger.replay ops s = some t) (cut : Nat) :
    ∃ middle, Multifinger.replay (ops.take cut) s = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some t ∧
      ∀ x, depth middle.tree x ≤ min (depth s.tree x + (ops.take cut).length)
        (depth t.tree x + (ops.drop cut).length) :=
  RotationBST.StaticTree.Trace.replay_prefix_depth executed cut

theorem replay_prefix_bound {ops : List Multifinger.Opcode} {s t : Pointer.Config}
    (executed : Multifinger.replay ops s = some t) {budget : ℝ}
    (cost : (ops.length : ℝ) ≤ budget) (cut : Nat) :
    ∃ middle, Multifinger.replay (ops.take cut) s = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some t ∧
      ∀ x, (depth middle.tree x : ℝ) ≤ depth s.tree x + budget :=
  RotationBST.StaticTree.Trace.replay_prefix_bound executed cost cut

theorem within_size_depth {a b : Pointer.Config} {cost : Nat} (trace : Pointer.Trace a b cost) :
    Pointer.TraceWithin (fun t => t.size = a.tree.size ∧ ∀ x, depth t x ≤ depth a.tree x + cost) a b cost :=
  RotationBST.StaticTree.Trace.within_size_depth trace

theorem plug_bound (cs : List Pointer.Frame) {s t : Tree} {factor constant : Nat}
    (factorPositive : 1 ≤ factor) (size : t.size = s.size)
    (bound : ∀ x, depth t x ≤ factor * depth s x + constant) :
    ∀ x, depth (Pointer.plug cs t) x ≤ factor * depth (Pointer.plug cs s) x + constant :=
  RotationBST.StaticTree.Trace.plug_bound cs factorPositive size bound

theorem within_embed {s t : Tree} {cost factor constant : Nat} (cs : List Pointer.Frame)
    (factorPositive : 1 ≤ factor)
    (h : Pointer.TraceWithin (fun u => u.size = s.size ∧
      ∀ x, depth u x ≤ factor * depth s x + constant) ⟨s, []⟩ ⟨t, []⟩ cost)
    (liveS : s ≠ .nil) (liveT : t ≠ .nil) :
    Pointer.TraceWithin (fun u => u.size = (Pointer.plug cs s).size ∧
      ∀ x, depth u x ≤ factor * depth (Pointer.plug cs s) x + constant)
      ⟨Pointer.plug cs s, []⟩ ⟨Pointer.plug cs t, []⟩ (cs.length + cost + cs.length) :=
  RotationBST.StaticTree.Trace.within_embed cs factorPositive h liveS liveT

theorem mirror_rank_depth (t : Tree) (x : Nat) (inside : x < t.size) :
    depth t.mirror (t.size - 1 - x) = depth t x :=
  RotationBST.StaticTree.Trace.mirror_rank_depth t x inside

theorem mirror_bound {s t : Tree} {factor constant : Nat} (factorPositive : 1 ≤ factor)
    (size : t.size = s.size) (bound : ∀ x, depth t x ≤ factor * depth s x + constant) :
    ∀ x, depth t.mirror x ≤ factor * depth s.mirror x + constant :=
  RotationBST.StaticTree.Trace.mirror_bound factorPositive size bound

theorem within_mirror_depth {a b : Pointer.Config} {cost factor constant : Nat}
    (factorPositive : 1 ≤ factor)
    (h : Pointer.TraceWithin (fun t => t.size = a.tree.size ∧
      ∀ x, depth t x ≤ factor * depth a.tree x + constant) a b cost) :
    Pointer.TraceWithin (fun t => t.size = a.mirror.tree.size ∧
      ∀ x, depth t x ≤ factor * depth a.mirror.tree x + constant) a.mirror b.mirror cost :=
  RotationBST.StaticTree.Trace.within_mirror_depth factorPositive h

theorem within_append {a b c : Pointer.Config} {firstCost lastCost f g u v : Nat}
    (positive : 1 ≤ g)
    (first : Pointer.TraceWithin (fun t => t.size = a.tree.size ∧
      ∀ x, depth t x ≤ f * depth a.tree x + u) a b firstCost)
    (last : Pointer.TraceWithin (fun t => t.size = b.tree.size ∧
      ∀ x, depth t x ≤ g * depth b.tree x + v) b c lastCost) :
    Pointer.TraceWithin (fun t => t.size = a.tree.size ∧
      ∀ x, depth t x ≤ (g * f) * depth a.tree x + (g * u + v)) a c (firstCost + lastCost) :=
  RotationBST.StaticTree.Trace.within_append positive first last

end RotationBST.StaticTree.Trace.Results

/-- info: abstract audit passed for `RotationBST.StaticTree.Trace.Results`: 13 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.StaticTree.Trace.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Models.Pointer.Invariant.Definitions.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract]
