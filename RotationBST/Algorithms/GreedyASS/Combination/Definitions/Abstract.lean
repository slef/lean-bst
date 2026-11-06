module

public import RotationBST.Algorithms.Combination.Online.Replay.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Worker.Pair.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Charges.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Combination.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Reference.Abstract
public import RotationBST.Models.Pointer.Lazy.Online.Definitions.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Combination
open Combo

abbrev SourceState := List Nat × Pointer.Lazy.Online.State

/-- One linear restart allowance covers both the GreedyASS and bottom-up
Tango sources, independently of the doubly logarithmic competitive factor. -/
noncomputable def overhead (saved : Tree) : Nat :=
  46225920 * saved.size

/-- The reference tree is an analysis parameter, not an algorithm input. -/
noncomputable def charges (saved reference : Tree) : Analysis.Charges :=
  fun side => if side then
    Charges.interleave (Tango.Combination.linearChargeFactor (Tango.balanced saved.size)) (Tango.balanced saved.size)
  else Charges.lazyFinger 46225920 reference

abbrev pairModel {saved : Tree} (left right : Worker.Replay.Planner SourceState saved) :=
  Worker.Pair.model (Worker.Replay.model left) (Worker.Replay.model right) false false

/-- One certified combined policy. Both sources, their shared snapshot, and
its interruptible replay implementation are fixed before choosing a benchmark
or request sequence. The source contract holds for every reference shape. -/
structure Policy (saved : Tree) (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) where
  left : Worker.Replay.Planner SourceState saved
  right : Worker.Replay.Planner SourceState saved
  supported : ∀ reference : Tree, reference.size = saved.size →
    Analysis.WellBehaved (Worker.Pair.worker (Worker.Replay.worker left) (Worker.Replay.worker right) false false)
      saved.size (overhead saved) 1 20 (charges saved reference)
  prepared : Online.Prepared (pairModel left right) (Analysis.budget (overhead saved) 20)
    (57 * overhead saved) fields oldData
  implementation : Online.Replay.Implementation prepared

/-- The actual physical execution of the prepared policy, including startup. -/
noncomputable def Policy.cost {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (xs : List Nat) : Nat :=
  (Online.execute p.prepared none xs).2

noncomputable def Policy.finalTree {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (xs : List Nat) : Tree :=
  p.prepared.current (Online.execute p.prepared none xs).1

end RotationBST.Geometric.GreedyASS.Combination
