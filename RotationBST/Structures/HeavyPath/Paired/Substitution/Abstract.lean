module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Paired.Substitution.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Substitution.Results
open Paired LabelledCursor

theorem pushWith_trace {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) (frame : Frame α) (p : Stacks)
    (cs : List Pointer.Frame) :
    Pointer.Trace ⟨p.tree, replaceFrame payload frame :: cs⟩ ⟨(p.pushWith weight payload frame).tree, cs⟩ (p.pushCost frame) :=
  RotationBST.HeavyPath.Paired.pushWith_trace weight payload frame p cs

theorem pushWith_valid {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (payload : LabelledTree α → Tree) (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) : (p.pushWith weight payload frame).Valid :=
  RotationBST.HeavyPath.Paired.pushWith_valid payload valid nonnegative

theorem pushWith_amortized {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (payload : LabelledTree α → Tree) (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) :
    p.pushCost frame + (p.pushWith weight payload frame).potential ≤ 23 + p.potential :=
  RotationBST.HeavyPath.Paired.pushWith_amortized payload valid nonnegative

theorem pushWith_mass {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (payload : LabelledTree α → Tree) (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) :
    (p.pushWith weight payload frame).mass = p.mass + frameMass weight frame :=
  RotationBST.HeavyPath.Paired.pushWith_mass payload valid nonnegative

theorem pushWith_lower_size {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) (frame : Frame α) (p : Stacks) :
    (p.pushWith weight payload frame).lower.decode.tree.size =
      p.lower.decode.tree.size + Pointer.offset [replaceFrame payload frame] :=
  RotationBST.HeavyPath.Paired.pushWith_lower_size weight payload frame p

theorem buildWith_trace {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) (cs : List (Frame α)) (p : Stacks)
    (ds : List Pointer.Frame) :
    Pointer.Trace ⟨p.tree, cs.map (replaceFrame payload) ++ ds⟩
      ⟨(Stacks.buildWith weight payload cs p).tree, ds⟩ (Stacks.buildWithCost weight payload cs p) :=
  RotationBST.HeavyPath.Paired.buildWith_trace weight payload cs p ds

theorem buildWith_valid {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree) (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.buildWith weight payload cs p).Valid :=
  RotationBST.HeavyPath.Paired.buildWith_valid payload cs valid nonnegative

theorem buildWith_amortized {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree) (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    Stacks.buildWithCost weight payload cs p + (Stacks.buildWith weight payload cs p).potential ≤ 23 * cs.length + p.potential :=
  RotationBST.HeavyPath.Paired.buildWith_amortized payload cs valid nonnegative

theorem buildWith_mass {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree) (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.buildWith weight payload cs p).mass = p.mass + (cs.map (frameMass weight)).sum :=
  RotationBST.HeavyPath.Paired.buildWith_mass payload cs valid nonnegative

theorem buildWith_lower_size {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree) (cs : List (Frame α)) (p : Stacks) :
    (Stacks.buildWith weight payload cs p).lower.decode.tree.size =
      p.lower.decode.tree.size + Pointer.offset (cs.map (replaceFrame payload)) :=
  RotationBST.HeavyPath.Paired.buildWith_lower_size weight payload cs p

theorem buildWith_fringe {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree) (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.buildWith weight payload cs p).lower.decode.fringe =
      (lowerSlotsWith weight payload cs).reverse ++ p.lower.decode.fringe ∧
    (Stacks.buildWith weight payload cs p).upper.decode.mirror.fringe =
      p.upper.decode.mirror.fringe ++ upperSlotsWith weight payload cs :=
  RotationBST.HeavyPath.Paired.buildWith_fringe payload cs valid nonnegative

theorem buildWith_erase {α : Type} (weight : α → ℝ) (cs : List (Frame α)) (p : Stacks) :
    Stacks.buildWith weight LabelledTree.erase cs p = Stacks.build weight cs p :=
  RotationBST.HeavyPath.Paired.buildWith_erase weight cs p

theorem pushWith_congr {α : Type} (weight : α → ℝ) (frame : Frame α) (p : Stacks)
    {first second : LabelledTree α → Tree}
    (same : first (framePayload frame) = second (framePayload frame)) :
    p.pushWith weight first frame = p.pushWith weight second frame :=
  RotationBST.HeavyPath.Paired.pushWith_congr weight frame p same

theorem buildWith_congr {α : Type} (weight : α → ℝ) (cs : List (Frame α)) (p : Stacks)
    {first second : LabelledTree α → Tree}
    (same : ∀ frame ∈ cs, first (framePayload frame) = second (framePayload frame)) :
    Stacks.buildWith weight first cs p = Stacks.buildWith weight second cs p :=
  RotationBST.HeavyPath.Paired.buildWith_congr weight cs p same

theorem replaced_plug_size {α : Type} (payload : LabelledTree α → Tree) (cs : List (Frame α))
    (t : LabelledTree α) (focus : Tree) (focusSize : focus.size = t.erase.size)
    (same : ∀ frame ∈ cs, (payload (framePayload frame)).size = (framePayload frame).erase.size) :
    (Pointer.plug (cs.map (replaceFrame payload)) focus).size = (plug cs t).erase.size :=
  RotationBST.HeavyPath.Paired.replaced_plug_size payload cs t focus focusSize same

theorem buildWith_size {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (cs : List (Frame α)) (p : Stacks) (t : LabelledTree α) (focusSize : p.tree.size = t.erase.size)
    (same : ∀ frame ∈ cs, (payload (framePayload frame)).size = (framePayload frame).erase.size) :
    (Stacks.buildWith weight payload cs p).tree.size = (plug cs t).erase.size :=
  RotationBST.HeavyPath.Paired.buildWith_size weight payload cs p t focusSize same

theorem replaced_offset {α : Type} (payload : LabelledTree α → Tree) (cs : List (Frame α))
    (same : ∀ frame ∈ cs, (payload (framePayload frame)).size = (framePayload frame).erase.size) :
    Pointer.offset (cs.map (replaceFrame payload)) = Pointer.offset (cs.map Frame.erase) :=
  RotationBST.HeavyPath.Paired.replaced_offset payload cs same

end RotationBST.HeavyPath.Paired.Substitution.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Paired.Substitution.Results`: 17 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Paired.Substitution.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract]
