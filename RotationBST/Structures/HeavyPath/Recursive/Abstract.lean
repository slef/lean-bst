module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Recursive.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.Results
open Paired LabelledCursor
open PopTart PopTart.WeightedTree

theorem extract_payload_size {α : Type} (weight : α → ℝ) (t : LabelledTree α)
    {frame : Frame α} (mem : frame ∈ (extract weight t).context) :
    (framePayload frame).erase.size < t.erase.size :=
  RotationBST.HeavyPath.Recursive.extract_payload_size weight t mem

theorem extract_payload_positive {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {frame : Frame α} (mem : frame ∈ (extract weight t).context) :
    Positive weight (framePayload frame) :=
  RotationBST.HeavyPath.Recursive.extract_payload_positive positive mem

theorem rebuildFuel_layout {α : Type} {weight : α → ℝ} (fuel : Nat) {t : LabelledTree α}
    (positive : Positive weight t) (enough : t.erase.size ≤ fuel) :
    Layout weight t (rebuildFuel weight fuel t) :=
  RotationBST.HeavyPath.Recursive.rebuildFuel_layout fuel positive enough

theorem rebuild_layout {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) : Layout weight t (rebuild weight t) :=
  RotationBST.HeavyPath.Recursive.rebuild_layout positive

theorem layout_unfold {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree}
    (layout : Layout weight t shape) (nonempty : t ≠ .nil) :
    ∃ endpoint payload,
      (extract weight t).focus = .node .nil endpoint .nil ∧
      shape = (Stacks.buildWith weight payload (extract weight t).context Stacks.empty).tree ∧
      (Stacks.buildWith weight payload (extract weight t).context Stacks.empty).Valid ∧
      weight endpoint + (Stacks.buildWith weight payload (extract weight t).context Stacks.empty).mass =
        HeavyPath.mass weight t ∧
      ∀ frame ∈ (extract weight t).context,
        Layout weight (framePayload frame) (payload (framePayload frame)) :=
  RotationBST.HeavyPath.Recursive.layout_unfold layout nonempty

theorem layout_size {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree}
    (layout : Layout weight t shape) : shape.size = t.erase.size :=
  RotationBST.HeavyPath.Recursive.layout_size layout

theorem rebuild_size {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) : (rebuild weight t).size = t.erase.size :=
  RotationBST.HeavyPath.Recursive.rebuild_size positive

theorem rebuild_labels {α : Type} [Preorder α] {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (ordered : t.Ordered) :
    ∃! u : LabelledTree α, u.erase = rebuild weight t ∧ u.inorder = t.inorder ∧ u.Ordered :=
  RotationBST.HeavyPath.Recursive.rebuild_labels positive ordered

theorem rebuild_initialization {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) :
    ∃ cost, cost ≤ 16 * t.erase.size ∧ Pointer.Trace ⟨t.erase, []⟩ ⟨rebuild weight t, []⟩ cost :=
  RotationBST.HeavyPath.Recursive.rebuild_initialization positive

theorem layout_unique {α : Type} {weight : α → ℝ} {t : LabelledTree α} {first second : Tree}
    (left : Layout weight t first) (right : Layout weight t second) : first = second :=
  RotationBST.HeavyPath.Recursive.layout_unique left right

theorem rebuildFuel_eq {α : Type} {weight : α → ℝ} (fuel : Nat) {t : LabelledTree α}
    (positive : Positive weight t) (enough : t.erase.size ≤ fuel) :
    rebuildFuel weight fuel t = rebuild weight t :=
  RotationBST.HeavyPath.Recursive.rebuildFuel_eq fuel positive enough

theorem rebuild_eq {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    rebuild weight t =
      (Stacks.buildWith weight (rebuild weight) (extract weight t).context Stacks.empty).tree :=
  RotationBST.HeavyPath.Recursive.rebuild_eq positive nonempty

theorem rebuild_pair {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    let q := extract weight t
    let p := Stacks.buildWith weight (rebuild weight) q.context Stacks.empty
    ∃ endpoint, q.focus = .node .nil endpoint .nil ∧ rebuild weight t = p.tree ∧
      p.Valid ∧ weight endpoint + p.mass = HeavyPath.mass weight t ∧
      p.lower.decode.fringe = (lowerSlotsWith weight (rebuild weight) q.context).reverse ++ [(.nil, 0)] ∧
      p.upper.decode.mirror.fringe = [(.nil, 0)] ++ upperSlotsWith weight (rebuild weight) q.context :=
  RotationBST.HeavyPath.Recursive.rebuild_pair positive nonempty

theorem rebuild_root_key {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    (Pointer.Config.mk (rebuild weight t) []).key? = (extract weight t).erase.key? :=
  RotationBST.HeavyPath.Recursive.rebuild_root_key positive nonempty

theorem extract_payload_half {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {frame : Frame α} (mem : frame ∈ (extract weight t).context) :
    2 * mass weight (framePayload frame) ≤ mass weight t :=
  RotationBST.HeavyPath.Recursive.extract_payload_half positive mem

theorem extract_charge_bounds {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {frame : Frame α} (mem : frame ∈ (extract weight t).context) :
    0 < weight (frameKey frame) ∧ weight (frameKey frame) ≤ frameMass weight frame ∧
      mass weight (framePayload frame) ≤ frameMass weight frame :=
  RotationBST.HeavyPath.Recursive.extract_charge_bounds positive mem

theorem rootPair_source {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    (rootPair weight t).Valid ∧ (rootPair weight t).mass ≤ HeavyPath.mass weight t ∧
      rebuild weight t = (rootPair weight t).tree :=
  RotationBST.HeavyPath.Recursive.rootPair_source positive nonempty

theorem depth_telescope {whole child key d : ℝ}
    (keyPositive : 0 < key) (keyMass : key ≤ child) (half : 2 * child ≤ whole)
    (bound : d ≤ 8 + 7 * Real.logb 2 (whole / child) + (7 + 15 * Real.logb 2 (child / key))) :
    d ≤ 7 + 15 * Real.logb 2 (whole / key) :=
  RotationBST.HeavyPath.Recursive.depth_telescope keyPositive keyMass half bound

theorem payload_depth_step {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    {frame : Frame α} (member : frame ∈ (extract weight t).context) {offset depth x : Nat} {keyWeight : ℝ}
    (slot : LocatedSlot (.node (rootPair weight t).lower.decode (rootPair weight t).upper.decode.mirror)
      (rebuild weight (framePayload frame)) (frameMass weight frame) offset depth)
    (inside : x < (rebuild weight (framePayload frame)).size)
    (keyPositive : 0 < keyWeight) (keyMass : keyWeight ≤ HeavyPath.mass weight (framePayload frame))
    (childBound : (Tree.depth (rebuild weight (framePayload frame)) x : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight (framePayload frame) / keyWeight)) :
    (Tree.depth (rebuild weight t) (offset + x) : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / keyWeight) :=
  RotationBST.HeavyPath.Recursive.payload_depth_step positive nonempty member slot inside keyPositive keyMass childBound

theorem successor_depth_step {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    {frame : Frame α} (member : frame ∈ (extract weight t).context) {offset depth : Nat}
    (slot : LocatedSlot (.node (rootPair weight t).lower.decode (rootPair weight t).upper.decode.mirror)
      (rebuild weight (framePayload frame)) (frameMass weight frame) offset depth)
    (existsKey : offset + (rebuild weight (framePayload frame)).size < (rebuild weight t).size) :
    (Tree.depth (rebuild weight t) (offset + (rebuild weight (framePayload frame)).size) : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight (frameKey frame)) :=
  RotationBST.HeavyPath.Recursive.successor_depth_step positive nonempty member slot existsKey

theorem predecessor_depth_step {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    {frame : Frame α} (member : frame ∈ (extract weight t).context) {offset depth : Nat}
    (slot : LocatedSlot (.node (rootPair weight t).lower.decode (rootPair weight t).upper.decode.mirror)
      (rebuild weight (framePayload frame)) (frameMass weight frame) offset depth)
    (existsKey : 0 < offset) :
    (Tree.depth (rebuild weight t) (offset - 1) : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight (frameKey frame)) :=
  RotationBST.HeavyPath.Recursive.predecessor_depth_step positive nonempty member slot existsKey

theorem context_inorder {α : Type} (cs : List (Frame α)) (t : LabelledTree α) :
    (plug cs t).inorder = (lowerFrames cs).flatMap lowerBlock ++
      t.inorder ++ (upperFrames cs).flatMap upperBlock :=
  RotationBST.HeavyPath.Recursive.context_inorder cs t

theorem rebuild_depth {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) {before after : List α} {key : α}
    (occurrence : t.inorder = before ++ key :: after) :
    (Tree.depth (rebuild weight t) before.length : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight key) :=
  RotationBST.HeavyPath.Recursive.rebuild_depth positive occurrence

theorem rebuild_depth_at {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (rank : Fin t.inorder.length) :
    (Tree.depth (rebuild weight t) rank.val : ℝ) ≤
      7 + 15 * Real.logb 2 (HeavyPath.mass weight t / weight (t.inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Recursive.rebuild_depth_at positive rank

theorem rebuild_unit_depth {α : Type} (t : LabelledTree α) (rank : Nat)
    (valid : rank < t.erase.size) :
    (Tree.depth (rebuild (fun _ => 1) t) rank : ℝ) ≤
      7 + 15 * Real.logb 2 (t.erase.size : ℝ) :=
  RotationBST.HeavyPath.Recursive.rebuild_unit_depth t rank valid

theorem rebuild_search_walk {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (rank : Fin t.inorder.length) :
    ∃ (visited : Pointer.Config) (cost : Nat),
      visited.tree = rebuild weight t ∧ visited.key? = some rank.val ∧
      Pointer.Trace ⟨rebuild weight t, []⟩ visited cost ∧
      Pointer.Trace visited ⟨rebuild weight t, []⟩ cost ∧
      (1 + 2 * cost : ℝ) ≤
        15 + 30 * Real.logb 2 (HeavyPath.mass weight t / weight (t.inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Recursive.rebuild_search_walk positive rank

end RotationBST.HeavyPath.Recursive.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Recursive.Results`: 26 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Recursive.Results allowing [
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
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract,
  RotationBST.Structures.PopTart.Located.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
