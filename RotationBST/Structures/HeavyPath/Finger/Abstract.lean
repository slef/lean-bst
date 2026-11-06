module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Results
open Paired Recursive LabelledCursor PopTart PopTart.WeightedTree PopTart.Chocolate

theorem sideSlots_nonempty {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (boundary : LabelledTree α) (carry : ℝ) (fs : List (Frame α)) :
    sideSlots weight payload boundary carry fs ≠ [] :=
  RotationBST.HeavyPath.Finger.sideSlots_nonempty weight payload boundary carry fs

theorem sideSlots_nonnegative {α : Type} {weight : α → ℝ} (payload : LabelledTree α → Tree)
    {boundary : LabelledTree α} (boundaryPositive : Positive weight boundary)
    {carry : ℝ} (carryNonnegative : 0 ≤ carry) {fs : List (Frame α)}
    (framesPositive : ∀ f ∈ fs, Positive weight (framePayload f) ∧ 0 < weight (frameKey f)) :
    ∀ entry ∈ sideSlots weight payload boundary carry fs, 0 ≤ entry.2 :=
  RotationBST.HeavyPath.Finger.sideSlots_nonnegative payload boundaryPositive carryNonnegative framesPositive

theorem sideSlots_mass {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (boundary : LabelledTree α) (carry : ℝ) (fs : List (Frame α)) :
    ((sideSlots weight payload boundary carry fs).map Prod.snd).sum =
      carry + HeavyPath.mass weight boundary + (fs.map (frameMass weight)).sum :=
  RotationBST.HeavyPath.Finger.sideSlots_mass weight payload boundary carry fs

theorem sideSlots_span {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (boundary : LabelledTree α) (carry : ℝ) (fs : List (Frame α)) :
    fringeSpan (sideSlots weight payload boundary carry fs) =
      (fs.map (fun f => (payload (framePayload f)).size + 1)).sum + (payload boundary).size + 1 :=
  RotationBST.HeavyPath.Finger.sideSlots_span weight payload boundary carry fs

theorem frame_mass_partition {α : Type} (weight : α → ℝ) (cs : List (Frame α)) :
    ((lowerFrames cs).map (frameMass weight)).sum + ((upperFrames cs).map (frameMass weight)).sum =
      (cs.map (frameMass weight)).sum :=
  RotationBST.HeavyPath.Finger.frame_mass_partition weight cs

theorem assemble_valid_fringe (slots : List (Tree × ℝ)) (nonempty : slots ≠ [])
    (nonnegative : ∀ entry ∈ slots, 0 ≤ entry.2) :
    (assemble slots).Valid 0 ∧ (assemble slots).decode.fringe = slots :=
  RotationBST.HeavyPath.Finger.assemble_valid_fringe slots nonempty nonnegative

theorem assemble_mass (slots : List (Tree × ℝ)) (nonempty : slots ≠ [])
    (nonnegative : ∀ entry ∈ slots, 0 ≤ entry.2) :
    (assemble slots).decode.mass = (slots.map Prod.snd).sum :=
  RotationBST.HeavyPath.Finger.assemble_mass slots nonempty nonnegative

theorem build_valid_fringe {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    (build weight cs left right).Valid ∧
    (build weight cs left right).lower.decode.mirror.fringe =
      sideSlots weight (rebuild weight) left 0 (lowerFrames cs) ∧
    (build weight cs left right).upper.decode.fringe =
      (sideSlots weight (rebuild weight) right 0 (upperFrames cs).reverse).reverse :=
  RotationBST.HeavyPath.Finger.build_valid_fringe positive

theorem build_mass {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    weight key + (build weight cs left right).mass = HeavyPath.mass weight (plug cs (.node left key right)) :=
  RotationBST.HeavyPath.Finger.build_mass positive

theorem build_side_sizes {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    (build weight cs left right).lower.decode.tree.mirror.size =
      ((lowerFrames cs).flatMap lowerBlock).length + left.erase.size ∧
    (build weight cs left right).upper.decode.tree.size =
      right.erase.size + ((upperFrames cs).flatMap upperBlock).length :=
  RotationBST.HeavyPath.Finger.build_side_sizes positive

theorem build_size {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    (build weight cs left right).tree.size = (plug cs (.node left key right)).erase.size :=
  RotationBST.HeavyPath.Finger.build_size positive

theorem lower_blocks_offset {α : Type} (cs : List (Frame α)) :
    ((lowerFrames cs).flatMap lowerBlock).length = Pointer.offset (cs.map Frame.erase) :=
  RotationBST.HeavyPath.Finger.lower_blocks_offset cs

theorem build_root_key {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    (Pointer.Config.mk (build weight cs left right).tree []).key? =
      (Config.mk (.node left key right) cs).erase.key? :=
  RotationBST.HeavyPath.Finger.build_root_key positive

theorem build_labels {α : Type} [Preorder α] {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right)))
    (ordered : (plug cs (.node left key right)).Ordered) :
    ∃! u : LabelledTree α, u.erase = (build weight cs left right).tree ∧
      u.inorder = (plug cs (.node left key right)).inorder ∧ u.Ordered :=
  RotationBST.HeavyPath.Finger.build_labels positive ordered

theorem build_initialization {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ cost, cost ≤ 16 * (plug cs (.node left key right)).erase.size ∧
      Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩
        ⟨(build weight cs left right).tree, []⟩ cost :=
  RotationBST.HeavyPath.Finger.build_initialization positive

theorem located_depth {p : Pair} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) subtree weight offset depth)
    (positive : 0 < weight) : (depth : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Finger.located_depth valid slot positive

theorem located_mass {p : Pair} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) subtree weight offset depth) :
    0 ≤ weight ∧ weight ≤ p.mass :=
  RotationBST.HeavyPath.Finger.located_mass valid slot

theorem located_key_bound {p : Pair} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) subtree weight offset depth)
    (positive : 0 < weight) (rank : Nat) (inside : rank < subtree.size) :
    (Tree.depth p.tree (offset + rank) : ℝ) ≤
      8 + 7 * Real.logb 2 (p.mass / weight) + Tree.depth subtree rank :=
  RotationBST.HeavyPath.Finger.located_key_bound valid slot positive rank inside

theorem located_predecessor_bound {p : Pair} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) subtree weight offset depth)
    (positive : 0 < weight) (existsKey : 0 < offset) :
    (Tree.depth p.tree (offset - 1) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Finger.located_predecessor_bound valid slot positive existsKey

theorem located_successor_bound {p : Pair} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) subtree weight offset depth)
    (positive : 0 < weight) (existsKey : offset + subtree.size < p.tree.size) :
    (Tree.depth p.tree (offset + subtree.size) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Finger.located_successor_bound valid slot positive existsKey

theorem payload_estimate {whole pair charge child key d : ℝ}
    (keyPositive : 0 < key) (keyMass : key ≤ child) (childCharge : child ≤ charge)
    (chargeMass : charge ≤ pair) (sourceMass : pair ≤ whole)
    (bound : d ≤ 8 + 7 * Real.logb 2 (pair / charge) + (7 + 15 * Real.logb 2 (child / key))) :
    d ≤ 15 + 15 * Real.logb 2 (whole / key) :=
  RotationBST.HeavyPath.Finger.payload_estimate keyPositive keyMass childCharge chargeMass sourceMass bound

theorem build_depth {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right)))
    {before after : List α} {target : α}
    (occurrence : (plug cs (.node left key right)).inorder = before ++ target :: after) :
    (Tree.depth (build weight cs left right).tree before.length : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight (plug cs (.node left key right)) / weight target) :=
  RotationBST.HeavyPath.Finger.build_depth positive occurrence

theorem build_depth_at {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right)))
    (rank : Fin (plug cs (.node left key right)).inorder.length) :
    (Tree.depth (build weight cs left right).tree rank.val : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight (plug cs (.node left key right)) /
        weight ((plug cs (.node left key right)).inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Finger.build_depth_at positive rank

theorem build_unit_depth {α : Type} (cs : List (Frame α)) (left right : LabelledTree α) (key : α)
    (rank : Nat) (valid : rank < (plug cs (.node left key right)).erase.size) :
    (Tree.depth (build (fun _ => 1) cs left right).tree rank : ℝ) ≤
      15 + 15 * Real.logb 2 ((plug cs (.node left key right)).erase.size : ℝ) :=
  RotationBST.HeavyPath.Finger.build_unit_depth cs left right key rank valid

theorem build_search_walk {α : Type} {weight : α → ℝ} {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right)))
    (rank : Fin (plug cs (.node left key right)).inorder.length) :
    ∃ (visited : Pointer.Config) (cost : Nat),
      visited.tree = (build weight cs left right).tree ∧ visited.key? = some rank.val ∧
      Pointer.Trace ⟨(build weight cs left right).tree, []⟩ visited cost ∧
      Pointer.Trace visited ⟨(build weight cs left right).tree, []⟩ cost ∧
      (1 + 2 * cost : ℝ) ≤ 31 + 30 * Real.logb 2
        (HeavyPath.mass weight (plug cs (.node left key right)) /
          weight ((plug cs (.node left key right)).inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Finger.build_search_walk positive rank

end RotationBST.HeavyPath.Finger.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.Results`: 25 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.PopTart.Located.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
