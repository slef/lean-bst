module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Paired.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Results
open PopTart PopTart.Chocolate LabelledCursor
open PopTart.WeightedTree

theorem empty_valid : Stacks.empty.Valid :=
  RotationBST.HeavyPath.Paired.empty_valid

theorem push_trace {α : Type} (weight : α → ℝ) (frame : Frame α) (p : Stacks)
    (cs : List Pointer.Frame) :
    Pointer.Trace ⟨p.tree, frame.erase :: cs⟩ ⟨(p.push weight frame).tree, cs⟩ (p.pushCost frame) :=
  RotationBST.HeavyPath.Paired.push_trace weight frame p cs

theorem push_valid {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) : (p.push weight frame).Valid :=
  RotationBST.HeavyPath.Paired.push_valid valid nonnegative

theorem push_amortized {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) :
    p.pushCost frame + (p.push weight frame).potential ≤ 23 + p.potential :=
  RotationBST.HeavyPath.Paired.push_amortized valid nonnegative

theorem push_mass {α : Type} {weight : α → ℝ} {frame : Frame α} {p : Stacks}
    (valid : p.Valid) (nonnegative : 0 ≤ frameMass weight frame) :
    (p.push weight frame).mass = p.mass + frameMass weight frame :=
  RotationBST.HeavyPath.Paired.push_mass valid nonnegative

theorem push_lower_size {α : Type} (weight : α → ℝ) (frame : Frame α) (p : Stacks) :
    (p.push weight frame).lower.decode.tree.size =
      p.lower.decode.tree.size + Pointer.offset [frame.erase] :=
  RotationBST.HeavyPath.Paired.push_lower_size weight frame p

theorem build_trace {α : Type} (weight : α → ℝ) (cs : List (Frame α)) (p : Stacks)
    (ds : List Pointer.Frame) :
    Pointer.Trace ⟨p.tree, cs.map Frame.erase ++ ds⟩
      ⟨(Stacks.build weight cs p).tree, ds⟩ (Stacks.buildCost weight cs p) :=
  RotationBST.HeavyPath.Paired.build_trace weight cs p ds

theorem build_valid {α : Type} {weight : α → ℝ} (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.build weight cs p).Valid :=
  RotationBST.HeavyPath.Paired.build_valid cs valid nonnegative

theorem build_amortized {α : Type} {weight : α → ℝ} (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    Stacks.buildCost weight cs p + (Stacks.build weight cs p).potential ≤ 23 * cs.length + p.potential :=
  RotationBST.HeavyPath.Paired.build_amortized cs valid nonnegative

theorem build_mass {α : Type} {weight : α → ℝ} (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.build weight cs p).mass = p.mass + (cs.map (frameMass weight)).sum :=
  RotationBST.HeavyPath.Paired.build_mass cs valid nonnegative

theorem build_lower_size {α : Type} (weight : α → ℝ) (cs : List (Frame α)) (p : Stacks) :
    (Stacks.build weight cs p).lower.decode.tree.size =
      p.lower.decode.tree.size + Pointer.offset (cs.map Frame.erase) :=
  RotationBST.HeavyPath.Paired.build_lower_size weight cs p

theorem extract_build {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    let q := extract weight t
    let p := Stacks.build weight q.context Stacks.empty
    ∃ x cost, q.focus = .node .nil x .nil ∧ p.Valid ∧
      weight x + p.mass = HeavyPath.mass weight t ∧
      Pointer.Trace ⟨t.erase, []⟩ ⟨p.tree, []⟩ cost ∧
      cost + p.potential ≤ 24 * q.context.length ∧
      (Pointer.Config.mk p.tree []).key? = q.erase.key? :=
  RotationBST.HeavyPath.Paired.extract_build positive nonempty

theorem build_fringe {α : Type} {weight : α → ℝ} (cs : List (Frame α)) {p : Stacks}
    (valid : p.Valid) (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.build weight cs p).lower.decode.fringe =
      (lowerSlots weight cs).reverse ++ p.lower.decode.fringe ∧
    (Stacks.build weight cs p).upper.decode.mirror.fringe =
      p.upper.decode.mirror.fringe ++ upperSlots weight cs :=
  RotationBST.HeavyPath.Paired.build_fringe cs valid nonnegative

theorem empty_build_fringe {α : Type} {weight : α → ℝ} (cs : List (Frame α))
    (nonnegative : ∀ frame ∈ cs, 0 ≤ frameMass weight frame) :
    (Stacks.build weight cs Stacks.empty).lower.decode.fringe =
      (lowerSlots weight cs).reverse ++ [(.nil, 0)] ∧
    (Stacks.build weight cs Stacks.empty).upper.decode.mirror.fringe =
      [(.nil, 0)] ++ upperSlots weight cs :=
  RotationBST.HeavyPath.Paired.empty_build_fringe cs nonnegative

theorem lower_depth {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt p.lower.decode subtree weight depth) (positive : 0 < weight) :
    ((depth + 1 : Nat) : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Paired.lower_depth valid slot positive

theorem upper_depth {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt p.upper.decode.mirror subtree weight depth) (positive : 0 < weight) :
    ((depth + 1 : Nat) : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Paired.upper_depth valid slot positive

theorem lower_access {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt p.lower.decode subtree weight depth)
    (positive : 0 < weight) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth + 1 ∧ Pointer.plug cs subtree = p.tree ∧
      Pointer.Trace ⟨p.tree, []⟩ ⟨subtree, cs⟩ (depth + 1) ∧
      ((depth + 1 : Nat) : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Paired.lower_access valid slot positive nonempty

theorem upper_access {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt p.upper.decode.mirror subtree weight depth)
    (positive : 0 < weight) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth + 1 ∧ Pointer.plug cs subtree = p.tree ∧
      Pointer.Trace ⟨p.tree, []⟩ ⟨subtree, cs⟩ (depth + 1) ∧
      ((depth + 1 : Nat) : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Paired.upper_access valid slot positive nonempty

theorem extract_build_labelled {α : Type} [Preorder α] {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) (ordered : t.Ordered) :
    let p := Stacks.build weight (extract weight t).context Stacks.empty
    ∃ u : LabelledTree α, ∃ rotations cost,
      u.erase = p.tree ∧ u.inorder = t.inorder ∧ u.Ordered ∧
      LabelledTree.Rotations t u rotations ∧ rotations ≤ cost ∧
      Pointer.Trace ⟨t.erase, []⟩ ⟨p.tree, []⟩ cost ∧
      cost + p.potential ≤ 24 * (extract weight t).context.length :=
  RotationBST.HeavyPath.Paired.extract_build_labelled positive nonempty ordered

theorem lower_key_depth {p : Stacks} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.lower.decode subtree weight offset depth) (x : Nat) (inside : x < subtree.size) :
    Tree.depth p.tree (offset + x) = depth + 1 + Tree.depth subtree x :=
  RotationBST.HeavyPath.Paired.lower_key_depth slot x inside

theorem upper_key_depth {p : Stacks} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.upper.decode.mirror subtree weight offset depth) (x : Nat) (inside : x < subtree.size) :
    Tree.depth p.tree (p.lower.decode.tree.size + 1 + offset + x) =
      depth + 1 + Tree.depth subtree x :=
  RotationBST.HeavyPath.Paired.upper_key_depth slot x inside

theorem lower_key_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.lower.decode subtree weight offset depth) (positive : 0 < weight)
    (x : Nat) (inside : x < subtree.size) :
    (Tree.depth p.tree (offset + x) : ℝ) ≤
      8 + 7 * Real.logb 2 (p.mass / weight) + Tree.depth subtree x :=
  RotationBST.HeavyPath.Paired.lower_key_bound valid slot positive x inside

theorem upper_key_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.upper.decode.mirror subtree weight offset depth) (positive : 0 < weight)
    (x : Nat) (inside : x < subtree.size) :
    (Tree.depth p.tree (p.lower.decode.tree.size + 1 + offset + x) : ℝ) ≤
      8 + 7 * Real.logb 2 (p.mass / weight) + Tree.depth subtree x :=
  RotationBST.HeavyPath.Paired.upper_key_bound valid slot positive x inside

theorem lower_separator_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.lower.decode subtree weight offset depth) (positive : 0 < weight) :
    (Tree.depth p.tree (offset + subtree.size) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Paired.lower_separator_bound valid slot positive

theorem upper_separator_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.upper.decode.mirror subtree weight offset depth) (positive : 0 < weight) :
    (Tree.depth p.tree (p.lower.decode.tree.size + offset) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Paired.upper_separator_bound valid slot positive

theorem located_depth {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset depth)
    (positive : 0 < weight) : (depth : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Paired.located_depth valid slot positive

theorem located_mass {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset depth) :
    0 ≤ weight ∧ weight ≤ p.mass :=
  RotationBST.HeavyPath.Paired.located_mass valid slot

theorem located_key_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset depth)
    (positive : 0 < weight) (x : Nat) (inside : x < subtree.size) :
    (Tree.depth p.tree (offset + x) : ℝ) ≤
      8 + 7 * Real.logb 2 (p.mass / weight) + Tree.depth subtree x :=
  RotationBST.HeavyPath.Paired.located_key_bound valid slot positive x inside

theorem located_successor_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset depth)
    (positive : 0 < weight) (existsKey : offset + subtree.size < p.tree.size) :
    (Tree.depth p.tree (offset + subtree.size) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Paired.located_successor_bound valid slot positive existsKey

theorem located_predecessor_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset depth)
    (positive : 0 < weight) (existsKey : 0 < offset) :
    (Tree.depth p.tree (offset - 1) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) :=
  RotationBST.HeavyPath.Paired.located_predecessor_bound valid slot positive existsKey

end RotationBST.HeavyPath.Paired.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Paired.Results`: 30 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Paired.Results allowing [
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
  RotationBST.Structures.PopTart.Located.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
