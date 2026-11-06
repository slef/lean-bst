module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Recursive.History.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History.Results
open Paired LabelledCursor

theorem path_mass {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    (valid : PathValid weight es p) : p.mass = (es.map (fun e => frameMass weight e.source)).sum :=
  RotationBST.HeavyPath.Recursive.History.path_mass valid

theorem path_partition {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    {t : LabelledTree α} {endpoint : α}
    (context : es.map Entry.source = (extract weight t).context)
    (valid : PathValid weight es p) (focus : (extract weight t).focus = .node .nil endpoint .nil) :
    weight endpoint + p.mass = mass weight t :=
  RotationBST.HeavyPath.Recursive.History.path_partition context valid focus

theorem layout_positive {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) : Positive weight t :=
  RotationBST.HeavyPath.Recursive.History.layout_positive layout

theorem layout_size {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) : shape.size = t.erase.size :=
  RotationBST.HeavyPath.Recursive.History.layout_size layout

theorem layout_labels {α : Type} [Preorder α] {weight : α → ℝ} {t : LabelledTree α}
    {shape : Tree} {credit : Nat} (layout : Layout weight t shape credit) (ordered : t.Ordered) :
    ∃! u : LabelledTree α, u.erase = shape ∧ u.inorder = t.inorder ∧ u.Ordered :=
  RotationBST.HeavyPath.Recursive.History.layout_labels layout ordered

theorem of_canonical {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree}
    (layout : Recursive.Layout weight t shape) : ∃ credit, Layout weight t shape credit :=
  RotationBST.HeavyPath.Recursive.History.of_canonical layout

theorem rebuild_history {α : Type} {weight : α → ℝ} {t : LabelledTree α} (positive : Positive weight t) :
    ∃ credit, Layout weight t (rebuild weight t) credit :=
  RotationBST.HeavyPath.Recursive.History.rebuild_history positive

theorem layout_depth {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) {before after : List α} {key : α}
    (occurrence : t.inorder = before ++ key :: after) :
    (Tree.depth shape before.length : ℝ) ≤ 7 + 15 * Real.logb 2 (mass weight t / weight key) :=
  RotationBST.HeavyPath.Recursive.History.layout_depth layout occurrence

theorem layout_depth_at {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) (rank : Fin t.inorder.length) :
    (Tree.depth shape rank.val : ℝ) ≤
      7 + 15 * Real.logb 2 (mass weight t / weight (t.inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Recursive.History.layout_depth_at layout rank

theorem layout_search_walk {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) (rank : Fin t.inorder.length) :
    ∃ (visited : Pointer.Config) (cost : Nat), visited.tree = shape ∧ visited.key? = some rank.val ∧
      Pointer.Trace ⟨shape, []⟩ visited cost ∧ Pointer.Trace visited ⟨shape, []⟩ cost ∧
      (1 + 2 * cost : ℝ) ≤ 15 + 30 * Real.logb 2 (mass weight t / weight (t.inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Recursive.History.layout_search_walk layout rank

theorem pop_path {α : Type} {weight : α → ℝ} {es : List (Entry α)} {e : Entry α} {p : Stacks}
    (valid : PathValid weight (es ++ [e]) p) :
    ∃ rest : Stacks, PathValid weight es rest ∧
      Pointer.Trace ⟨p.tree, []⟩ ⟨e.wrap rest.tree, []⟩ (p.exposeCost e.source) ∧
      p.exposeCost e.source + rest.potential ≤ 24 + p.potential :=
  RotationBST.HeavyPath.Recursive.History.pop_path valid

theorem layout_expose {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {shape : Tree} {credit : Nat} (layout : Layout weight (.node l x r) shape credit) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Layout weight l a leftCredit ∧ Layout weight r b rightCredit ∧
      Pointer.Trace ⟨shape, []⟩ ⟨.node a b, []⟩ cost ∧
      cost + leftCredit + rightCredit ≤ 24 + credit :=
  RotationBST.HeavyPath.Recursive.History.layout_expose layout

theorem layout_join {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {a b : Tree} {leftCredit rightCredit : Nat}
    (left : Layout weight l a leftCredit) (right : Layout weight r b rightCredit)
    (keyPositive : 0 < weight x) :
    ∃ (shape : Tree) (credit cost : Nat), Layout weight (.node l x r) shape credit ∧
      Pointer.Trace ⟨.node a b, []⟩ ⟨shape, []⟩ cost ∧
      cost + credit ≤ 24 + leftCredit + rightCredit :=
  RotationBST.HeavyPath.Recursive.History.layout_join left right keyPositive

theorem of_canonical_bounded {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree}
    (layout : Recursive.Layout weight t shape) :
    ∃ credit, Layout weight t shape credit ∧ credit ≤ 23 * t.erase.size :=
  RotationBST.HeavyPath.Recursive.History.of_canonical_bounded layout

theorem rebuild_history_bounded {α : Type} {weight : α → ℝ} {t : LabelledTree α} (positive : Positive weight t) :
    ∃ credit, Layout weight t (rebuild weight t) credit ∧ credit ≤ 23 * t.erase.size :=
  RotationBST.HeavyPath.Recursive.History.rebuild_history_bounded positive

theorem layout_expose_bounded {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {shape : Tree} {credit : Nat} (layout : Layout weight (.node l x r) shape credit) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Layout weight l a leftCredit ∧ Layout weight r b rightCredit ∧
      Pointer.Trace ⟨shape, []⟩ ⟨.node a b, []⟩ cost ∧
      cost + leftCredit + rightCredit ≤ 24 + credit ∧
      (cost : ℝ) ≤ 10 + 10 * Real.logb 2 shape.size :=
  RotationBST.HeavyPath.Recursive.History.layout_expose_bounded layout

theorem layout_join_bounded {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {a b : Tree} {leftCredit rightCredit : Nat}
    (left : Layout weight l a leftCredit) (right : Layout weight r b rightCredit)
    (keyPositive : 0 < weight x) :
    ∃ (shape : Tree) (credit cost : Nat), Layout weight (.node l x r) shape credit ∧
      Pointer.Trace ⟨.node a b, []⟩ ⟨shape, []⟩ cost ∧
      cost + credit ≤ 24 + leftCredit + rightCredit ∧
      (cost : ℝ) ≤ 10 + 14 * Real.logb 2 (Tree.node a b).size :=
  RotationBST.HeavyPath.Recursive.History.layout_join_bounded left right keyPositive

theorem push_path_within {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    (valid : PathValid weight es p) (e : Entry α) (nonnegative : 0 ≤ frameMass weight e.source) :
    PathValid weight (es ++ [e]) (p.pushWith weight (fun _ => e.shape) e.source) ∧
      Pointer.TraceWithin (fun t => t.size = (e.wrap p.tree).size ∧
        ∀ x, Tree.depth t x ≤ 4 * Tree.depth (e.wrap p.tree) x + 16) ⟨e.wrap p.tree, []⟩ ⟨(p.pushWith weight (fun _ => e.shape) e.source).tree, []⟩
        (p.pushCost e.source + 1) ∧
      p.pushCost e.source + 1 + (p.pushWith weight (fun _ => e.shape) e.source).potential ≤ 24 + p.potential :=
  RotationBST.HeavyPath.Recursive.History.push_path_within valid e nonnegative

theorem pop_path_within {α : Type} {weight : α → ℝ} {es : List (Entry α)} {e : Entry α} {p : Stacks}
    (valid : PathValid weight (es ++ [e]) p) :
    ∃ rest : Stacks, PathValid weight es rest ∧
      Pointer.TraceWithin (fun t => t.size = p.tree.size ∧
        ∀ x, Tree.depth t x ≤ 4 * Tree.depth p.tree x + 10) ⟨p.tree, []⟩ ⟨e.wrap rest.tree, []⟩ (p.exposeCost e.source) ∧
      p.exposeCost e.source + rest.potential ≤ 24 + p.potential :=
  RotationBST.HeavyPath.Recursive.History.pop_path_within valid

theorem layout_expose_within {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {shape : Tree} {credit : Nat} (layout : Layout weight (.node l x r) shape credit) :
    ∃ (a b : Tree) (leftCredit rightCredit cost : Nat),
      Layout weight l a leftCredit ∧ Layout weight r b rightCredit ∧
      Pointer.TraceWithin (fun t => t.size = shape.size ∧
        ∀ x, Tree.depth t x ≤ 4 * Tree.depth shape x + 10) ⟨shape, []⟩ ⟨.node a b, []⟩ cost ∧
      cost + leftCredit + rightCredit ≤ 24 + credit ∧
      (cost : ℝ) ≤ 10 + 10 * Real.logb 2 shape.size :=
  RotationBST.HeavyPath.Recursive.History.layout_expose_within layout

theorem layout_join_within {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    {a b : Tree} {leftCredit rightCredit : Nat}
    (left : Layout weight l a leftCredit) (right : Layout weight r b rightCredit)
    (keyPositive : 0 < weight x) :
    ∃ (shape : Tree) (credit cost : Nat), Layout weight (.node l x r) shape credit ∧
      Pointer.TraceWithin (fun t => t.size = (Tree.node a b).size ∧
        ∀ x, Tree.depth t x ≤ 4 * Tree.depth (.node a b) x + 16) ⟨.node a b, []⟩ ⟨shape, []⟩ cost ∧
      cost + credit ≤ 24 + leftCredit + rightCredit ∧
      (cost : ℝ) ≤ 10 + 14 * Real.logb 2 (Tree.node a b).size :=
  RotationBST.HeavyPath.Recursive.History.layout_join_within left right keyPositive

theorem path_potential_bound {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks}
    (valid : PathValid weight es p) : p.potential ≤ 20 * es.length :=
  RotationBST.HeavyPath.Recursive.History.path_potential_bound valid

theorem layout_potential_bound {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    {shape : Tree} {credit : Nat} (layout : Layout weight t shape credit) :
    credit ≤ 20 * t.erase.size :=
  RotationBST.HeavyPath.Recursive.History.layout_potential_bound layout

end RotationBST.HeavyPath.Recursive.History.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Recursive.History.Results`: 23 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Recursive.History.Results allowing [
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
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.History.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Models.Pointer.Invariant.Definitions.Abstract]
