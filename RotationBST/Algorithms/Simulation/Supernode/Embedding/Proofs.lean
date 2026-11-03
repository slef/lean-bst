module

public import RotationBST.Algorithms.Simulation.Supernode.Embedding.Defs
public import RotationBST.Models.Rotation.Basic

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open Pointer.Lazy

theorem withGaps_size (shape : Tree) (gaps : Nat → Tree) (offset : Nat) :
    (withGaps shape gaps offset).size = shape.size := by
  induction shape generalizing offset with
  | nil => rfl
  | node l r il ir => simp only [withGaps, Skeleton.size, Tree.size, il, ir]

/-- Every single key-only rotation lifts to exactly one full-tree rotation;
no node in a gap subtree is rotated. -/
theorem withGaps_rotate {s t : Tree} (step : Rotate s t) (gaps : Nat → Tree) (offset : Nat) :
    Rotate (withGaps s gaps offset).tree (withGaps t gaps offset).tree := by
  induction step generalizing offset with
  | right =>
    simpa only [withGaps, Skeleton.tree, Tree.size, Nat.add_assoc] using Rotate.right
  | left =>
    simpa only [withGaps, Skeleton.tree, Tree.size, Nat.add_assoc] using Rotate.left
  | inLeft step ih =>
    simpa only [withGaps, Skeleton.tree, step.size_eq] using (ih offset).inLeft
  | inRight step ih =>
    exact (ih _).inRight

/-- The ordered list of untouched gap subtrees is unchanged by each rotation. -/
theorem withGaps_fringe_step {s t : Tree} (step : Rotate s t) (gaps : Nat → Tree) (offset : Nat) :
    (withGaps s gaps offset).fringe = (withGaps t gaps offset).fringe := by
  induction step generalizing offset with
  | right => simp only [withGaps, Skeleton.fringe, Tree.size, Nat.add_assoc, List.append_assoc]
  | left => simp only [withGaps, Skeleton.fringe, Tree.size, Nat.add_assoc, List.append_assoc]
  | inLeft step ih => simp only [withGaps, Skeleton.fringe, ih, step.size_eq]
  | inRight step ih => simp only [withGaps, Skeleton.fringe, ih]

/-- All certified split rotations can act inside a supernode with arbitrary
untouched gap subtrees, with exactly the same cost and ordered fringe. -/
theorem withGaps_rotations {s t : Tree} {cost : Nat} (steps : Rotations s t cost)
    (gaps : Nat → Tree) (offset : Nat) :
    Rotations (withGaps s gaps offset).tree (withGaps t gaps offset).tree cost ∧
      (withGaps s gaps offset).fringe = (withGaps t gaps offset).fringe := by
  induction steps with
  | refl => exact ⟨.refl, rfl⟩
  | step first rest ih =>
    exact ⟨.step (withGaps_rotate first gaps offset) ih.1,
      (withGaps_fringe_step first gaps offset).trans ih.2⟩

theorem gapWeight_add (gaps : Nat → Tree) (offset first second : Nat) :
    gapWeight gaps offset (first + second) =
      gapWeight gaps offset first + gapWeight gaps (offset + first) second := by
  induction first generalizing offset with
  | zero => simp [gapWeight]
  | succ first ih =>
    simp only [Nat.succ_add, gapWeight, ih]
    simp only [Nat.succ_eq_add_one, Nat.add_assoc]

theorem withGaps_tree_size (shape : Tree) (gaps : Nat → Tree) (offset : Nat) :
    (withGaps shape gaps offset).tree.size = shape.size + gapWeight gaps offset (shape.size + 1) := by
  induction shape generalizing offset with
  | nil => simp [withGaps, Skeleton.tree, Tree.size, gapWeight]
  | node l r il ir =>
    simp only [withGaps, Skeleton.tree, Tree.size, il, ir]
    rw [show l.size + 1 + r.size + 1 = (l.size + 1) + (r.size + 1) by omega, gapWeight_add gaps offset (l.size + 1) (r.size + 1)]
    simp only [Nat.add_assoc]
    omega

/-- Exposing a supernode rank accesses exactly its full-tree rank; the sizes
of gap subtrees affect ranks but do not add rotations. -/
theorem withGaps_access {s t : Tree} {rank cost : Nat} (access : Access s t rank cost)
    (gaps : Nat → Tree) (offset : Nat) :
    Access (withGaps s gaps offset).tree (withGaps t gaps offset).tree
      (keyRank gaps offset rank) cost := by
  refine ⟨(withGaps_rotations access.1 gaps offset).1, ?_⟩
  cases t with
  | nil => exact False.elim access.2
  | node l r =>
    have root : l.size = rank := access.2
    change (withGaps l gaps offset).tree.size = _
    rw [withGaps_tree_size, root]
    rfl

end RotationBST.Geometric.Online.Supernode
