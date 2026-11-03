module

public import RotationBST.Algorithms.Tango.Auxiliary.Access
public import RotationBST.Algorithms.Splay.Updates.Basic

@[expose] public section
namespace RotationBST.Geometric.Region
open Pointer.Lazy.Skeleton

/-- Split a nonempty auxiliary prefix by splaying its predecessor. Marking the
right child detaches its auxiliary component without deleting its global keys. -/
theorem auxiliary_split (s : Region) (k : Nat) (positive : 0 < k) (valid : k ≤ s.size) :
    ∃ a b : Region,
      shape (.node a (.hole b.tree)) = (Splay.Updates.split (shape s) k).left ∧
      shape b = (Splay.Updates.split (shape s) k).right ∧
      s.fringe = (Pointer.Lazy.Skeleton.node a b).fringe ∧
      Rotations s.tree (.node a.tree b.tree) (Splay.Updates.split (shape s) k).cost := by
  have hv : k - 1 < (shape s).size := by rw [shape_size]; omega
  have access := (Splay.run_correct (shape s) (k - 1) hv).1
  obtain ⟨u, hu, hf, rotations⟩ := lift_rotations access.1 s rfl
  cases u with
  | hole t => rw [← hu] at access; exact False.elim access.2
  | node a b =>
    refine ⟨a, b, ?_, ?_, hf, ?_⟩
    all_goals
      simp only [Splay.Updates.split, ite_eq_right (show k ≠ 0 by omega)]
      rw [← hu]
      first | rfl | exact rotations

/-- Join adjacent auxiliary components. The right component is the final
fringe subtree of the left one, so exposing the left maximum makes the join a
change of marking, with no extra global rotation. -/
theorem auxiliary_join (left right : Region)
    (attached : left.fringe.getLast? = some right.tree) :
    ∃ u : Region, shape u = (Splay.Updates.join (shape left) (shape right)).1 ∧
      u.fringe = left.fringe.dropLast ++ right.fringe ∧
      Rotations left.tree u.tree (Splay.Updates.join (shape left) (shape right)).2 := by
  cases left with
  | hole t =>
    have ht : t = right.tree := by simpa only [fringe, List.getLast?_singleton, Option.some.injEq] using attached
    exact ⟨right, rfl, by simp [fringe], by simpa only [tree, ht, shape, Splay.Updates.join] using
      (Rotations.refl (t := right.tree))⟩
  | node l r =>
    let s : Region := .node l r
    have positive : 0 < (shape s).size := by simp [s, shape, Tree.size]
    have access := (Splay.run_correct (shape s) ((shape s).size - 1) (by omega)).1
    obtain ⟨u, hu, hf, rotations⟩ := lift_rotations access.1 s rfl
    have sizes := access.1.size_eq
    cases u with
    | hole t => rw [← hu] at access; exact False.elim access.2
    | node a b =>
      have root := access.2
      rw [← hu] at root sizes
      simp only [shape, Tree.size, shape_size] at root sizes
      have bz : b.size = 0 := by rw [shape_size] at positive; omega
      cases b with
      | node c d => simp only [size] at bz; omega
      | hole t =>
        have ht : t = right.tree := by
          have old : s.fringe.getLast? = some right.tree := attached
          rw [hf] at old
          simpa only [fringe, List.getLast?_append, List.getLast?_singleton, Option.some_or,
            Option.some.injEq] using old
        refine ⟨.node a right, ?_, ?_, ?_⟩
        · change shape (.node a right) =
            (match (Splay.run (shape s) ((shape s).size - 1)).1 with
            | .nil => (shape right, (Splay.run (shape s) ((shape s).size - 1)).2)
            | .node a _ => (.node a (shape right), (Splay.run (shape s) ((shape s).size - 1)).2)).1
          rw [← hu]
          rfl
        · change (Pointer.Lazy.Skeleton.node a right).fringe = s.fringe.dropLast ++ right.fringe
          rw [hf]
          simp [fringe]
        · change Rotations s.tree (Pointer.Lazy.Skeleton.node a right).tree _
          simp only [Splay.Updates.join, shape]
          split <;> simpa only [s, shape, tree, ht] using rotations

end RotationBST.Geometric.Region
