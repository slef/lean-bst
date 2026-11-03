module

public import RotationBST.Models.Region.Bounds
public import RotationBST.Structures.Treap.Interval
public import RotationBST.Models.Region.Defs

@[expose] public section
namespace RotationBST.Geometric.Region
open Pointer.Lazy.Skeleton

/-- Heapifying the current row restores the full next-touch treap invariant,
including every edge leading into an untouched fringe subtree. -/
theorem restore {P : Finset Point} {time : Nat} (sat : ASS P) (s : Region) (lo : Nat)
    (active : ActiveHeap (nextTouch P (time + 1)) s lo)
    (complete : ∀ x, x ∈ keys s lo ↔ (x, time) ∈ P ∧ lo ≤ x ∧ x < lo + s.tree.size)
    (fringe : ∀ e ∈ holes s lo, Heap (nextTouch P (time + 1)) e.2 e.1) :
    Heap (nextTouch P (time + 1)) s.tree lo := by
  induction s generalizing lo with
  | hole t => exact fringe (lo, t) (List.mem_cons_self ..)
  | node l r il ir =>
    obtain ⟨leftComplete, rightComplete⟩ := complete_children complete
    refine ⟨?_, il lo active.2.1 leftComplete ?_,
      ir (lo + l.tree.size + 1) active.2.2 rightComplete ?_⟩
    · intro x hx
      have rootCurrent := ((complete (lo + l.tree.size)).mp (Finset.mem_insert_self ..)).1
      apply interval_minimum (low := lo) (high := lo + (Tree.node l.tree r.tree).size)
        sat rootCurrent (by omega) (by simp only [Tree.size]; omega)
        (by omega) (by simp only [Tree.size]; omega)
      intro y hy hlo hhi
      exact active.1 y ((complete y).mpr ⟨hy, hlo, hhi⟩)
    · intro e he
      exact fringe e (List.mem_append_left _ he)
    · intro e he
      exact fringe e (List.mem_append_right _ he)

end RotationBST.Geometric.Region
