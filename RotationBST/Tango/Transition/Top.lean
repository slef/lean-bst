module

public import RotationBST.Tango.Transition.Abstract
public import RotationBST.Arboral.Treap.Regions.Bounds

@[expose] public section
namespace RotationBST.Tango
open Arboral Pointer.Lazy.Skeleton

theorem topIn_bounds {t : Tree} {lo low high x : Nat} (h : topIn t lo low high = some x) :
    lo ≤ x ∧ x < lo + t.size ∧ low ≤ x ∧ x < high := by
  induction t generalizing lo with
  | nil => simp [topIn] at h
  | node l r il ir =>
    simp only [topIn] at h
    split at h
    · have := ir h
      simp only [Tree.size]; omega
    · split at h
      · have := il h
        simp only [Tree.size]; omega
      · have he := Option.some.inj h
        simp only [Tree.size]; omega

theorem topIn_exists (t : Tree) (lo low high : Nat)
    (lower : lo ≤ low) (upper : high ≤ lo + t.size) (nonempty : low < high) :
    ∃ x, topIn t lo low high = some x := by
  induction t generalizing lo with
  | nil => simp only [Tree.size] at upper; omega
  | node l r il ir =>
    simp only [topIn]
    split
    · apply ir (lo + l.size + 1) (by omega) (by simp only [Tree.size] at upper; omega)
    · split
      · exact il lo lower (by omega)
      · exact ⟨_, rfl⟩

/-- The shallowest key in an interval is an ancestor of every other key there,
so it inherits a heap's priority comparison on that interval. -/
theorem topIn_minimum {α : Type} [LE α] (priority : Nat → α) (t : Tree)
    (lo low high root x : Nat) (heap : Heap priority t lo)
    (top : topIn t lo low high = some root)
    (xlo : lo ≤ x) (xhi : x < lo + t.size) (lowx : low ≤ x) (xhigh : x < high) :
    priority root ≤ priority x := by
  induction t generalizing lo with
  | nil => simp [topIn] at top
  | node l r il ir =>
    simp only [topIn] at top
    split at top
    · exact ir (lo + l.size + 1) heap.2.2 top (by omega)
        (by simp only [Tree.size] at xhi; omega)
    · split at top
      · exact il lo heap.2.1 top xlo (by omega)
      · have heq := Option.some.inj top
        have h := heap.1 (x - lo) (by simp only [Tree.size] at xhi; omega)
        have hx : lo + (x - lo) = x := by omega
        simpa only [heq, hx] using h

/-- If a rooted region touches any key of an interval, it touches its top key. -/
theorem topIn_active (s : Region) (lo low high x root : Nat)
    (active : x ∈ Arboral.Region.keys s lo) (lowx : low ≤ x) (xhigh : x < high)
    (top : topIn s.tree lo low high = some root) : root ∈ Arboral.Region.keys s lo := by
  induction s generalizing lo with
  | hole t => simp [Arboral.Region.keys] at active
  | node l r il ir =>
    simp only [tree, topIn] at top
    split at top
    · have hx : x ∈ Arboral.Region.keys r (lo + l.tree.size + 1) := by
        rcases Finset.mem_insert.mp active with he | he
        · omega
        rcases Finset.mem_union.mp he with he | he
        · have := Arboral.Region.keys_bounds he; omega
        · exact he
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ir _ hx top))
    · split at top
      · have hx : x ∈ Arboral.Region.keys l lo := by
          rcases Finset.mem_insert.mp active with he | he
          · omega
          rcases Finset.mem_union.mp he with he | he
          · exact he
          · have := Arboral.Region.keys_bounds he; omega
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (il _ hx top))
      · have he := Option.some.inj top
        rw [← he]
        exact Finset.mem_insert_self ..

end RotationBST.Tango
