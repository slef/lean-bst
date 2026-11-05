module

public import RotationBST.Models.Pointer.Lazy.Skeleton

@[expose] public section
namespace RotationBST.Pointer

private def fullSkeleton : Tree → Lazy.Skeleton
  | .nil => .hole .nil
  | .node l r => .node (fullSkeleton l) (fullSkeleton r)

private theorem fullSkeleton_spec (t : Tree) :
    (fullSkeleton t).tree = t ∧ (fullSkeleton t).size = t.size ∧
      (fullSkeleton t).fringe = List.replicate (t.size + 1) Tree.nil := by
  induction t with
  | nil => simp [fullSkeleton, Lazy.Skeleton.tree, Lazy.Skeleton.size,
      Lazy.Skeleton.fringe, Tree.size]
  | node l r il ir =>
    simp only [fullSkeleton, Lazy.Skeleton.tree, Lazy.Skeleton.size,
      Lazy.Skeleton.fringe, il.1, ir.1, il.2.1, ir.2.1, il.2.2, ir.2.2, Tree.size]
    simp [List.replicate_append_replicate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Any two rank-labelled trees on the same key set can be reshaped using
linearly many physical pointer instructions, with the cursor at the root at
both ends. This makes changes of initial tree explicit in cost comparisons. -/
theorem reshape (s t : Tree) (same : s.size = t.size) :
    ∃ k, k ≤ 16 * s.size ∧ Trace ⟨s, []⟩ ⟨t, []⟩ k := by
  have hs := fullSkeleton_spec s
  have ht := fullSkeleton_spec t
  obtain ⟨k, bound, trace⟩ := Lazy.Skeleton.reshape (fullSkeleton s) (fullSkeleton t)
    (by rw [hs.2.2, ht.2.2, same])
  exact ⟨k, by simpa only [hs.2.1] using bound, by simpa only [hs.1, ht.1] using trace⟩

/-- Charge an initial root-to-root trace to the first actual request. -/
theorem Execution.prepend {s t u : Tree} {x : Nat} {xs : List Nat} {k m : Nat}
    (initial : Trace ⟨s, []⟩ ⟨t, []⟩ k) (run : Execution t (x :: xs) u m) :
    Execution s (x :: xs) u (k + m) := by
  cases run with
  | cons first rest =>
    obtain ⟨visited, finish, before, after, outward, key, inward, tree, rfl⟩ := first
    have request : Serves s _ x (k + (1 + before + after)) :=
      ⟨visited, finish, k + before, after, initial.append outward, key, inward, tree, by omega⟩
    simpa only [Nat.add_assoc] using Execution.cons request rest

end RotationBST.Pointer
