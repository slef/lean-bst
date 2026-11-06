module

public import RotationBST.Structures.TreeBuffer.Shared.Operations
public import RotationBST.Models.Pointer.Routing.Complete

@[expose] public section
namespace RotationBST.TreeBuffer.Shared
open LabelledCursor

/-- The abstract scan's decreasing-distance move is exactly the move selected
by the executable shared-node router, with its four-unit charge. -/
theorem navigate_matching {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) (a b : Pointer.Config) (target nextKey : Nat)
    (tree : a.tree = s.tree.erase) (key : a.key? = some (s.position i))
    (move : Pointer.Move a b) (atNext : b.key? = some nextKey) (existing : target < s.tree.erase.size)
    (closer : LazyFinger.distance b.tree nextKey target + 1 = LazyFinger.distance s.tree.erase (s.position i) target) :
    ∃ t, Step s i t none 4 ∧ t.tree.erase = b.tree ∧ t.position = Function.update s.position i nextKey := by
  obtain ⟨c, entry, view, erased⟩ := view_matches s data valid i a tree key
  obtain ⟨routing, stored⟩ := view_invariants view valid
  have fields := IntervalMetadata.Access.read_valid (c.map Nodes.Entry.routing) routing entry.key entry.bounds
    (by simp only [map_read, view.2.1, Option.map_some, Nodes.Entry.routing])
  have chosen := Pointer.Routing.next_of_move _ target nextKey
    (by simpa only [map_erase, erased] using fields) move atNext
    (by simpa only [tree] using existing) (by simpa only [tree, view.2.2] using closer)
  have different : entry.key ≠ target := by
    intro same
    have zero := LazyFinger.distance_self s.tree.erase (s.position i) (valid.2.2 i)
    rw [view.2.2] at same
    rw [← same, zero] at closer
    omega
  obtain ⟨next, actualKey, execution, _, atActual, _, nextFields, _⟩ :=
    Nodes.progress data target c entry view.2.1 routing stored
      (by simpa only [← erase_tree, view.1] using existing) different
  have projectedRun : IntervalMetadata.Access.route target (c.map Nodes.Entry.routing) =
      some (4, next.map Nodes.Entry.routing) := by
    simpa only [execution, Option.map_some] using (Nodes.route_routing target c).symm
  have computed := IntervalMetadata.Access.route_erase target (c.map Nodes.Entry.routing) entry.key entry.bounds
    (by simp only [map_read, view.2.1, Option.map_some, Nodes.Entry.routing])
  simp only [projectedRun, Option.map_some, map_erase, erased, chosen] at computed
  have nextErased : next.erase = b := Option.some.inj computed
  obtain ⟨nextEntry, read, entryKey⟩ := read_at_key next nextFields nextKey (by simpa only [nextErased] using atNext)
  refine ⟨⟨next.tree, Function.update s.position i nextEntry.key⟩,
    .navigate target view execution read, ?_, ?_⟩
  · rw [erase_tree, nextErased]
  · rw [entryKey]

end RotationBST.TreeBuffer.Shared
