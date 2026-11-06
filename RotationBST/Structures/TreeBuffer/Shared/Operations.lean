module

public import RotationBST.Structures.TreeBuffer.Shared.Preservation
public import RotationBST.Models.Pointer.Location

@[expose] public section
namespace RotationBST.TreeBuffer.Shared
open LabelledCursor

theorem view_key {α : Type} {fingers : Nat} {s : State α fingers} {i : Fin fingers}
    {c : Config (Nodes.Entry α)} {entry : Nodes.Entry α} (view : View s i c entry)
    {data : Nat → α} (valid : s.Valid data) : c.erase.key? = some (s.position i) := by
  have fields := IntervalMetadata.Access.read_valid (c.map Nodes.Entry.routing)
    (view_invariants view valid).1 entry.key entry.bounds
    (by simp only [map_read, view.2.1, Option.map_some, Nodes.Entry.routing])
  simpa only [map_erase, view.2.2] using fields.2.1

/-- The selected persistent finger is represented by the specified shape
cursor, without performing a new search or resetting its position. -/
theorem view_matches {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) (shape : Pointer.Config)
    (tree : shape.tree = s.tree.erase) (key : shape.key? = some (s.position i)) :
    ∃ c entry, View s i c entry ∧ c.erase = shape := by
  obtain ⟨c, entry, view⟩ := view_exists s data valid i
  refine ⟨c, entry, view, Pointer.Config.ext_key ?_ (view_key view valid) key⟩
  rw [← erase_tree, view.1, tree]

/-- A prescribed legal navigation primitive lifts to the shared labelled tree
for one unit, retaining every other finger. -/
theorem move_witness {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) (op : Multifinger.Opcode) (a b : Pointer.Config)
    (tree : a.tree = s.tree.erase) (key : a.key? = some (s.position i))
    (execution : Multifinger.perform op a = some b) (move : Pointer.Move a b) (nextKey : Nat)
    (atNext : b.key? = some nextKey) :
    ∃ c next entry nextEntry, View s i c entry ∧ LabelledCursor.perform op c = some next ∧
      Pointer.Move c.erase next.erase ∧ next.read = some nextEntry ∧ next.erase = b ∧ nextEntry.key = nextKey := by
  obtain ⟨c, entry, view, erased⟩ := view_matches s data valid i a tree key
  have mapped := perform_erase op c
  rw [erased, execution] at mapped
  obtain ⟨next, localRun, nextErased⟩ := Option.map_eq_some_iff.mp mapped
  have localMove : Pointer.Move c.erase next.erase := by simpa only [erased, nextErased] using move
  have routing : Nodes.Routing next := by
    simpa only [Nodes.Routing, IntervalMetadata.Access.Canonical, map_tree, move_tree localRun localMove]
      using (view_invariants view valid).1
  obtain ⟨nextEntry, read, atKey⟩ := read_at_key next routing nextKey (by simpa only [nextErased] using atNext)
  exact ⟨c, next, entry, nextEntry, view, localRun, localMove, read, nextErased, atKey⟩

theorem move_exists {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) (op : Multifinger.Opcode) (a b : Pointer.Config)
    (tree : a.tree = s.tree.erase) (key : a.key? = some (s.position i))
    (execution : Multifinger.perform op a = some b) (move : Pointer.Move a b) (nextKey : Nat)
    (atNext : b.key? = some nextKey) :
    ∃ t, Step s i t none 1 ∧ t.tree.erase = b.tree ∧
      t.position = Function.update s.position i nextKey := by
  obtain ⟨c, next, entry, nextEntry, view, localRun, localMove, read, nextErased, atKey⟩ :=
    move_witness s data valid i op a b tree key execution move nextKey atNext
  refine ⟨⟨next.tree, Function.update s.position i nextEntry.key⟩,
    .move op view localRun localMove read, ?_, ?_⟩
  · rw [erase_tree, nextErased]
  · rw [atKey]

/-- Routing from any finger uses the executable interval rule and charges its
three field reads plus the selected pointer move. -/
theorem navigate_exists {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) (target : Nat) (existing : target < s.tree.erase.size)
    (different : s.position i ≠ target) :
    ∃ t, Step s i t none 4 ∧ t.tree = s.tree ∧
      LazyFinger.distance t.tree.erase (t.position i) target + 1 =
        LazyFinger.distance s.tree.erase (s.position i) target := by
  obtain ⟨c, entry, view⟩ := view_exists s data valid i
  obtain ⟨routing, stored⟩ := view_invariants view valid
  obtain ⟨next, nextKey, execution, _, atNext, closer, fields, _⟩ :=
    Nodes.progress data target c entry view.2.1 routing stored
      (by simpa only [← erase_tree, view.1] using existing) (by simpa only [view.2.2] using different)
  obtain ⟨nextEntry, read, key⟩ := read_at_key next fields nextKey atNext
  refine ⟨⟨next.tree, Function.update s.position i nextEntry.key⟩,
    .navigate target view execution read, (Nodes.route_tree execution).trans view.1, ?_⟩
  simpa only [Function.update_self, key, ← erase_tree, view.1, view.2.2] using closer

theorem read_exists {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) : Step s i s (some (.read (s.position i) (data (s.position i)))) 1 := by
  obtain ⟨c, entry, view⟩ := view_exists s data valid i
  apply Step.read view
  simpa only [view.2.2] using Nodes.read_correct data c entry view.2.1 (view_invariants view valid).2

theorem write_exists {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) (value : α) :
    ∃ t, Step s i t (some (.write (s.position i) value)) 1 ∧ t.position = s.position := by
  obtain ⟨c, entry, view⟩ := view_exists s data valid i
  obtain ⟨routing, stored⟩ := view_invariants view valid
  obtain ⟨next, execution, _, _, _⟩ := Nodes.write_correct data c entry value view.2.1 routing stored
  exact ⟨⟨next.tree, s.position⟩, .write value view execution, rfl⟩

/-- Every legal rotation lifts with the fifteen-unit local maintenance charge.
Both the selected node and all inactive fingers retain their identities. -/
theorem rotate_witness {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) (side : IntervalMetadata.Maintenance.Side) (a b : Pointer.Config)
    (tree : a.tree = s.tree.erase) (key : a.key? = some (s.position i))
    (execution : Multifinger.perform side.opcode a = some b) :
    ∃ before after entry, View s i before.cursor entry ∧ Nodes.maintain side before = some after ∧
      after.cursor.erase = b := by
  obtain ⟨c, entry, view, erased⟩ := view_matches s data valid i a tree key
  obtain ⟨routing, stored⟩ := view_invariants view valid
  let before : Nodes.State α := ⟨c, (0, ⟨0, 0⟩), (0, ⟨0, 0⟩)⟩
  obtain ⟨after, localRun, nextShape, _, _, _, _⟩ := Nodes.implement side data before b
    (by simpa only [before, erased] using execution) routing stored
  exact ⟨before, after, entry, view, localRun, nextShape⟩

theorem rotate_exists {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) (side : IntervalMetadata.Maintenance.Side) (a b : Pointer.Config)
    (tree : a.tree = s.tree.erase) (key : a.key? = some (s.position i))
    (execution : Multifinger.perform side.opcode a = some b) :
    ∃ t, Step s i t none 15 ∧ t.tree.erase = b.tree ∧ t.position = s.position := by
  obtain ⟨before, after, entry, view, localRun, nextShape⟩ := rotate_witness s data valid i side a b tree key execution
  refine ⟨⟨after.cursor.tree, s.position⟩, .rotate side view localRun, ?_, rfl⟩
  rw [erase_tree, nextShape]

end RotationBST.TreeBuffer.Shared
