module

public import RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Nodes.Bridge
public import RotationBST.Models.Labelled.Cursor.Lift
public import RotationBST.Models.Pointer.Search

@[expose] public section
namespace RotationBST.TreeBuffer.Shared
open LabelledCursor

theorem view_invariants {α : Type} {fingers : Nat} {s : State α fingers} {i : Fin fingers}
    {c : Config (Nodes.Entry α)} {entry : Nodes.Entry α} (view : View s i c entry)
    {data : Nat → α} (valid : s.Valid data) : Nodes.Routing c ∧ Nodes.Stored data c := by
  constructor
  · simpa only [Nodes.Routing, IntervalMetadata.Access.Canonical, map_tree, view.1,
      LabelledTree.erase_map] using valid.1
  · simpa only [Nodes.Stored, map_tree, ← erase_tree, view.1] using valid.2.1

/-- A nonempty labelled cursor reads the key denoted by its shape cursor. -/
theorem read_at_key {α : Type} (c : Config (Nodes.Entry α)) (routing : Nodes.Routing c)
    (key : Nat) (atKey : c.erase.key? = some key) :
    ∃ entry, c.read = some entry ∧ entry.key = key := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => simp [Config.erase, LabelledTree.erase, Pointer.Config.key?] at atKey
  | node l entry r =>
    have fields := IntervalMetadata.Access.read_valid
      ((Config.mk (.node l entry r) cs).map Nodes.Entry.routing) routing entry.key entry.bounds rfl
    have localKey := fields.2.1
    simp only [map_erase] at localKey
    have same : some entry.key = some key := localKey.symm.trans atKey
    exact ⟨entry, rfl, Option.some.inj same⟩

/-- Every persistent key has a coherent view of the current shared tree.
Existence of this view supplies no uncharged navigation operation. -/
theorem view_exists {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) :
    ∃ c entry, View s i c entry := by
  obtain ⟨a, b, cs, tree, key, _⟩ := Pointer.search_location s.tree.erase (s.position i) (valid.2.2 i)
  let shape : Pointer.Config := ⟨.node a b, cs⟩
  obtain ⟨c, whole, erased⟩ := lift_config shape s.tree tree.symm
  have routing : Nodes.Routing c := by
    simpa only [Nodes.Routing, IntervalMetadata.Access.Canonical, map_tree, whole,
      LabelledTree.erase_map] using valid.1
  have atKey : c.erase.key? = some (s.position i) := by
    rw [erased]
    exact congrArg some key
  obtain ⟨entry, read, key⟩ := read_at_key c routing (s.position i) atKey
  exact ⟨c, entry, whole, read, key⟩

theorem move_tree {α : Type} {op : Multifinger.Opcode} {c next : Config α}
    (execution : perform op c = some next) (move : Pointer.Move c.erase next.erase) : next.tree = c.tree := by
  apply Representation.Bridge.ext
  · simpa only [erase_tree] using move.tree_eq.symm
  · exact (perform_inorder execution).symm

end RotationBST.TreeBuffer.Shared
