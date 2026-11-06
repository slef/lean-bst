module

public import RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract
public import RotationBST.Models.Labelled.Cursor.Map.Basic
public import RotationBST.Models.Labelled.Intervals.Access.Correctness

@[expose] public section
namespace RotationBST.TreeBuffer.Nodes
open LabelledCursor

theorem route_routing {α : Type} (target : Nat) (c : Config (Entry α)) :
    (route target c).map (fun result => (result.1, result.2.map Entry.routing)) =
      IntervalMetadata.Access.route target (c.map Entry.routing) := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => rfl
  | node l e r =>
    cases chosen : Pointer.Routing.choose ⟨e.bounds.low, e.key, e.bounds.high⟩ target with
    | none => simp [route, IntervalMetadata.Access.route, Config.map, Config.read, LabelledTree.map, Entry.routing, chosen]
    | some direction =>
      cases direction with
      | left => cases l <;> simp [route, IntervalMetadata.Access.route, Config.map, Config.read,
          LabelledTree.map, Entry.routing, chosen, perform, Frame.map]
      | right => cases r <;> simp [route, IntervalMetadata.Access.route, Config.map, Config.read,
          LabelledTree.map, Entry.routing, chosen, perform, Frame.map]
      | parent =>
        cases cs with
        | nil => simp [route, IntervalMetadata.Access.route, Config.map, Config.read,
            LabelledTree.map, Entry.routing, chosen]
        | cons frame cs => cases frame <;> simp [route, IntervalMetadata.Access.route, Config.map, Config.read,
            LabelledTree.map, Entry.routing, chosen, perform, Frame.map]

theorem route_tree {α : Type} {target cost : Nat} {s t : Config (Entry α)}
    (execution : route target s = some (cost, t)) : t.tree = s.tree := by
  rcases s with ⟨focus, cs⟩
  cases focus with
  | nil => simp [route, Config.read] at execution
  | node l e r =>
    cases chosen : Pointer.Routing.choose ⟨e.bounds.low, e.key, e.bounds.high⟩ target with
    | none => simp [route, Config.read, chosen] at execution
    | some direction =>
      cases direction with
      | left =>
        cases l <;> simp [route, Config.read, chosen, perform] at execution
        obtain ⟨rfl, rfl⟩ := execution
        rfl
      | right =>
        cases r <;> simp [route, Config.read, chosen, perform] at execution
        obtain ⟨rfl, rfl⟩ := execution
        rfl
      | parent =>
        cases cs with
        | nil => simp [route, Config.read, chosen] at execution
        | cons frame cs =>
          cases frame <;> simp [route, Config.read, chosen, perform] at execution
          all_goals obtain ⟨rfl, rfl⟩ := execution; rfl

/-- Reading routing words and following a link leaves all buffer cells intact. -/
theorem route_preserves {α : Type} (data : Nat → α) {target cost : Nat} {s t : Config (Entry α)}
    (execution : route target s = some (cost, t)) (routing : Routing s) (stored : Stored data s) :
    cost = 4 ∧ Routing t ∧ Stored data t := by
  have run : IntervalMetadata.Access.route target (s.map Entry.routing) = some (cost, t.map Entry.routing) := by
    simpa only [execution, Option.map_some] using (route_routing target s).symm
  refine ⟨IntervalMetadata.Access.route_cost run, ?_, ?_⟩
  · simpa only [Routing, IntervalMetadata.Access.Canonical, map_tree, route_tree execution] using routing
  · simpa only [Stored, map_tree, ← erase_tree, route_tree execution] using stored

/-- Every pending different key has a charged route step on the actual combined
node representation, with both representation invariants retained. -/
theorem progress {α : Type} (data : Nat → α) (target : Nat) (c : Config (Entry α)) (entry : Entry α)
    (read : c.read = some entry) (routing : Routing c) (stored : Stored data c)
    (valid : target < c.erase.tree.size) (different : entry.key ≠ target) :
    ∃ next key, route target c = some (4, next) ∧ Pointer.Move c.erase next.erase ∧
      next.erase.key? = some key ∧
      LazyFinger.distance next.erase.tree key target + 1 = LazyFinger.distance c.erase.tree entry.key target ∧
      Routing next ∧ Stored data next := by
  obtain ⟨nextProjected, key, routed, physical, atKey, closer, _⟩ :=
    IntervalMetadata.Access.progress target (c.map Entry.routing) routing entry.key entry.bounds
      (by simp only [map_read, read, Option.map_some, Entry.routing])
      (by simpa only [map_erase] using valid) different
  have projected := route_routing target c
  rw [routed] at projected
  obtain ⟨⟨cost, next⟩, execution, projection⟩ := Option.map_eq_some_iff.mp projected
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj projection
  obtain ⟨_, fields, cells⟩ := route_preserves data execution routing stored
  refine ⟨next, key, execution, ?_, ?_, ?_, fields, cells⟩
  · simpa only [map_erase] using physical
  · simpa only [map_erase] using atKey
  · simpa only [map_erase] using closer

end RotationBST.TreeBuffer.Nodes
