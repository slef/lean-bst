module

public import RotationBST.Models.Labelled.Intervals.Access.Fields
public import RotationBST.Models.Pointer.Routing.Correctness
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.IntervalMetadata.Access
open LabelledCursor

/-- Erasing labels commutes with reading the stored routing view and moving. -/
theorem route_erase (target : Nat) (c : Config (Nat × Bounds)) (key : Nat) (bounds : Bounds)
    (read : c.read = some (key, bounds)) :
    (route target c).map (fun result => result.2.erase) =
      Pointer.Routing.next ⟨bounds.low, key, bounds.high⟩ c.erase target := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => simp [Config.read] at read
  | node l entry r =>
    cases Option.some.inj read
    cases chosen : Pointer.Routing.choose ⟨bounds.low, key, bounds.high⟩ target with
    | none => simp [route, Config.read, chosen, Pointer.Routing.next]
    | some direction =>
      cases direction with
      | left => cases l <;> simp [route, Config.read, chosen, Pointer.Routing.next,
          Pointer.Routing.perform, Config.erase, perform, LabelledTree.erase, Frame.erase]
      | right => cases r <;> simp [route, Config.read, chosen, Pointer.Routing.next,
          Pointer.Routing.perform, Config.erase, perform, LabelledTree.erase, Frame.erase]
      | parent =>
        cases cs with
        | nil => simp [route, Config.read, chosen, Pointer.Routing.next,
            Pointer.Routing.perform, Config.erase, perform, LabelledTree.erase]
        | cons frame cs => cases frame <;> simp [route, Config.read, chosen, Pointer.Routing.next,
            Pointer.Routing.perform, Config.erase, perform, LabelledTree.erase, Frame.erase]

theorem route_cost {target cost : Nat} {s t : Config (Nat × Bounds)}
    (execution : route target s = some (cost, t)) : cost = 4 := by
  have bound (o : Option (Config (Nat × Bounds)))
      (result : o.bind (fun next => some (4, next)) = some (cost, t)) : cost = 4 := by
    cases o <;> simp_all
  simp [route, Option.bind_eq_some_iff] at execution
  obtain ⟨key, bounds, _, direction, _, result⟩ := execution
  cases direction with
  | left => exact bound _ result
  | right => exact bound _ result
  | parent =>
    cases context : s.context with
    | nil => simp [context] at result
    | cons frame cs => cases frame <;> simp only [context] at result <;> exact bound _ result

/-- Successful routing preserves all labels and fields; no write or rotation
is hidden inside the four-unit route step. -/
theorem route_tree {target cost : Nat} {s t : Config (Nat × Bounds)}
    (execution : route target s = some (cost, t)) : t.tree = s.tree := by
  rcases s with ⟨focus, cs⟩
  cases focus with
  | nil => simp [route, Config.read] at execution
  | node l entry r =>
    rcases entry with ⟨key, bounds⟩
    cases chosen : Pointer.Routing.choose ⟨bounds.low, key, bounds.high⟩ target with
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

/-- Correct stored fields give an actual labelled move toward every different
existing target, paying for the field reads as well as navigation. -/
theorem progress (target : Nat) (c : Config (Nat × Bounds)) (canonical : Canonical c)
    (key : Nat) (bounds : Bounds) (read : c.read = some (key, bounds))
    (valid : target < c.erase.tree.size) (different : key ≠ target) :
    ∃ next nextKey, route target c = some (4, next) ∧ Pointer.Move c.erase next.erase ∧
      next.erase.key? = some nextKey ∧
      LazyFinger.distance next.erase.tree nextKey target + 1 =
        LazyFinger.distance c.erase.tree key target ∧ Canonical next := by
  obtain ⟨nextShape, nextKey, chosen, physical, nextAt, closer⟩ :=
    Pointer.Routing.next_correct _ c.erase target (read_valid c canonical key bounds read) valid different
  have mapped := route_erase target c key bounds read
  rw [chosen] at mapped
  obtain ⟨⟨cost, next⟩, execution, erased⟩ := Option.map_eq_some_iff.mp mapped
  have charge := route_cost execution
  subst cost
  subst nextShape
  refine ⟨next, nextKey, execution, physical, nextAt, closer, ?_⟩
  unfold Canonical
  rw [route_tree execution]
  exact canonical

end RotationBST.IntervalMetadata.Access
