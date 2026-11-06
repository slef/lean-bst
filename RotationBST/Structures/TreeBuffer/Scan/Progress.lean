module

public import RotationBST.Structures.TreeBuffer.Scan.Potential
public import RotationBST.Bounds.LazyFinger.WalkMetric
public import RotationBST.Models.Pointer.Routing.Correctness
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Scan

/-- The scan's distance-decreasing step is selected by local interval fields,
not by a search for a shortest-path witness. -/
theorem local_route (s : State) (valid : s.Valid) (pending : s.requests ≠ [])
    (cursor : Pointer.Config) (tree : cursor.tree = s.tree) (key : cursor.key? = some s.position)
    (view : Pointer.Routing.View) (fields : view.Valid cursor) (different : s.position ≠ s.target) :
    ∃ next position, Pointer.Routing.next view cursor s.target = some next ∧
      Step s { s with tree := next.tree, position := position } 1 0 := by
  have same : view.key = s.position := Option.some.inj (fields.2.1.symm.trans key)
  obtain ⟨next, position, chosen, move, nextKey, closer⟩ := Pointer.Routing.next_correct view cursor s.target fields
    (by rw [tree]; exact target_valid s valid pending) (by simpa only [same] using different)
  exact ⟨next, position, chosen, .move tree move key nextKey pending (by simpa only [tree, same] using closer)⟩

/-- Every pending scan has a legal next action. -/
theorem next_exists (s : State) (valid : s.Valid) (pending : s.requests ≠ []) :
    ∃ t, Step s t 1 0 := by
  by_cases arrived : s.position = s.target
  · exact ⟨s.afterVisit, .visit pending arrived⟩
  · obtain ⟨a, tree, key, _, _⟩ := Pointer.search_readonly s.tree s.position valid.1
    let view : Pointer.Routing.View := ⟨Pointer.offset a.context, s.position, Pointer.offset a.context + a.focus.size⟩
    obtain ⟨b, y, _, step⟩ := local_route s valid pending a tree key view ⟨rfl, key, rfl⟩ arrived
    exact ⟨{ s with tree := b.tree, position := y }, step⟩

/-- Once external rotations stop, a scan always finishes. -/
theorem finish (s : State) (valid : s.Valid) :
    ∃ t work, Trace s t work 0 ∧ t.requests = [] ∧ work ≤ potential s := by
  generalize amount : potential s = fuel
  induction fuel using Nat.strong_induction_on generalizing s with
  | ind fuel ih =>
    by_cases pending : s.requests ≠ []
    · obtain ⟨t, first⟩ := next_exists s valid pending
      have nextValid := first.valid valid
      have decrease := first.potential_bound valid
      have smaller : potential t < fuel := by omega
      obtain ⟨u, work, rest, done, bound⟩ := ih (potential t) smaller t nextValid rfl
      exact ⟨u, 1 + work, .step first rest, done, by omega⟩
    · exact ⟨s, 0, .refl, by simpa using pending, Nat.zero_le _⟩

theorem Step.size_eq {s t : State} {k r : Nat} (step : Step s t k r) : s.tree.size = t.tree.size := by
  cases step with
  | move tree move _ _ _ _ => exact congrArg Tree.size (tree.symm.trans move.tree_eq)
  | visit _ _ => rfl
  | rotate rotation => exact rotation.size_eq

theorem Trace.size_eq {s t : State} {k r : Nat} (trace : Trace s t k r) : s.tree.size = t.tree.size := by
  induction trace with
  | refl => rfl
  | step first _ ih => exact first.size_eq.trans ih

/-- Every change in the pending sequence removes exactly one charged cell. -/
theorem Step.progress {s t : State} {k r : Nat} (step : Step s t k r) :
    t.requests = s.requests ∨ (s.requests = s.target :: t.requests ∧ k = 1) := by
  cases step with
  | move tree move _ _ _ _ =>
    exact Or.inl (by simp only [State.requests, ← tree, move.tree_eq])
  | visit pending _ => exact Or.inr ⟨requests_cons _ pending, rfl⟩
  | rotate rotation => exact Or.inl (by simp only [State.requests, ← rotation.size_eq])

/-- Finishing a scan must pay for every pending cell. -/
theorem Trace.visits_le {s t : State} {k r : Nat} (trace : Trace s t k r) :
    s.requests.length ≤ k + t.requests.length := by
  induction trace with
  | refl => simp
  | step first _ ih =>
    rcases first.progress with unchanged | ⟨cons, cost⟩
    · rw [unchanged] at ih; omega
    · rw [cons, List.length_cons]; omega

theorem Trace.valid {s t : State} {k r : Nat} (trace : Trace s t k r) (valid : s.Valid) : t.Valid := by
  induction trace with
  | refl => exact valid
  | step first _ ih => exact ih (first.valid valid)

theorem Trace.append {s t u : State} {k r h q : Nat} (first : Trace s t k r) (last : Trace t u h q) :
    Trace s u (k + h) (r + q) := by
  induction first with
  | refl => simpa using last
  | step step _ ih => simpa only [Nat.add_assoc] using Trace.step step (ih last)

/-- Any finite interleaved prefix can be completed within the same total
linear bound once the external rotations stop. -/
theorem complete_after {s t : State} {work rotations : Nat} (trace : Trace s t work rotations)
    (valid : s.Valid) :
    ∃ u extra, Trace s u (work + extra) rotations ∧ u.requests = [] ∧
      work + extra ≤ 4 * s.tree.size + 3 * rotations := by
  obtain ⟨u, extra, rest, done, _⟩ := finish t (trace.valid valid)
  have complete : Trace s u (work + extra) rotations := by simpa using trace.append rest
  exact ⟨u, extra, complete, done, complete.cost valid⟩

end RotationBST.TreeBuffer.Scan
