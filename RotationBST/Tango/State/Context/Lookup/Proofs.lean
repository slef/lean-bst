module

public import RotationBST.Tango.State.Context.Lookup.Abstract
public import RotationBST.Tango.State.Context.Localization

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

/-- Locate a fringe occurrence by index, retaining the exact effect of replacing
it. In particular, equal subtree shapes at other positions are left alone. -/
theorem locateIndex_spec (s child : MarkedTree) (i : Nat)
    (atIndex : s.fringe[i]? = some child) (nonempty : child ≠ .nil) :
    ∃ fs : List Frame, locateIndex s i = some (child, fs) ∧
      fs ≠ [] ∧ Boundary fs ∧ plug fs child = s ∧
      ∀ target, (plug fs target).fringe = s.fringe.set i target := by
  induction s generalizing i with
  | nil =>
    have member := List.mem_of_getElem? atIndex
    have h : child = .nil := by simpa [fringe] using member
    exact False.elim (nonempty h)
  | node l r cl cr il ir =>
    let left := if cl then [l] else l.fringe
    let right := if cr then [r] else r.fringe
    change (left ++ right)[i]? = some child at atIndex
    change ∃ fs : List Frame, locateIndex (.node l r cl cr) i = some (child, fs) ∧
      fs ≠ [] ∧ Boundary fs ∧ plug fs child = .node l r cl cr ∧
      ∀ target, (plug fs target).fringe = (left ++ right).set i target
    by_cases hi : i < left.length
    · rw [List.getElem?_append_left hi] at atIndex
      have sets (target : MarkedTree) := List.set_append_left (t := right) i target hi
      cases cl
      · obtain ⟨fs, found, hn, hb, hp, hr⟩ := il i atIndex
        refine ⟨fs ++ [.left r false cr], ?_, by simp, ?_, ?_, ?_⟩
        · have h : i < l.fringe.length := by simpa [left] using hi
          simp [locateIndex, h, found]
        · cases fs with
          | nil => contradiction
          | cons f fs => exact hb
        · rw [plug_append, hp]; rfl
        · intro target
          rw [sets, plug_append]
          change (plug fs target).fringe ++ right = left.set i target ++ right
          rw [hr]; rfl
      · have iz : i = 0 := by simpa [left] using hi
        subst i
        have hc : l = child := by simpa [left] using atIndex
        subst child
        refine ⟨[.left r true cr], by simp [locateIndex], by simp, rfl, rfl, ?_⟩
        intro target
        rw [sets]
        rfl
    · have hi' : left.length ≤ i := by omega
      rw [List.getElem?_append_right hi'] at atIndex
      have sets (target : MarkedTree) := List.set_append_right (s := left) (t := right) i target hi'
      cases cr
      · obtain ⟨fs, found, hn, hb, hp, hr⟩ := ir (i - left.length) atIndex
        refine ⟨fs ++ [.right l false cl], ?_, by simp, ?_, ?_, ?_⟩
        · dsimp only [left] at hi found
          simp [locateIndex, hi, found]
        · cases fs with
          | nil => contradiction
          | cons f fs => exact hb
        · rw [plug_append, hp]; rfl
        · intro target
          rw [sets, plug_append]
          change left ++ (plug fs target).fringe = left ++ right.set (i - left.length) target
          rw [hr]; rfl
      · have iz : i - left.length = 0 := by
          obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp atIndex
          simpa [right] using h
        have hc : r = child := by simpa [right, iz] using atIndex
        subst child
        refine ⟨[.right l true cl], ?_, by simp, rfl, rfl, ?_⟩
        · dsimp only [left] at hi iz
          simp [locateIndex, hi, iz]
        · intro target
          rw [sets, iz]
          rfl

end RotationBST.Tango.Context
