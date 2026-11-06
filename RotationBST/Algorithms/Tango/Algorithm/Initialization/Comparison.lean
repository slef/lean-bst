module

public import RotationBST.Algorithms.Tango.Algorithm.Initialization.Execution
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Initialization
open MarkedTree Context

/-- The refined charge never exceeds the previous uniform update allowance. -/
theorem updateCharge_le (reference : MarkedTree) (key : Nat) (next : Bool)
    (paths : reference.PathMarked) (valid : key < reference.tree.size) :
    updateCharge reference key next ≤ 14 * Real.logb 2 (height reference.tree) + 4 := by
  obtain ⟨fs, l, r, cl, cr, located, source, target⟩ := locateKey_spec reference key next valid
  simp only [updateCharge, located]
  cases cl <;> cases cr
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · change componentCharge (componentAddress fs).2 l r next ≤ _
    let inner := (componentAddress fs).2
    let outer := (splitComponent fs).2
    have context : fs = inner ++ outer := by
      simpa only [inner, outer, componentAddress_inner] using (splitComponent_spec fs).1
    have after : reference.setPreference key next = plug outer (plug inner (.node l r (!next) next)) := by
      rw [target, context, plug_append]
    have targetPaths := after ▸ setPreference_pathMarked reference key next paths
    have size : (plug inner (.node l r (!next) next)).region.size ≤ height reference.tree := by
      have bound := (region_size_le_height _ (pathMarked_focus outer _ targetPaths)).trans (height_le_plug outer _)
      simpa only [← after, setPreference_tree] using bound
    have monotone := Splay.Updates.log_nat_mono size
    dsimp only [inner] at monotone
    have nonnegative := Bounds.logb_nat_nonneg (height reference.tree)
    by_cases empty : (if next then l else r) = .nil
    · simp only [componentCharge, ite_eq_left empty]
      linarith
    · simp only [componentCharge, ite_eq_right empty]
      linarith

/-- First settings retain their local savings when the entire charge log is
compared with the existing policy contract. -/
theorem logCharge_le (reference : MarkedTree) (updates : List PreferenceUpdate)
    (paths : reference.PathMarked) (valid : ∀ u ∈ updates, u.key < reference.tree.size) :
    logCharge reference updates ≤ updates.length * (14 * Real.logb 2 (height reference.tree) + 4) := by
  induction updates generalizing reference with
  | nil => simp [logCharge]
  | cons u us ih =>
    have first := updateCharge_le reference u.key u.next paths (valid u (by simp))
    have rest := ih (reference.setPreference u.key u.next) (setPreference_pathMarked reference u.key u.next paths)
      (by intro v member; simpa only [setPreference_tree] using valid v (by simp [member]))
    simp only [setPreference_tree] at rest
    simp only [logCharge, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

end RotationBST.Tango.Initialization
