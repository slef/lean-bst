module

public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.Accounting
public import RotationBST.Algorithms.Tango.State.Context.Preference
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.BottomUp
open MarkedTree Context Initialization

theorem firstLogCharge_append (reference : MarkedTree) (xs ys : List PreferenceUpdate) :
    firstLogCharge reference (xs ++ ys) = firstLogCharge reference xs +
      firstLogCharge (reference.applyPreferences xs) ys := by
  induction xs generalizing reference with
  | nil => simp [firstLogCharge, applyPreferences]
  | cons u us ih => simp [firstLogCharge, applyPreferences, ih, add_assoc]

/-- A genuine component boundary has no retained unmarked ancestor frame. -/
theorem componentAddress_boundary (fs : List Frame) (boundary : Boundary fs) :
    (componentAddress fs).2 = [] := by
  cases fs with
  | nil => rfl
  | cons f fs =>
    have marked : f.marked = true := boundary
    simp [componentAddress, marked]

theorem locateKey_plug_root (fs : List Frame) (l r : MarkedTree) (cl cr : Bool) :
    (plug fs (.node l r cl cr)).locateKey (offset fs 0 + l.tree.size) = some (.node l r cl cr, fs) := by
  rw [locateKey_plug fs (.node l r cl cr) l.tree.size (by simp only [tree, Tree.size]; omega)]
  simp [locateKey]

/-- Root first settings charge the exact local component selected by the
compiled context, including any unmarked ancestors. -/
theorem first_root_exact (fs : List Frame) (l r : MarkedTree) (next : Bool) :
    firstLogCharge (plug fs (.node l r true true)) [⟨offset fs 0 + l.tree.size, none, next⟩] =
      componentCharge (componentAddress fs).2 l r next := by
  simp [firstLogCharge, firstAt, updateCharge, locateKey_plug_root]

/-- A first-setting root is paid by its own reference height when its
context begins at a component boundary. -/
theorem first_root_local (fs : List Frame) (l r : MarkedTree) (next : Bool)
    (paths : (MarkedTree.node l r true true).PathMarked) (boundary : Boundary fs) :
    firstLogCharge (plug fs (.node l r true true)) [⟨offset fs 0 + l.tree.size, none, next⟩] ≤
      localCredit (plug fs (.node l r true true)).tree (offset fs 0 + l.tree.size) := by
  rw [first_root_exact, componentAddress_boundary fs boundary]
  have nextPaths : (MarkedTree.node l r (!next) next).PathMarked := by
    cases next <;> simpa [PathMarked] using paths
  have size := region_size_le_height (MarkedTree.node l r (!next) next) nextPaths
  have logarithm := Splay.Updates.log_nat_mono size
  unfold localCredit
  rw [heightAt_plug fs (.node l r true true) l.tree.size (by simp only [tree, Tree.size]; omega)]
  simp only [tree, heightAt, lt_self_iff_false, ite_false, ite_true]
  simp only [tree] at logarithm
  by_cases empty : (if next then l else r) = .nil
  · simp only [componentCharge, ite_eq_left empty]
    have positive := Bounds.logb_nat_nonneg (height (.node l.tree r.tree))
    linarith
  · simp only [componentCharge, ite_eq_right empty, plug]
    linarith

/-- An attachment to an existing ancestor component still has one uniform
height charge. No assumption about a local boundary is used. -/
theorem first_root_global (fs : List Frame) (l r : MarkedTree) (next : Bool)
    (paths : (plug fs (.node l r true true)).PathMarked) :
    firstLogCharge (plug fs (.node l r true true)) [⟨offset fs 0 + l.tree.size, none, next⟩] ≤
      14 * Real.logb 2 (height (plug fs (.node l r true true)).tree) + 4 := by
  have bound := updateCharge_le (plug fs (.node l r true true)) (offset fs 0 + l.tree.size) next paths
    (key_in_plug fs (.node l r true true) l.tree.size (by simp only [tree, Tree.size]; omega))
  simpa only [firstLogCharge, firstAt, locateKey_plug_root, Bool.and_self, ite_true, add_zero] using bound

end RotationBST.Tango.BottomUp
