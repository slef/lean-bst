module

public import RotationBST.Algorithms.Tango.Algorithm.Initialization.Definitions.Abstract
public import RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Initialization
public import RotationBST.Algorithms.Tango.State.Preferences.Sequence
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Initialization
open MarkedTree Context

/-- The computed first-update charge retains the precise component located
by the compiler, so it can be accumulated over the actual reference log. -/
theorem first_update (s reference : MarkedTree) (key : Nat) (next : Bool)
    (l r : MarkedTree) (fs : List Frame)
    (same : s.nesting = reference.nesting) (valid : key < reference.tree.size)
    (located : reference.locateKey key = some (.node l r true true, fs)) :
    ((s.updatePreference reference key next).2 : ℝ) +
      (s.updatePreference reference key next).1.potential - s.potential ≤
        componentCharge (componentAddress fs).2 l r next := by
  obtain ⟨gs, a, b, cl, cr, found, source, target⟩ := locateKey_spec reference key next valid
  have eq := Option.some.inj (found.symm.trans located)
  cases eq
  let inner := (componentAddress fs).2
  have foundComponent : reference.componentAt (componentAddress fs).1 = some (plug inner (.node l r true true)) := by
    rw [source]
    exact componentAddress_spec fs _
  have nonempty : plug inner (.node l r true true) ≠ .nil := by
    by_cases empty : inner = []
    · simp [empty, plug]
    · exact plug_nonempty inner _ empty
  have computed := editAt_simulates (componentAddress fs).1 s reference
    (plug inner (.node l r true true)) (plug inner (.node l r (!next) next)).nesting
    (componentCharge inner l r next)
    (fun actual => actual.setMarksInPath inner l r true true next) same foundComponent nonempty
    (fun actual nested => setMarksInPath_initial_charge actual inner (componentAddress_unmarked fs) l r next nested)
  simpa only [updatePreference, found] using computed.2.2

/-- Every compiled update has the refined charge without weakening its
physical rotations or exact next nesting. -/
theorem update_spec (s reference : MarkedTree) (key : Nat) (next : Bool)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked)
    (valid : key < reference.tree.size) :
    (s.updatePreference reference key next).1.nesting = (reference.setPreference key next).nesting ∧
      Rotations s.tree (s.updatePreference reference key next).1.tree
        (s.updatePreference reference key next).2 ∧
      ((s.updatePreference reference key next).2 : ℝ) +
        (s.updatePreference reference key next).1.potential - s.potential ≤ updateCharge reference key next := by
  obtain ⟨nested, rotations, bound⟩ := updatePreference_spec s reference key next same paths valid
  refine ⟨nested, rotations, ?_⟩
  obtain ⟨fs, l, r, cl, cr, located, _, _⟩ := locateKey_spec reference key next valid
  simp only [updateCharge, located]
  cases cl <;> cases cr
  · exact bound
  · exact bound
  · exact bound
  · exact first_update s reference key next l r fs same valid located

/-- The precise update charges telescope against the actual BST potential. -/
theorem log_spec (s reference : MarkedTree) (updates : List PreferenceUpdate)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked)
    (valid : ∀ update ∈ updates, update.key < reference.tree.size) :
    (s.updatePreferences reference updates).1.nesting = (reference.applyPreferences updates).nesting ∧
      Rotations s.tree (s.updatePreferences reference updates).1.tree (s.updatePreferences reference updates).2 ∧
      ((s.updatePreferences reference updates).2 : ℝ) +
        (s.updatePreferences reference updates).1.potential - s.potential ≤ logCharge reference updates := by
  induction updates generalizing s reference with
  | nil => exact ⟨same, .refl, by simp [updatePreferences, logCharge]⟩
  | cons u us ih =>
    obtain ⟨nested, first, ba⟩ := update_spec s reference u.key u.next same paths (valid u (by simp))
    obtain ⟨finalNesting, remaining, bb⟩ := ih (s.updatePreference reference u.key u.next).1
      (reference.setPreference u.key u.next) nested (setPreference_pathMarked reference u.key u.next paths)
      (by intro v hv; simpa only [setPreference_tree] using valid v (by simp [hv]))
    refine ⟨finalNesting, first.append remaining, ?_⟩
    simp only [updatePreferences, logCharge, Nat.cast_add]
    linarith

theorem logCharge_append (reference : MarkedTree) (xs ys : List PreferenceUpdate) :
    logCharge reference (xs ++ ys) = logCharge reference xs + logCharge (reference.applyPreferences xs) ys := by
  induction xs generalizing reference with
  | nil => simp [logCharge, applyPreferences]
  | cons u us ih => simp [logCharge, applyPreferences, ih, add_assoc]

end RotationBST.Tango.Initialization
