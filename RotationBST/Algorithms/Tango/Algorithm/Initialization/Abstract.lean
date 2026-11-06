module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Algorithm.Initialization.AbstractBridge

@[expose] public section
namespace RotationBST.Tango.Algorithm.Initialization.Results
open RotationBST.Tango.Initialization MarkedTree Context Wilber

theorem update_spec (s reference : MarkedTree) (key : Nat) (next : Bool)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked)
    (valid : key < reference.tree.size) :
    (s.updatePreference reference key next).1.nesting = (reference.setPreference key next).nesting ∧
      Rotations s.tree (s.updatePreference reference key next).1.tree
        (s.updatePreference reference key next).2 ∧
      ((s.updatePreference reference key next).2 : ℝ) +
        (s.updatePreference reference key next).1.potential - s.potential ≤ updateCharge reference key next :=
  RotationBST.Tango.Initialization.update_spec s reference key next same paths valid

theorem log_spec (s reference : MarkedTree) (updates : List PreferenceUpdate)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked)
    (valid : ∀ update ∈ updates, update.key < reference.tree.size) :
    (s.updatePreferences reference updates).1.nesting = (reference.applyPreferences updates).nesting ∧
      Rotations s.tree (s.updatePreferences reference updates).1.tree (s.updatePreferences reference updates).2 ∧
      ((s.updatePreferences reference updates).2 : ℝ) +
        (s.updatePreferences reference updates).1.potential - s.potential ≤ logCharge reference updates :=
  RotationBST.Tango.Initialization.log_spec s reference updates same paths valid

theorem logCharge_append (reference : MarkedTree) (xs ys : List PreferenceUpdate) :
    logCharge reference (xs ++ ys) = logCharge reference xs + logCharge (reference.applyPreferences xs) ys :=
  RotationBST.Tango.Initialization.logCharge_append reference xs ys

theorem request_spec (s : MarkedTree) (reference : Tree) (past : List Nat) (x : Nat)
    (maintained : Maintains s reference past) (history : ∀ y ∈ past, y < reference.size)
    (valid : x < reference.size) :
    Access s.tree (s.serve reference past x).1.tree x (s.serve reference past x).2 ∧
      Maintains (s.serve reference past x).1 reference (past ++ [x]) ∧
      ((s.serve reference past x).2 : ℝ) + (s.serve reference past x).1.potential - s.potential ≤
        requestCharge reference past x :=
  RotationBST.Tango.Initialization.request_spec s reference past x maintained history valid

theorem sequenceCharge_eq (reference : Tree) (past xs : List Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    sequenceCharge reference past xs = logCharge (canonical reference 0 past) (preferenceLog reference past xs) +
      xs.length * (3 * Real.logb 2 (height reference) + 1) :=
  RotationBST.Tango.Initialization.sequenceCharge_eq reference past xs history valid

theorem runFrom_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = s.serve reference past x)
    (s : MarkedTree) (past xs : List Nat)
    (maintained : Maintains s reference past) (history : ∀ y ∈ past, y < reference.size)
    (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.runFrom past s xs).2 : ℝ) +
      (p.runFrom past s xs).1.potential - s.potential ≤ sequenceCharge reference past xs :=
  RotationBST.Tango.Initialization.runFrom_bound p steps s past xs maintained history valid

theorem run_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = s.serve reference past x)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.run xs).2 : ℝ) ≤
      logCharge (initial reference) (preferenceLog reference [] xs) +
        xs.length * (3 * Real.logb 2 (height reference) + 1) :=
  RotationBST.Tango.Initialization.run_bound p steps xs valid

theorem updateCharge_le (reference : MarkedTree) (key : Nat) (next : Bool)
    (paths : reference.PathMarked) (valid : key < reference.tree.size) :
    updateCharge reference key next ≤ 14 * Real.logb 2 (height reference.tree) + 4 :=
  RotationBST.Tango.Initialization.updateCharge_le reference key next paths valid

theorem logCharge_le (reference : MarkedTree) (updates : List PreferenceUpdate)
    (paths : reference.PathMarked) (valid : ∀ u ∈ updates, u.key < reference.tree.size) :
    logCharge reference updates ≤ updates.length * (14 * Real.logb 2 (height reference.tree) + 4) :=
  RotationBST.Tango.Initialization.logCharge_le reference updates paths valid

theorem policy_exists (reference : Tree) :
    ∃ p : Policy reference,
      (∀ past s x, p.step past s x = s.serve reference past x) ∧
      ∀ xs, (∀ x ∈ xs, x < reference.size) →
        ((p.run xs).2 : ℝ) ≤ logCharge (initial reference) (preferenceLog reference [] xs) +
          xs.length * (3 * Real.logb 2 (height reference) + 1) :=
  RotationBST.Tango.Initialization.policy_exists reference

theorem virgin_step (reference : MarkedTree) (key : Nat) (next : Bool)
    (valid : key < reference.tree.size) :
    virginCount (reference.setPreference key next) + (if firstAt reference key then 1 else 0) =
      virginCount reference :=
  RotationBST.Tango.Initialization.virgin_step reference key next valid

theorem virgin_log (reference : MarkedTree) (updates : List PreferenceUpdate)
    (valid : ∀ u ∈ updates, u.key < reference.tree.size) :
    firstCount reference updates + virginCount (reference.applyPreferences updates) = virginCount reference :=
  RotationBST.Tango.Initialization.virgin_log reference updates valid

theorem virgin_canonical (t : Tree) (past : List Nat) (history : ∀ x ∈ past, x < t.size) :
    virginCount (canonical t 0 past) + initializations t past = t.size :=
  RotationBST.Tango.Initialization.virgin_canonical t past history

theorem firstCount_generated (t : Tree) (past xs : List Nat)
    (history : ∀ x ∈ past, x < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    firstCount (canonical t 0 past) (preferenceLog t past xs) + initializations t past =
      initializations t (past ++ xs) :=
  RotationBST.Tango.Initialization.firstCount_generated t past xs history valid

theorem laterCount_generated (t : Tree) (past xs : List Nat)
    (history : ∀ x ∈ past, x < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    laterCount (canonical t 0 past) (preferenceLog t past xs) + interleave t past =
      interleave t (past ++ xs) :=
  RotationBST.Tango.Initialization.laterCount_generated t past xs history valid

theorem logCharge_split (reference : MarkedTree) (updates : List PreferenceUpdate)
    (valid : ∀ u ∈ updates, u.key < reference.tree.size) :
    logCharge reference updates = firstLogCharge reference updates +
      laterCount reference updates * (14 * Real.logb 2 (height reference.tree) + 4) :=
  RotationBST.Tango.Initialization.logCharge_split reference updates valid

theorem firstLogCharge_le (reference : MarkedTree) (updates : List PreferenceUpdate)
    (paths : reference.PathMarked) (valid : ∀ u ∈ updates, u.key < reference.tree.size) :
    firstLogCharge reference updates ≤ firstCount reference updates *
      (14 * Real.logb 2 (height reference.tree) + 4) :=
  RotationBST.Tango.Initialization.firstLogCharge_le reference updates paths valid

theorem generated_split (reference : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    logCharge (initial reference) (preferenceLog reference [] xs) =
      firstLogCharge (initial reference) (preferenceLog reference [] xs) +
        interleave reference xs * (14 * Real.logb 2 (height reference) + 4) :=
  RotationBST.Tango.Initialization.generated_split reference xs valid

theorem separated_run_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = s.serve reference past x)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.run xs).2 : ℝ) ≤ firstLogCharge (initial reference) (preferenceLog reference [] xs) +
      interleave reference xs * (14 * Real.logb 2 (height reference) + 4) +
      xs.length * (3 * Real.logb 2 (height reference) + 1) :=
  RotationBST.Tango.Initialization.separated_run_bound p steps xs valid

theorem separated_competitive {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = s.serve reference past x)
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : reference.size = start.size) (execution : RotationBST.Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤ firstLogCharge (initial reference) (preferenceLog reference [] xs) +
      (56 * Real.logb 2 (height reference) + 16) * (offline + xs.length : Nat) :=
  RotationBST.Tango.Initialization.separated_competitive p steps size execution

end RotationBST.Tango.Algorithm.Initialization.Results

/-- info: abstract audit passed for `RotationBST.Tango.Algorithm.Initialization.Results`: 20 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.Algorithm.Initialization.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Algorithms.Tango.Algorithm.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Algorithm.Request.Abstract,
  RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Defs,
  RotationBST.Algorithms.Tango.State.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Updates.Abstract,
  RotationBST.Bounds.Interleave.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Paths.Abstract,
  RotationBST.Bounds.Interleave.Wilber.Abstract,
  RotationBST.Bounds.Interleave.Transition.Defs,
  RotationBST.Algorithms.Tango.State.Preferences.Defs,
  RotationBST.Algorithms.Tango.State.Preferences.Lookup.Defs,
  RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.ComponentPath.Defs,
  RotationBST.Algorithms.Tango.State.ComponentPath.Address.Defs,
  RotationBST.Algorithms.Tango.State.Context.Defs,
  RotationBST.Algorithms.Tango.State.Context.Lookup.Defs,
  RotationBST.Algorithms.Tango.State.Context.Fringe.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Edits.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.Rebuild.Defs,
  RotationBST.Algorithms.Tango.State.Splay.Defs,
  RotationBST.Algorithms.Tango.State.Cut.Defs,
  RotationBST.Algorithms.Tango.State.Join.Defs,
  RotationBST.Models.Region.Abstract,
  RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Initialization.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Algorithm.Initialization.Definitions.Abstract]
