module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.AbstractBridge

@[expose] public section
namespace RotationBST.Tango.BottomUp.Results
open MarkedTree Initialization Wilber

theorem setPreference_commute (s : MarkedTree) (x y : Nat) (a b : Bool)
    (different : x ≠ y) :
    (s.setPreference x a).setPreference y b = (s.setPreference y b).setPreference x a :=
  RotationBST.Tango.MarkedTree.setPreference_commute s x y a b different

theorem applyPreferences_reverse (s : MarkedTree) (updates : List PreferenceUpdate)
    (distinct : updates.Pairwise (fun u v => u.key ≠ v.key)) :
    s.applyPreferences updates.reverse = s.applyPreferences updates :=
  RotationBST.Tango.MarkedTree.applyPreferences_reverse s updates distinct

theorem preferenceUpdates_reverse_canonical (t : Tree) (past : List Nat) (x : Nat)
    (history : ∀ y ∈ past, y < t.size) (valid : x < t.size) :
    (canonical t 0 past).applyPreferences (preferenceUpdates t 0 past x).reverse =
      canonical t 0 (past ++ [x]) :=
  RotationBST.Tango.MarkedTree.preferenceUpdates_reverse_canonical t past x history valid

theorem request_spec (s : MarkedTree) (reference : Tree) (past : List Nat) (x : Nat)
    (maintained : Maintains s reference past) (history : ∀ y ∈ past, y < reference.size)
    (valid : x < reference.size) :
    Access s.tree (serve s reference past x).1.tree x (serve s reference past x).2 ∧
      Maintains (serve s reference past x).1 reference (past ++ [x]) ∧
      ((serve s reference past x).2 : ℝ) + (serve s reference past x).1.potential - s.potential ≤
        requestCharge reference past x :=
  RotationBST.Tango.BottomUp.request_spec s reference past x maintained history valid

theorem sequenceCharge_eq (reference : Tree) (past xs : List Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    sequenceCharge reference past xs = logCharge (canonical reference 0 past) (log reference past xs) +
      xs.length * (3 * Real.logb 2 (height reference) + 1) :=
  RotationBST.Tango.BottomUp.sequenceCharge_eq reference past xs history valid

theorem runFrom_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    (s : MarkedTree) (past xs : List Nat)
    (maintained : Maintains s reference past) (history : ∀ y ∈ past, y < reference.size)
    (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.runFrom past s xs).2 : ℝ) +
      (p.runFrom past s xs).1.potential - s.potential ≤ sequenceCharge reference past xs :=
  RotationBST.Tango.BottomUp.runFrom_bound p steps s past xs maintained history valid

theorem run_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.run xs).2 : ℝ) ≤
      logCharge (initial reference) (log reference [] xs) +
        xs.length * (3 * Real.logb 2 (height reference) + 1) :=
  RotationBST.Tango.BottomUp.run_bound p steps xs valid

theorem policy_exists (reference : Tree) :
    ∃ p : Policy reference,
      (∀ past s x, p.step past s x = serve s reference past x) ∧
      ∀ xs, (∀ x ∈ xs, x < reference.size) →
        ((p.run xs).2 : ℝ) ≤ logCharge (initial reference) (log reference [] xs) +
          xs.length * (3 * Real.logb 2 (height reference) + 1) :=
  RotationBST.Tango.BottomUp.policy_exists reference

theorem log_canonical (reference : Tree) (past xs : List Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    (canonical reference 0 past).applyPreferences (log reference past xs) =
      canonical reference 0 (past ++ xs) :=
  RotationBST.Tango.BottomUp.log_canonical reference past xs history valid

theorem firstCharge_log (reference : Tree) (past xs : List Nat) (w : Nat → ℝ) :
    firstCharge (log reference past xs) w = firstCharge (preferenceLog reference past xs) w :=
  RotationBST.Tango.BottomUp.firstCharge_log reference past xs w

theorem balanced_remainingCharge (n : Nat) (past xs : List Nat)
    (valid : ∀ key ∈ xs, key < n) :
    firstCharge (log (balanced n) past xs) (localCredit (balanced n)) ≤
      42 * n - observedCharge (balanced n) 0 past (localCredit (balanced n)) :=
  RotationBST.Tango.BottomUp.balanced_remainingCharge n past xs valid

theorem firstCount_generated (t : Tree) (past xs : List Nat)
    (history : ∀ x ∈ past, x < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    firstCount (canonical t 0 past) (log t past xs) + initializations t past =
      initializations t (past ++ xs) :=
  RotationBST.Tango.BottomUp.firstCount_generated t past xs history valid

theorem laterCount_generated (t : Tree) (past xs : List Nat)
    (history : ∀ x ∈ past, x < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    laterCount (canonical t 0 past) (log t past xs) + interleave t past =
      interleave t (past ++ xs) :=
  RotationBST.Tango.BottomUp.laterCount_generated t past xs history valid

theorem generated_split (reference : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    logCharge (initial reference) (log reference [] xs) =
      firstLogCharge (initial reference) (log reference [] xs) +
        interleave reference xs * (14 * Real.logb 2 (height reference) + 4) :=
  RotationBST.Tango.BottomUp.generated_split reference xs valid

theorem separated_competitive {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : reference.size = start.size) (execution : RotationBST.Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤ firstLogCharge (initial reference) (log reference [] xs) +
      (56 * Real.logb 2 (height reference) + 16) * (offline + xs.length : Nat) :=
  RotationBST.Tango.BottomUp.separated_competitive p steps size execution

theorem log_append (reference : Tree) (past xs ys : List Nat) :
    log reference past (xs ++ ys) = log reference past xs ++ log reference (past ++ xs) ys :=
  RotationBST.Tango.BottomUp.log_append reference past xs ys

theorem runFrom_append {reference : Tree} (p : Policy reference)
    (past : List Nat) (s : MarkedTree) (xs ys : List Nat) :
    p.runFrom past s (xs ++ ys) =
      let first := p.runFrom past s xs
      let rest := p.runFrom (past ++ xs) first.1 ys
      (rest.1, first.2 + rest.2) :=
  RotationBST.Tango.Policy.runFrom_append p past s xs ys

theorem first_log_bound (reference : Tree) (past xs : List Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    firstLogCharge (canonical reference 0 past) (log reference past xs) ≤
      firstCharge (log reference past xs) (localCredit reference) +
        xs.length * (14 * Real.logb 2 (height reference) + 4) :=
  RotationBST.Tango.BottomUp.first_log_bound reference past xs history valid

theorem startup_bound (reference : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    firstLogCharge (initial reference) (log reference [] xs) ≤
      localAllowance reference + xs.length * (14 * Real.logb 2 (height reference) + 4) :=
  RotationBST.Tango.BottomUp.startup_bound reference xs valid

theorem balanced_startup_remaining (n : Nat) (past xs : List Nat)
    (history : ∀ y ∈ past, y < n) (valid : ∀ x ∈ xs, x < n) :
    firstLogCharge (canonical (balanced n) 0 past) (log (balanced n) past xs) ≤
      42 * n - observedCharge (balanced n) 0 past (localCredit (balanced n)) +
        xs.length * (14 * Real.logb 2 (height (balanced n)) + 4) :=
  RotationBST.Tango.BottomUp.balanced_startup_remaining n past xs history valid

theorem linear_run_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.run xs).2 : ℝ) ≤ localAllowance reference +
      interleave reference xs * (14 * Real.logb 2 (height reference) + 4) +
        xs.length * (17 * Real.logb 2 (height reference) + 5) :=
  RotationBST.Tango.BottomUp.linear_run_bound p steps xs valid

theorem linear_competitive {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : reference.size = start.size) (execution : RotationBST.Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤ localAllowance reference +
      (70 * Real.logb 2 (height reference) + 20) * (offline + xs.length : Nat) :=
  RotationBST.Tango.BottomUp.linear_competitive p steps size execution

theorem balanced_competitive (n : Nat) (p : Policy (balanced n))
    (steps : ∀ past s x, p.step past s x = serve s (balanced n) past x)
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : start.size = n) (execution : RotationBST.Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤ 42 * n +
      (70 * Real.logb 2 (Nat.log2 n + 1) + 20) * (offline + xs.length : Nat) :=
  RotationBST.Tango.BottomUp.balanced_competitive n p steps size execution

theorem balanced_policy (n : Nat) :
    ∃ p : Policy (balanced n),
      (∀ past s x, p.step past s x = serve s (balanced n) past x) ∧
      ∀ (start finish : Tree) (xs : List Nat) (offline : Nat), start.size = n →
        RotationBST.Execution start xs finish offline →
          ((p.run xs).2 : ℝ) + xs.length ≤ 42 * n +
            (70 * Real.logb 2 (Nat.log2 n + 1) + 20) * (offline + xs.length : Nat) :=
  RotationBST.Tango.BottomUp.balanced_policy n

end RotationBST.Tango.BottomUp.Results

/-- info: abstract audit passed for `RotationBST.Tango.BottomUp.Results`: 24 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.BottomUp.Results allowing [RotationBST.Models.Rotation.Abstract,
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
  RotationBST.Algorithms.Tango.Algorithm.Initialization.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Reference.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Initialization.Local.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Algorithm.BottomUp.Definitions.Abstract]
