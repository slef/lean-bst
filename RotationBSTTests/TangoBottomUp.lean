module

public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.TangoBottomUp
open Tango MarkedTree Initialization

private def reference : Tree := balanced 7
private def worker : Policy reference := BottomUp.policy reference

-- Reverse changes within each request, retaining the original request order.
example : (BottomUp.log reference [] [0, 6, 3]).map PreferenceUpdate.key = [0, 1, 3, 6, 5, 3, 3] ∧
    (BottomUp.log reference [0, 6] [3]).map PreferenceUpdate.key = [3] := by
  decide +kernel

-- The complete physical program makes real rotations and returns the root
-- request to the root. Repetitions and later direction changes remain valid.
example : ((worker.run [0, 6, 3]).1.tree, (worker.run [0, 6, 3]).2) = (reference, 8) ∧
    (worker.run [0, 6, 3, 3, 0, 6]).2 = 14 := by
  decide +kernel

-- Pausing after two requests and resuming on the returned marked tree gives
-- exactly the same final marks, shape, and summed rotation count.
example :
    let first := worker.run [0, 6]
    let rest := worker.runFrom [0, 6] first.1 [3, 3, 0, 6]
    worker.run [0, 6, 3, 3, 0, 6] = (rest.1, first.2 + rest.2) := by
  decide +kernel

-- Canonical agreement concerns all reference marks, not only tree size.
example : (initial reference).applyPreferences (BottomUp.log reference [] [0, 6, 3, 3, 0, 6]) =
    canonical reference 0 [0, 6, 3, 3, 0, 6] := by
  decide +kernel

-- Later switches are counted from actual intermediate marks in the reordered
-- execution; reversing assignments must not turn them into initializations.
example : firstCount (canonical reference 0 [0, 6]) (BottomUp.log reference [0, 6] [3, 3, 0, 6]) = 0 ∧
    laterCount (canonical reference 0 [0, 6]) (BottomUp.log reference [0, 6] [3, 3, 0, 6]) = 2 := by
  decide +kernel

private def targetSize (s : MarkedTree) (key : Nat) (next : Bool) : Nat :=
  match s.locateKey key with
  | some (.node l r _ _, fs) => (Context.plug (Context.componentAddress fs).2 (.node l r (!next) next)).region.size
  | _ => 0

-- Before the parent is attached upward, its first join stays local. The
-- top-down counterpart includes its ancestor and cannot use the same bound.
example :
    targetSize ((initial reference).setPreference 0 true) 1 true = 2 ∧
    targetSize ((initial reference).setPreference 3 true) 1 true = 3 ∧
    heightAt reference 1 = 2 := by
  decide +kernel

example : worker.run [] = (initial reference, 0) ∧
    ((BottomUp.policy (balanced 1)).run [0, 0, 0]).2 = 0 := by
  decide +kernel

-- The proved run contract applies to every valid future sequence, while
-- keeping the evolving first-join term explicit.
example (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    ((worker.run xs).2 : ℝ) ≤ firstLogCharge (initial reference) (BottomUp.log reference [] xs) +
      Wilber.interleave reference xs * (14 * Real.logb 2 (height reference) + 4) +
      xs.length * (3 * Real.logb 2 (height reference) + 1) := by
  exact BottomUp.separated_run_bound worker (fun _ _ _ => rfl) xs valid

-- The only nonlocal first join can genuinely exceed its local credit.
-- Two observed ancestors prefer left; their three-node subtree is untouched.
private def small : Tree := balanced 3
private def attached : Tree := .node (.node small .nil) .nil

example : firstLogCharge (canonical attached 0 [4, 3])
    (BottomUp.log attached [4, 3] [0]) = 18 := by
  norm_num [firstLogCharge, firstAt, updateCharge, componentCharge, BottomUp.log,
    preferenceUpdates, canonical, initial, attached, small, balanced, Tree.size,
    Wilber.regions, Wilber.labels, Wilber.leftRequests, Wilber.rightRequests,
    locateKey, setPreference, Context.componentAddress, Context.Frame.marked,
    Context.plug, Context.Frame.fill, MarkedTree.region, MarkedTree.tree,
    Pointer.Lazy.Skeleton.size]
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.logb_pow]
  norm_num

example : firstCharge (BottomUp.log attached [4, 3] [0]) (localCredit attached) = 12 := by
  norm_num [firstCharge, BottomUp.log, preferenceUpdates, attached, small, balanced,
    Tree.size, Wilber.regions, Wilber.leftRequests, Wilber.rightRequests,
    localCredit, heightAt, height]

-- The attachment allowance handles that case for every continuation, with
-- no successful-charge or component-boundary premise.
example (xs : List Nat) (valid : ∀ x ∈ xs, x < attached.size) :
    firstLogCharge (canonical attached 0 [4, 3]) (BottomUp.log attached [4, 3] xs) ≤
      firstCharge (BottomUp.log attached [4, 3] xs) (localCredit attached) +
        xs.length * (14 * Real.logb 2 (height attached) + 4) := by
  exact BottomUp.Results.first_log_bound attached [4, 3] xs
    (by intro y member; simp at member; rcases member with rfl | rfl <;> decide +kernel)
    valid

-- The whole-run bound removes the firstLogCharge term, including for
-- incomplete reference levels and any offline starting shape.
example {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = 10) (run : Execution s xs t k) :
    ((((BottomUp.policy (balanced 10)).run xs).2 : ℝ) + xs.length) ≤ 42 * 10 +
      (70 * Real.logb 2 (Nat.log2 10 + 1) + 20) * (k + xs.length : Nat) := by
  exact BottomUp.Results.balanced_competitive 10 (BottomUp.policy (balanced 10)) (fun _ _ _ => rfl) size run

end RotationBST.Tests.TangoBottomUp
