module

public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.Locality
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.BottomUp
open MarkedTree Context Initialization Wilber

private theorem append_first_root (whole : MarkedTree) (fs : List Frame) (l r : MarkedTree)
    (next : Bool) (prior : List PreferenceUpdate)
    (after : whole.applyPreferences prior = plug fs (.node l r true true))
    (paths : whole.PathMarked)
    (paid : firstLogCharge whole prior ≤ firstCharge prior (localCredit whole.tree)) :
    let updates := prior ++ [⟨offset fs 0 + l.tree.size, none, next⟩]
    firstLogCharge whole updates ≤ firstCharge updates (localCredit whole.tree) +
      (14 * Real.logb 2 (height whole.tree) + 4) ∧
      (Boundary fs → firstLogCharge whole updates ≤ firstCharge updates (localCredit whole.tree)) := by
  have currentPaths : (plug fs (.node l r true true)).PathMarked := after ▸ applyPreferences_pathMarked whole prior paths
  have currentTree : (plug fs (.node l r true true)).tree = whole.tree := by rw [← after, applyPreferences_tree]
  have globalBound := first_root_global fs l r next currentPaths
  rw [currentTree] at globalBound
  have credit := localCredit_nonneg whole.tree (offset fs 0 + l.tree.size)
  have creditSum : firstCharge (prior ++ [⟨offset fs 0 + l.tree.size, none, next⟩]) (localCredit whole.tree) =
      firstCharge prior (localCredit whole.tree) + localCredit whole.tree (offset fs 0 + l.tree.size) := by
    rw [firstCharge_append]
    simp [firstCharge]
  dsimp only
  rw [firstLogCharge_append, after, creditSum]
  refine ⟨by linarith, ?_⟩
  intro boundary
  have bound := first_root_local fs l r next (pathMarked_focus fs _ currentPaths) boundary
  rw [currentTree] at bound
  linarith

/-- A first traversal of an unobserved subtree pays every interior join from
local credit. Only its root can attach to an existing ancestor component. -/
theorem initial_request_charge (t : Tree) (fs : List Frame) (x : Nat)
    (paths : (plug fs (initial t)).PathMarked) (valid : x < t.size) :
    let updates := (preferenceUpdates t (offset fs 0) [] x).reverse
    let whole := plug fs (initial t)
    firstLogCharge whole updates ≤ firstCharge updates (localCredit whole.tree) +
      (14 * Real.logb 2 (height whole.tree) + 4) ∧
      (Boundary fs → firstLogCharge whole updates ≤ firstCharge updates (localCredit whole.tree)) := by
  induction t generalizing fs x with
  | nil => simp [Tree.size] at valid
  | node l r il ir =>
    have hv : x < l.size + 1 + r.size := valid
    by_cases left : x < l.size
    · let childFrames := Frame.left (initial r) true true :: fs
      let prior := (preferenceUpdates l (offset fs 0) [] x).reverse
      let child := (initial l).applyFrom (offset fs 0) prior
      have childPaths : (plug childFrames (initial l)).PathMarked := paths
      have paid := (il childFrames x childPaths left).2 (show Boundary childFrames from rfl)
      have after : (plug fs (initial (.node l r))).applyPreferences prior =
          plug fs (.node child (initial r) true true) := by
        have effect := applyPreferences_plug childFrames (initial l) prior
          (by intro u member; simpa only [childFrames, offset, Frame.offset, initial_tree] using
            preferenceUpdates_bounds l (offset fs 0) [] x u (List.mem_reverse.mp member))
        exact effect
      have finish := append_first_root (plug fs (initial (.node l r))) fs child (initial r) true prior after paths paid
      have size : child.tree.size = l.size := by simp [child]
      have side : x ≤ l.size := by omega
      simpa only [preferenceUpdates, ite_eq_left hv, regions, List.filter_nil, List.map_nil, List.getLast?_nil,
        reduceCtorEq, ite_false, List.singleton_append, ite_eq_left left, leftRequests,
        List.reverse_cons, decide_eq_true side, size, prior, initial, childFrames, offset, Frame.offset] using finish
    · by_cases root : x = l.size
      · subst x
        have finish := append_first_root (plug fs (initial (.node l r))) fs (initial l) (initial r) true [] rfl paths
          (by simp [firstLogCharge, firstCharge])
        simpa [preferenceUpdates, hv, regions, firstCharge, firstLogCharge, initial] using finish
      · have right : x - l.size - 1 < r.size := by omega
        let childFrames := Frame.right (initial l) true true :: fs
        let prior := (preferenceUpdates r (offset fs 0 + l.size + 1) [] (x - l.size - 1)).reverse
        let child := (initial r).applyFrom (offset fs 0 + l.size + 1) prior
        have childPaths : (plug childFrames (initial r)).PathMarked := paths
        have paid := (ir childFrames (x - l.size - 1) childPaths right).2 (show Boundary childFrames from rfl)
        have after : (plug fs (initial (.node l r))).applyPreferences prior =
            plug fs (.node (initial l) child true true) := by
          have effect := applyPreferences_plug childFrames (initial r) prior
            (by intro u member; simpa only [childFrames, offset, Frame.offset, initial_tree] using
              preferenceUpdates_bounds r (offset fs 0 + l.size + 1) [] (x - l.size - 1) u (List.mem_reverse.mp member))
          simpa only [childFrames, plug, Frame.fill, offset, Frame.offset, initial_tree, initial] using effect
        have finish := append_first_root (plug fs (initial (.node l r))) fs (initial l) child false prior after paths
          (by simpa only [childFrames, plug, Frame.fill, offset, Frame.offset, initial_tree, initial] using paid)
        have side : ¬ x ≤ l.size := by omega
        simpa only [preferenceUpdates, ite_eq_left hv, regions, List.filter_nil, List.map_nil, List.getLast?_nil,
          reduceCtorEq, ite_false, List.singleton_append, ite_eq_right left, ite_eq_right root, rightRequests,
          List.reverse_cons, decide_eq_false side, initial_tree, prior, initial] using finish

end RotationBST.Tango.BottomUp
