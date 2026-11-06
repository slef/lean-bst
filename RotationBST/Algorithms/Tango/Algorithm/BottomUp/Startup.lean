module

public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.FirstRequest
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.BottomUp
open MarkedTree Context Initialization Wilber

private theorem append_seen_root (whole : MarkedTree) (fs : List Frame) (l r : MarkedTree)
    (old next : Bool) (prior : List PreferenceUpdate)
    (after : whole.applyPreferences prior = plug fs (.node l r (!old) old))
    (paid : firstLogCharge whole prior ≤ firstCharge prior (localCredit whole.tree) +
      (14 * Real.logb 2 (height whole.tree) + 4)) :
    let updates := prior ++ (if old = next then [] else [⟨offset fs 0 + l.tree.size, some old, next⟩])
    firstLogCharge whole updates ≤ firstCharge updates (localCredit whole.tree) +
      (14 * Real.logb 2 (height whole.tree) + 4) := by
  dsimp only
  rw [firstLogCharge_append, after, firstCharge_append]
  cases old <;> cases next <;>
    simpa [firstLogCharge, firstAt, locateKey_plug_root, firstCharge] using paid

/-- In bottom-up order, the first settings in any one request spend their
local credit plus at most one attachment charge for existing ancestors. -/
theorem request_first_charge (t : Tree) (past : List Nat) (fs : List Frame) (x : Nat)
    (history : ∀ y ∈ past, y < t.size)
    (paths : (plug fs (localCanonical t past)).PathMarked) (valid : x < t.size) :
    let updates := (preferenceUpdates t (offset fs 0) past x).reverse
    let whole := plug fs (localCanonical t past)
    firstLogCharge whole updates ≤ firstCharge updates (localCredit whole.tree) +
      (14 * Real.logb 2 (height whole.tree) + 4) := by
  induction t generalizing past fs x with
  | nil => simp [Tree.size] at valid
  | node l r il ir =>
    by_cases empty : past = []
    · subst past
      have initialEq : localCanonical (.node l r) [] = initial (.node l r) := by
        rw [localCanonical_eq _ [] (by simp), canonical_initial]
      simpa only [initialEq] using (initial_request_charge (.node l r) fs x (initialEq ▸ paths) valid).1
    · have hv : x < l.size + 1 + r.size := valid
      have filtered : past.filter (fun y => decide (y < l.size + 1 + r.size)) = past := by
        apply List.filter_eq_self.mpr
        intro y member
        simpa only [Tree.size, decide_eq_true_eq] using history y member
      cases last : (regions l.size (l.size + 1 + r.size) past).getLast? with
      | none =>
        have none := List.getLast?_eq_none_iff.mp last
        simp only [regions, filtered, List.map_eq_nil_iff] at none
        exact False.elim (empty none)
      | some old =>
        let L := localCanonical l (leftRequests l.size past)
        let R := localCanonical r (rightRequests l.size past)
        have parent : localCanonical (.node l r) past = .node L R (!old) old := by
          cases old <;> simp only [localCanonical, last, Bool.not_true, Bool.not_false, L, R]
        rw [parent] at paths ⊢
        have leftHistory : ∀ y ∈ leftRequests l.size past, y < l.size := by
          intro y member
          exact of_decide_eq_true (List.mem_filter.mp member).2
        have rightHistory : ∀ y ∈ rightRequests l.size past, y < r.size := by
          intro y member
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp member
          have root := of_decide_eq_true (List.mem_filter.mp hz).2
          have bound := history z (List.mem_filter.mp hz).1
          simp only [Tree.size] at bound
          omega
        by_cases left : x < l.size
        · let childFrames := Frame.left R (!old) old :: fs
          let prior := (preferenceUpdates l (offset fs 0) (leftRequests l.size past) x).reverse
          let child := L.applyFrom (offset fs 0) prior
          have paid := il (leftRequests l.size past) childFrames x leftHistory paths left
          have after : (plug fs (.node L R (!old) old)).applyPreferences prior =
              plug fs (.node child R (!old) old) := by
            exact applyPreferences_plug childFrames L prior
              (by intro u member; simpa only [childFrames, offset, Frame.offset, L, localCanonical_tree] using
                preferenceUpdates_bounds l (offset fs 0) (leftRequests l.size past) x u (List.mem_reverse.mp member))
          have finish := append_seen_root (plug fs (.node L R (!old) old)) fs child R old true prior after paid
          have size : child.tree.size = l.size := by simp [child, L]
          have side : x ≤ l.size := by omega
          by_cases same : old = true <;>
            simpa [preferenceUpdates, hv, last, left, side, same, size, prior, childFrames, offset, Frame.offset] using finish
        · by_cases root : x = l.size
          · subst x
            have paid : firstLogCharge (plug fs (.node L R (!old) old)) [] ≤
                firstCharge [] (localCredit (plug fs (.node L R (!old) old)).tree) +
                  (14 * Real.logb 2 (height (plug fs (.node L R (!old) old)).tree) + 4) := by
              simp only [firstLogCharge, firstCharge, List.filter_nil, List.map_nil, List.sum_nil, zero_add]
              have positive := Bounds.logb_nat_nonneg (height (plug fs (.node L R (!old) old)).tree)
              linarith
            have finish := append_seen_root (plug fs (.node L R (!old) old)) fs L R old true [] rfl paid
            by_cases same : old = true <;>
              simpa [preferenceUpdates, hv, last, same, L, localCanonical_tree] using finish
          · have right : x - l.size - 1 < r.size := by omega
            let childFrames := Frame.right L old (!old) :: fs
            let prior := (preferenceUpdates r (offset fs 0 + l.size + 1) (rightRequests l.size past) (x - l.size - 1)).reverse
            let child := R.applyFrom (offset fs 0 + l.size + 1) prior
            have paid := ir (rightRequests l.size past) childFrames (x - l.size - 1) rightHistory paths right
            have after : (plug fs (.node L R (!old) old)).applyPreferences prior =
                plug fs (.node L child (!old) old) := by
              have effect := applyPreferences_plug childFrames R prior
                (by intro u member; simpa only [childFrames, offset, Frame.offset, L, R, localCanonical_tree] using
                  (preferenceUpdates_bounds r (offset fs 0 + l.size + 1) (rightRequests l.size past)
                    (x - l.size - 1) u (List.mem_reverse.mp member)))
              simpa only [childFrames, plug, Frame.fill, offset, Frame.offset, L, localCanonical_tree] using effect
            have finish := append_seen_root (plug fs (.node L R (!old) old)) fs L child old false prior after
              (by simpa only [childFrames, plug, Frame.fill, offset, Frame.offset, L, localCanonical_tree] using paid)
            have side : ¬ x ≤ l.size := by omega
            by_cases same : old = false <;>
              simpa [preferenceUpdates, hv, last, left, root, side, same, prior, L, localCanonical_tree] using finish

end RotationBST.Tango.BottomUp
