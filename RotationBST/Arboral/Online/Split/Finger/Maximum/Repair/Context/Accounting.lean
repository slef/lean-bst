module

public import RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Context.Proofs
public import RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Frame.Accounting

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem maximumRepairContext_same (fs : List Frame) (h : Nat) (focus : Multiway) :
    maximumRepairContext h h focus fs = ⟨plug fs focus, h + fs.length, 0⟩ := by
  cases fs <;> simp [maximumRepairContext, plug]

/-- Each continuing step pays for itself by deleting one enclosing node. Only
the final step needs the fixed allowance, independently of cascade length. -/
theorem maximumRepairContext_one_level (fs : List Frame) {h : Nat} {focus : Multiway}
    (balanced : Balanced h focus) (ancestors : Valid (h + 1) fs)
    (left : ∀ f ∈ fs, IsRightFrame f) :
    (maximumRepairContext (h + 1) h focus fs).cost + 2 * (maximumRepairContext (h + 1) h focus fs).tree.nodes ≤
      2 * (plug fs focus).nodes + 16 := by
  induction fs generalizing h focus with
  | nil => simp [maximumRepairContext, plug]
  | cons f fs ih =>
    have head := left f (List.mem_cons_self ..)
    have tail := fun g hg => left g (List.mem_cons_of_mem _ hg)
    have step := maximumRepairFrame_balance balanced ancestors.1 head (by omega)
    have charge := maximumRepairFrame_cost (h + 1) h focus f head
    have charged : (match fs with
        | [] => (maximumRepairFrame (h + 1) h focus f).cost
        | _ :: _ => maximumRepairFrameOpenCost (h + 1) h focus f) ≤ 10 := by
      cases fs <;> simp only <;> omega
    have inputNodes := plug_nodes fs (f.fill focus)
    have afterNodes := plug_nodes fs (maximumRepairFrame (h + 1) h focus f).tree
    by_cases continues : (maximumRepairFrame (h + 1) h focus f).height = h + 1
    · have merge := maximumRepairFrame_merge focus ancestors.1 head continues
      have childBalance : Balanced (h + 1) (maximumRepairFrame (h + 1) h focus f).tree := by
        have result := step.1
        rw [continues] at result
        exact result
      have result := ih childBalance ancestors.2 tail
      have cheap : (match fs with
          | [] => (maximumRepairFrame (h + 1) h focus f).cost
          | _ :: _ => maximumRepairFrameOpenCost (h + 1) h focus f) ≤ 2 := by
        cases fs <;> simp only <;> omega
      simp only [maximumRepairContext, show h ≠ h + 1 by omega, ite_false, continues, plug]
      cases fs <;> simp_all +arith <;> omega
    · have restored : (maximumRepairFrame (h + 1) h focus f).height = h + 1 + 1 := by omega
      have nodes := maximumRepairFrame_nodes (h + 1) h focus f head
      simp only [maximumRepairContext, show h ≠ h + 1 by omega, ite_false, restored, maximumRepairContext_same, plug]
      cases fs <;> simp_all +arith <;> omega

/-- An arbitrary initial height gap costs linearly in that gap. Any subsequent
one-level cascade is paid from the multiway node reserve. -/
theorem maximumRepairContext_credit (fs : List Frame) {expected actual : Nat} {focus : Multiway}
    (balanced : Balanced actual focus) (ancestors : Valid expected fs)
    (left : ∀ f ∈ fs, IsRightFrame f) (shorter : actual ≤ expected) :
    (maximumRepairContext expected actual focus fs).cost + 2 * (maximumRepairContext expected actual focus fs).tree.nodes ≤
      2 * (plug fs focus).nodes + 6 * (expected - actual) + 26 := by
  by_cases same : actual = expected
  · subst actual
    rw [maximumRepairContext_same]
    simp
  cases fs with
  | nil => simp [maximumRepairContext, plug]; omega
  | cons f fs =>
    have head := left f (List.mem_cons_self ..)
    have tail := fun g hg => left g (List.mem_cons_of_mem _ hg)
    have step := maximumRepairFrame_balance balanced ancestors.1 head shorter
    have charge := maximumRepairFrame_cost expected actual focus f head
    have nodes := maximumRepairFrame_nodes expected actual focus f head
    have charged : (match fs with
        | [] => (maximumRepairFrame expected actual focus f).cost
        | _ :: _ => maximumRepairFrameOpenCost expected actual focus f) ≤ 4 * (expected + 1 - actual) + 2 := by
      cases fs <;> simp only <;> omega
    have paid : (maximumRepairContext (expected + 1) (maximumRepairFrame expected actual focus f).height
        (maximumRepairFrame expected actual focus f).tree fs).cost +
        2 * (maximumRepairContext (expected + 1) (maximumRepairFrame expected actual focus f).height
          (maximumRepairFrame expected actual focus f).tree fs).tree.nodes ≤
        2 * (plug fs (maximumRepairFrame expected actual focus f).tree).nodes + 16 := by
      by_cases restored : (maximumRepairFrame expected actual focus f).height = expected + 1
      · rw [restored, maximumRepairContext_same]
        simp
      · have continues : (maximumRepairFrame expected actual focus f).height = expected := by omega
        have childBalance : Balanced expected (maximumRepairFrame expected actual focus f).tree := by
          have result := step.1
          rw [continues] at result
          exact result
        rw [continues]
        exact maximumRepairContext_one_level fs childBalance ancestors.2 tail
    have inputNodes := plug_nodes fs (f.fill focus)
    have afterNodes := plug_nodes fs (maximumRepairFrame expected actual focus f).tree
    simp only [maximumRepairContext, same, ite_false, plug]
    cases fs <;> simp_all +arith <;> omega

end RotationBST.Arboral.Split.Multiway.Finger
